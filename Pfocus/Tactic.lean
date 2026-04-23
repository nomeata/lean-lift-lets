/-
Copyright (c) 2026 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license.

The `pfocus` tactic family.

This file defines the syntax category `pfocus` (the "pfocus mode"), the entry
tactic `pfocus => ...`, and every tactic that is valid inside pfocus mode.

The design closely mirrors `conv`:

* `pfocus` is a standalone syntax category declared via `declare_syntax_cat`,
  with its own sequence combinators (`pfocusSeq`) and bracketing form
  (`pfocusSeqBracketed`). This keeps the grammar isolated from `tactic` so
  that pfocus-mode tactics cannot accidentally be invoked at the top level.
* The entry tactic `pfocus =>` transforms the current goal `⊢ P` into
  `⊢ pfocus (fun p => p) P` and runs a `pfocusSeq`.
* Navigation tactics (`left`, `right`, `out`) only rearrange the outer
  context `C` and the focused proposition. They are implemented as direct
  manipulations of the goal using `pfocus_intro`/`pfocus_elim` as bridges.
* Action tactics (`closing`, `conv`, `apply`, etc.) make real progress on the
  focus using `pfocus_imp`. `PFocusable` is synthesized from the shape of the
  outer context.

The reader interested in writing their own custom tactic family can treat
this file as an annotated example: every non-obvious `MetaM` move is either
documented inline or reflects a choice called out in the README.
-/
import Lean
import Pfocus.Basic
import Pfocus.Delab
import Pfocus.Attr

namespace Pfocus

open Lean Elab Tactic Meta

/-! ## Syntax category

Pfocus-mode tactics live in their own syntax category so that they cannot be
confused with plain `tactic` syntax. The bracketed form mirrors the conv
category exactly.
-/

/-- The syntax category of tactics valid inside `pfocus => ...`. -/
declare_syntax_cat pfocus (behavior := both)

/-- A non-empty indented sequence of pfocus tactics, separated by newlines or `;`. -/
syntax pfocusSeq1Indented := sepBy1IndentSemicolon(pfocus)
/-- A brace-bracketed sequence of pfocus tactics. Useful for inline use. -/
syntax pfocusSeqBracketed := "{" withoutPosition(sepByIndentSemicolon(pfocus)) "}"
/-- Either form of pfocus tactic sequence. -/
syntax pfocusSeq := pfocusSeqBracketed <|> pfocusSeq1Indented

-- (The `paren` grouping form `( ... )` is intentionally omitted here because
-- of parser interactions with ordinary term-level tuples. Users who need
-- grouping can use bracketed `{ ... }` instead.)

/-! ## MetaM helpers

These helpers parse and construct the shape of pfocus goals. A pfocus goal is
a metavariable whose type is literally `pfocus C P` — the gadget defined in
`Pfocus.Basic` — with `C` in the "canonical composable form" built by the
instances of `PFocusable`.
-/

/--
Match a pfocus goal type `pfocus C P` and return the outer context and the
focused proposition. Fails with a clear error if the target is not a pfocus
goal.
-/
def matchPFocusGoal (e : Expr) : MetaM (Expr × Expr) := do
  -- Strip any enclosing `mdata` (for example the `noImplicitLambda`
  -- annotation that `have`/`let` tactics place around the updated target).
  let e := (← instantiateMVars e).consumeMData
  unless e.isAppOfArity ``Pfocus.pfocus 2 do
    throwError "not a pfocus goal:{indentExpr e}\nare you inside a `pfocus => ...` block?"
  let outer := e.appFn!.appArg!
  let focus := e.appArg!
  return (outer, focus)

initialize registerTraceClass `Pfocus.matchGoal

/-- `True : Prop` as an expression. -/
def mkTrueExpr : Expr := .const ``True []

/-- Alias for `mkTrueExpr`, used internally where the emphasis is on
comparing the focus against `True`. -/
private def trueExpr : Expr := mkTrueExpr

/-- `Prop` as an expression (i.e. `Sort 0`). -/
def mkPropExpr : Expr := .sort .zero

/--
Build `fun p : Prop => body`, using `p` as the binder name. `body` must refer
to `p` as `bvar 0` and may mention expressions from the surrounding context
(which should already be lifted by one bvar).
-/
def mkPropLam (body : Expr) : Expr :=
  .lam `p mkPropExpr body .default

/--
Given a β-normal outer `body` (referring to the focus as `bvar 0`) and two
proposition expressions `X Y : Prop`, along with a term `h : X → Y` and a term
`cx : body[X/bvar 0]`, build a term of type `body[Y/bvar 0]`.

This is the recursive core of pfocus's monotonicity. It handles:
* `body = bvar 0` (identity) — returns `h cx`.
* `body = l ∧ r` where exactly one side mentions the focus — recurses into
  that side and reassembles with `And.intro`.

The alternatives are rejected as errors; the tactic family only ever builds
outers fitting these patterns. Beta-reduction is applied eagerly.
-/
partial def buildMonoBody (body X Y h cx : Expr) : MetaM Expr := do
  let body := body.headBeta
  if body.isBVar && body.bvarIdx! == 0 then
    return .app h cx
  let_expr And l r := body | throwError "buildMono: unsupported structure{indentExpr body}"
  let lHasP := l.hasLooseBVar 0
  let rHasP := r.hasLooseBVar 0
  if lHasP == rHasP then
    throwError "buildMono: exactly one side of `And` should mention the focus{indentExpr body}"
  if lHasP then
    let cL ← mkAppM ``And.left #[cx]
    let cR ← mkAppM ``And.right #[cx]
    let newL ← buildMonoBody l X Y h cL
    mkAppM ``And.intro #[newL, cR]
  else
    let cL ← mkAppM ``And.left #[cx]
    let cR ← mkAppM ``And.right #[cx]
    let newR ← buildMonoBody r X Y h cR
    mkAppM ``And.intro #[cL, newR]

/--
Build the monotonicity term for an outer context, specialized to specific
source and target focus expressions. Returns an `Expr` of type
`(X → Y) → outer X → outer Y`.

Taking `X, Y` up-front means the returned term has a type that matches what
`pfocus_imp_raw` expects, without any implicit-argument inference.
-/
def buildMonoSpec (outer X Y : Expr) : MetaM Expr := do
  let outer ← whnf outer
  let .lam _ _ body _ := outer
    | throwError "buildMono: outer context is not a lambda{indentExpr outer}"
  let arrow ← mkArrow X Y
  withLocalDeclD `h arrow fun h => do
    let bodyX := body.instantiate1 X
    withLocalDeclD `cx bodyX fun cx => do
      let result ← buildMonoBody body X Y h cx
      mkLambdaFVars #[h, cx] result

/--
Get the current main goal's target as a pfocus goal.
-/
def getPFocusTarget : TacticM (MVarId × Expr × Expr) := do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let target ← mvarId.getType
    let _tup1 ← matchPFocusGoal target
    let (outer, focus) := _tup1
    return (mvarId, outer, focus)

/--
Replace the main goal with a new pfocus goal `pfocus newOuter newFocus`,
assigning the old goal via `pfocus_intro (pfocus_elim newMVar)`. This relies
on `(newOuter) (newFocus)` being β-definitionally equal to `(oldOuter)
(oldFocus)`, which the navigation tactics `left`, `right`, and `out` always
arrange.
-/
def replaceWithFocusGoal (newOuter newFocus : Expr) : TacticM Unit := do
  let _tup2 ← getPFocusTarget
  let (mvarId, oldOuter, oldFocus) := _tup2
  mvarId.withContext do
    let newType ← mkAppM ``Pfocus.pfocus #[newOuter, newFocus]
    let newMVar ← mkFreshExprSyntheticOpaqueMVar newType (← mvarId.getTag)
    -- `pfocus_elim newMVar : newOuter newFocus`, which is β-defeq to
    -- `oldOuter oldFocus`. The explicit args to `pfocus_intro` below force
    -- the result type to be `pfocus oldOuter oldFocus` (= old target).
    let elim ← mkAppM ``Pfocus.pfocus_elim #[newMVar]
    let intro ← mkAppOptM ``Pfocus.pfocus_intro
      #[some oldOuter, some oldFocus, some elim]
    mvarId.assign intro
    replaceMainGoal [newMVar.mvarId!]

/-! ## Entry tactic

`pfocus =>` enters pfocus mode by wrapping the current goal in the identity
outer context. A pfocus sequence then refines the goal. On exit, we strip the
outer wrapper automatically.
-/

/-- Enter pfocus mode. Doesn't assign `entryGoal`; that happens in
`exitPFocus` after the block's `extraDecls` have been collected. -/
def enterPFocus : TacticM PFocusState := do
  let entryGoal ← getMainGoal
  let entryDecl ← entryGoal.getDecl
  let entryLCtx := entryDecl.lctx
  entryGoal.withContext do
    let target := entryDecl.type
    let idOuter := mkPropLam (.bvar 0)
    let rootType ← mkAppM ``Pfocus.pfocus #[idOuter, target]
    let rootMVar ← mkFreshExprSyntheticOpaqueMVar rootType (← entryGoal.getTag)
    replaceMainGoal [rootMVar.mvarId!]
    return { entryGoal, entryLCtx, rootMVar := rootMVar.mvarId!, extraDecls := #[] }

/--
Check if an outer context `outer : Prop → Prop` is the identity `fun p : Prop => p`.
Used to detect when pfocus mode can exit trivially.
-/
def isIdOuter (outer : Expr) : MetaM Bool := do
  match (← whnf outer) with
  | .lam _ _ body _ => return body == mkBVar 0
  | _ => return false

/--
Walk `body` (the body of an outer lambda, with the focus as `bvar 0`) and
find the *innermost* `And` where the focus appears as a direct child.

Returns `(D_body, other, isLeft)` where:
* `D_body` is `body` with that innermost `And` replaced by just the focus
  (`bvar 0`). Wrapping it in `fun p => D_body` gives the outer context with
  one frame peeled off.
* `other` is the sibling of the focus in that innermost `And`, with bvars
  lowered to the outer scope.
* `isLeft` is true when the focus was the left operand, false otherwise.

The innermost `And` corresponds to the most recently pushed focus step
(`left` or `right`), which is exactly what `out` and `done` should undo.
-/
private partial def stripInnermost (body : Expr) : MetaM (Expr × Expr × Bool) := do
  let_expr And l r := body
    | throwError "outer body is not an `And`:{indentExpr body}"
  let lHasP := l.hasLooseBVar 0
  let rHasP := r.hasLooseBVar 0
  if lHasP && !rHasP then
    if l == .bvar 0 then
      return (.bvar 0, r.lowerLooseBVars 0 1, true)
    let (newL, other, isLeft) ← stripInnermost l
    return (mkApp2 (.const ``And []) newL r, other, isLeft)
  if rHasP && !lHasP then
    if r == .bvar 0 then
      return (.bvar 0, l.lowerLooseBVars 0 1, false)
    let (newR, other, isLeft) ← stripInnermost r
    return (mkApp2 (.const ``And []) l newR, other, isLeft)
  throwError "outer's `And` does not isolate the focus:{indentExpr body}"

/-- Strip the innermost frame off an outer lambda. -/
private def matchAndFrameImpl (outer : Expr) : MetaM (Expr × Expr × Bool) := do
  let outer ← whnf outer
  let .lam _ _ body _ := outer
    | throwError "expected `fun p => ...` outer context, got{indentExpr outer}"
  let (newBody, other, isLeft) ← stripInnermost body
  return (mkPropLam newBody, other, isLeft)

def outStep : TacticM Unit := do
  let _tup3 ← getPFocusTarget
  let (mvarId, outer, focus) := _tup3
  mvarId.withContext do
    if (← isIdOuter outer) then
      throwError "`out`: already at the top of pfocus mode; nothing to step out of"
    let (D, other, isLeft) ← matchAndFrameImpl outer
    let newFocus :=
      if isLeft then mkApp2 (.const ``And []) focus other
      else mkApp2 (.const ``And []) other focus
    replaceWithFocusGoal D newFocus

/--
Exit pfocus mode: close the wrapper around the current goal.

Repeatedly calls `outStep` until the outer context is the identity, then
replaces `pfocus id P` with just `P`.

Called automatically at the end of every `pfocus => ...` block. Users can
call `exit` explicitly to leave pfocus mode mid-block, for example inside
control combinators.
-/
def exitPFocus : PFocusM Unit := do
  -- If there's a remaining pfocus goal, β-unwrap it to its underlying
  -- proposition so the user can continue in regular tactic mode. (The
  -- whole point of pfocus is that `pfocus C P` is definitionally `C P`.)
  if !(← getGoals).isEmpty then
    let g ← getMainGoal
    let target := (← instantiateMVars (← g.getType)).consumeMData
    if target.isAppOfArity ``Pfocus.pfocus 2 then
      let outer := target.appFn!.appArg!
      let focus := target.appArg!
      g.withContext do
        let underlying := outer.beta #[focus]
        if ← isDefEq underlying trueExpr then
          let intro ← mkAppOptM ``Pfocus.pfocus_intro
            #[some outer, some focus, some (.const ``True.intro [])]
          g.assign intro
          replaceMainGoal []
        else
          let newMVar ← mkFreshExprSyntheticOpaqueMVar underlying (← g.getTag)
          let intro ← mkAppOptM ``Pfocus.pfocus_intro
            #[some outer, some focus, some newMVar]
          g.assign intro
          replaceMainGoal [newMVar.mvarId!]
  -- Now assign `entryGoal` — for the first time — by wrapping `rootMVar`'s
  -- value with `let`-bindings for every decl that `have`/`let` added.
  -- Build a local context containing the extras (derived from the entry
  -- lctx) so that `mkLetFVars` can reach them.
  let state ← get
  let extLCtx := state.extraDecls.foldl (init := state.entryLCtx) fun lctx d =>
    lctx.mkLetDecl d.fvarId d.userName d.type d.value
  withLCtx extLCtx #[] do
    let rootValue ← instantiateMVars (.mvar state.rootMVar)
    let extraFVars := state.extraDecls.map fun d => Expr.fvar d.fvarId
    let wrapped ← mkLetFVars (usedLetOnly := false) extraFVars rootValue
    state.entryGoal.assign wrapped

/-! ## Navigation tactics

These tactics are purely structural: they rearrange the outer context `C` and
the focused proposition without touching the actual "proposition being
proved". Equivalently, `newOuter newFocus` is always β-defeq to `oldOuter
oldFocus`.
-/

/-- Focus on the left conjunct: from `pfocus C (A ∧ B)` to `pfocus (fun p => C (p ∧ B)) A`. -/
syntax (name := left) "left" : pfocus
/-- Focus on the right conjunct: from `pfocus C (A ∧ B)` to `pfocus (fun p => C (A ∧ p)) B`. -/
syntax (name := right) "right" : pfocus
/-- Move one level out of the current focus, reversing the last `left` or `right`. -/
syntax (name := out) "out" : pfocus

/-- Parse the focus as `And A B`. -/
private def matchAnd (focus : Expr) : MetaM (Expr × Expr) := do
  let_expr And A B := focus
    | throwError "expected a conjunction as the focus, got{indentExpr focus}"
  return (A, B)

/-- β-normalize a `fun p => body` outer: if `body` is `(fun q => body') arg`,
reduce. This keeps outer contexts in a canonical β-normal form, which
simplifies `buildMono` and keeps the goal display readable. -/
private def betaNormOuter (outer : Expr) : Expr :=
  match outer with
  | .lam n t body bi => .lam n t body.headBeta bi
  | _ => outer

@[pfocus_tactic Pfocus.left] def evalLeft : PFocusTactic := fun _ => do
  let _tup5 ← getPFocusTarget
  let (mvarId, outer, focus) := _tup5
  mvarId.withContext do
    let _tup6 ← matchAnd focus
    let (A, B) := _tup6
    -- new outer body: `outer (bvar 0 ∧ B)`, β-reduced.
    let outer' := outer.liftLooseBVars 0 1
    let B' := B.liftLooseBVars 0 1
    let innerAnd := mkApp2 (.const ``And []) (.bvar 0) B'
    let newOuter := betaNormOuter (mkPropLam (mkApp outer' innerAnd))
    replaceWithFocusGoal newOuter A

@[pfocus_tactic Pfocus.right] def evalRight : PFocusTactic := fun _ => do
  let _tup7 ← getPFocusTarget
  let (mvarId, outer, focus) := _tup7
  mvarId.withContext do
    let _tup8 ← matchAnd focus
    let (A, B) := _tup8
    let outer' := outer.liftLooseBVars 0 1
    let A' := A.liftLooseBVars 0 1
    let innerAnd := mkApp2 (.const ``And []) A' (.bvar 0)
    let newOuter := betaNormOuter (mkPropLam (mkApp outer' innerAnd))
    replaceWithFocusGoal newOuter B

@[pfocus_tactic Pfocus.out] def evalOut : PFocusTactic := fun _ => outStep

/--
Apply `pfocus_imp` with a user-supplied implication `h : X → Y` to weaken
the focus from `Y` to `X`.

Given the current goal `pfocus C Y` and a proof `h : X → Y`, it creates a
new goal `pfocus C X` and assigns the old one to `pfocus_imp_raw (mono h)
newGoal`. The monotonicity witness is built from the outer's structure by
`buildMonoSpec`.
-/
def applyPFocusImp (h : Expr) (X : Expr) : PFocusM Unit := do
  let _tup15 ← getPFocusTarget
  let (mvarId, outer, focus) := _tup15
  mvarId.withContext do
    let newType ← mkAppM ``Pfocus.pfocus #[outer, X]
    let newMVar ← mkFreshExprSyntheticOpaqueMVar newType (← mvarId.getTag)
    let mono ← buildMonoSpec outer X focus
    let hMorphism := mkApp mono h
    let proof ← mkAppOptM ``Pfocus.pfocus_imp_raw
      #[some outer, some X, some focus, some hMorphism, some newMVar]
    mvarId.assign proof
    replaceMainGoal [newMVar.mvarId!]

/-! ### `exists`: commit a witness for an existential

`exists` on a focus `∃ x : α, P x` behaves like a `constructor` step:
a fresh metavariable `?x : α` is created and the focus becomes `P ?x`.
The metavariable can be assigned later by other tactics inside the pfocus
block (typically via `exact`, `rfl`, `apply`, etc.).

Because a pfocus goal's *outer* doesn't change here, the whole transition
is just `pfocus_imp` with the morphism `fun p : P ?x => ⟨?x, p⟩`, which
takes `outer (P ?x)` back to `outer (∃ x, P x)`.
-/

/-- Introduce an existential witness mvar and focus on the body. -/
syntax (name := existsTac) "exists" : pfocus

@[pfocus_tactic Pfocus.existsTac] def evalExistsTac : PFocusTactic := fun _ => do
  let _tup ← getPFocusTarget
  let (mvarId, _, focus) := _tup
  mvarId.withContext do
    let focusW := focus.consumeMData
    unless focusW.isAppOfArity ``Exists 2 do
      throwError "`exists`: focus is not an existential:{indentExpr focus}"
    let α := focusW.appFn!.appArg!
    let P := focusW.appArg!
    -- Fresh witness mvar, in the same context as the pfocus goal.
    let xMVar ← mkFreshExprMVar α (userName := `x)
    -- New focus: `P ?x` (β-applied).
    let newFocus := P.beta #[xMVar]
    -- `h : P ?x → (∃ x, P x)` = `fun p => ⟨?x, p⟩`; feed to applyPFocusImp.
    let h ← withLocalDeclD `p newFocus fun p => do
      let pair ← mkAppOptM ``Exists.intro #[some α, some P, some xMVar, some p]
      mkLambdaFVars #[p] pair
    applyPFocusImp h newFocus

/-- Do nothing. Useful for empty pfocus sequences. -/
syntax (name := skip) "skip" : pfocus

@[pfocus_tactic Pfocus.skip] def evalSkip : PFocusTactic := fun _ => pure ()

/-- Print the current pfocus goal state. -/
syntax (name := traceState) "trace_state" : pfocus

@[pfocus_tactic Pfocus.traceState] def evalTraceState : PFocusTactic := fun _ => do
  let g ← getMainGoal
  logInfo m!"{g}"

/-! ### `done`

`done` is the natural companion of `closing`: after we have proved a piece of
a conjunction and the focus has been reduced to `True`, `done` steps out of
the enclosing `And` frame by absorbing the `True` via `true_and_elim` /
`and_true_elim`. It is a small miracle of type-class dispatch: we construct
the implication `B → True ∧ B` (or `A → A ∧ True`) and let `pfocus_imp`
relieve the goal. -/

/-- `done` discharges a `pfocus C True` goal by popping the outer `∧` frame. -/
syntax (name := doneTac) "done" : pfocus

/--
Recognize the outermost `And` layer of an outer context.

After β-normalization, our outers have shape `fun p => body` where `body` is
a conjunction `l ∧ r` with exactly one side mentioning `p`. We return the
inner outer `D` (a lambda that drills one layer deeper), the sibling `other`
(the side that does *not* mention `p`), and a boolean marking a left or
right frame.
-/
private def matchAndFrame (outer : Expr) : MetaM (Expr × Expr × Bool) :=
  matchAndFrameImpl outer

/--
Build `fun (o : other) => (⟨⟨⟩, o⟩ : True ∧ other)`, witnessing `other → True ∧ other`.
-/
private def mkTrueAndIntro (other : Expr) : MetaM Expr :=
  withLocalDeclD `o other fun o => do
    let pair ← mkAppOptM ``And.intro
      #[some trueExpr, some other, some (.const ``True.intro []), some o]
    mkLambdaFVars #[o] pair

/-- Build `fun (o : other) => (⟨o, ⟨⟩⟩ : other ∧ True)`. -/
private def mkAndTrueIntro (other : Expr) : MetaM Expr :=
  withLocalDeclD `o other fun o => do
    let pair ← mkAppOptM ``And.intro
      #[some other, some trueExpr, some o, some (.const ``True.intro [])]
    mkLambdaFVars #[o] pair

@[pfocus_tactic Pfocus.doneTac] def evalDone : PFocusTactic := fun _ => do
  let _tup9 ← getPFocusTarget
  let (mvarId, outer, focus) := _tup9
  mvarId.withContext do
    unless (← isDefEq focus trueExpr) do
      throwError "`done`: focus is not `True`:{indentExpr focus}"
    let _tup10 ← matchAndFrame outer
    let (D, other, isLeft) := _tup10
    let newType ← mkAppM ``Pfocus.pfocus #[D, other]
    let newMVar ← mkFreshExprSyntheticOpaqueMVar newType (← mvarId.getTag)
    let elim ← mkAppM ``Pfocus.pfocus_elim #[newMVar]
    -- Build the implication `other → (inner step applied to True)`.
    let h ← if isLeft then mkTrueAndIntro other else mkAndTrueIntro other
    -- Targets the step's conjunction, e.g. `And True other` or `And other True`.
    let stepAtTrue :=
      if isLeft then mkApp2 (.const ``And []) trueExpr other
      else mkApp2 (.const ``And []) other trueExpr
    -- Propagate `h : other → stepAtTrue` through `D` using a meta-constructed
    -- monotonicity witness. This avoids relying on `PFocusable` instance
    -- synthesis (which fails for outers containing β-redexes or shadowed
    -- binders).
    let monoD ← buildMonoSpec D other stepAtTrue
    let monoCall := mkApp2 monoD h elim
    let _tup11 ← matchPFocusGoal (← mvarId.getType)
    let (oldOuter, oldFocus) := _tup11
    let intro ← mkAppOptM ``Pfocus.pfocus_intro
      #[some oldOuter, some oldFocus, some monoCall]
    mvarId.assign intro
    replaceMainGoal [newMVar.mvarId!]

/-! ### `exit`

`exit` is the user-facing form of `exitPFocus`. It leaves pfocus mode,
replacing the `pfocus _ P` wrapper with `P`. The tactic `pfocus => ...`
calls `exit` implicitly at the end of the block. -/

/-- Leave pfocus mode early. Equivalent to a trailing `exit` at the end of a block. -/
syntax (name := exitTac) "exit" : pfocus

@[pfocus_tactic Pfocus.exitTac] def evalExit : PFocusTactic := fun _ => exitPFocus

/-! ### `next`

`next` navigates to the next "unfinished" leaf in the conjunction tree. It
repeatedly pops frames (via `done` when the focus is `True`, or `out`
otherwise) until it is on a left-frame, then goes `out`, `right`, and dives
into the leftmost leaf with repeated `left`.
-/

/-- Go to the next unfinished conjunct leaf in the tree. -/
syntax (name := nextTac) "next" : pfocus

/-- Repeatedly pop right-frames or completed subtrees. -/
private partial def nextPopRight : PFocusM Unit := do
  let _tup12 ← getPFocusTarget
  let (_, outer, focus) := _tup12
  if (← isIdOuter outer) then
    throwError "`next`: no more unfinished conjuncts"
  else if (← isDefEq focus trueExpr) then
    evalDone .missing
    nextPopRight
  else
    let _tup13 ← matchAndFrame outer
    let (_, _, isLeft) := _tup13
    if !isLeft then
      outStep
      nextPopRight

/-- Descend to the leftmost leaf of the current focus. -/
private partial def nextDescendLeft : PFocusM Unit := do
  let _tup14 ← getPFocusTarget
  let (_, _, focus) := _tup14
  if focus.and?.isSome then
    evalLeft .missing
    nextDescendLeft

@[pfocus_tactic Pfocus.nextTac] def evalNext : PFocusTactic := fun _ => do
  nextPopRight
  outStep
  evalRight .missing
  nextDescendLeft

/-! ## Action tactics: making progress on the focus -/

/-- Build `fun p : Prop => p`. Needed when the outer is identity. -/
private def idOuterExpr : Expr := mkPropLam (.bvar 0)

/-! ### `tactic => tac`: general escape hatch

Running a tactic on a *copy* of the current focus, capturing the resulting
proof term as an implication `(And of new goals) → focus`, and plugging that
implication into `pfocus_imp`.

This is the most general action: `apply`, `closing`, and `assumption` are
defined as special cases or wrappers around `tactic`.
-/

/-- `tactic => tac` runs a regular tactic `tac` against a copy of the current focus,
and updates the pfocus goal so that the produced subgoals become the new focus
(conjoined when there are many). If the tactic closes all goals, the focus
becomes `True` and a trailing `done` strips the outer frame. -/
syntax (name := tacticTac) "tactic" " => " tacticSeq : pfocus

/--
Build the conjunction of a list of propositions, or `True` if the list is empty.
Right-nested, so the proof structure is `⟨h1, h2, ..., hn⟩`.
-/
private def mkConjunction : List Expr → Expr
  | [] => trueExpr
  | [p] => p
  | p :: ps => mkApp2 (.const ``And []) p (mkConjunction ps)

/--
Build a proof of `mkConjunction ps` from proofs of each `p ∈ ps` (in order).
`components[i]` should be a proof of `ps[i]`.
-/
private def mkConjProof (ps : List Expr) (components : List Expr) : MetaM Expr := do
  match ps, components with
  | [], [] => return .const ``True.intro []
  | [_], [c] => return c
  | _p :: ps', c :: cs' =>
      let rest ← mkConjProof ps' cs'
      mkAppM ``And.intro #[c, rest]
  | _, _ => throwError "mkConjProof: length mismatch"

/--
Destructure a proof of `mkConjunction ps` into proofs of each component.
Returns a list of `Expr`s whose types are `ps`, all sharing the current
local context.

Rather than build destructors via `And.left`/`And.right`, we use `Prod.mk`-
style projections directly at the `Expr` level. For `[]` we return `[]`
unconditionally.
-/
private def projConj (ps : List Expr) (h : Expr) : MetaM (List Expr) := do
  match ps with
  | [] => return []
  | [_] => return [h]
  | _ :: ps' =>
      let left ← mkAppM ``And.left #[h]
      let right ← mkAppM ``And.right #[h]
      let rest ← projConj ps' right
      return left :: rest

/--
Core action: run `action` (a plain `TacticM` computation) on a fresh goal
whose type is the current focus, then fold the resulting open subgoals into
the new focus via `pfocus_imp`.

Contracts:
* `action` must not change the list of goals outside the single starting one.
* Any subgoals it returns must share the local context of the starting goal;
  otherwise the implication closure step fails (we check this and raise a
  useful error).
-/
def runActionOnFocus (action : MVarId → TacticM (List MVarId)) : PFocusM Unit := do
  let _tup16 ← getPFocusTarget
  let (mvarId, _, focus) := _tup16
  mvarId.withContext do
    -- Fresh goal with the current focus as its target.
    let focusMVar ← mkFreshExprSyntheticOpaqueMVar focus (← mvarId.getTag)
    -- Save and restore the global goal list around the action, since the
    -- action typically calls `setGoals` to install the focus as the only
    -- goal. After the action returns, we still need to manipulate the
    -- original pfocus goal.
    let savedGoals ← getGoals
    let subgoals ←
      try
        action focusMVar.mvarId!
      finally
        setGoals savedGoals
    -- Validate local-context stability. The implication we construct
    -- lives in the pfocus goal's context, so every produced subgoal must
    -- share that context exactly — no new fvars from `intro`, no cleared
    -- hypotheses, etc. If a pfocus action needs a temporary hypothesis,
    -- the user must close the goal within the action itself.
    let baseLCtx := (← mvarId.getDecl).lctx
    let checkSharedLCtx (g : MVarId) : TacticM Unit := do
      let gLCtx := (← g.getDecl).lctx
      unless gLCtx.isSubPrefixOf baseLCtx && baseLCtx.isSubPrefixOf gLCtx do
        throwError "\
          a pfocus action produced a subgoal whose local context differs \
          from the enclosing pfocus goal. This typically happens when a \
          tactic like `intro` introduces a new hypothesis that cannot be \
          propagated out. Close such goals inside the `tactic => ...` block.\
          \n\nOffending goal:{indentD (MessageData.ofGoal g)}"
    for g in subgoals do checkSharedLCtx g
    -- Build an implication `(∧ of subgoal types) → focus`.
    -- Rather than assigning each subgoal's mvar to a projection of the new
    -- hypothesis `h` (which is unsafe because `h` is not in those mvars'
    -- declared local contexts), we instantiate `focusMVar`'s partial proof
    -- and then do a plain `Expr` substitution of the subgoal mvars. This
    -- keeps the substitution purely at the term level.
    let subTypes ← subgoals.mapM fun g => g.getType
    let conj := mkConjunction subTypes
    let implProof ← withLocalDeclD `h conj fun h => do
      let parts ← projConj subTypes h
      let body ← instantiateMVars focusMVar
      let subst := subgoals.zip parts
      let body := body.replace fun e =>
        match e with
        | .mvar m =>
          match subst.find? (fun (g, _) => g == m) with
          | some (_, part) => some part
          | none => none
        | _ => none
      mkLambdaFVars #[h] body
    applyPFocusImp implProof conj
    -- When the action closed everything, the focus is now `True`. If there
    -- is an enclosing `And` frame, `done` strips it and re-focuses on the
    -- sibling. At the top level (outer = id) we simply stop: `exitPFocus`
    -- at the end of the block will unwrap `pfocus id True`, and the user
    -- is left with a trivial `True` remainder.
    if subgoals.isEmpty then
      let _tup17 ← getPFocusTarget
      let (_, outerAfter, _) := _tup17
      unless (← isIdOuter outerAfter) do
        evalDone .missing

@[pfocus_tactic Pfocus.tacticTac] def evalTacticTac : PFocusTactic := fun stx => do
  match stx with
  | `(pfocus| tactic => $code) =>
    runActionOnFocus fun gmv => do
      setGoals [gmv]
      evalTactic code
      return (← getGoals)
  | _ => throwUnsupportedSyntax

/-! ### `closing => tac`

`closing` is `tactic` with the additional promise that the tactic closes all
subgoals. If it does not, we error out.
-/

/-- `closing => tac` closes the entire focus by running `tac` as a regular tactic. -/
syntax (name := closingTac) "closing" " => " tacticSeq : pfocus

@[pfocus_tactic Pfocus.closingTac] def evalClosing : PFocusTactic := fun stx => do
  match stx with
  | `(pfocus| closing => $code) =>
    runActionOnFocus fun gmv => do
      setGoals [gmv]
      evalTactic code
      let rem ← getGoals
      unless rem.isEmpty do
        throwError "`closing =>` did not close all goals:\n{goalsToMessageData rem}"
      return []
  | _ => throwUnsupportedSyntax

/-! ### Convenience wrappers around `closing` -/

/-- `assumption` closes the focus using a hypothesis in the local context. -/
macro "assumption" : pfocus => `(pfocus| closing => assumption)
/-- `rfl` closes the focus by reflexivity. -/
macro "rfl" : pfocus => `(pfocus| closing => rfl)
/-- `grind` closes the focus using `grind`. -/
macro "grind" : pfocus => `(pfocus| closing => grind)
/-- `trivial` closes the focus using `trivial`. -/
macro "trivial" : pfocus => `(pfocus| closing => trivial)

/-! ### `apply e` -/

/-- `apply thm` applies a theorem to the focus; any resulting subgoals sharing
the current local context become the new focus (conjoined). -/
syntax (name := applyTac) "apply " term : pfocus

@[pfocus_tactic Pfocus.applyTac] def evalApply : PFocusTactic := fun stx => do
  match stx with
  | `(pfocus| apply $e) =>
    runActionOnFocus fun gmv => do
      setGoals [gmv]
      evalTactic (← `(tactic| apply $e))
      return (← getGoals)
  | _ => throwUnsupportedSyntax

/-! ### `conv =>`, `rw`, `simp`

Running `conv => cs` on the focus produces an equation `focus = focus'`. We
then use `Eq.mp` together with `pfocus_imp` to replace the focus with the
new RHS.
-/

/-- `conv => cs` rewrites the focus using conv-mode tactics. -/
syntax (name := convTac) "conv" " => " Lean.Parser.Tactic.Conv.convSeq : pfocus

@[pfocus_tactic Pfocus.convTac] def evalConv : PFocusTactic := fun stx => do
  match stx with
  | `(pfocus| conv => $code) =>
    let _tup17 ← getPFocusTarget
    let (mvarId, _, focus) := _tup17
    mvarId.withContext do
      -- Build conv goal `focus = ?rhs`, run `conv`, get `?rhs` and proof.
      let _tup18 ← Conv.convert focus (evalTactic code)
      let (rhs, eqProof) := _tup18
      -- `Eq.mpr` lifts `focus = rhs` to `rhs → focus`. The implicit args are
      -- `α := focus` and `β := rhs`.
      let h ← mkAppOptM ``Eq.mpr #[some focus, some rhs, some eqProof]
      applyPFocusImp h rhs
  | _ => throwUnsupportedSyntax

/-- `rw [rules]` rewrites the focus. Shorthand for `conv => rw [rules]`. -/
macro "rw " s:Lean.Parser.Tactic.rwRuleSeq : pfocus =>
  `(pfocus| conv => rw $s:rwRuleSeq)

/-- `simp` simplifies the focus. Shorthand for `conv => simp`. -/
macro "simp" : pfocus => `(pfocus| conv => simp)

-- Forwarding `simp [lemmas]` to `conv => simp [lemmas]` is possible with
-- more syntax-plumbing code; the MVP users can write
-- `conv => simp [lemma1, lemma2]` directly.

-- These dispatch by re-running the `conv` pfocus-tactic via `evalPfocusCat`,
-- which the full file defines further below. Circular: forward reference via
-- `evalTactic` + the general `conv` syntax.

/-! ### `have` and `let` passthroughs

These tactics just enrich the local context; they leave the focus
unchanged. We delegate to the regular `tactic` passthrough.
-/

/-!
### `have` and `let`

These extend the local context and leave the pfocus goal's type unchanged.
We do *not* rewrite the proof term with a `.letE` wrapper at each step;
instead we directly extend the current pfocus goal's local context and
record the decl so that `exitPFocus` can wrap the final proof once. This
keeps every intermediate proof term free of let-bindings.
-/

/-- `have h : t := v` extends the local context. -/
syntax (name := haveTac) "have " ident (" : " term)? " := " term : pfocus
/-- `let x : t := v` extends the local context with a let-binding. -/
syntax (name := letTac) "let " ident (" : " term)? " := " term : pfocus

/--
Core of `have`/`let` in pfocus: elaborate the type (or infer from value),
elaborate the value, allocate a fresh let-fvar, extend the current pfocus
goal's declared local context with it, and record it in the state.
-/
def addPFocusLetDecl (name : Name) (typeStx? : Option Syntax) (valueStx : Syntax) :
    PFocusM Unit := do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let expectedType ← match typeStx? with
      | some t => Lean.Elab.Term.elabType t
      | none   => mkFreshTypeMVar
    let value ← Lean.Elab.Term.elabTermEnsuringType valueStx expectedType
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let type ← instantiateMVars expectedType
    let value ← instantiateMVars value
    let fvarId ← mkFreshFVarId
    let decl ← mvarId.getDecl
    let newLCtx := decl.lctx.mkLetDecl fvarId name type value
    modifyMCtx fun mctx =>
      mctx.modifyExprMVarDecl mvarId fun d => { d with lctx := newLCtx }
    let newDecl : PFocusLetDecl :=
      { fvarId, userName := name, type, value }
    modify fun s => { s with extraDecls := s.extraDecls.push newDecl }

@[pfocus_tactic Pfocus.haveTac] def evalHaveTac : PFocusTactic := fun stx => do
  match stx with
  | `(pfocus| have $x:ident : $t:term := $v:term) =>
    addPFocusLetDecl x.getId (some t.raw) v.raw
  | `(pfocus| have $x:ident := $v:term) =>
    addPFocusLetDecl x.getId none v.raw
  | _ => throwUnsupportedSyntax
@[pfocus_tactic Pfocus.letTac] def evalLetTac : PFocusTactic := fun stx => do
  match stx with
  | `(pfocus| let $x:ident : $t:term := $v:term) =>
    addPFocusLetDecl x.getId (some t.raw) v.raw
  | `(pfocus| let $x:ident := $v:term) =>
    addPFocusLetDecl x.getId none v.raw
  | _ => throwUnsupportedSyntax
/-- `show P'` changes the focus to a definitionally-equal proposition. -/
syntax (name := showTac) "show " term : pfocus

@[pfocus_tactic Pfocus.showTac] def evalShow : PFocusTactic := fun stx => do
  match stx with
  | `(pfocus| show $t) =>
    let _tup19 ← getPFocusTarget
    let (mvarId, outer, _) := _tup19
    mvarId.withContext do
      let newFocus ← Term.elabType t
      let newType ← mkAppM ``Pfocus.pfocus #[outer, newFocus]
      -- Check defeq of the new pfocus type with the old (via `newFocus ≡ focus`).
      let newMVar ← mkFreshExprSyntheticOpaqueMVar newType (← mvarId.getTag)
      let _tup20 ← matchPFocusGoal (← mvarId.getType)
      let (oldOuter, oldFocus) := _tup20
      let elim ← mkAppM ``Pfocus.pfocus_elim #[newMVar]
      let intro ← mkAppOptM ``Pfocus.pfocus_intro
        #[some oldOuter, some oldFocus, some elim]
      mvarId.assign intro
      replaceMainGoal [newMVar.mvarId!]
  | _ => throwUnsupportedSyntax

/-! ## Entry-point tactic (top-level `tactic` category)

The `pfocus =>` tactic runs a pfocus sequence and then automatically exits.
-/

/--
`pfocus => ...` enters pfocus mode and runs the given pfocus tactic sequence.
Inside pfocus mode, the goal has the shape `⊢ pfocus C P`, which displays as
`⊢ ⇣ P`: the outer context `C` is hidden, and only the currently-focused
proposition `P` is shown.

Pfocus mode exits automatically at the end of the block. The remaining goal,
if any, is whatever is left of the original proposition after the focused
pieces have been discharged.
-/
syntax (name := pfocusTac) "pfocus" " => " pfocusSeq : tactic

/--
Dispatch a single pfocus syntax tree to a handler registered via the
`@[pfocus_tactic]` attribute. Mirrors how `evalTactic` dispatches regular
tactic syntax via `@[tactic]`.
-/
partial def evalPfocusCat (stx : Syntax) : PFocusM Unit :=
  withRef stx do
    let kind := stx.getKind
    if kind == nullKind then
      for arg in stx.getArgs do evalPfocusCat arg
      return
    -- Expand any matching `macro` registered for this kind, then recurse.
    let macros := macroAttribute.getEntries (← getEnv) kind
    if let m :: _ := macros then
      let stx' ← adaptMacro m.value stx
      evalPfocusCat stx'
      return
    let handlers := pfocusTacticAttr.getEntries (← getEnv) kind
    match handlers with
    | h :: _ => h.value stx
    | [] => throwError m!"pfocus tactic '{kind}' has not been implemented"

/--
Walk an `sepBy1IndentSemicolon`-style sequence, calling `evalPfocusCat` on
each pfocus-category element and recording info for the separators.
-/
def evalPfocusSepByIndent (stx : Syntax) : PFocusM Unit := do
  for arg in stx.getArgs, i in *...stx.getArgs.size do
    if i % 2 == 0 then
      evalPfocusCat arg
    else
      saveTacticInfoForToken arg

/-- Evaluate a `pfocusSeq`, whether bracketed or indented. -/
def evalPfocusSeq (stx : Syntax) : PFocusM Unit := do
  if stx.getKind == ``pfocusSeqBracketed then
    evalPfocusSepByIndent stx[1]
  else
    evalPfocusSepByIndent stx[0]

@[tactic pfocusTac] def evalPfocus : Tactic := fun stx => do
  match stx with
  | `(tactic| pfocus => $code) => do
      let initState ← enterPFocus
      let runBody : PFocusM Unit := do
        evalPfocusSeq code
        exitPFocus
      runBody.run' initState
  | _ => throwUnsupportedSyntax

end Pfocus
