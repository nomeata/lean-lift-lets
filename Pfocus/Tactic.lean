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
  -- annotation that `have`/`let` tactics place around the updated target)
  -- and any outstanding mvar indirection.
  let e := (← instantiateMVars e).consumeMData
  unless e.isAppOfArity ``Pfocus.pfocus 3 do
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
      #[none, some oldOuter, some oldFocus, some elim]
    mvarId.assign intro
    replaceMainGoal [newMVar.mvarId!]

/-! ## Entry tactic

`pfocus =>` enters pfocus mode by wrapping the current goal in the identity
outer context. A pfocus sequence then refines the goal. On exit, we strip the
outer wrapper automatically.
-/

/-- Enter pfocus mode: replace the main goal `⊢ P` with `⊢ pfocus (fun p => p) P`. -/
def enterPFocus : TacticM Unit := do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let target ← mvarId.getType
    let idOuter := mkPropLam (.bvar 0)
    let newType ← mkAppM ``Pfocus.pfocus #[idOuter, target]
    let newMVar ← mkFreshExprSyntheticOpaqueMVar newType (← mvarId.getTag)
    -- `pfocus_elim newMVar : (fun p => p) target` = `target` (β-defeq).
    let elim ← mkAppM ``Pfocus.pfocus_elim #[newMVar]
    mvarId.assign elim
    replaceMainGoal [newMVar.mvarId!]

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
def exitPFocus : TacticM Unit := do
  -- Idempotent: do nothing if there is no remaining goal, or if the main
  -- goal is not a pfocus goal. The first case occurs when a predicate-focus
  -- `tactic =>` has already fully committed a witness and closed the `∃`.
  if (← getGoals).isEmpty then return
  let mvarIdInit ← getMainGoal
  let targetInit ← instantiateMVars (← mvarIdInit.getType)
  unless targetInit.isAppOf ``Pfocus.pfocus do return
  let (mvarId, outer, focus) ← getPFocusTarget
  -- β-reduce `outer focus` to get the underlying proposition, and emit that
  -- as the remaining goal. This is what the whole pfocus mode was
  -- wrapping: `pfocus C P` is definitionally `C P`. The structure of the
  -- outer (id / conjunction / existential / ...) doesn't matter here — any
  -- `C P` reduces to the same Prop up to β.
  mvarId.withContext do
    let underlying := outer.beta #[focus]
    -- `pfocus _ True` (after β) closes trivially; short-circuit so the user
    -- doesn't have to dispatch a leftover `True` goal.
    if ← isDefEq underlying trueExpr then
      let intro ← mkAppOptM ``Pfocus.pfocus_intro
        #[none, some outer, some focus, some (.const ``True.intro [])]
      mvarId.assign intro
      replaceMainGoal []
    else
      let newMVar ← mkFreshExprSyntheticOpaqueMVar underlying (← mvarId.getTag)
      let intro ← mkAppOptM ``Pfocus.pfocus_intro
        #[none, some outer, some focus, some newMVar]
      mvarId.assign intro
      replaceMainGoal [newMVar.mvarId!]

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

@[tactic left] def evalLeft : Tactic := fun _ => do
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

@[tactic right] def evalRight : Tactic := fun _ => do
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

@[tactic out] def evalOut : Tactic := fun _ => outStep

/-! ### `intro`: step into an existential

Turn `pfocus C (∃ x : α, P x)` into `pfocus (fun p : α → Prop => C (∃ x, p x))
(fun x => P x)`, shifting the focus from the whole existential to the body
predicate.

Once inside, `tactic => ...` handles the predicate focus specially (see
`runActionOnFocus`): it creates a fresh mvar `?x` for the bound variable and
lets the user either commit a witness or transform the predicate without
committing.
-/

/-- Step into an existential: focus on the body predicate. -/
syntax (name := introTac) "intro" : pfocus

@[tactic introTac] def evalIntroTac : Tactic := fun _ => do
  let _tup ← getPFocusTarget
  let (mvarId, outer, focus) := _tup
  mvarId.withContext do
    -- Expect `focus = @Exists α P`.
    let focus := focus.consumeMData
    unless focus.isAppOfArity ``Exists 2 do
      throwError "`intro`: focus is not an existential:{indentExpr focus}"
    let α := focus.appFn!.appArg!
    let P := focus.appArg!
    -- Build `fun p : α → Prop => outer (∃ x : α, p x)`, β-normalized.
    let predType ← mkArrow α mkPropExpr
    let outer' := outer.liftLooseBVars 0 1
    let α' := α.liftLooseBVars 0 1
    let u ← getLevel α
    let bodyExists := mkApp2 (.const ``Exists [u]) α' (.bvar 0)
    let newOuterBody := mkApp outer' bodyExists
    let newOuter := betaNormOuter (Expr.lam `p predType newOuterBody .default)
    let newType ← mkAppM ``Pfocus.pfocus #[newOuter, P]
    let newMVar ← mkFreshExprSyntheticOpaqueMVar newType (← mvarId.getTag)
    -- Close old goal: `pfocus_intro (pfocus_elim newMVar)`.
    let elim ← mkAppM ``Pfocus.pfocus_elim #[newMVar]
    let intro ← mkAppOptM ``Pfocus.pfocus_intro
      #[none, some outer, some focus, some elim]
    mvarId.assign intro
    replaceMainGoal [newMVar.mvarId!]

/-- Do nothing. Useful for empty pfocus sequences. -/
syntax (name := skip) "skip" : pfocus

@[tactic skip] def evalSkip : Tactic := fun _ => pure ()

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

@[tactic doneTac] def evalDone : Tactic := fun _ => do
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
      #[none, some oldOuter, some oldFocus, some monoCall]
    mvarId.assign intro
    replaceMainGoal [newMVar.mvarId!]

/-! ### `exit`

`exit` is the user-facing form of `exitPFocus`. It leaves pfocus mode,
replacing the `pfocus _ P` wrapper with `P`. The tactic `pfocus => ...`
calls `exit` implicitly at the end of the block. -/

/-- Leave pfocus mode early. Equivalent to a trailing `exit` at the end of a block. -/
syntax (name := exitTac) "exit" : pfocus

@[tactic exitTac] def evalExit : Tactic := fun _ => exitPFocus

/-! ### `next`

`next` navigates to the next "unfinished" leaf in the conjunction tree. It
repeatedly pops frames (via `done` when the focus is `True`, or `out`
otherwise) until it is on a left-frame, then goes `out`, `right`, and dives
into the leftmost leaf with repeated `left`.
-/

/-- Go to the next unfinished conjunct leaf in the tree. -/
syntax (name := nextTac) "next" : pfocus

/-- Repeatedly pop right-frames or completed subtrees. -/
private partial def nextPopRight : TacticM Unit := do
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
private partial def nextDescendLeft : TacticM Unit := do
  let _tup14 ← getPFocusTarget
  let (_, _, focus) := _tup14
  if focus.and?.isSome then
    evalLeft .missing
    nextDescendLeft

@[tactic nextTac] def evalNext : Tactic := fun _ => do
  nextPopRight
  outStep
  evalRight .missing
  nextDescendLeft

/-! ## Action tactics: making progress on the focus -/

/-- Build `fun p : Prop => p`. Needed when the outer is identity. -/
private def idOuterExpr : Expr := mkPropLam (.bvar 0)

/--
Apply `pfocus_imp` with a user-supplied implication `h : X → Y` to weaken the
focus from `Y` to `X`.

This is the primitive action. Given the current goal `pfocus C Y` and a proof
`h : X → Y`, it creates a new goal `pfocus C X` and assigns the old one to
`pfocus_imp h newGoal`.

`C` must have a `PFocusable` instance; this is always the case for outers
built by the navigation tactics.
-/
def applyPFocusImp (h : Expr) (X : Expr) : TacticM Unit := do
  let _tup15 ← getPFocusTarget
  let (mvarId, outer, focus) := _tup15
  mvarId.withContext do
    let newType ← mkAppM ``Pfocus.pfocus #[outer, X]
    let newMVar ← mkFreshExprSyntheticOpaqueMVar newType (← mvarId.getTag)
    -- Construct the monotonicity witness for `outer` directly, rather than
    -- relying on `PFocusable` instance synthesis. This keeps the approach
    -- robust to the shape of `outer` — instance synthesis would require
    -- higher-order unification that Lean doesn't always solve.
    let mono ← buildMonoSpec outer X focus
    -- `mono : (X → focus) → outer X → outer focus`. Compose with `h` to get
    -- the direct morphism `outer X → outer focus` that `pfocus_imp_raw`
    -- expects.
    let hMorphism := mkApp mono h
    let proof ← mkAppOptM ``Pfocus.pfocus_imp_raw
      #[none, some outer, some X, some focus, some hMorphism, some newMVar]
    mvarId.assign proof
    replaceMainGoal [newMVar.mvarId!]

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
When the focus is itself a function `α → Prop` (i.e. a predicate) and the
outer context is the canonical `fun p => ∃ x, p x` wrapper, running a
`tactic => ...` needs special treatment: we create a fresh metavariable
`?x : α` as a stand-in for the yet-to-be-chosen witness, run the user's
tactic against the goal `focus ?x`, and finish up based on whether `?x` was
assigned.

If the tactic assigns `?x` to some witness `e`, we add `let x := e` to the
local context and close the original `∃` using `Exists.intro x`. If it does
not (and the tactic leaves no subgoals), we currently error — a predicate
rewrite without committing can be expressed through `conv => ...`.
-/
private def runExistsAction (mvarId : MVarId) (outer focus α : Expr)
    (action : MVarId → TacticM (List MVarId)) : TacticM Unit := do
  -- Verify outer shape: `fun p : α → Prop => ∃ x : α, p x`, i.e.
  -- `fun p => Exists α p`.
  let outerW ← whnf outer
  let .lam _ _ outerBody _ := outerW
    | throwError "\
        `tactic =>` with a predicate focus requires the outer to be \
        `fun p : α → Prop => ∃ x, p x`, but the outer is:{indentExpr outer}"
  let outerBody := outerBody.consumeMData
  unless outerBody.isAppOfArity ``Exists 2
      && outerBody.appArg! == .bvar 0 do
    throwError "\
      `tactic =>` with a predicate focus requires the outer to be \
      `fun p => ∃ x, p x`, but the outer body is:{indentExpr outerBody}"
  -- Create the witness mvar and the applied focus goal.
  let xMVar ← mkFreshExprMVar α (userName := `x)
  let appGoal := focus.beta #[xMVar]
  let focusMVar ← mkFreshExprSyntheticOpaqueMVar appGoal (← mvarId.getTag)
  -- Run the user action on the fresh goal.
  let savedGoals ← getGoals
  let subgoals ←
    try action focusMVar.mvarId!
    finally setGoals savedGoals
  -- Subgoal local contexts must match the base context.
  let baseLCtx := (← mvarId.getDecl).lctx
  for g in subgoals do
    let gLCtx := (← g.getDecl).lctx
    unless gLCtx.isSubPrefixOf baseLCtx && baseLCtx.isSubPrefixOf gLCtx do
      throwError "\
        a pfocus action produced a subgoal whose local context differs \
        from the enclosing pfocus goal. Close such goals inside the \
        `tactic => ...` block.\n\nOffending goal:{
          indentD (MessageData.ofGoal g)}"
  -- Decide based on whether the witness mvar was assigned.
  let xInst ← instantiateMVars xMVar
  if !xInst.isMVar then
    /- ### Assigned case

    The tactic assigned `?x` to some witness `e`. For a clean proof term
    (no dangling metavariables), `e` must itself be ground. We enforce this
    here; the alternative would be to lift the remaining mvars out as new
    existentials, which we leave for a later iteration.
    -/
    let e := xInst
    if e.hasExprMVar then
      throwError "\
        `tactic =>` with an existential focus: the assigned witness still \
        contains unassigned metavariables:{indentExpr e}"
    unless subgoals.isEmpty do
      throwError "\
        `tactic =>` with an existential focus: the tactic committed a \
        witness but left {subgoals.length} open subgoal(s). Close them \
        inside the `tactic =>` block."
    -- Build the closing term, adding `let x := e` to the local context.
    let proofTerm ← Meta.withLetDecl `x α e fun x => do
      let focusProof ← instantiateMVars focusMVar
      let existsProof ← mkAppOptM ``Exists.intro
        #[none, some focus, some x, some focusProof]
      let oldIntro ← mkAppOptM ``Pfocus.pfocus_intro
        #[none, some outer, some focus, some existsProof]
      mkLetFVars #[x] oldIntro
    mvarId.assign proofTerm
    replaceMainGoal []
    return
  /- ### Unassigned case

  The tactic transformed the predicate but didn't commit a witness. We
  keep the `∃` in the outer and build a new predicate focus by abstracting
  the witness mvar `?x` over the subgoals' types.

  Concretely: each subgoal `g_i : T_i(?x)` becomes part of a new predicate
  `λ x => T_1(x) ∧ ... ∧ T_n(x)`. The focus proof (which references `?x`
  and the `g_i`) becomes a transport `∀ x, (∧ T_i(x)) → old_focus x`, and
  that's lifted through the `∃` to give the morphism for `pfocus_imp_raw`.
  -/
  let focusId := focusMVar.mvarId!
  unless (← focusId.isAssigned) do
    -- Tactic did nothing observable: the goal list still contains the
    -- original focus mvar. No update to the pfocus state.
    return
  let focusProof ← instantiateMVars (.mvar focusId)
  -- Require the tactic's result to be "ground modulo ?x and the declared
  -- subgoals". Lifting arbitrary new mvars as existentials is out of scope.
  let allowed : Std.HashSet MVarId :=
    (subgoals.foldl (·.insert ·) (∅ : Std.HashSet MVarId)).insert xMVar.mvarId!
  let freshMVars :=
    (focusProof.collectMVars {}).result.filter (!allowed.contains ·)
  unless freshMVars.isEmpty do
    throwError "\
      `tactic =>` with an existential focus: the tactic left \
      {freshMVars.size} new unassigned metavariable(s) beyond the witness \
      `?x` and its declared subgoals. Please close them inside the \
      `tactic =>` block."
  let subTypes ← subgoals.mapM fun g => g.getType
  let (newPred, mpForall) ← withLocalDeclD `x α fun x => do
    let replaceX (e : Expr) : Expr :=
      e.replace fun sub =>
        if sub.isMVar && sub.mvarId! == xMVar.mvarId! then some x else none
    let subTypesX := subTypes.map replaceX
    let conjX := mkConjunction subTypesX
    let newPredLam ← mkLambdaFVars #[x] conjX
    let focusProofX := replaceX focusProof
    let mp ← withLocalDeclD `h conjX fun h => do
      let parts ← projConj subTypesX h
      let subst := subgoals.zip parts
      let body := focusProofX.replace fun sub =>
        match sub with
        | .mvar m =>
          match subst.find? (fun (g, _) => g == m) with
          | some (_, p) => some p
          | none => none
        | _ => none
      mkLambdaFVars #[h] body
    let mpForall ← mkLambdaFVars #[x] mp
    return (newPredLam, mpForall)
  -- `hMorphism : (∃ x, newPred x) → (∃ x, focus x)`, i.e. `outer newPred → outer focus`.
  let newExists ← mkAppM ``Exists #[newPred]
  let hMorphism ← withLocalDeclD `e newExists fun e => do
    let matcher ← withLocalDeclD `a α fun a => do
      let haType := newPred.beta #[a]
      withLocalDeclD `ha haType fun ha => do
        let mpApplied := mkApp2 mpForall a ha
        let intro ← mkAppOptM ``Exists.intro
          #[none, some focus, some a, some mpApplied]
        mkLambdaFVars #[a, ha] intro
    let body ← mkAppM ``Exists.elim #[e, matcher]
    mkLambdaFVars #[e] body
  -- New pfocus goal: `pfocus outer newPred`.
  let newType ← mkAppM ``Pfocus.pfocus #[outer, newPred]
  let newMVar ← mkFreshExprSyntheticOpaqueMVar newType (← mvarId.getTag)
  let proof ← mkAppOptM ``Pfocus.pfocus_imp_raw
    #[none, some outer, some newPred, some focus, some hMorphism, some newMVar]
  mvarId.assign proof
  replaceMainGoal [newMVar.mvarId!]

/--
Core action: run `action` (a plain `TacticM` computation) on a fresh goal
whose type is the current focus, then fold the resulting open subgoals into
the new focus via `pfocus_imp`.

When the focus is a predicate (has a `∀`-type), we dispatch to
`runExistsAction` above instead.

Contracts:
* `action` must not change the list of goals outside the single starting one.
* Any subgoals it returns must share the local context of the starting goal;
  otherwise the implication closure step fails (we check this and raise a
  useful error).
-/
def runActionOnFocus (action : MVarId → TacticM (List MVarId)) : TacticM Unit := do
  let _tup16 ← getPFocusTarget
  let (mvarId, outer, focus) := _tup16
  mvarId.withContext do
    -- Predicate-focus case: the focus itself is a function `α → …`. The
    -- outer must be an existential wrapper and the tactic gets a fresh
    -- witness mvar.
    let focusType ← instantiateMVars (← inferType focus)
    if let .forallE _ α _ _ := focusType then
      return ← runExistsAction mvarId outer focus α action
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

@[tactic tacticTac] def evalTacticTac : Tactic := fun stx => do
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

@[tactic closingTac] def evalClosing : Tactic := fun stx => do
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

@[tactic applyTac] def evalApply : Tactic := fun stx => do
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

@[tactic convTac] def evalConv : Tactic := fun stx => do
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

They *cannot* use the `runActionOnFocus` machinery, since that copies the
focus into a fresh goal (and any new hypothesis would live on the fresh
goal, not on the pfocus goal we want to carry forward). Instead, we run the
regular `have`/`let` tactic on the pfocus goal itself.
-/

/-- `have h : t := pf` extends the local context. -/
syntax (name := haveTac) "have " Lean.Parser.Term.letDecl : pfocus
/-- `let x : t := v` extends the local context with a let-binding. -/
syntax (name := letTac) "let " Lean.Parser.Term.letDecl : pfocus

@[tactic haveTac] def evalHaveTac : Tactic := fun stx => do
  match stx with
  | `(pfocus| have $d:letDecl) => evalTactic (← `(tactic| have $d:letDecl))
  | _ => throwUnsupportedSyntax
@[tactic letTac] def evalLetTac : Tactic := fun stx => do
  match stx with
  | `(pfocus| let $d:letDecl) => evalTactic (← `(tactic| let $d:letDecl))
  | _ => throwUnsupportedSyntax
/-- `show P'` changes the focus to a definitionally-equal proposition. -/
syntax (name := showTac) "show " term : pfocus

@[tactic showTac] def evalShow : Tactic := fun stx => do
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
        #[none, some oldOuter, some oldFocus, some elim]
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
Dispatch a single pfocus syntax tree. We rely on the elaborator table that
`@[tactic ...]` attributes populate; Lean's `evalTactic` treats unknown
categories generically.
-/
partial def evalPfocusCat (stx : Syntax) : TacticM Unit := do
  withRef stx <| withTacticInfoContext stx <|
    Elab.Tactic.evalTactic stx

/--
Walk an `sepBy1IndentSemicolon`-style sequence, calling `evalPfocusCat` on
each pfocus-category element and recording info for the separators. Mirrors
the `conv` implementation.
-/
def evalPfocusSepByIndent (stx : Syntax) : TacticM Unit := do
  for arg in stx.getArgs, i in *...stx.getArgs.size do
    if i % 2 == 0 then
      evalPfocusCat arg
    else
      saveTacticInfoForToken arg

/-- Evaluate a `pfocusSeq`, whether bracketed or indented.

The `syntax pfocusSeq := pfocusSeqBracketed <|> pfocusSeq1Indented`
declaration does not introduce a wrapping node kind. Instead, `stx` is
*either* a `pfocusSeqBracketed` node (`{ items }`) or a
`pfocusSeq1Indented` node (just the items). For the former, `stx[1]` is
the inner separated list; for the latter, `stx[0]` is. -/
def evalPfocusSeq (stx : Syntax) : TacticM Unit := do
  if stx.getKind == ``pfocusSeqBracketed then
    evalPfocusSepByIndent stx[1]
  else
    -- `pfocusSeq1Indented`
    evalPfocusSepByIndent stx[0]

@[tactic pfocusTac] def evalPfocus : Tactic := fun stx => do
  match stx with
  | `(tactic| pfocus => $code) => do
      enterPFocus
      evalPfocusSeq code
      exitPFocus
  | _ => throwUnsupportedSyntax

/-! ## `paren` passthrough -/

@[tactic paren] def evalParen : Tactic := fun stx => do
  -- `( $seq )`
  evalPfocusSeq stx[1]

end Pfocus
