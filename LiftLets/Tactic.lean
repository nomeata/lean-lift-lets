/-
Copyright (c) 2026 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license.

The `liftLets` tactic family.

The design is deliberately thin:

* `lift_lets => …` is a tactic-language host. Inside its block the user
  runs lift_lets-mode tactics, which live in a `LiftLetsM` state monad
  carrying a list of tracked metavariables and an accumulating list of
  let-decls introduced by `have`/`let`.
* The only primitive that makes progress on the proof is `tactic => …`,
  which runs a regular Lean tactic on the current main goal, checks
  that every new subgoal shares the main goal's local context, and
  tracks the new subgoals.
* `have` and `let` directly extend the declared local context of every
  tracked mvar (so a subsequent `exact h` can unify `?x := h` without
  zeta-reduction).
* At `lift_lets => …` exit, the proof term is wrapped once with all the
  accumulated let-decls via `mkLetFVars`, and the original goal is
  assigned for the first time.

A handful of convenience tactics (`apply`, `constructor`, `assumption`,
`rfl`, `trivial`, `grind`, `exact`, `rw`, `simp`) expand to
`tactic => …` plus the relevant regular-tactic argument.

The focusing combinators `·` and `next` select a single subgoal to
continue on.
-/

import Lean
import LiftLets.Basic
import LiftLets.Attr

namespace LiftLets

open Lean Elab Tactic Meta

/-! ## Syntax category

LiftLets-mode tactics form their own syntax category, so they don't leak
into the regular `tactic` grammar.
-/

declare_syntax_cat liftLets (behavior := both)

syntax liftLetsSeq1Indented := sepBy1IndentSemicolon(liftLets)
syntax liftLetsSeqBracketed := "{" withoutPosition(sepByIndentSemicolon(liftLets)) "}"
syntax liftLetsSeq := liftLetsSeqBracketed <|> liftLetsSeq1Indented

/-! ## State helpers -/

/-- Track a freshly-allocated mvar so future `have`/`let` extend its
declared local context. -/
def trackLiftLetsMVar (mvarId : MVarId) : LiftLetsM Unit :=
  modify fun s => { s with trackedMVars := s.trackedMVars.push mvarId }

/-- Are two local contexts equal in the lift_lets-relevant sense — same
fvars in the same order? -/
def lctxEqLiftLets (a b : LocalContext) : Bool :=
  a.isSubPrefixOf b && b.isSubPrefixOf a

/-- Extend the declared local context of every tracked mvar with a new
let-decl.

Even *assigned* mvars get their lctx updated: we use `rootMVar`'s
current lctx as the canonical record of what's been added (so
`exitLiftLets` can recover the let-decls without a parallel state
field), and `rootMVar` gets assigned as soon as the first `tactic => …`
runs. Updating an assigned mvar's lctx is safe because we only ever
append decls — its existing assignment still type-checks in the larger
context. -/
def extendTrackedLCtxs (tracked : Array MVarId) (fvarId : FVarId)
    (userName : Name) (type value : Expr) : TacticM Unit := do
  for m in tracked do
    let d ← m.getDecl
    let newLCtx := d.lctx.mkLetDecl fvarId userName type value
    modifyMCtx fun mctx =>
      mctx.modifyExprMVarDecl m fun md => { md with lctx := newLCtx }

/-! ## Enter / exit -/

/-- Enter lift_lets mode.

Does *not* assign `entryGoal`; that happens in `exitLiftLets`, at which
point the accumulated let-decls are wrapped around the proof term with
`mkLetFVars`. Between entry and exit the user sees `rootMVar` as the
main goal; it has the same type and (initially) the same local context
as `entryGoal`.
-/
def enterLiftLets : TacticM LiftLetsState := do
  let entryGoal ← getMainGoal
  let entryDecl ← entryGoal.getDecl
  let entryLCtx := entryDecl.lctx
  entryGoal.withContext do
    let rootMVar ← mkFreshExprSyntheticOpaqueMVar entryDecl.type (← entryGoal.getTag)
    replaceMainGoal [rootMVar.mvarId!]
    return {
      entryGoal, entryLCtx, rootMVar := rootMVar.mvarId!
      trackedMVars := #[rootMVar.mvarId!]
    }

/-- Exit lift_lets mode.

The authoritative record of the let-decls introduced during the block
is the `LocalContext` attached to `rootMVar`: every `have`/`let` we saw
has already extended that lctx. So at exit we just diff it against the
entry lctx, wrap the `rootMVar` value with one `let`-binding per
newcomer via `mkLetFVars`, and assign the original goal for the first
time.

Unassigned subgoals (from `tactic => …` calls that left open branches)
stay in the main goal list for the user to continue with *inside* the
extended context.
-/
def exitLiftLets : LiftLetsM Unit := do
  let state ← get
  -- `rootMVar`'s declared lctx always reflects every `have`/`let` we
  -- have extended — but the *ambient* MetaM lctx, inside any open
  -- `withLetDecl` scopes from the CPS chain, does as well. We use the
  -- ambient one here so that `mkLetFVars` finds the decls without
  -- needing a `withLCtx` dance.
  let currentLCtx ← liftM (getLCtx : TacticM LocalContext)
  let extraFVars : Array Expr := Id.run do
    let mut acc : Array Expr := #[]
    for decl in currentLCtx do
      unless state.entryLCtx.contains decl.fvarId do
        acc := acc.push (.fvar decl.fvarId)
    return acc
  -- No withLCtx: we are already inside every `withLetDecl` scope that
  -- accumulated during the block, so `getLCtx` above already sees the
  -- new decls, and `mkLetFVars` looks them up in the ambient context.
  let rootValue ← instantiateMVars (.mvar state.rootMVar)
  let wrapped ← mkLetFVars (usedLetOnly := false) extraFVars rootValue
  state.entryGoal.assign wrapped

/-! ## Dispatcher -/

/-- Build a `TacticInfo` for a lift_lets-tactic invocation, using the
current `TacticM` state as the "after" state. -/
private def mkLiftLetsTacticInfoNow
    (stx : Syntax) (mctxBefore : MetavarContext)
    (goalsBefore : List MVarId) : TacticM Info := do
  return Info.ofTacticInfo {
    elaborator := (← readThe Elab.Tactic.Context).elaborator
    mctxBefore, goalsBefore
    stx
    mctxAfter := (← getMCtx)
    goalsAfter := (← getUnsolvedGoals)
  }

/-- Dispatch a single `liftLets` syntax tree.

Written in plain `do`-notation for `LiftLetsM`: `withRef`, `getMCtx`,
`pushInfoLeaf`, `throwError`, etc. are lifted automatically via our
`MonadLift`/`MonadRef`/`MonadExceptOf`/… instances. The `pushInfoLeaf`
*after* the handler runs is the magic that gives us the same
before-state/after-state hover behaviour as regular Lean tactics: for a
scope-introducing handler like `have`/`let`, the "after" snapshot is
taken inside the `withLetDecl` scope, because that's where the handler's
continuation runs. -/
partial def evalLiftLetsCat (stx : Syntax) : LiftLetsM Unit := withRef stx do
  let kind := stx.getKind
  if kind == nullKind then
    for arg in stx.getArgs do evalLiftLetsCat arg
    return
  let mctxBefore ← getMCtx
  let goalsBefore ← getUnsolvedGoals
  let macros := macroAttribute.getEntries (← getEnv) kind
  if let m :: _ := macros then
    let stx' ← liftM (adaptMacro m.value stx : TacticM _)
    evalLiftLetsCat stx'
  else
    let handlers := liftLetsTacticAttr.getEntries (← getEnv) kind
    match handlers with
    | h :: _ => h.value stx
    | [] => throwError m!"lift_lets tactic '{kind}' has not been implemented"
  -- Push the info leaf *after* the handler. Runs inside any scope the
  -- handler opened (e.g. `withLetDecl`), so `mctxAfter`/`goalsAfter`
  -- reflect the scope's effect on tracked mvars.
  let info ← mkLiftLetsTacticInfoNow stx mctxBefore goalsBefore
  pushInfoLeaf info

/-- Walk a `sepBy1IndentSemicolon`-style sequence. -/
partial def evalLiftLetsSepByIndent (stx : Syntax) : LiftLetsM Unit := do
  for arg in stx.getArgs, i in *...stx.getArgs.size do
    if i % 2 == 1 then
      saveTacticInfoForToken arg
    else
      evalLiftLetsCat arg

/-- Evaluate a `liftLetsSeq`, bracketed or indented. -/
def evalLiftLetsSeq (stx : Syntax) : LiftLetsM Unit := do
  if stx.getKind == ``liftLetsSeqBracketed then
    evalLiftLetsSepByIndent stx[1]
  else
    evalLiftLetsSepByIndent stx[0]

/-! ## `tactic => …`

The one primitive. Runs a regular Lean tactic on the current main goal,
inherits its subgoals as tracked mvars, and errors if any of those
subgoals has a different local context from the input mvar.
-/

/-- `tactic => tac` runs `tac` on the current main goal, tracking the
new subgoals. -/
syntax (name := tacticTac) "tactic" " => " tacticSeq : liftLets

@[lift_lets_tactic LiftLets.tacticTac] def evalTacticTac : LiftLetsTactic := fun stx => do
  let `(liftLets| tactic => $code) := stx | throwUnsupportedSyntax
  let mvarId ← getMainGoal
  let baseLCtx := (← mvarId.getDecl).lctx
  -- Save and restore the global goal list around the tactic call.
  let subgoals ← liftM do
    let savedGoals ← getGoals
    try
      setGoals [mvarId]
      evalTactic code
      pure (← getGoals)
    finally
      setGoals savedGoals
  -- Every subgoal must share the base context exactly.
  for g in subgoals do
    let gLCtx := (← g.getDecl).lctx
    unless lctxEqLiftLets baseLCtx gLCtx do
      throwError "\
        `tactic =>` produced a subgoal whose local context differs \
        from the main goal. Use a lift_lets-level `have`/`let` to \
        introduce hypotheses so they reach every tracked goal.\
        \n\nOffending goal:{indentD (MessageData.ofGoal g)}"
    trackLiftLetsMVar g
  replaceMainGoal subgoals

/-! ## Convenience wrappers around `tactic => …` -/

macro "apply " e:term : liftLets => `(liftLets| tactic => apply $e)
macro "exact " e:term : liftLets => `(liftLets| tactic => exact $e)
macro "constructor" : liftLets => `(liftLets| tactic => constructor)
macro "assumption" : liftLets => `(liftLets| tactic => assumption)
macro "rfl" : liftLets => `(liftLets| tactic => rfl)
macro "trivial" : liftLets => `(liftLets| tactic => trivial)
macro "grind" : liftLets => `(liftLets| tactic => grind)
macro "show " t:term : liftLets => `(liftLets| tactic => show $t)
macro "rw " s:Lean.Parser.Tactic.rwRuleSeq : liftLets =>
  `(liftLets| tactic => rw $s:rwRuleSeq)
macro "simp" : liftLets => `(liftLets| tactic => simp)

/-! ## `have`, `let`

Elaborate the type and value in the current main goal's context, then
extend the declared local context of every tracked mvar with the new
let-decl. The proof term we eventually build is free of any `.letE`
wrappers from `have`/`let` — those are inserted once, at exit, via
`mkLetFVars`.
-/

syntax (name := haveTac) "have " ident (" : " term)? " := " term : liftLets
syntax (name := letTac) "let "  ident (" : " term)? " := " term : liftLets

def addLiftLetsDecl (name : Name) (typeStx? : Option Syntax) (valueStx : Syntax) :
    LiftLetsM Unit := do
  -- Elaborate the type and value in the current main goal's context.
  let (type, value) ← liftM do
    let mvarId ← getMainGoal
    mvarId.withContext do
      let expectedType ← match typeStx? with
        | some t => Lean.Elab.Term.elabType t
        | none   => mkFreshTypeMVar
      let value ← Lean.Elab.Term.elabTermEnsuringType valueStx expectedType
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      pure ((← instantiateMVars expectedType), (← instantiateMVars value))
  -- Open a `withLetDecl` scope around the rest of the block: the ambient
  -- MetaM local context gains the new fvar, and every subsequent tactic
  -- (plus `exitLiftLets`) runs inside the scope. Then extend every
  -- tracked mvar's declared lctx so future assignments referencing the
  -- new fvar don't zeta-reduce.
  let fvar ← LiftLetsM.withLetDecl name type value
  extendTrackedLCtxs (← get).trackedMVars fvar.fvarId! name type value

@[lift_lets_tactic LiftLets.haveTac] def evalHaveTac : LiftLetsTactic := fun stx =>
  match stx with
  | `(liftLets| have $x:ident : $t:term := $v:term) =>
    addLiftLetsDecl x.getId (some t.raw) v.raw
  | `(liftLets| have $x:ident := $v:term) =>
    addLiftLetsDecl x.getId none v.raw
  | _ => throwUnsupportedSyntax

@[lift_lets_tactic LiftLets.letTac] def evalLetTac : LiftLetsTactic := fun stx =>
  match stx with
  | `(liftLets| let $x:ident : $t:term := $v:term) =>
    addLiftLetsDecl x.getId (some t.raw) v.raw
  | `(liftLets| let $x:ident := $v:term) =>
    addLiftLetsDecl x.getId none v.raw
  | _ => throwUnsupportedSyntax

/-! ## Focusing: `·` and `next`

`· tacs` focuses on the first goal, runs `tacs`, and fails if any
goals remain. `next => tacs` is the same but without the
"must close" requirement.
-/

syntax (name := dotTac) patternIgnore("·" <|> ".") liftLetsSeq : liftLets
syntax (name := nextTac) "next" " => " liftLetsSeq : liftLets

private def focusImpl (code : Syntax) (mustClose : Bool) : LiftLetsM Unit :=
  fun s realK => do
    match (← getGoals) with
    | [] => throwError "no goals"
    | g :: rest =>
      setGoals [g]
      -- Pass the outer realK *into* the inner CPS chain as its tail.
      -- If the inner block introduces a `have`/`let` (opening a
      -- `withLetDecl` scope), the goal-restoration and the outer
      -- continuation both run *inside* that scope. That's what lets
      -- a `let` introduced inside a `·`-block remain visible to
      -- subsequent siblings at the outer level.
      (evalLiftLetsSeq code) s (fun _ s' => do
        let remaining ← getGoals
        if mustClose && !remaining.isEmpty then
          throwError "`·`-block did not close the focused goal"
        setGoals (remaining ++ rest)
        realK () s')

@[lift_lets_tactic LiftLets.dotTac] def evalDot : LiftLetsTactic := fun stx =>
  -- The `patternIgnore("·" <|> ".")` in the declaration means the
  -- leading token is recognised as either symbol; we don't need to
  -- distinguish them here.
  focusImpl stx[1] true

@[lift_lets_tactic LiftLets.nextTac] def evalNext : LiftLetsTactic := fun stx =>
  match stx with
  | `(liftLets| next => $seq:liftLetsSeq) => focusImpl seq false
  | _ => throwUnsupportedSyntax

/-! ## Minor tactics -/

syntax (name := skip) "skip" : liftLets
syntax (name := traceState) "trace_state" : liftLets
syntax (name := rotateLeft) "rotate_left" (ppSpace num)? : liftLets
syntax (name := rotateRight) "rotate_right" (ppSpace num)? : liftLets

@[lift_lets_tactic LiftLets.skip] def evalSkip : LiftLetsTactic := fun _ => pure ()

@[lift_lets_tactic LiftLets.traceState] def evalTraceState : LiftLetsTactic := fun _ => liftM do
  let gs ← getGoals
  match gs with
  | [] => logInfo "no goals"
  | _  => logInfo (goalsToMessageData gs)

/-- Cycle the goal list left by `n` (default 1). -/
@[lift_lets_tactic LiftLets.rotateLeft] def evalRotateLeft : LiftLetsTactic := fun stx => liftM do
  let n : Nat := stx[1].getOptional?.map (·.toNat : Syntax → Nat) |>.getD 1
  setGoals <| (← getGoals).rotateLeft n

/-- Cycle the goal list right by `n` (default 1). -/
@[lift_lets_tactic LiftLets.rotateRight] def evalRotateRight : LiftLetsTactic := fun stx => liftM do
  let n : Nat := stx[1].getOptional?.map (·.toNat : Syntax → Nat) |>.getD 1
  setGoals <| (← getGoals).rotateRight n

/-! ## Entry-point tactic -/

/--
`lift_lets => …` runs a sequence of lift_lets-mode tactics, with a shared
local context that `have`/`let` can extend across every goal produced
by the block. Unlike a bare `refine` or `exact`, any let-bindings
introduced inside the block are carried through cleanly to the final
proof term: they are applied via `mkLetFVars` once, at exit time,
rather than being zeta-reduced into every intermediate step.
-/
syntax (name := liftLetsTac) "lift_lets" " => " liftLetsSeq : tactic

@[tactic liftLetsTac] def evalLiftLets : Tactic := fun stx => do
  match stx with
  | `(tactic| lift_lets => $code) => do
      let initState ← enterLiftLets
      let runBody : LiftLetsM Unit := do
        evalLiftLetsSeq code
        exitLiftLets
      runBody.run' initState
      return
  | _ => throwUnsupportedSyntax

end LiftLets
