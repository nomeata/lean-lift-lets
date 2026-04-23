/-
Copyright (c) 2026 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license.

The `pfocus` tactic family.

The design is deliberately thin:

* `pfocus => …` is a tactic-language host. Inside its block the user
  runs pfocus-mode tactics, which live in a `PFocusM` state monad
  carrying a list of tracked metavariables and an accumulating list of
  let-decls introduced by `have`/`let`.
* The only primitive that makes progress on the proof is `tactic => …`,
  which runs a regular Lean tactic on the current main goal, checks
  that every new subgoal shares the main goal's local context, and
  tracks the new subgoals.
* `have` and `let` directly extend the declared local context of every
  tracked mvar (so a subsequent `exact h` can unify `?x := h` without
  zeta-reduction).
* At `pfocus => …` exit, the proof term is wrapped once with all the
  accumulated let-decls via `mkLetFVars`, and the original goal is
  assigned for the first time.

A handful of convenience tactics (`apply`, `constructor`, `assumption`,
`rfl`, `trivial`, `grind`, `exact`, `rw`, `simp`) expand to
`tactic => …` plus the relevant regular-tactic argument.

The focusing combinators `·` and `next` select a single subgoal to
continue on.
-/

import Lean
import Pfocus.Basic
import Pfocus.Attr

namespace Pfocus

open Lean Elab Tactic Meta

/-! ## Syntax category

Pfocus-mode tactics form their own syntax category, so they don't leak
into the regular `tactic` grammar.
-/

declare_syntax_cat pfocus (behavior := both)

syntax pfocusSeq1Indented := sepBy1IndentSemicolon(pfocus)
syntax pfocusSeqBracketed := "{" withoutPosition(sepByIndentSemicolon(pfocus)) "}"
syntax pfocusSeq := pfocusSeqBracketed <|> pfocusSeq1Indented

/-! ## State helpers -/

/-- Track a freshly-allocated mvar so future `have`/`let` extend its
declared local context. -/
def trackPFocusMVar (mvarId : MVarId) : PFocusM Unit :=
  modify fun s => { s with trackedMVars := s.trackedMVars.push mvarId }

/-- Are two local contexts equal in the pfocus-relevant sense — same
fvars in the same order? -/
private def lctxEqPFocus (a b : LocalContext) : Bool :=
  a.isSubPrefixOf b && b.isSubPrefixOf a

/-- Extend the declared local context of every tracked (unassigned) mvar
with a new let-decl. -/
private def extendTrackedLCtxs (fvarId : FVarId) (userName : Name)
    (type value : Expr) : PFocusM Unit := do
  let tracked := (← get).trackedMVars
  for m in tracked do
    if (← m.isAssigned) then continue
    let d ← m.getDecl
    let newLCtx := d.lctx.mkLetDecl fvarId userName type value
    modifyMCtx fun mctx =>
      mctx.modifyExprMVarDecl m fun md => { md with lctx := newLCtx }

/-! ## Enter / exit -/

/-- Enter pfocus mode.

Does *not* assign `entryGoal`; that happens in `exitPFocus`, at which
point the accumulated let-decls are wrapped around the proof term with
`mkLetFVars`. Between entry and exit the user sees `rootMVar` as the
main goal; it has the same type and (initially) the same local context
as `entryGoal`.
-/
def enterPFocus : TacticM PFocusState := do
  let entryGoal ← getMainGoal
  let entryDecl ← entryGoal.getDecl
  let entryLCtx := entryDecl.lctx
  entryGoal.withContext do
    let rootMVar ← mkFreshExprSyntheticOpaqueMVar entryDecl.type (← entryGoal.getTag)
    replaceMainGoal [rootMVar.mvarId!]
    return {
      entryGoal, entryLCtx, rootMVar := rootMVar.mvarId!
      extraDecls := #[]
      trackedMVars := #[rootMVar.mvarId!]
    }

/-- Exit pfocus mode.

Collect every let-decl the block accumulated, build a local context
containing them, wrap the current `rootMVar` value with `mkLetFVars`,
and assign the original goal. Unassigned goals (from `tactic => …`
calls that left subgoals) are left in the main goal list for the user
to continue with *inside* the extended context.
-/
def exitPFocus : PFocusM Unit := do
  let state ← get
  let extLCtx := state.extraDecls.foldl (init := state.entryLCtx) fun lctx d =>
    lctx.mkLetDecl d.fvarId d.userName d.type d.value
  withLCtx extLCtx #[] do
    let rootValue ← instantiateMVars (.mvar state.rootMVar)
    let extraFVars := state.extraDecls.map fun d => Expr.fvar d.fvarId
    let wrapped ← mkLetFVars (usedLetOnly := false) extraFVars rootValue
    state.entryGoal.assign wrapped

/-! ## Dispatcher -/

/-- Produce a `TacticInfo` record for an invocation of a pfocus tactic,
so the infoview shows the goal state on hover. -/
private def mkPfocusTacticInfo (stx : Syntax) (mctxBefore : MetavarContext)
    (goalsBefore : List MVarId) : PFocusM Info := do
  return Info.ofTacticInfo {
    elaborator := (← readThe Elab.Tactic.Context).elaborator
    mctxBefore, goalsBefore
    stx
    mctxAfter := (← getMCtx)
    goalsAfter := (← getUnsolvedGoals)
  }

/-- Dispatch a single pfocus syntax tree via the `@[pfocus_tactic]`
attribute, expanding any matching `macro` first. -/
partial def evalPfocusCat (stx : Syntax) : PFocusM Unit :=
  withRef stx do
    let kind := stx.getKind
    if kind == nullKind then
      for arg in stx.getArgs do evalPfocusCat arg
      return
    let macros := macroAttribute.getEntries (← getEnv) kind
    if let m :: _ := macros then
      let stx' ← adaptMacro m.value stx
      evalPfocusCat stx'
      return
    let handlers := pfocusTacticAttr.getEntries (← getEnv) kind
    match handlers with
    | h :: _ =>
      let mctxBefore ← getMCtx
      let goalsBefore ← getUnsolvedGoals
      withInfoContext (h.value stx) (mkPfocusTacticInfo stx mctxBefore goalsBefore)
    | [] => throwError m!"pfocus tactic '{kind}' has not been implemented"

/-- Walk a `sepBy1IndentSemicolon`-style sequence. -/
def evalPfocusSepByIndent (stx : Syntax) : PFocusM Unit := do
  for arg in stx.getArgs, i in *...stx.getArgs.size do
    if i % 2 == 0 then
      evalPfocusCat arg
    else
      saveTacticInfoForToken arg

def evalPfocusSeq (stx : Syntax) : PFocusM Unit := do
  if stx.getKind == ``pfocusSeqBracketed then
    evalPfocusSepByIndent stx[1]
  else
    evalPfocusSepByIndent stx[0]

/-! ## `tactic => …`

The one primitive. Runs a regular Lean tactic on the current main goal,
inherits its subgoals as tracked mvars, and errors if any of those
subgoals has a different local context from the input mvar.
-/

/-- `tactic => tac` runs `tac` on the current main goal, tracking the
new subgoals. -/
syntax (name := tacticTac) "tactic" " => " tacticSeq : pfocus

@[pfocus_tactic Pfocus.tacticTac] def evalTacticTac : PFocusTactic := fun stx => do
  match stx with
  | `(pfocus| tactic => $code) => do
    let mvarId ← getMainGoal
    let baseLCtx := (← mvarId.getDecl).lctx
    -- Save and restore the global goal list around the tactic call.
    let savedGoals ← getGoals
    let subgoals ←
      try
        setGoals [mvarId]
        evalTactic code
        pure (← getGoals)
      finally
        setGoals savedGoals
    -- Every subgoal must share the base context exactly. If a tactic
    -- wants to introduce a new hypothesis, users have to do that via
    -- the pfocus-level `have`/`let` instead (which extends *every*
    -- tracked mvar's context, not just the subgoal's).
    for g in subgoals do
      let gLCtx := (← g.getDecl).lctx
      unless lctxEqPFocus baseLCtx gLCtx do
        throwError "\
          `tactic =>` produced a subgoal whose local context differs \
          from the main goal. Use a pfocus-level `have`/`let` to \
          introduce hypotheses so they reach every tracked goal.\
          \n\nOffending goal:{indentD (MessageData.ofGoal g)}"
      trackPFocusMVar g
    -- Replace main goal list with the subgoals.
    replaceMainGoal subgoals
  | _ => throwUnsupportedSyntax

/-! ## Convenience wrappers around `tactic => …` -/

macro "apply " e:term : pfocus => `(pfocus| tactic => apply $e)
macro "exact " e:term : pfocus => `(pfocus| tactic => exact $e)
macro "constructor" : pfocus => `(pfocus| tactic => constructor)
macro "assumption" : pfocus => `(pfocus| tactic => assumption)
macro "rfl" : pfocus => `(pfocus| tactic => rfl)
macro "trivial" : pfocus => `(pfocus| tactic => trivial)
macro "grind" : pfocus => `(pfocus| tactic => grind)
macro "show " t:term : pfocus => `(pfocus| tactic => show $t)
macro "rw " s:Lean.Parser.Tactic.rwRuleSeq : pfocus =>
  `(pfocus| tactic => rw $s:rwRuleSeq)
macro "simp" : pfocus => `(pfocus| tactic => simp)

/-! ## `have`, `let`

Elaborate the type and value in the current main goal's context, then
extend the declared local context of every tracked mvar with the new
let-decl. The proof term we eventually build is free of any `.letE`
wrappers from `have`/`let` — those are inserted once, at exit, via
`mkLetFVars`.
-/

syntax (name := haveTac) "have " ident (" : " term)? " := " term : pfocus
syntax (name := letTac) "let "  ident (" : " term)? " := " term : pfocus

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
    extendTrackedLCtxs fvarId name type value
    let newDecl : PFocusLetDecl := { fvarId, userName := name, type, value }
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

/-! ## Focusing: `·` and `next`

`· tacs` focuses on the first goal, runs `tacs`, and fails if any
goals remain. `next => tacs` is the same but without the
"must close" requirement.
-/

syntax (name := dotTac) patternIgnore("·" <|> ".") pfocusSeq : pfocus
syntax (name := nextTac) "next" " => " pfocusSeq : pfocus

private def focusImpl (code : Syntax) (mustClose : Bool) : PFocusM Unit := do
  match (← getGoals) with
  | [] => throwError "no goals"
  | g :: rest =>
    setGoals [g]
    try
      evalPfocusSeq code
    finally
      let remaining ← getGoals
      if mustClose && !remaining.isEmpty then
        throwError "`·`-block did not close the focused goal"
      setGoals (remaining ++ rest)

@[pfocus_tactic Pfocus.dotTac] def evalDot : PFocusTactic := fun stx => do
  -- The `patternIgnore("·" <|> ".")` in the declaration means the
  -- leading token is recognised as either symbol; we don't need to
  -- distinguish them here.
  let seq := stx[1]
  focusImpl seq true

@[pfocus_tactic Pfocus.nextTac] def evalNext : PFocusTactic := fun stx => do
  match stx with
  | `(pfocus| next => $seq:pfocusSeq) => focusImpl seq false
  | _ => throwUnsupportedSyntax

/-! ## Minor tactics -/

syntax (name := skip) "skip" : pfocus
syntax (name := traceState) "trace_state" : pfocus

@[pfocus_tactic Pfocus.skip] def evalSkip : PFocusTactic := fun _ => pure ()

@[pfocus_tactic Pfocus.traceState] def evalTraceState : PFocusTactic := fun _ => do
  let gs ← getGoals
  match gs with
  | [] => logInfo "no goals"
  | _  => logInfo (goalsToMessageData gs)

/-! ## Entry-point tactic -/

/--
`pfocus => …` runs a sequence of pfocus-mode tactics, with a shared
local context that `have`/`let` can extend across every goal produced
by the block. Unlike a bare `refine` or `exact`, any let-bindings
introduced inside the block are carried through cleanly to the final
proof term: they are applied via `mkLetFVars` once, at exit time,
rather than being zeta-reduced into every intermediate step.
-/
syntax (name := pfocusTac) "pfocus" " => " pfocusSeq : tactic

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
