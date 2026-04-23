/-
Copyright (c) 2026 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license.

LiftLets-mode monad and state.

Pure monad machinery: no syntax, no attribute registration. The tactic
attribute (`@[lift_lets_tactic …]`) lives in `LiftLets.Attr`; the syntax
category and elaborators live in `LiftLets.Tactic`.
-/
import Lean

namespace LiftLets

open Lean Elab Tactic Meta

/-- State threaded through a `lift_lets => ...` block.

* `entryGoal` — the goal that was main when `lift_lets =>` was entered.
  Not assigned until `exitLiftLets` runs.
* `entryLCtx` — `entryGoal`'s local context at entry. Used at exit to
  find the let-decls that were added during the block, simply by
  diffing `entryLCtx` against `rootMVar`'s current local context.
* `rootMVar` — the proof-shaped mvar that, when ultimately instantiated,
  yields a proof of `entryGoal`'s target.
* `trackedMVars` — every metavariable allocated inside the block (the
  root, lift_lets leaves, witness mvars from `refine ⟨?_, _⟩`, subgoal
  mvars, …). On every `have`/`let` we extend *each* tracked mvar's
  declared local context with the new let-decl, so later tactics that
  assign any of them with a term referencing the let-bound name can do
  so without triggering zeta-reduction.

We deliberately do *not* carry a list of the let-decls themselves: the
authoritative record is the `LocalContext` carried by `rootMVar` (and
every other tracked mvar). `exitLiftLets` recovers the list to wrap
around the proof by diffing that against `entryLCtx`.
-/
structure LiftLetsState where
  entryGoal : MVarId
  entryLCtx : LocalContext
  rootMVar : MVarId
  trackedMVars : Array MVarId := #[]

/-- The monad in which lift_lets-mode tactics run.

A pinned-to-`Unit` CPS-plus-state transformer over `TacticM`: each
`LiftLetsM` action, when "invoked", takes the current state and a
continuation `α → LiftLetsState → TacticM Unit`, and chooses how to
call that continuation. Most tactics do their work and then call it.
The interesting case is `have`/`let`, which wraps the continuation in
`Meta.withLetDecl`: every subsequent tactic in the block (and the exit
step) then runs *inside* the scope, so the ambient `MetaM` local
context carries the let-decls for free.

This is morally `StateCpsT LiftLetsState TacticM` with the
continuation-return type fixed to `Unit` (pinning it keeps the
resulting type in `Type`, which `KeyedDeclsAttribute` requires).

Not every `TacticM` typeclass propagates here automatically — CPS
monads famously don't all play nice with e.g. `MonadFinally`. The
dispatcher in `LiftLets.Tactic` handles `MonadFinally`-flavoured
combinators (`withInfoContext`, `withRef`) at the underlying
`TacticM` layer by running the handler's continuation as a TacticM
action. -/
def LiftLetsM (α : Type) : Type :=
  LiftLetsState → (α → LiftLetsState → TacticM Unit) → TacticM Unit

namespace LiftLetsM

@[always_inline]
instance : Monad LiftLetsM where
  pure a   := fun s k => k a s
  bind x f := fun s k => x s fun a s' => f a s' k
  map f x  := fun s k => x s fun a s' => k (f a) s'

@[always_inline]
instance : MonadStateOf LiftLetsState LiftLetsM where
  get         := fun s k => k s s
  set s       := fun _ k => k ⟨⟩ s
  modifyGet f := fun s k => let (a, s') := f s; k a s'

@[always_inline]
instance : MonadLift TacticM LiftLetsM where
  monadLift x := fun s k => x >>= (k . s)

/-- Throw an exception by ignoring the continuation. `tryCatch` runs
`x` and, if the underlying `TacticM` throws, replaces the computation
with `handler e`. (The continuation is called at most once.) -/
@[always_inline]
instance : MonadExceptOf Exception LiftLetsM where
  throw e := fun _ _ => throw e
  tryCatch x handler := fun s k =>
    tryCatch (x s k) fun e => (handler e) s k

/-- `MonadRef` — lifts the underlying `TacticM` instance through the
state and continuation. -/
@[always_inline]
instance : MonadRef LiftLetsM where
  getRef := fun s k => do let r ← getRef; k r s
  withRef ref x := fun s k => withRef ref (x s k)

/-- Message-context add lifts through the underlying `TacticM`. -/
instance : AddMessageContext LiftLetsM where
  addMessageContext m :=
    liftM (m := TacticM) (AddMessageContext.addMessageContext m)

/-- Error-message context add lifts through as well; this is what
`throwError` needs (via `MonadError`). -/
instance : AddErrorMessageContext LiftLetsM where
  add ref m := liftM (m := TacticM) (AddErrorMessageContext.add ref m)

/-- Run a unit-valued `LiftLetsM` action in `TacticM` by supplying
`pure` as the terminal continuation. The result-type of the monad is
pinned to `Unit`, so the `LiftLetsTactic` handler type stays in
`Type` (which is what `KeyedDeclsAttribute` requires). Hence: run' only. -/
@[inline]
def run' (x : LiftLetsM Unit) (s : LiftLetsState) : TacticM Unit :=
  x s (fun _ _ => pure ())

/-- Lift a TacticM-level scope-introducer into `LiftLetsM`. The
continuation (i.e. the rest of the block) runs inside whatever scope
`scope` sets up. This is the key primitive that lets `have`/`let`
extend the ambient `MetaM` local context for every subsequent tactic. -/
@[inline]
def liftScope (scope : TacticM Unit → TacticM Unit) : LiftLetsM Unit :=
  fun s k => scope (k () s)

/-- Like `liftScope` but the scope also produces a value. -/
@[inline]
def liftScope1 {α} (scope : (α → TacticM Unit) → TacticM Unit) : LiftLetsM α :=
  fun s k => scope (fun a => k a s)

/-- `Meta.withLetDecl`, lifted as a CPS-style `LiftLetsM` action. The
continuation (i.e. everything after the `← withLetDecl …` line in a
`do`-block) runs inside the scope, so the ambient `MetaM` local context
contains the new fvar for every subsequent tactic in the block. -/
@[inline]
def withLetDecl (name : Name) (type value : Expr) : LiftLetsM Expr :=
  liftScope1 fun k => Meta.withLetDecl name type value (fun fvar => k fvar)

end LiftLetsM

end LiftLets
