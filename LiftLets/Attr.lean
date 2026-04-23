/-
Copyright (c) 2026 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license.

LiftLets-mode monad, state, and attribute.

Declaring the attribute here (rather than in `LiftLets.Tactic`) lets it run
in the `initialize` pass *before* the tactics that use it get elaborated
— a same-file `initialize` happens too late for `@[lift_lets_tactic …]` to
be visible.
-/
import Lean
import LiftLets.Basic

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

/-- The monad in which lift_lets-mode tactics run. -/
abbrev LiftLetsM := StateRefT LiftLetsState TacticM

/-- Signature of a lift_lets-mode tactic elaborator. -/
abbrev LiftLetsTactic := Syntax → LiftLetsM Unit

/-! ### Attribute for registering lift_lets tactics

`@[lift_lets_tactic LiftLets.left]` registers a `LiftLetsTactic` for the syntax
kind `LiftLets.left`. This mirrors `@[tactic …]` for the regular tactic
category. `mkElabAttribute` integrates the attribute with Lean's
environment so it shows up normally in tooling.
-/

unsafe def liftLetsTacticAttrImpl :
    IO (Lean.KeyedDeclsAttribute LiftLetsTactic) :=
  Lean.Elab.mkElabAttribute LiftLetsTactic
    `builtin_lift_lets_tactic `lift_lets_tactic `LiftLets
    ``LiftLets.LiftLetsTactic "lift_lets"

@[implemented_by liftLetsTacticAttrImpl]
opaque mkLiftLetsTacticAttr : IO (Lean.KeyedDeclsAttribute LiftLetsTactic)

initialize liftLetsTacticAttr : Lean.KeyedDeclsAttribute LiftLetsTactic ←
  mkLiftLetsTacticAttr

end LiftLets
