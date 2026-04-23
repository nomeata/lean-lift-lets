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

/-- A let-declaration introduced by `have`/`let` inside lift_lets mode. -/
structure LiftLetsDecl where
  fvarId : FVarId
  userName : Name
  type : Expr
  value : Expr

/-- State threaded through a `lift_lets => ...` block.

* `entryGoal` — the goal that was main when `lift_lets =>` was entered. Not
  assigned until `exitLiftLets` runs.
* `entryLCtx` — `entryGoal`'s local context at entry.
* `rootMVar` — the proof-shaped mvar that, when ultimately instantiated,
  yields a proof of `entryGoal`'s target.
* `extraDecls` — let-decls added in this block, in order, to be wrapped
  around the proof at exit.
* `trackedMVars` — every metavariable allocated inside the block (the
  root, lift_lets leaves, witness mvars from `exists`, subgoal mvars…). When
  `have`/`let` extends the context we extend *each* tracked mvar's
  declared local context too, so later tactics that assign any of them
  can do so in terms of the new let-bound variable without triggering
  zeta-reduction.
-/
structure LiftLetsState where
  entryGoal : MVarId
  entryLCtx : LocalContext
  rootMVar : MVarId
  extraDecls : Array LiftLetsDecl := #[]
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
