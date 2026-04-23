/-
Copyright (c) 2026 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license.

Attribute for registering lift_lets-mode tactic elaborators.

Declaring the attribute here (rather than in `LiftLets.Tactic`) lets it
run in the `initialize` pass *before* the tactics that use it get
elaborated — a same-file `initialize` happens too late for
`@[lift_lets_tactic …]` to be visible.
-/
import LiftLets.Monad

namespace LiftLets

open Lean Elab Tactic

/-- Signature of a lift_lets-mode tactic elaborator. -/
abbrev LiftLetsTactic := Syntax → LiftLetsM Unit

/-! `@[lift_lets_tactic LiftLets.left]` registers a `LiftLetsTactic` for
the syntax kind `LiftLets.left`. This mirrors `@[tactic …]` for the
regular tactic category. `mkElabAttribute` integrates the attribute with
Lean's environment so it shows up normally in tooling. -/

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
