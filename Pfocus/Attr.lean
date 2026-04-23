/-
Copyright (c) 2026 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license.

Pfocus-mode monad, state, and attribute.

Declaring the attribute here (rather than in `Pfocus.Tactic`) lets it run
in the `initialize` pass *before* the tactics that use it get elaborated
— a same-file `initialize` happens too late for `@[pfocus_tactic …]` to
be visible.
-/
import Lean
import Pfocus.Basic

namespace Pfocus

open Lean Elab Tactic Meta

/-- A let-declaration introduced by `have`/`let` inside pfocus mode. -/
structure PFocusLetDecl where
  fvarId : FVarId
  userName : Name
  type : Expr
  value : Expr

/-- State threaded through a `pfocus => ...` block.

* `entryGoal` — the goal that was main when `pfocus =>` was entered. Not
  assigned until `exitPFocus` runs.
* `entryLCtx` — `entryGoal`'s local context at entry.
* `rootMVar` — the proof-shaped mvar that, when ultimately instantiated,
  yields a proof of `entryGoal`'s target.
* `extraDecls` — let-decls added in this block, in order, to be wrapped
  around the proof at exit.
-/
structure PFocusState where
  entryGoal : MVarId
  entryLCtx : LocalContext
  rootMVar : MVarId
  extraDecls : Array PFocusLetDecl := #[]

/-- The monad in which pfocus-mode tactics run. -/
abbrev PFocusM := StateRefT PFocusState TacticM

/-- Signature of a pfocus-mode tactic elaborator. -/
abbrev PFocusTactic := Syntax → PFocusM Unit

/-! ### Attribute for registering pfocus tactics

`@[pfocus_tactic Pfocus.left]` registers a `PFocusTactic` for the syntax
kind `Pfocus.left`. This mirrors `@[tactic …]` for the regular tactic
category. `mkElabAttribute` integrates the attribute with Lean's
environment so it shows up normally in tooling.
-/

unsafe def pfocusTacticAttrImpl :
    IO (Lean.KeyedDeclsAttribute PFocusTactic) :=
  Lean.Elab.mkElabAttribute PFocusTactic
    `builtin_pfocus_tactic `pfocus_tactic `Pfocus
    ``Pfocus.PFocusTactic "pfocus"

@[implemented_by pfocusTacticAttrImpl]
opaque mkPfocusTacticAttr : IO (Lean.KeyedDeclsAttribute PFocusTactic)

initialize pfocusTacticAttr : Lean.KeyedDeclsAttribute PFocusTactic ←
  mkPfocusTacticAttr

end Pfocus
