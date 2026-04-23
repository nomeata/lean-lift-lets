import Pfocus
open Pfocus

/-!
Tests for existential focusing. The `intro` navigation tactic steps into
an `∃`, turning `pfocus C (∃ x, P x)` into `pfocus (fun p => C (∃ x, p x))
(fun x => P x)`. Inside that predicate focus, `tactic => ...` creates a
fresh `?x` mvar for the bound variable; if the tactic assigns it, a
`let x := e` is added to the local context.
-/

-- Committing a witness via `exact rfl`.
example : ∃ x : Nat, x = 5 := by
  pfocus =>
    intro
    -- focus: `fun x => x = 5`
    tactic =>
      -- goal here is `?x = 5`; `rfl` unifies ?x with 5 and closes.
      exact rfl

-- Same, but making the outer do real work first: the pfocus block
-- introduces a shared hypothesis that the predicate focus can rely on.
example (n : Nat) (h : n + 0 = n) : ∃ x : Nat, x + 0 = x := by
  pfocus =>
    have h' : n + 0 = n := h
    intro
    -- predicate focus, with h' in scope.
    tactic =>
      exact h'

-- Unassigned case: `tactic =>` errors with a clear message because it
-- didn't commit a witness.
/-- error: `tactic =>` with an existential focus: the tactic did not commit a witness for the bound variable. Use `conv => ...` to transform the predicate without committing, or arrange for the tactic to pick a witness (e.g. via `exact`). -/
#guard_msgs in
example : ∃ x : Nat, True := by
  pfocus =>
    intro
    tactic =>
      trivial
