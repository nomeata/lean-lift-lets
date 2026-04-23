import Pfocus
open Pfocus

/-!
Tests for existential focusing. The `intro` navigation tactic steps into
an `∃`, turning `pfocus C (∃ x, P x)` into `pfocus (fun p => C (∃ x, p x))
(fun x => P x)`. Inside that predicate focus, `tactic => ...` creates a
fresh `?x` mvar for the bound variable; if the tactic assigns it, a
`let x := e` is added to the local context and the `∃` is discharged.
If it doesn't, the `∃` stays in the goal with a possibly rewritten
predicate.
-/

-- Assigned case: committing a witness via `exact rfl` (which unifies ?x
-- with the concrete RHS).
example : ∃ x : Nat, x = 5 := by
  pfocus =>
    intro
    tactic =>
      exact rfl

-- Assigned case with a shared hypothesis across the pfocus block.
example (n : Nat) (h : n + 0 = n) : ∃ x : Nat, x + 0 = x := by
  pfocus =>
    have h' : n + 0 = n := h
    intro
    tactic =>
      exact h'

-- Unassigned case: the tactic rewrites the predicate without committing
-- a witness. The `∃` stays in the goal after pfocus exits; we close it
-- with a regular tactic.
example (h : ∀ y : Nat, y + 0 = y) : ∃ x : Nat, x + 0 = x := by
  pfocus =>
    intro
    tactic =>
      -- `apply h` closes against a generic `?x`, leaves `?x` unassigned.
      apply h
  -- Pfocus leaves `⊢ ∃ x : Nat, True` (or equivalent) to be closed.
  exact ⟨0, trivial⟩

-- When the tactic inside a predicate focus leaves no open subgoals but
-- also doesn't commit a witness, the new predicate collapses to
-- `fun _ => True`; the ∃ is still trivially closable outside the block.
example (g : Nat → Prop) (hg : ∀ n, g n) : ∃ x : Nat, g x := by
  pfocus =>
    intro
    tactic =>
      apply hg
  exact ⟨0, trivial⟩
