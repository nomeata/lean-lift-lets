import Pfocus
open Pfocus

/-!
Tests for the `exists` pfocus tactic: it works like `constructor`, creating
a fresh mvar `?x : α` as the witness and turning the focus from
`∃ x : α, P x` into `P ?x`. Subsequent pfocus tactics can unify `?x` with
a concrete value, or fail if they leave it unconstrained.
-/

-- The simplest case: `rfl` unifies `?x` with the concrete RHS.
example : ∃ x : Nat, x = 5 := by
  pfocus =>
    exists
    closing => rfl

-- Context-building happens before committing the witness.
example (n : Nat) (h : n + 0 = n) : ∃ x : Nat, x + 0 = x := by
  pfocus =>
    have h' : n + 0 = n := h
    exists
    closing => exact h'

-- `apply` leaves `?x` unassigned, so we need a subsequent step that picks
-- a concrete witness (here, `exact hg 0` unifies `?x := 0`).
example (g : Nat → Prop) (hg : ∀ n, g n) : ∃ x : Nat, g x := by
  pfocus =>
    exists
    closing => exact hg 0

-- Key use case: `have`/`let` at the pfocus level is visible across the
-- `exists`. The let binding is applied to the final proof term as a
-- single outer `let` (not zeta-inlined into each use).
example (n : Nat) : ∃ x : Nat, x + 0 = n ∧ True := by
  pfocus =>
    have h : n + 0 = n := by simp
    exists
    left
    closing => exact h

-- `let` works the same way and emits a pfocus goal that references the
-- let-bound identifier rather than zeta-reducing it away.
example : ∃ x : Nat, x = 3 + 2 := by
  pfocus =>
    let five := 3 + 2
    exists
    closing =>
      show _ = five
      rfl
