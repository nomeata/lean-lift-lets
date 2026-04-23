import Pfocus
open Pfocus

/-!
Test that `have`/`let` introduced inside pfocus mode *after* `exists`
don't get zeta-reduced when the existential witness gets assigned.

This is the motivating example from the design discussion: the
`exact h'` should unify `?x := m` (the let-bound identifier), not
`?x := n + 1` (its value).
-/

example (g : Nat → Prop) (n : Nat) (h : (n + 1) + 0 = (n + 1)) (hg : g (n + 1)) :
    ∃ x : Nat, x + 0 = x ∧ g x := by
  pfocus =>
    exists
    let m := n + 1
    have h' : m + 0 = m := h
    left
    closing => exact h'
  -- The remaining sibling is `g ?x`, with `?x` unified against `m`.
  -- Because `m`'s definition was a `let`, `?x` is `m`, not `n + 1`
  -- (no zeta-reduction on the assignment).
  show g m
  exact hg

-- Variant from the original request: the let/have come *after* `left`
-- and an intermediate no-op `tactic =>` before the closing.
example (g : Nat → Prop) (n : Nat) (h : (n + 1) + 0 = (n + 1)) (hg : g (n + 1)) :
    ∃ x : Nat, (x + 0 = x ∧ g x) := by
  pfocus =>
    exists
    left
    let m := n + 1
    have h' : m + 0 = m := h
    tactic => skip
    closing => exact h'
  show g m
  exact hg
