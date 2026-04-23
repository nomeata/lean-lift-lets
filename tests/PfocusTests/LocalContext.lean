import Pfocus
open Pfocus

/-! Test that `tactic =>` rejects actions that leave subgoals whose local
context differs from the pfocus goal. -/

-- The `rw [h]` produces three goals with dependencies on hypotheses added
-- by `intro`; we expect a user-friendly error rather than a type mismatch.
/-- error: a pfocus action produced a subgoal whose local context differs from the enclosing pfocus goal. This typically happens when a tactic like `intro` introduces a new hypothesis that cannot be propagated out. Close such goals inside the `tactic => ...` block.

Offending goal:
  case a
  P1 : Nat → Prop
  P2 : Prop
  x : Nat
  h : (∀ (y : Nat), P1 y) → P2 → x + 0 = x
  y✝ : Nat
  ⊢ P1 y✝ -/
#guard_msgs in
example {P1 : Nat → Prop} {P2 : Prop} (x : Nat)
    (h : (∀ y, P1 y) → P2 → x + 0 = x) : (x + 0 = x) ∧ True := by
  pfocus =>
    left
    tactic =>
      rw [h]
      intro
  trivial

-- The same proof works when the extra goals are discharged inside the
-- `tactic =>` block, since the only subgoal then is the rewritten focus
-- and it shares the base context.
example {P1 : Nat → Prop} {P2 : Prop} (x : Nat)
    (h : (∀ y, P1 y) → P2 → x + 0 = x)
    (hP1 : ∀ y, P1 y) (hP2 : P2) : (x + 0 = x) ∧ True := by
  pfocus =>
    left
    tactic =>
      rw [h] <;> first | exact hP1 | exact hP2
