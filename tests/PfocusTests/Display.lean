import Pfocus
open Pfocus

/-!
Verify the `?x`-style display for predicate focuses. The pfocus goal
`pfocus (fun p => ∃ x, p x) (fun x => x + 0 = x)` renders as
`⇣ ?x + 0 = ?x` — the bound variable is shown as a `?x` named hole so
the user sees the applied body rather than a raw lambda.
-/

/--
info: n : Nat
h : n + 0 = n
⊢ ⇣ (?x + 0 = ?x)
-/
#guard_msgs in
example (n : Nat) (h : n + 0 = n) : ∃ x : Nat, x + 0 = x := by
  pfocus =>
    exists
    trace_state
    tactic => exact h

-- Plain Prop focus still renders as before (no `?`-substitution).
/--
info: ⊢ ⇣ (0 = 0 ∧ True)
-/
#guard_msgs in
example : 0 = 0 ∧ True := by
  pfocus =>
    trace_state
    left
    rfl
