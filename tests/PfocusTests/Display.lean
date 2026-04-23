import Pfocus
open Pfocus

/-!
Verify how the pfocus goal renders in the infoview.

`exists` now introduces a *real* fresh mvar as the witness, so the user
sees the metavariable directly in the focus — no special unexpander
rewriting is needed.
-/

/--
info: ⊢ ⇣ (0 = 0 ∧ True)
-/
#guard_msgs in
example : 0 = 0 ∧ True := by
  pfocus =>
    trace_state
    left
    rfl
