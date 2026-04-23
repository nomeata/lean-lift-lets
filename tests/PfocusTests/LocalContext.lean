import Pfocus

/-!
Test that `tactic => …` rejects new subgoals whose local context
differs from the main goal's (e.g. after `intro` adds a hypothesis).
The user-facing error points them at `have`/`let` at the pfocus level,
which *is* allowed to extend the context.
-/

/--
error: `tactic =>` produced a subgoal whose local context differs from the main goal. Use a pfocus-level `have`/`let` to introduce hypotheses so they reach every tracked goal.

Offending goal:
  P Q : Prop
  p a✝ : P
  ⊢ Q
-/
#guard_msgs in
example (P Q : Prop) (p : P) : P → Q := by
  pfocus =>
    tactic => intro

-- Using pfocus `have` instead: the extra hypothesis is propagated
-- into every tracked subgoal, so the proof succeeds.
example (P Q R : Prop) (f : P → Q → R) (p : P) (q : Q) : R := by
  pfocus =>
    apply f
    · exact p
    · exact q
