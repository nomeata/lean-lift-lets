import Pfocus

/-!
# Pfocus: a focused walkthrough

Open this file with the infoview on to get a feel for pfocus mode.
Every section is a small example that illustrates one feature; the
sections build on each other.
-/

namespace Demo

/-!
## 1. What `pfocus => …` does

Inside a `pfocus => …` block the library keeps a list of tracked
metavariables — subgoals the user has yet to close — and defers the
*assignment* of the original goal until the end of the block. That
means pfocus-level `have`/`let` can extend the local context in a way
that reaches every tracked subgoal, with no zeta-reduction on
assignments.

Anything the user runs with `tactic => tac` is a plain Lean tactic, so
inside pfocus mode you still have the familiar tactic language; the
new piece is the shared context.
-/

-- Closing a simple goal with `exact` (a shortcut for `tactic => exact`).
example (A : Prop) (a : A) : A := by
  pfocus =>
    exact a

/-!
## 2. Splitting a goal with `constructor`

`constructor` is a pfocus wrapper around `tactic => constructor`. The
new subgoals become tracked mvars; we then close each one.
-/

example (A B : Prop) (a : A) (b : B) : A ∧ B := by
  pfocus =>
    constructor
    · exact a
    · exact b

/-!
## 3. Shared `have`/`let`

The key pfocus feature: `have`/`let` at the pfocus level are visible
across every tracked subgoal. The binding is wrapped once around the
final proof term as an outer `let` — not duplicated into every leaf.
-/

example (A B : Prop) (h : A → B) (a : A) : A ∧ B := by
  pfocus =>
    have hb : B := h a
    constructor
    · exact a
    · exact hb

/-!
## 4. Context extensions stick across the witness of an `∃`

When `refine ⟨?_, ?_⟩` creates a witness subgoal plus a body subgoal,
a later `have` is propagated to the witness mvar too. So `exact m`
where `m` is a pfocus-level `let` unifies the witness against `m`,
not the underlying value — no zeta.
-/

example (g : Nat → Prop) (n : Nat) (h : (n + 1) + 0 = (n + 1)) (hg : g (n + 1)) :
    ∃ x : Nat, x + 0 = x ∧ g x := by
  pfocus =>
    tactic => refine ⟨?_, ?_, ?_⟩
    let m := n + 1
    have h' : m + 0 = m := h
    · exact m
    · exact h'
    · exact hg

/-!
## 5. `apply` and regular tactics

`apply`, `exact`, `rfl`, `trivial`, `assumption`, `grind`, `rw`, `simp`
are pfocus-level shortcuts around `tactic => …`. If you need a tactic
without a shortcut, just use the escape hatch.
-/

example (A B : Prop) (f : A → B) (a : A) : B := by
  pfocus =>
    apply f
    exact a

example (n : Nat) : n + 0 = n := by
  pfocus =>
    tactic => simp

/-!
## 6. Focusing with `·` and `next`

`· tacs` focuses on the first goal, runs `tacs`, and requires it to
close the goal. `next => tacs` focuses without the must-close check.
-/

example (P Q R : Prop) (p : P) (q : Q) (r : R) : P ∧ Q ∧ R := by
  pfocus =>
    constructor
    · exact p
    constructor
    · exact q
    · exact r

end Demo
