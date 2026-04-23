import LiftLets

/-!
# lift-lets: a focused walkthrough

Open this file with the infoview on to get a feel for lift_lets mode.
Every section is a small example that illustrates one feature; the
sections build on each other.
-/

namespace Demo

/-!
## 1. What `lift_lets => …` does

Inside a `lift_lets => …` block the library keeps a list of tracked
metavariables — subgoals the user has yet to close — and defers the
*assignment* of the original goal until the end of the block. That
means lift_lets-level `have`/`let` can extend the local context in a way
that reaches every tracked subgoal, with no zeta-reduction on
assignments.

Anything the user runs with `tactic => tac` is a plain Lean tactic, so
inside lift_lets mode you still have the familiar tactic language; the
new piece is the shared context.
-/

-- Closing a simple goal with `exact` (a shortcut for `tactic => exact`).
example (A : Prop) (a : A) : A := by
  lift_lets =>
    exact a

/-!
## 2. Splitting a goal with `constructor`

`constructor` is a lift_lets wrapper around `tactic => constructor`. The
new subgoals become tracked mvars; we then close each one.
-/

example (A B : Prop) (a : A) (b : B) : A ∧ B := by
  lift_lets =>
    constructor
    · exact a
    · exact b

/-!
## 3. Shared `have`/`let`

The key lift_lets feature: `have`/`let` at the lift_lets level are visible
across every tracked subgoal. The binding is wrapped once around the
final proof term as an outer `let` — not duplicated into every leaf.
-/

example (A B : Prop) (h : A → B) (a : A) : A ∧ B := by
  lift_lets =>
    have hb : B := h a
    constructor
    · exact a
    · exact hb

/-!
## 4. Context extensions stick across the witness of an `∃`

When `refine ⟨?_, ?_⟩` creates a witness subgoal plus a body subgoal,
a later `have` is propagated to the witness mvar too. So `exact m`
where `m` is a lift_lets-level `let` unifies the witness against `m`,
not the underlying value — no zeta.
-/

example (g : Nat → Prop) (n : Nat) (h : (n + 1) + 0 = (n + 1)) (hg : g (n + 1)) :
    ∃ x : Nat, x + 0 = x ∧ g x := by
  lift_lets =>
    tactic => refine ⟨?_, ?_, ?_⟩
    let m := n + 1
    have h' : m + 0 = m := h
    · exact m
    · exact h'
    · exact hg

/-!
## 5. `apply` and regular tactics

`apply`, `exact`, `rfl`, `trivial`, `assumption`, `grind`, `rw`, `simp`
are lift_lets-level shortcuts around `tactic => …`. If you need a tactic
without a shortcut, just use the escape hatch.
-/

example (A B : Prop) (f : A → B) (a : A) : B := by
  lift_lets =>
    apply f
    exact a

example (n : Nat) : n + 0 = n := by
  lift_lets =>
    tactic => simp

/-!
## 6. Focusing with `·` and `next`

`· tacs` focuses on the first goal, runs `tacs`, and requires it to
close the goal. `next => tacs` focuses without the must-close check.
-/

example (P Q R : Prop) (p : P) (q : Q) (r : R) : P ∧ Q ∧ R := by
  lift_lets =>
    constructor
    · exact p
    constructor
    · exact q
    · exact r

/-!
## 7. A larger example

A proof that threads two `let`s through a tree of subgoals. Each `let`
is introduced *after* `constructor` has split the existential into a
witness subgoal plus the body; the witness is then supplied by `exact
as` (resp. `exact bs`), which unifies directly against the lift_lets-level
let-fvar — no zeta-reduction — so the remaining subgoals still see the
same `as` / `bs` identifiers.
-/

example (xs : List Nat) (h : xs.length = 10) :
    ∃ as bs, as.length = 5 ∧ xs = as ++ bs ∧ as.length = bs.length := by
  lift_lets =>
    constructor
    constructor
    constructor
    · let as := xs.take 5
      have has : List.length as = 5 := by grind
      exact has
    · constructor
      · tactic => symm
        let bs := xs.drop 5
        tactic => change as ++ bs = xs
        apply List.take_append_drop
      · tactic => grind

end Demo
