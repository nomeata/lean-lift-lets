import Pfocus

/-!
# Pfocus: a focused walkthrough

This file is meant to be read top-to-bottom, with the infoview open, to
develop intuition for `pfocus`. Each section is a short example that
illustrates one feature of the tactic family; they build on each other.
-/

open Pfocus

namespace Demo

/-!
## 1. Basics

`pfocus =>` is an entry tactic: it wraps the current goal in a `pfocus` box
so that the pfocus navigation and action tactics can see it. Think of it as
`conv =>` for conjunctions.
-/

-- Inside `pfocus`, the infoview shows `⊢ ⇣ P` — the focus is `P`, and the
-- outer context is hidden.
example (A B : Prop) (a : A) (b : B) : A ∧ B := by
  pfocus =>
    -- focus: A ∧ B
    left
    -- focus: A
    assumption
  exact b  -- `pfocus` leaves `B` as the remaining goal.

/-!
## 2. Shared local context

A key feature of `pfocus` is that the local context is shared across the
conjuncts. Anything introduced by `have` or `let` inside a pfocus block is
visible in every focus.
-/

example (P Q R : Prop) (p : P) (h₁ : P → Q) (h₂ : Q → R) : Q ∧ R := by
  pfocus =>
    have hq : Q := h₁ p
    have hr : R := h₂ hq
    left
    assumption
  exact h₂ (h₁ p)

/-!
## 3. Navigation: `left`, `right`, `out`

`left` and `right` dive into the left/right conjunct of an `∧`. `out` goes
back up one level. Navigation never changes the underlying proposition —
only which piece is in focus.
-/

example (A B C : Prop) (a : A) (b : B) (c : C) : (A ∧ B) ∧ C := by
  pfocus =>
    left
    -- focus: A ∧ B
    right
    -- focus: B
    assumption
    out
    -- focus: A ∧ B again, but the `B` part has been discharged.
    left
    assumption
  exact c

/-!
## 4. Actions

Actions are pfocus tactics that make real progress on the focus:

* `closing => tac` runs `tac` as a regular tactic and expects it to close
  the focus entirely.
* `assumption`, `rfl`, `trivial`, `grind` are wrappers around `closing =>`.
* `conv => ...` rewrites the focus using a conv block.
* `rw [h]` is a wrapper around `conv => rw [h]`.
* `apply thm` applies a theorem; the resulting subgoals become the new
  (conjoined) focus.
* `tactic => ...` is the most general form: it runs a regular tactic,
  captures the resulting subgoals, and threads them back through the outer
  context.
-/

-- `rw` inside pfocus: only affects the focus.
example (x : Nat) (h : x + 0 = x) : (x + 0 = x) ∧ True := by
  pfocus =>
    left
    rw [h]
    -- focus is now `x = x`
  trivial

-- `apply` propagates subgoals. When `apply h` produces one goal, the focus
-- becomes that goal; when it produces multiple, the focus becomes a
-- conjunction that you can step into.
example (A B : Prop) (f : A → B) (a : A) : B ∧ True := by
  pfocus =>
    left
    apply f
    assumption

end Demo
