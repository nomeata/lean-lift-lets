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

/-!
## 5. Existentials

`pfocus` also understands `∃`. The `exists` navigation tactic steps into an
existential, turning `⊢ ⇣ ∃ x, P x` into a predicate focus that displays
as `⊢ ⇣ ?x + 0 = ?x` (for instance): the bound variable shows up as a
`?x` placeholder so the applied body is visible. Inside that predicate
focus, `tactic => ...` behaves differently from the proposition case: it
creates a *fresh metavariable* `?x : α` to stand in for the witness, then
runs the user's tactic against the goal `P ?x`.

Two outcomes matter:

* If the tactic *assigns* `?x` to some term `e` (typically via `exact`
  that unifies `?x` with the concrete value), a `let x := e` is added to
  the local context and the `∃` is discharged via `Exists.intro x`.
* If the tactic *doesn't* assign `?x`, the `∃` stays in the goal; the
  predicate may have been transformed along the way.

This lets context-building steps (`have`, `let`) happen *outside* the
witness choice, which you can't do if you blindly `constructor` up-front.
-/

-- Witness-commit: `rfl` unifies `?x` with `5`, and we're done.
example : ∃ x : Nat, x = 5 := by
  pfocus =>
    exists
    -- focus: `fun x => x = 5`, with a fresh `?x : Nat` in scope for the
    -- `tactic =>` block.
    tactic =>
      exact rfl

-- Shared context across a witness commit. `h'` is introduced in pfocus
-- mode, before entering the existential; once inside, the fresh `?x` can
-- be unified against whatever `h'` requires.
example (n : Nat) (h : n + 0 = n) : ∃ x : Nat, x + 0 = x := by
  pfocus =>
    have h' : n + 0 = n := h
    exists
    tactic =>
      exact h'

-- No-witness-commit: the tactic does useful predicate work without
-- picking a specific `x`. The `∃` stays in the goal for us to close
-- afterwards.
example (g : Nat → Prop) (hg : ∀ n, g n) : ∃ x : Nat, g x := by
  pfocus =>
    exists
    tactic =>
      apply hg  -- closes against a generic `?x`; `?x` stays free.
  -- After exit, the goal is `∃ x, True` (the predicate collapsed).
  exact ⟨0, trivial⟩

end Demo
