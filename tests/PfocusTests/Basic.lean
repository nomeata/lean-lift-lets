import Pfocus

/-!
Basic tests for the `pfocus` tactic family.

These tests exercise one feature each; the expected behaviors are noted
in-line. Build this file with `lake env lean tests/Basic.lean` (or just
`lake build` after adding it to `lakefile.toml`).
-/


open Pfocus

section Navigation

-- `left` focuses on the left conjunct.
example (A B : Prop) (a : A) (b : B) : A ∧ B := by
  pfocus =>
    left
    closing => exact a
  -- remaining goal: B
  exact b

-- `right` focuses on the right conjunct.
example (A B : Prop) (a : A) (b : B) : A ∧ B := by
  pfocus =>
    right
    closing => exact b
  exact a

-- A completed pfocus block returns to the outer goal.
example (A : Prop) (a : A) : A ∧ A := by
  pfocus =>
    left
    closing => exact a
  exact a

-- `out` undoes a focus step.
example (A B : Prop) (a : A) (b : B) : A ∧ B := by
  pfocus =>
    left
    out
    right
    closing => exact b
  exact a

end Navigation

section Closing

-- `assumption` closes the focus from a hypothesis.
example (A B : Prop) (a : A) (b : B) : A ∧ B := by
  pfocus =>
    left
    assumption
  exact b

-- `trivial` closes trivial focuses.
example : True ∧ (2 = 2) := by
  pfocus =>
    left
    trivial
  rfl

-- `rfl` closes an equality focus.
example (x : Nat) : (x + 0 = x) ∧ True := by
  pfocus =>
    left
    closing => rfl

end Closing

section Apply

-- `apply` with no subgoals closes the focus.
example (A B : Prop) (h : A → B) (a : A) : B ∧ True := by
  pfocus =>
    left
    apply h
    closing => exact a

end Apply

section HaveAndLet

example (A B : Prop) (h : A → B) (a : A) : A ∧ B := by
  pfocus =>
    have hb : B := h a
    left
    assumption
  exact h a

end HaveAndLet

section Exit

-- explicit exit leaves pfocus mode.
example (A : Prop) (a : A) : A := by
  pfocus =>
    exit
  exact a

end Exit

section Nested

-- Three-way conjunction, focusing each piece.
example (A B C : Prop) (a : A) (b : B) (c : C) : A ∧ B ∧ C := by
  pfocus =>
    left
    assumption
  pfocus =>
    left
    assumption
  exact c

-- Moving `out` works.
example (A B : Prop) (a : A) (b : B) : A ∧ B := by
  pfocus =>
    right
    out
    left
    assumption
  exact b

end Nested

section ConvAndRw

-- `conv` changes the focus via an equation.
example (x : Nat) (h : x + 0 = x) : (x + 0 = x + 0) ∧ True := by
  pfocus =>
    left
    conv => rw [h]
    closing => rfl

-- `rw` wraps `conv => rw`.
example (x : Nat) (h : x = x + 0) : (x + 0 = x + 0) ∧ True := by
  pfocus =>
    left
    rw [← h]
    closing => rfl

end ConvAndRw

section DoneAndNext

-- `done` strips the enclosing `_ ∧ True` / `True ∧ _` after closing.
example (A B : Prop) (a : A) (b : B) : A ∧ B := by
  pfocus =>
    left
    closing => exact a
    -- `closing` has already called `done`; focus is now B.
    closing => exact b

-- `next` steps to the next unfinished leaf in a right-nested tree.
example (A B C : Prop) (a : A) (b : B) (c : C) : A ∧ B ∧ C := by
  pfocus =>
    left
    assumption
    -- After `done`, outer = id, focus = B ∧ C.
    left
    assumption
  exact c

end DoneAndNext

section Show

-- `show` changes the focus to a definitionally-equal proposition.
example (A : Prop) (a : A) : (A ∧ True) := by
  pfocus =>
    left
    show A
    assumption

end Show
