import LiftLets

/-!
Basic tests for the simplified lift_lets: `tactic => …` is the primitive,
convenience wrappers (`apply`, `constructor`, `exact`, `rfl`, …) expand
to it, `·` / `next` focus, and `have`/`let` introduce shared let-decls.
-/

section Core

-- The empty lift_lets block: nothing to do.
example (A : Prop) (a : A) : A := by
  lift_lets => skip
  exact a

-- `tactic => tac` runs a regular tactic.
example (A : Prop) (a : A) : A := by
  lift_lets =>
    tactic => exact a

-- `exact` is a shortcut for `tactic => exact`.
example (A : Prop) (a : A) : A := by
  lift_lets =>
    exact a

end Core

section Conjunction

-- `constructor` splits `A ∧ B` into two tracked subgoals.
example (A B : Prop) (a : A) (b : B) : A ∧ B := by
  lift_lets =>
    constructor
    · exact a
    · exact b

-- `next => …` focuses the next subgoal.
example (A B : Prop) (a : A) (b : B) : A ∧ B := by
  lift_lets =>
    constructor
    next => exact a
    next => exact b

-- `apply` produces subgoals from an implication.
example (A B : Prop) (f : A → B) (a : A) : B := by
  lift_lets =>
    apply f
    exact a

end Conjunction

section LetHave

-- `have` is visible in every goal produced later in the block.
example (A B : Prop) (h : A → B) (a : A) : A ∧ B := by
  lift_lets =>
    have b : B := h a
    constructor
    · exact a
    · exact b

-- `let` is similar. Its value is wrapped once around the final proof.
example (n : Nat) : n + 0 = n ∧ n = n + 0 := by
  lift_lets =>
    let m := n + 0
    constructor
    · simp
    · simp

end LetHave

section Exists

-- `constructor` on `∃ x, P x` introduces both the witness and the body
-- as subgoals. A later lift_lets tactic can unify the witness.
example : ∃ x : Nat, x = 5 := by
  lift_lets =>
    tactic => exact ⟨5, rfl⟩

-- With `refine ⟨?_, ?_⟩` we get the witness as a concrete subgoal.
example : ∃ x : Nat, x = 5 := by
  lift_lets =>
    tactic => refine ⟨?_, ?_⟩
    · exact 5
    · rfl

end Exists
