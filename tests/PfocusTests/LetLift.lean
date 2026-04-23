import Pfocus

/-!
Main feature of pfocus mode: `have`/`let` introduced *mid-proof* remain
visible and usable across the remaining subgoals, and the let-bindings
show up in the final proof term — they are not zeta-reduced into every
use site.

The motivating example from the design discussion: a `let` introduced
between `constructor` (which creates an existential witness + body
subgoals) and the `exact` that closes the body must not zeta-reduce the
witness assignment into the body's underlying value.
-/

example (g : Nat → Prop) (n : Nat) (h : (n + 1) + 0 = (n + 1)) (hg : g (n + 1)) :
    ∃ x : Nat, x + 0 = x ∧ g x := by
  pfocus =>
    tactic => refine ⟨?_, ?_, ?_⟩
    -- three subgoals: `?x : Nat`, `?x + 0 = ?x`, and `g ?x`.
    let m := n + 1
    have h' : m + 0 = m := h
    · exact m
    · exact h'
    · exact hg

-- `let` at the pfocus level survives `apply` producing new subgoals.
example (f : Nat → Nat → Prop) (g : ∀ a b, f a b) : f 0 0 ∧ f 1 1 := by
  pfocus =>
    let zero := (0 : Nat)
    constructor
    · exact g zero zero
    · exact g 1 1

-- `have` introduced in one branch is NOT visible in sibling branches,
-- because it isn't a pfocus-level `have` (it's inside `tactic =>`).
-- The pfocus-level `have` above `constructor` is; the inner
-- `tactic => have` here is strictly local.
example (A B : Prop) (a : A) (b : B) : A ∧ B := by
  pfocus =>
    constructor
    · tactic =>
        have _ := a
        exact a
    · exact b
