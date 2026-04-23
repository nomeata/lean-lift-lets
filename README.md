# pfocus

A small Lean 4 library of tactics that maintain a *focus* inside a proof
goal, letting you discharge pieces of a conjunction one at a time while
sharing a growing local context. Think of `conv`, but aimed at conjunctions
rather than rewriting.

## Quick start

```lean
import Pfocus
open Pfocus

example (P Q R : Prop) (p : P) (h₁ : P → Q) (h₂ : Q → R) : Q ∧ R := by
  pfocus =>
    have hq : Q := h₁ p          -- shared across the whole pfocus block
    left                         -- focus: Q
    closing => exact hq
  exact h₂ (h₁ p)                -- remaining goal: R
```

Inside a `pfocus => ...` block, the infoview shows `⊢ ⇣ P` where `P` is the
currently focused subproposition. The outer surrounding context — what will
be reassembled around `P` — is hidden.

## Feature overview

### Navigation

| tactic  | effect                                                          |
| ------- | --------------------------------------------------------------- |
| `left`  | focus on the left conjunct (`A ∧ B` → focus on `A`)            |
| `right` | focus on the right conjunct (`A ∧ B` → focus on `B`)           |
| `out`   | undo one focus step                                             |
| `done`  | after the focus has been reduced to `True`, pop the frame      |
| `next`  | navigate to the next unfinished leaf in the conjunction tree   |
| `exists`| commit an existential (creates a fresh witness mvar `?x`)      |
| `exit`  | leave `pfocus` mode early                                       |
| `skip`  | do nothing                                                      |

Navigation is purely structural: `newOuter newFocus` is always β-definitionally
equal to `oldOuter oldFocus`. The only step that changes the underlying
proposition is `done`, which absorbs a `True` via `true_and` / `and_true`.

### Actions

| tactic               | effect                                                     |
| -------------------- | ---------------------------------------------------------- |
| `closing => tac`     | discharge the focus by running `tac`                       |
| `assumption`         | = `closing => assumption`                                  |
| `rfl`                | = `closing => rfl`                                         |
| `trivial`            | = `closing => trivial`                                     |
| `grind`              | = `closing => grind`                                       |
| `conv => cs`         | rewrite the focus using a `conv` block                     |
| `rw [thms]`          | = `conv => rw [thms]`                                      |
| `apply e`            | apply `e`; resulting subgoals become the new focus         |
| `tactic => tac`      | run any tactic; subgoals become the focus (conjoined)     |
| `show P'`            | change the focus to a definitionally-equal proposition     |

### Context

| tactic                 | effect                                                   |
| ---------------------- | -------------------------------------------------------- |
| `have h : t := pf`     | extend the local context, focus unchanged                |
| `let x : t := v`       | extend the local context with a let-binding              |

All context tactics operate on the pfocus goal directly and propagate to the
remaining focus.

## Design at a glance

The core gadget is

```lean
@[irreducible] def pfocus (C : Prop → Prop) (P : Prop) : Prop := C P
```

marked `@[irreducible]` so the tactic framework can see it in goals without
Lean unfolding it under us. Navigation tactics manipulate the *outer
context* `C` and the *focused proposition* `P`, always preserving `C P` up
to β-reduction. Progress tactics reduce to `pfocus_imp`:

```lean
theorem pfocus_imp_raw {C : Prop → Prop} {X Y : Prop}
    (mono : (X → Y) → C X → C Y) (h : X → Y) (c : pfocus C X) : pfocus C Y
```

The monotonicity witness `mono` is constructed on the fly by a short
`MetaM` function (`buildMonoSpec`) that walks the structure of `C`. A
user-facing `PFocusable` class ships with instances for the identity,
left-and, and right-and contexts; these let users state their own
monotonicity results about `pfocus` without going through `MetaM`.

### File map

| file               | role                                                      |
| ------------------ | --------------------------------------------------------- |
| `Pfocus/Basic.lean`  | `pfocus`, `pfocus_intro`/`elim`, `PFocusable`, `pfocus_imp` |
| `Pfocus/Delab.lean`  | infoview rendering as `⇣ P`                              |
| `Pfocus/Tactic.lean` | syntax category `pfocus`, entry tactic, all inner tactics |
| `tests/Basic.lean`   | small unit tests for every tactic                        |
| `tests/Demo.lean`    | walkthrough-style demonstration                          |

## Why this design?

* **Isolated syntax category.** `pfocus => ...` introduces a real syntax
  category, mirroring how `conv` is structured. This prevents accidental
  mixing with regular tactics and lets us have a `left`/`right`/`out` that
  don't collide with other tactic meanings.

* **β-normal outer contexts.** After each navigation step, we β-normalize
  the outer context before storing it in the goal. This keeps the goal
  printout small and, more importantly, lets `buildMono` produce a term
  whose type matches the goal exactly — no surprises from unreduced
  applications of the previous outer.

* **Meta-constructed monotonicity.** Rather than relying on `PFocusable`
  instance synthesis for monotonicity (which requires higher-order
  unification that Lean doesn't always find), we walk the outer's body and
  construct a concrete `mono` term in `MetaM`. The type class remains as a
  user-facing API, with the obvious instances.

* **Idempotent `exit`.** `exitPFocus` is idempotent: if the current goal is
  not a pfocus goal, it does nothing. This lets `pfocus => ...` always call
  `exit` at the end of the block, regardless of what the user did inside.

## A walkthrough of one goal

```lean
example (A B C : Prop) (a : A) (b : B) (c : C) : (A ∧ B) ∧ C := by
  pfocus =>
    -- ⊢ ⇣ (A ∧ B) ∧ C
    left
    -- ⊢ ⇣ A ∧ B
    right
    -- ⊢ ⇣ B
    assumption
    -- after closing + done: ⊢ ⇣ A
    assumption
    -- after closing + done: ⊢ ⇣ C (right sibling of the outer `left`)
    -- `exit` will unwrap to `C`
  exact c
```

## Existentials

`pfocus` can also focus inside an `∃`. The `exists` tactic behaves like
`constructor` — it creates a fresh mvar `?x` for the witness and turns
the focus from `∃ x, P x` into `P ?x`. Any later pfocus tactic that
unifies against `?x` (e.g. `exact`, `rfl`, `apply`) commits the witness.

Crucially, `pfocus` defers the assignment of the outer goal until exit
time, so `have`/`let` introduced *before* `exists` remain available to
tactics *after* `exists`, and the let-bindings are wrapped once around
the final proof term rather than zeta-inlined into every use:

```lean
example (n : Nat) : ∃ x : Nat, x + 0 = n ∧ True := by
  pfocus =>
    have h : n + 0 = n := by simp   -- visible across `exists`
    exists
    left
    closing => exact h
```

## Limitations

The MVP covers `And` and `Exists`. Other monotone connectives (`Or` on one
side, `→`, universe-quantified forms) are natural extensions: each needs a
new matcher in `Tactic.lean` plus, for the `And`-style ones, an entry in
`PFocusable`. Nested existentials and non-trivial outer wrapping around an
`∃` aren't yet supported by the `tactic =>` specialization.

## Contributing

Please open an issue or pull request on GitHub. The library is intended
both as a useful tactic and as an annotated example of how to build a
custom tactic family in Lean 4, so improvements to clarity of the
implementation are especially welcome.
