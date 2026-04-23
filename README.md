# lift-lets

A small Lean 4 tactic family whose `lift_lets => …` block lets you
thread `have` / `let` bindings introduced mid-proof through every
remaining subgoal — with the bindings showing up as a single outer
`let` on the final proof term rather than being zeta-reduced into each
leaf.

## Quick start

```lean
import LiftLets

example (g : Nat → Prop) (n : Nat) (h : (n + 1) + 0 = (n + 1))
    (hg : g (n + 1)) : ∃ x : Nat, x + 0 = x ∧ g x := by
  lift_lets =>
    tactic => refine ⟨?_, ?_, ?_⟩
    let m := n + 1
    have h' : m + 0 = m := h
    · exact m                -- unifies the witness `?x` with `m`, not `n + 1`
    · exact h'
    · exact hg
```

The `let m := n + 1` introduced *after* `refine ⟨?_, ?_, ?_⟩` is visible
across the three subgoals it creates — including the witness subgoal —
and when `exact m` runs, the witness is assigned to `m`, not to its
underlying `n + 1` (no zeta-reduction on the assignment).

## `lift_lets =>` (this tactic) vs `lift_let` / `lift_lets` (Lean core)

Lean's core library ships a `lift_let` / `lift_lets` tactic that
rewrites a goal's *expression* to pull `let` bindings nested inside a
term up to the outermost level — it's a transformation on the goal,
applied after you've typed in some let-heavy expression. Useful, but
different in intent.

The `lift_lets =>` tactic *here* does something closer to what the name
says, but at the *proof-term* level: if you introduce a `let` inside
the block, the resulting proof term is morally the same as if you had
wrapped the whole block in a single `let` at the outside. We aren't
rewriting the goal; we're arranging for the `let` to land on the
outside of the proof we build, instead of being duplicated into every
branch (or zeta-inlined) by the ordinary tactic machinery.

Concretely: when Lean's regular `have` / `let` tactics are used inside
a many-branch proof (like one with `constructor` or `refine`), each
branch becomes its own subgoal mvar, and `have`/`let` assigns the
current mvar to `let x := e; ?newGoal`. Every branch that follows
closes its own `newGoal`, and the final proof term has a `.letE`
wrapper per branch that used `x` — or, if Lean chose to zeta-reduce
during the assignment, no `.letE` at all and `x`'s value inlined at
every use site. Neither is what you want for cases like "the witness
of an `∃` should literally be the let-bound name `m`".

`lift_lets =>` instead:

* tracks every metavariable produced during the block,
* when you say `have` / `let`, extends the *declared local context* of
  each tracked mvar (rather than assigning it with a `.letE`), and
* at block exit, wraps the whole proof term with one `let`-binding per
  decl via `mkLetFVars` and only then assigns the original goal.

That way the intermediate proof structure stays clean, and any
branch-closing tactic that unifies against the `let`-bound name does so
*by name* — no zeta-reduction back to the underlying value.

## How it works

`lift_lets => …` runs a small state machine on top of `TacticM`:

* The original main goal is saved but *not assigned* on entry. A fresh
  goal of the same type becomes the main goal instead.
* As the block runs, the library tracks every metavariable it produces
  (the fresh root, any subgoals `tactic =>` introduces, witness mvars
  from `refine ⟨?_, _⟩`, …).
* A lift_lets-level `have`/`let` extends the declared local context of
  every tracked mvar — not only the current main goal. Later tactics
  that assign any tracked mvar with a term mentioning the let-bound
  variable stick without zeta-reducing back to the underlying value.
* On exit, the library wraps the fresh root's proof term with a single
  `let`-binding per decl (via `mkLetFVars`) and only then assigns the
  original goal. The resulting term has one outer `let` per `have` /
  `let`, regardless of how many leaves used it.

Inside the block the user works in plain `TacticM` — there is no
gadget type wrapping the goal, no special connective navigation. The
only primitive is:

```
tactic => tac
```

which runs `tac` on the current main goal and adopts its open subgoals,
provided they share the input mvar's local context.

## Tactics

### Primitive

| tactic                 | effect                                                    |
| ---------------------- | --------------------------------------------------------- |
| `tactic => tac`        | run a regular Lean tactic; adopt any new subgoals         |

### Convenience wrappers (all expand to `tactic => …`)

| tactic                 | effect                                                    |
| ---------------------- | --------------------------------------------------------- |
| `exact e`              | `tactic => exact e`                                       |
| `apply e`              | `tactic => apply e`                                       |
| `constructor`          | `tactic => constructor`                                   |
| `assumption`           | `tactic => assumption`                                    |
| `rfl`, `trivial`       | the obvious wrappers                                      |
| `grind`                | `tactic => grind`                                         |
| `show t`               | `tactic => show t`                                        |
| `rw [rules]`           | `tactic => rw [rules]`                                    |
| `simp`                 | `tactic => simp`                                          |

### Shared context

| tactic                   | effect                                                  |
| ------------------------ | ------------------------------------------------------- |
| `have h : T := e`        | propagates `h := e` into every tracked mvar's lctx     |
| `let x : T := e`         | same, as a `let`-decl                                   |

### Focusing

| tactic                   | effect                                                  |
| ------------------------ | ------------------------------------------------------- |
| `· tacs`                 | focus first goal; `tacs` must close it                  |
| `next => tacs`           | focus first goal; no must-close check                   |
| `rotate_left [n]`        | cycle the goal list left by `n` (default 1)             |
| `rotate_right [n]`       | cycle the goal list right by `n` (default 1)            |

### Housekeeping

| tactic                   | effect                                                  |
| ------------------------ | ------------------------------------------------------- |
| `skip`                   | do nothing                                              |
| `trace_state`            | print the current tracked goals                         |

## File map

| file                    | role                                                      |
| ----------------------- | --------------------------------------------------------- |
| `LiftLets/Basic.lean`   | (reserved for shared definitions)                         |
| `LiftLets/Attr.lean`    | `LiftLetsState`, `LiftLetsM`, and `@[lift_lets_tactic]`   |
| `LiftLets/Tactic.lean`  | syntax category, entry tactic, and all lift_lets tactics  |
| `tests/LiftLetsTests/`  | unit tests + a demo file                                  |

## Limitations

* `lift_lets => …` blocks cannot be nested.
* `tactic => tac` insists that every new subgoal has *exactly* the
  same local context as the main goal it was run on. If you need to
  introduce a hypothesis that all tracked goals should see, use the
  lift_lets-level `have`/`let` instead.
