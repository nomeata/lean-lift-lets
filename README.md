# pfocus

A small Lean 4 tactic family that lets `have` / `let` bindings introduced
mid-proof reach every remaining subgoal, without zeta-reducing those
bindings into each leaf of the final proof term.

## Quick start

```lean
import Pfocus

example (g : Nat → Prop) (n : Nat) (h : (n + 1) + 0 = (n + 1))
    (hg : g (n + 1)) : ∃ x : Nat, x + 0 = x ∧ g x := by
  pfocus =>
    tactic => refine ⟨?_, ?_, ?_⟩
    let m := n + 1
    have h' : m + 0 = m := h
    · exact m                -- unifies the witness `?x` with `m`
    · exact h'
    · exact hg
```

The `let m := n + 1` introduced *after* `refine ⟨?_, ?_, ?_⟩` is visible
across the three subgoals it creates — including the witness subgoal —
and the witness is assigned to `m` rather than to `n + 1` (no zeta
reduction).

## How it works

`pfocus => …` runs a small state machine on top of `TacticM`:

* The original main goal is saved but *not assigned* on entry. A fresh
  goal of the same type becomes the main goal instead.
* As the block runs, the library tracks every metavariable it produces
  (the fresh root, any subgoals `tactic =>` introduces, witness mvars
  from `refine ⟨?_, _⟩`, …).
* A pfocus-level `have`/`let` extends the declared local context of
  every tracked mvar — not only the current main goal. Later tactics
  that assign any tracked mvar with a term mentioning the let-bound
  variable stick without zeta-reducing back to the underlying value.
* On exit, the library wraps the fresh root's proof term with a single
  `let`-binding per decl (via `mkLetFVars`) and only then assigns the
  original goal. The resulting term has one outer `let` per `have`/
  `let`, regardless of how many leaves they were used in.

Inside the block the user works in plain `TacticM` — there is no
gadget type wrapping the goal, no `pfocus_imp`, no special form of
`And` navigation. The only primitive is:

```
tactic => tac
```

which runs `tac` and adopts its open subgoals, provided they share the
input mvar's local context.

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

### Housekeeping

| tactic                   | effect                                                  |
| ------------------------ | ------------------------------------------------------- |
| `skip`                   | do nothing                                              |
| `trace_state`            | print the current tracked goals                         |

## File map

| file                  | role                                                      |
| --------------------- | --------------------------------------------------------- |
| `Pfocus/Basic.lean`   | (reserved for shared definitions)                         |
| `Pfocus/Attr.lean`    | `PFocusState`, `PFocusM`, and `@[pfocus_tactic]`          |
| `Pfocus/Tactic.lean`  | syntax category, entry tactic, and all pfocus tactics    |
| `tests/PfocusTests/`  | unit tests + a demo file                                  |

## Limitations

* `pfocus => …` blocks cannot be nested. `@[pfocus_tactic]` writes into
  a standard Lean attribute and the state is per-invocation via
  `StateRefT`, so nesting would make sense conceptually, but the
  current dispatcher doesn't re-enter.
* `tactic => tac` insists that every new subgoal has *exactly* the
  same local context as the main goal it was run on. If you need to
  introduce a hypothesis that all tracked goals should see, use pfocus
  `have`/`let` instead.
