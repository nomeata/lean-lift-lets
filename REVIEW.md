# Persona reviews

The MVP was reviewed in the style of three Lean insiders. Below are the
concerns each raised and how the implementation now addresses them.

## Leo de Moura — MetaM discipline and proof terms

**Concerns**

1. *Unsafe mvar assignment inside `withLocalDeclD`.* The original
   `runActionOnFocus` collected subgoals, introduced a fresh hypothesis `h`
   with `withLocalDeclD`, and then assigned each subgoal's mvar to a
   projection of `h`. Those assignments referenced `h`, which was not in
   the subgoals' declared local contexts — a classic way to produce
   ill-scoped proof terms.

2. *Higher-order instance synthesis is fragile.* The original design
   routed monotonicity through a `PFocusable` class. For outer contexts
   built by `left`/`right`, Lean's instance search was forced to solve
   higher-order unification problems like
   `PFocusable (fun p => (fun q => q) (p ∧ B))`, which it could not
   always handle.

3. *Redundant wrapping in proof terms.* Moving focus requires a
   `pfocus_intro (pfocus_elim _)` sandwich; this clutters the resulting
   term.

**Fixes**

1. `runActionOnFocus` no longer assigns subgoal mvars. Instead it
   instantiates the focus proof and substitutes each subgoal mvar with
   the corresponding projection of `h` via `Expr.replace`. The assignment
   happens purely at the term level, avoiding any local-context hazard.
   See the "Build an implication" block in `runActionOnFocus`.

2. A `buildMonoSpec` meta function now synthesizes the monotonicity term
   directly from the shape of the outer context. It walks the β-normal
   body and builds `⟨h cx.left, cx.right⟩`-style pairs at each step. The
   `PFocusable` class is preserved as a user-facing API (with the obvious
   instances) but the tactic no longer relies on instance search.

3. The `pfocus_intro (pfocus_elim _)` wrapping is irreducible by
   design: `pfocus` is `@[irreducible]` so that Lean does not
   spontaneously unfold the gadget in goals. The wrapping is the cost of
   that invariant. To compensate, `replaceWithFocusGoal` is the only
   function that constructs this pattern, so the cost is confined to a
   single helper; everything else reads as a direct proof.

## Sebastian Ullrich — Syntax, grammar, extensibility

**Concerns**

1. *Leaky imports.* The initial implementation opened
   `Lean.Parser.Tactic` at file scope. That dropped pattern-matching
   shortcuts that collided with do-notation tuple destructuring, producing
   cryptic "unsupported pattern in syntax match" errors from places
   apparently unrelated to the opens.

2. *Fragile simp argument forwarding.* Forwarding a full simp argument
   list (with optional discharger, `only`, lemmas) through a macro is
   error-prone because the simp grammar is deeply nested.

3. *Missing grouping.* Sebastian would want `(seq)` grouping, like conv
   has, but the naive `(` syntax collides with term-level tuples.

**Fixes**

1. The `open Lean.Parser.Tactic` is gone; individual parsers such as
   `Lean.Parser.Tactic.rwRuleSeq` are referenced by full name. This is
   verbose but stable.

2. The `simp` forwarder was pared down to `simp` (no arguments). Users
   who need simp-with-lemmas are expected to write `conv => simp [...]`
   explicitly. The MVP defers the full macro — it's easy to add later
   without breaking anything.

3. Grouping is provided by the bracketed form `{ seq }` inherited from
   `pfocusSeqBracketed`. A `( seq )` grouping was prototyped but omitted
   pending a principled way to disambiguate it from term-level tuples.

## Marc Huisinga — Infoview

**Concerns**

1. *Scoped notation and unexpander.* Originally both were `scoped`. That
   meant a user who hadn't `open Pfocus` saw the raw
   `pfocus (fun p => ...) P` spelling inside a pfocus block, undoing the
   whole point of the custom display.

2. *Information tree integrity.* Dispatching pfocus-category tactics
   through `evalTactic` needs to still produce a single info tree per
   tactic, or the infoview's per-position state reconstruction breaks.

**Fixes**

1. The notation and unexpander are no longer `scoped`; they fire
   whenever Lean pretty-prints a `Pfocus.pfocus` application.

2. `evalPfocusCat` wraps each dispatch in `withTacticInfoContext stx`, and
   `evalPfocusSepByIndent` calls `saveTacticInfoForToken` on every
   separator. This mirrors the pattern in `Lean/Elab/Tactic/Conv/Basic.lean`,
   which Marc maintains, and was validated by running the test file with
   the infoview open to confirm that goal states appear for each step.
