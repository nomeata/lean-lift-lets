/-
Copyright (c) 2026 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license.

Core definitions for the `pfocus` tactic family.

This file defines:

* The gadget `pfocus : (Prop → Prop) → Prop → Prop`, which is definitionally
  `C P`, but marked `@[irreducible]` so that the tactic framework can recognize
  and preserve it in goals.
* `pfocus_intro`/`pfocus_elim` as the only bridges between `pfocus C P` and `C P`.
* A class `PFocusable` witnessing monotonicity of an outer context `C`, together
  with instances that let instance synthesis handle every outer context that the
  tactics actually build.
* The key lemma `pfocus_imp`, which exposes monotonicity under the `pfocus`
  wrapper: it lets us weaken the focused proposition.

Design rationale:

The `pfocus` definition is deliberately irreducible. That way, the elaborator
never spontaneously unfolds our gadget and the goal keeps its shape across
tactic invocations. The price we pay is that *moving the focus* is no longer a
purely definitional operation from the viewpoint of the elaborator — we use
`pfocus_intro ∘ pfocus_elim` to bridge the two presentations, relying on
`isDefEq` under the `pfocus` wrapper to do β.

The monotonicity witness is carried by a type class. Using a class means that
tactics can build outer contexts in a canonical composable form
`fun p => D (p ∧ B)` (etc.) and let instance search recover the proof. All
outer contexts built by the tactics in this file are in that form, and the
provided instances cover them.
-/

namespace Pfocus

/--
`pfocus C P` is definitionally equal to `C P`, but is marked `@[irreducible]`
so tactics can recognize it and prevent Lean from unfolding it. It represents
the focus state of the `pfocus` tactic family: `C` is the outer context and
`P` is the currently-focused proposition.
-/
@[irreducible]
def pfocus (C : Prop → Prop) (P : Prop) : Prop := C P

/-- `C P` implies `pfocus C P`. This is the only way to introduce `pfocus`. -/
theorem pfocus_intro {C : Prop → Prop} {P : Prop} (h : C P) : pfocus C P := by
  unfold pfocus; exact h

/-- `pfocus C P` implies `C P`. This is the only way to eliminate `pfocus`. -/
theorem pfocus_elim {C : Prop → Prop} {P : Prop} (h : pfocus C P) : C P := by
  unfold pfocus at h; exact h

/--
A class witnessing that an outer context `C : Prop → Prop` is monotone:
implications propagate through `C`. Every outer context built by the `pfocus`
tactics is monotone, and the instances below cover all shapes the tactics
produce.
-/
class PFocusable (C : Prop → Prop) : Prop where
  /-- Monotonicity: from `X → Y` and `C X`, obtain `C Y`. -/
  mono : ∀ {X Y : Prop}, (X → Y) → C X → C Y

/-- The identity outer context is monotone. -/
instance PFocusable.id_inst : PFocusable (fun p : Prop => p) where
  mono h := h

/--
If `D` is a pfocus-able outer context, then so is the context that wraps `D` in
the left conjunct `_ ∧ B`. This is the shape built by the `left` tactic.
-/
instance PFocusable.inLeft {D : Prop → Prop} [inst : PFocusable D] (B : Prop) :
    PFocusable (fun p : Prop => D (p ∧ B)) where
  mono h := inst.mono (fun ⟨x, b⟩ => ⟨h x, b⟩)

/--
If `D` is a pfocus-able outer context, then so is the context that wraps `D` in
the right conjunct `A ∧ _`. This is the shape built by the `right` tactic.
-/
instance PFocusable.inRight {D : Prop → Prop} [inst : PFocusable D] (A : Prop) :
    PFocusable (fun p : Prop => D (A ∧ p)) where
  mono h := inst.mono (fun ⟨a, x⟩ => ⟨a, h x⟩)

/--
Key monotonicity lemma. If we can weaken the focus from `X` to `Y`, we can
weaken the whole `pfocus` goal.

Tactics that make progress on the focus use this lemma in reverse: to prove
`pfocus C Y`, build a term `h : X → Y` and reduce to proving `pfocus C X`.
-/
theorem pfocus_imp {C : Prop → Prop} [PFocusable C] {X Y : Prop}
    (h : X → Y) (c : pfocus C X) : pfocus C Y :=
  pfocus_intro (PFocusable.mono h (pfocus_elim c))

/--
"Raw" morphism lemma: given any function `C X → C Y`, transport a `pfocus C
X` into a `pfocus C Y`. Used by the tactic implementation, which builds the
morphism term directly in `MetaM` — this keeps the approach robust to the
shape of `C` and works uniformly for `Prop` focuses and predicate focuses.

For the common `Prop` case, callers build the morphism as
`PFocusable.mono h` for some implication `h : X → Y`. For the predicate case
(e.g. `C = fun p => ∃ x, p x`), callers build it as
`fun e => e.elim (fun x hx => ⟨x, transport hx⟩)`.
-/
theorem pfocus_imp_raw {C : Prop → Prop} {X Y : Prop}
    (h : C X → C Y) (c : pfocus C X) : pfocus C Y :=
  pfocus_intro (h (pfocus_elim c))

end Pfocus
