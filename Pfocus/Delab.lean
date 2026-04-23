/-
Copyright (c) 2026 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license.

Delaboration for `pfocus` goals.

A `pfocus C P` application is displayed as `⇣ P`, with the outer context `C`
suppressed. This mirrors what `conv` does for its goals, where only the
currently-focused term is visible.

The notation `⇣ P` is a display-only syntax. If a user types it by hand
(they shouldn't), it elaborates as `pfocus (fun p => p) P`, which gives a
reasonable fallback.
-/
import Lean
import Pfocus.Basic

namespace Pfocus

/--
Display-only notation for the focused proposition inside `pfocus`. The
infoview shows `⇣ P` whenever the goal has shape `pfocus C P`, hiding the
outer context `C`.

If written explicitly in source, it stands for `pfocus id P`, matching the
starting state of `pfocus` mode.

We register the notation and unexpander as global (not `scoped`) so the
infoview uses them whether or not the user has `open Pfocus`. Without this,
users see the raw `pfocus (fun p => ...) P` spelling.
-/
notation:max "⇣ " p:max => Pfocus.pfocus (fun p : Prop => p) p

/--
Unexpander so that `pfocus C P` is rendered as `⇣ P` in the infoview,
regardless of the specific outer context `C`. This mirrors how `conv` goals
suppress the trivial `rhs` metavariable.

For a predicate focus `P = fun x => body`, we render with the bound
variable replaced by a `?x`-style placeholder, so the user sees the
applied body — e.g. `⇣ ?x + 0 = ?x` instead of `⇣ fun x => x + 0 = x`.
This matches the goal the user will see inside a `tactic => ...` block,
where a real fresh metavariable is substituted for the bound variable.
-/
@[app_unexpander Pfocus.pfocus]
def unexpandPFocus : Lean.PrettyPrinter.Unexpander := fun stx => do
  match stx with
  | `($_ $_ fun $x:ident => $body) => do
    let body' ← body.raw.replaceM fun s => do
      if s.isIdent && s.getId == x.getId then
        return some (← `(?$x)).raw
      else
        return none
    let bodyTerm : Lean.TSyntax `term := ⟨body'⟩
    `(⇣ $bodyTerm)
  | `($_ $_ $p) => `(⇣ $p)
  | _ => throw ()

end Pfocus
