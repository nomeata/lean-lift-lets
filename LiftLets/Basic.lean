/-
Copyright (c) 2026 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license.

The `liftLets` tactic family has no logical gadgets of its own: the
deferred-assignment + tracked-mvars design means lift_lets mode works
directly on the existing goal state, with `tactic => …` as the only
primitive that introduces new goals. This file is reserved for any
shared definitions the library might grow into.
-/
namespace LiftLets
end LiftLets
