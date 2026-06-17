# Scoped Refactor Archive

This directory archives the scoped-expression / `ProperSpine` refactor that was
backed out of the active proof backend.

Contents:

- `scoped-refactor.patch`: complete patch from the pre-refactor parent
  (`076452e`) to the archived working state, including the latest local
  contraction-lemma experiment.
- `ScopedExpr.lean`: standalone copy of the scoped syntax/proof file.
- `scoped-core-refactor.md`: planning and handoff notes for the scoped route.
- `commit-stat.txt`: summary of the original `scoped expressions refactor wip`
  commit.

Reason for backing out: the scoped approach clarified the mathematics, but the
local-local interchange proof started recreating the same diamond/lift
complexity in a second backend. The active repo should return to the existing
flat equations backend until a cleaner substitution framework is designed.
