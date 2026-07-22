# Cycle Article Review Fixes

## Goal

Apply the agreed review fixes to `articles/chapter4/cycle.md` without weakening
the article's theorem.

## Current State

- `cycle.md` cites `CycleProperties::assertModCycleEqualsMemCycle` as if it
  proves all-position equivalence between `ModCycle` and `MemCycle`, although
  the lemma itself is bounded to the first physical period.
- `MemCycle` is definitionally a wrapper around `ModCycle`: `MemCycle.apply`
  delegates to the wrapped cycle, and `MemCycle(values)` constructs that
  wrapped cycle from the same values.
- The all-position recursive/modulo equivalence proof exists in
  `RecursiveCycleMatchesModCycle::assertCycleAndRecursiveCycleMathForAnyValues`
  but is missing from `OBJECTS.md`.
- `cycle.md` links forward to `integral-cycle.md`, which leaks a later article
  into this article's moment-in-time framing.
- Appendix A omits full source snippets for `cycleValuePositiveOrZero` and
  `rotateAtValue`.

## Expected State

- `cycle.md` keeps the strong three-way semantic equality while explaining its
  proof route precisely.
- The forward link to `integral-cycle.md` is removed, while Future Work still
  mentions discrete integration as the natural next step.
- Appendix A includes the current real source snippets for positivity and
  rotation.
- `OBJECTS.md` includes the all-position recursive/modulo proof.

## Validation

- Run `git diff --check` because the changes are markdown-only.

## Learning Log

- The theorem should not be weakened: `MemCycle` and `ModCycle` are equal by
  definition for lookup, and recursive/modulo equality is proved by the
  all-position assertion proof.
- Applied the article and inventory fixes. `git diff --check` passes for the
  markdown-only changes.
- Added an explicit §3.3 equality-chain explanation showing
  `RecCycle(L)_i = ModCycle(L)_i = MemCycle(L)_i` from the §4 proof and
  `MemCycle.apply` delegation.
- Rewrote §5.5 so the math proves divisor/mod propagation directly from
  `ModCycle` after the equality proof. Removed schematic inline code snippets
  from §§5.7-5.8 and pointed to Appendix A.9/A.10 for the real source.
