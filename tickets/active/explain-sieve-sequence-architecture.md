# Explain Sieve Sequence Architecture

**Created:** 2026-07-15
**Status:** Active
**Owner:** Documentation cleanup for Chapter 6 sieve-sequence representation names

## Goal

Make the current Chapter 6 sieve-sequence architecture understandable to a new
reader without pretending the naming is clean. Add a package-level README and
improve the opening Scaladoc/Javadoc comments on the similarly named classes so
each file states:

- what representation or proof lane it owns,
- why it exists,
- how it differs from the other similarly named sequence classes,
- which proof boundary it should not be confused with.

## Current State

The code contains several similarly named surfaces:

- `SpecSieveSequence`: linear-scan mathematical source of truth.
- `CycleSieveSequence`: concrete gap-cycle implementation surface.
- `SpecDerivedSieveSequence`: canonical cycle derived from the spec plus proof
  bridges.
- `SpecDerivedBySurvivors`: value-level survivor proof wrapper around the
  canonical bridge.
- `SpecDerivedEquivalence`: small transfer wrapper between the canonical and
  survivor proof surfaces.
- `SieveSequenceNextLevel`: current residue/expand/filter/sort/gap/rotate
  pipeline plus walk/window helpers and proof lemmas.

This is difficult to read because the names all orbit "sieve sequence" and
"next", but the files belong to different layers: semantic spec, operational
cycle representation, bridge proofs, survivor proofs, and transition helpers.

## Similar Tickets And Source Context

- `tickets/sieve-sequence-epic.md`
  - Defines the three representation story: Spec, Canonical, and Cycle.
  - Warns that `nextGapsWalk` remains opaque and direct proofs timed out.
- `tickets/active/m-interval-density-and-sieve-sequence-v2.md`
  - Records the correction that count/period reasoning should be spec-level, not
    driven through `nextSorted` / `nextFiltered` implementation machinery.
- `tickets/done/spec-same-head-filter-density.md`
  - Documents why the same-head count theorem deliberately restarted from
    `SpecSieveSequence` and postponed real head-change/rotation.
- `tickets/active/repeat-filter-rotate-cycle-path.md`
  - Tracks the newer side-by-side transition lane that should make the
    repeat-filter-rotate checkpoints explicit without replacing current `next()`
    yet.
- `articles/chapter6/sieve-sequence.md`
  - Current article framing: the next-stage construction is conceptually
    `C -> E_h -> F -> nextGaps -> G'`, with the spec defining semantics first.

## Expected State

- Add `src/main/scala/v1/chapter6/seq/sieve/README.md`.
- Improve the opening comments in the main similarly named Scala files.
- Do not change code behavior, signatures, requires, assertions, or proof bodies.
- Do not rename files or methods in this pass.

## Validation Plan

- Check current verification log before editing Scala comments.
- After Scala comment edits, run `just verify` once.
- Run `git diff --check`.

## Learning Log

| Date | Progress | Notes |
|------|----------|-------|
| 2026-07-15 | Ticket created after reading related tickets and article sections. | This is a documentation-only cleanup, but Scala comment changes still require full verification by project rule. |
| 2026-07-15 | Added package README and top-level comments for the main similarly named sieve-sequence surfaces. | Full `just verify` passed with `15600 valid`, `0 invalid`, `0 unknown`. |
| 2026-07-15 | Downgraded `SieveSequenceByPrimes` documentation to legacy/avoid-new-work status after checking references. | Active source has no callers beyond the object itself; old mentions live in ticket history. |
