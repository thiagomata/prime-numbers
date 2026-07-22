# Retire Classic Cycle Integral Surface

**Created:** 2026-07-14
**Status:** Done

## Goal

Retire the duplicate `ClassicCycleIntegral` public surface now that active code
work has finished and the repository is green.

## Current State

`ClassicCycleIntegral` and `CycleIntegral` are definitionally identical over
`MemCycle`. The article now presents only the canonical recursive
`CycleIntegral` plus the closed-form `ModCycleIntegral`.

Initial verification baseline from `logs/verify.log`:

- `13954 valid`
- `0 invalid`
- `0 unknown`

## Expected State

The codebase should stop presenting `ClassicCycleIntegral` as a separate
mathematical implementation. The canonical recursive implementation should be
`CycleIntegral`, and compatibility with existing source should be preserved
unless a deliberate removal pass is approved separately.

## Similar Tickets and Prior Work

- `tickets/active/integral-cycle-examiner-review.md` recorded the publication
  decision to present only `CycleIntegral` and `ModCycleIntegral`.
- `TODO.md` contains the duplicate-surface cleanup item.
- `tickets/active/sieve-sequence-proof.md` contains historical references to
  `ClassicCycleIntegralProperties` as a proof idiom; these are notes, not
  active code dependencies.

## Validation Plan

1. Inspect all current references to `ClassicCycleIntegral` and the `classic`
   package.
2. Make one conservative compatibility-preserving code cleanup.
3. Run tests first.
4. Run full `just verify`.
5. Update `OBJECTS.md`, `TODO.md`, and this ticket to reflect the result.

## Learning Log

- Initial search shows active code references are confined to the classic
  implementation/properties package and its tests. Article references have
  already been removed.
- Updated `ClassicCycleIntegral` to delegate behavior to canonical
  `CycleIntegral`, preserving the old constructor and methods as a compatibility
  surface.
- Updated `ClassicCycleIntegralProperties` to import and accept canonical
  `CycleIntegral`; the old object name remains only as a compatibility namespace.
- Updated the old classic property tests to construct `CycleIntegral` while
  still exercising `ClassicCycleIntegralProperties`.
- Validation:
  - `just compile` passed.
  - Focused classic suites passed: 11 tests, 0 failures.
- Full `just verify` passed with `13950 valid`, `0 invalid`, `0 unknown`.
- Broad `just test` still has two unrelated `MainTest` help-text failures;
  classic cycle-integral tests passed before and after the property redirect.
