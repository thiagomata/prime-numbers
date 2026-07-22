# Integral Cycle Draft Property Audit

**Created:** 2026-07-14
**Status:** Active

## Goal

Check whether the three draft/pending properties in
`articles/chapter4/integral-cycle.md` are truly missing from the current Scala
verification code.

## Current State

The article marks these as mathematically proven but Stainless verification
pending:

- Section 5.1 modulo invariance.
- Section 5.3 right index shift.
- Section 5.4 left index shift.

The user asked to verify whether they are really missing.

## Expected State

Produce a source-backed classification for each property:

- already verified;
- partially covered by existing lemmas;
- genuinely missing.

## Validation Plan

1. Search existing `.holds` lemmas across cycle-integral, gap, filter, modulo,
   cycle, and list property modules.
2. Read the candidate lemma bodies before classifying them.
3. Cross-check TODO/article wording against actual source names and statements.
4. Report the classification without adding new lemmas in this audit pass.

## Learning Log

- Started audit; no code edits planned.
- Current verification baseline is green in `logs/verify.log`: `13950 valid`,
  `0 invalid`, `0 unknown`.
- Section 5.1 is not missing in the intended architecture. `MemCycle` is the
  memoized finite-period classification layer: its
  `modIsZeroForAllValues`, `modIsZeroForNoneValues`, and
  `modIsZeroForSomeValues` fields are checked by `CycleUtils.isValid`, and
  `CycleCheckMod.afterMethodListAndZeroModCountAreOnSync` proves that
  `checkMod(dividend)` stores the dividend in exactly the matching
  all/none/some class for stored cycle values. Separately,
  `GapProperties.assertModIsPeriodic(ci, m, pos)` proves
  `Calc.mod(ci(pos), m) == Calc.mod(ci(Calc.mod(pos,
  ci.period)), m)` under `ci.period > 0`, `m > 0`, `pos >= 0`,
  `Calc.mod(ci.sum, m) == 0`, and the full-cycle shift precondition
  `ci(ci.period) - ci(0) == ci.sum`. The article should cite those two
  verified finite-period layers instead of marking the property as simply
  pending, while being careful not to conflate the stored gap cycle with the
  accumulated Cycle Integral stream.
- Updated `articles/chapter4/integral-cycle.md` so §5.1 is no longer marked
  draft/pending and now cites the `MemCycle` classification layer plus the
  `GapProperties.assertModIsPeriodic` unbounded-lift theorem.
- Section 5.3 is now verified at the stored-period `CycleIntegral` level. Added
  `GapProperties.assertRotateOneCycleIntegralShiftsByOne`, which proves
  `shiftedCI(i) == originalCI(i + 1)` under the one-step backing-cycle rotation
  and shifted-initial-value preconditions, for `i + 1 < originalCI.period`.
  Focused verification passed (`50 valid`, `0 invalid`, `0 unknown`) and full
  verification passed (`14000 valid`, `0 invalid`, `0 unknown`). The remaining
  gap against the article's original wording is the all-position wrapper over
  already verified full-cycle shifts.
- Section 5.4 is genuinely missing as stated. No direct left-shift
  `CycleIntegral` theorem was found. The article also appears internally
  inconsistent here: the headline formula states
  `CycleIntegral(L, init)_i = CycleIntegral(L'', init'')_{i+1}`, while the final
  QED line states `CycleIntegral(L, init)_{i+1} =
  CycleIntegral(L'', init'')_i`.

## Source Evidence

- `src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala`
  - `assertModIsPeriodic`: verified modulo-periodicity theorem for §5.1.
  - `assertCIModDivFormula`: supporting closed-form/mod-div bridge.
  - `assertRotateOneShiftsIntegralByOne`: bounded shifted-list wrapper for the
    §5.3-adjacent finite statement.
  - `assertRotateOneCycleIntegralShiftsByOne`: stored-period `CycleIntegral`
    right-shift wrapper for §5.3.
- `src/main/scala/v1/chapter4/cycle/memory/MemCycle.scala`
  - `modIsZeroForAllValues`, `modIsZeroForNoneValues`, and
    `modIsZeroForSomeValues`: memoized classification of divisors over the
    finite stored cycle.
- `src/main/scala/v1/chapter4/cycle/memory/properties/CycleCheckMod.scala`
  - `afterMethodListAndZeroModCountAreOnSync`: verifies that `checkMod`
    synchronizes the cached class with the zero-mod count.
- `src/main/scala/v1/chapter3/list/ShiftedList.scala`
  - `ShiftedList.assertShiftedApplyIsOriginalPlusOne`: bounded finite
    positional-shift law.
- `src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala`
  - `assertCIShiftEqualsSum`: full-cycle shift theorem used by
    `assertModIsPeriodic`.
