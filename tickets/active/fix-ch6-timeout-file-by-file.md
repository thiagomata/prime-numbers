# Fix Chapter 6 Verification Timeout (file-by-file in dependency order)

**Created:** 2026-06-30
**Status:** In progress
**Depends on:** `verify-timeout-root-cause.md` (identifies 3 commented-out timeout VCs)

## Goal

Get `just verify-ch 6` to complete with `0 unknown` by working file-by-file
(and method-by-method where needed) in dependency order, uncommenting the
3 currently-disabled timeout candidates one at a time.

Per user guidance (2026-06-30): the strategy is to verify **file by file /
method by method in dependency order** rather than fighting one giant combined
VC tree.

## Current State

- Chapters 1-5 verified green: `verify-ch-5.log` shows `total: 981 valid: 981 ... unknown: 0`.
- `just test` passes: 133 tests, 0 failures.
- Chapter 6 has 3 commented-out `[TIMEOUT CANDIDATE]` items (from
  `verify-timeout-root-cause.md` Learning Log row 3):
  1. `CycleSieveSequence.scala` — constructor `require` + `nextWithGapCycle` /
     `next` / `nextFromWindow` methods (lines 24-92)
  2. `SieveSequenceProperties.scala` — `assertHeadIsPrime` (lines 59-63)
  3. `SpecCycleSieveEquivalence.scala` — `primorialMatchesSieveProduct`
     (line 24) and `assertConditionalNext*` (line 228+)
- No `verify.log` present; need a fresh baseline of ch6 as-is.

## Expected State

- `just verify-ch 6` completes: `unknown: 0`.
- All 3 timeout candidates re-enabled and verified, OR explicitly documented as
  open with a linked sub-ticket.
- Chapters 1-5 stay green (untouched).

## Dependency Order (within ch6, all in package v1.chapter6.seq.sieve)

Proof weight (holds/ensuring count) shown in parens.

1. **Leaf layer** (no ch6 cross-deps):
   - `SieveUtils.scala` (47) — heaviest leaf
   - `CompletePrimePrefix.scala` (1)
   - `CycleUtils.scala` (3)
   - `SieveSequenceByPrimes.scala` (0)
   - `CycleSieveSequence.scala` (1) — has commented timeout candidates
2. **Mid layer:**
   - `SpecSieveSequence.scala` (88) — very heavy
   - `SpecDerivedSieveSequence.scala` (10)
   - `SpecCycleSieveEquivalence.scala` (43) — has commented timeout candidates
3. **Top layer:**
   - `properties/SieveSequenceProperties.scala` (4) — has commented `assertHeadIsPrime`
   - `SieveSequenceNextLevel.scala` (16) — imports SieveSequenceProperties

## Plan

1. Baseline: run `just verify-ch 6` to see current state (candidates commented).
   Confirm it's green or identify which file times out.
2. For each timeout candidate, uncomment + verify the file in isolation
   (method-by-method with `--functions`), applying LEARNINGS.md techniques:
   - 1.1 private lemmas / 6.2 use private lemmas from same class
   - 1.2 `.ensuring` for propagation
   - 3.1 `modZeroPlusC`, 3.2 `APlusMultipleTimesBSameMod`
   - 4.1 prefix-product decomposition
   - ONE assertion per verify cycle (rule small-changes)
3. After each fix: `just verify-ch 6` full re-validation.
4. Stop & ask after 3 failed attempts on any single VC.

## Assumptions

- The commented candidates are the ONLY remaining timeout sources (root-cause
  ticket row 3 says so).
- Chapters 1-5 stay green; changes limited to ch6 files.
- Following ch5 pattern (delegate predicates, restore full postconditions) will
  apply where relevant.

## Validation

For each fix:
1. Focused verify on the changed function/file.
2. `just verify-ch 6` → `unknown: 0`.
3. `just test` → 133 passing.

## Progress Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-06-30 | Ticket created. Dependency order mapped. Strategy: file-by-file in dep order. | Run baseline. |
