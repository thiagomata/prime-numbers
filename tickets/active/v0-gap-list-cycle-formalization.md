# V0 Gap List and Cycle Formalization

**Status:** Active canonical ticket
**Created:** 2026-06-21

## Purpose

This is the coordination ticket for formalizing the gap-list and gap-cycle
properties around `SieveSequenceV0`.

Older gap tickets remain available as historical proof logs, but new work should
start here. When an old ticket contains a useful verified fact, copy the current
fact and source reference into this ticket or `OBJECTS.md` before continuing.

## Goal

Prove that the local V0 gap facts lift into a full next-level gap-list and
eventually gap-cycle transformation.

The expected ladder, sorted from lowest to highest estimated proof complexity,
is:

1. Gap positivity:
   - `gap(k) > 0`.
   - Estimated complexity: low. This is a direct wrapper over strict
     monotonicity.
   - Status: verified as `SieveSequenceV0.assertGapPositive(k)`.
2. Copy case:
   - if the immediate old successor survives the new filter, the next gap is
     the old gap.
   - Estimated complexity: low to medium. The core position-preservation lemma
     is already verified.
   - Status: verified as `SieveSequenceV0.assertFilterPreservesNextGap(nextSeq, k)`.
3. Gap periodicity:
   - `gap(k + p) == gap(k)`.
   - Estimated complexity: medium. This depends on block-shift facts at two
     adjacent indices.
   - Status: verified as `SieveSequenceV0.assertGapPeriodic(k, p)`.
4. Gap-period sum:
   - `sumGap(0, p) == filterModulus`.
   - Estimated complexity: medium. This depends on telescoping a bounded gap
     prefix.
   - Status: verified as `SieveSequenceV0.assertGapSum(p)`.
5. Merge landing point:
   - if the immediate old successor is removed by the new filter, the next
     sequence lands on the first later old survivor.
   - Estimated complexity: medium to high. The landing equality is already
     verified, but it depends on several ordering and filter-bridge helpers.
6. Merge gap-sum corollary:
   - the merged next gap equals the sum of old gaps until the first later
     survivor.
   - Estimated complexity: medium to high. This should compose the landing
     equality with `sumGap` telescoping.
7. Prefix lift:
   - repeat copy/merge across a bounded prefix of old generated values.
   - Estimated complexity: high. This introduces a recursive list-building
     proof and accounting for consumed old indices.
8. Gap-list cyclicity:
   - prove the finite gap list repeats as a cycle, so later gaps are found by
     cycling through the same bounded list.
   - Estimated complexity: high. This bridges finite gap-list equality to
     cycle access and repeated positions.
9. Cycle lift:
   - prove the bounded prefix corresponds to one rotated gap cycle.
   - Estimated complexity: very high. This combines prefix equality,
     positivity, non-emptiness, rotation, and cycle construction.
10. Conditional next-prime bridge:
   - when the next head alignment is available, connect the gap-list theorem to
     `SieveSequenceV0.next`.
   - Estimated complexity: very high. This depends on the separate conditional
     `nextPrime` / `apply(1)` alignment boundary.

## Complexity Rationale from `LEARNINGS.md`

The ordering above follows the project lessons:

- Prefer same-instance private lemmas for the early gap facts. `LEARNINGS.md`
  notes that private lemmas inside `SieveSequenceV0` propagate better than
  external `.holds` calls.
- Use `.ensuring` when a later lemma must consume an equality. This was the
  successful pattern for block-shift facts such as
  `apply(k + p) == apply(k) + filterModulus`.
- Use `indexOfAccepted(head + filterModulus)` as the period finder. Avoid
  proving residue-count equality before it is strictly needed, because counting
  residues requires heavier list-completeness lemmas.
- Keep copy and merge as local same-instance facts before attempting list
  construction. List construction introduces recursive accounting and larger
  VCs.
- Treat cross-instance calls as expensive. The conditional next-prime bridge is
  last because `LEARNINGS.md` records repeated timeouts when calling verified
  `SieveSequenceV0` lemmas on a different instance.
- Avoid deep number theory in this ticket. Bertrand, Jacobsthal, and prime-gap
  arguments are out of scope; use explicit preconditions or conditional
  branches for those boundaries.

## Current Verified Backbone

- `SieveSequenceV0.assertGapPositive(k)` proves each V0 gap is positive.
- `SieveSequenceV0.assertGapPeriodic(k, p)` proves periodicity when
  `apply(p) == head.value + filterModulus`.
- `SieveSequenceV0.assertGapSum(p)` proves the sum of one period is the
  filter modulus.
- `SieveSequenceV0.assertFilterPreservesNextPosition(nextSeq, k)` proves the
  copy case for an immediate successor that survives the new front filter.
- `SieveSequenceV0.assertFilterPreservesNextGap(nextSeq, k)` proves the
  copied-gap corollary: under the same immediate-survivor preconditions, the
  next sequence gap equals the old sequence gap.
- `SieveSequenceV0.assertSkipUntilNonMultiple(nextSeq, k, period)` proves the
  core merge case: when the immediate old successor is rejected by the new front
  filter, the next sequence lands exactly on the first later old-stream value
  that survives.
- `SieveSequenceV0.assertPeriodBoundIsNonMultiple(nextSeq, k, period)` exposes
  the period-search endpoint facts needed by callers: for `p =
  nextSeq.filterValues.head` and `bound = k + p * period`, it proves `p > 0`,
  `bound > k`, and `apply(bound)` is not a multiple of `p`.
- `SieveSequenceV0.assertMergeLandsOnFirstSurvivor(nextSeq, k, period)` is now
  a usable property-name alias for the merge landing proof. It consumes
  `assertPeriodBoundIsNonMultiple`, constructs the first-survivor witness, and
  proves the same landing equality as `assertSkipUntilNonMultiple`.
- `SieveSequenceV0.assertMergeGapEqualsOldGapSum(nextSeq, k, period)` proves
  the merged-gap corollary: when the new front filter removes the immediate old
  successor, the next sequence gap equals `sumGap(k, m)` for the first later
  old-stream survivor `m`.
- `SieveSequenceV0.next` now has an explicit `List.head`-style precondition:
  `primes.nextPrime.value < head.value * head.value`.

## Progress Log

- 2026-06-22: Audited the first property in the complexity ladder. Gap
  positivity is already verified in
  `src/main/scala/v1/seq/sieve/SieveSequenceV0.scala` as
  `assertGapPositive(k)`. The lemma requires `k >= 0`, calls
  `applyStrictlyIncreases(k)`, and proves
  `apply(k + 1) - apply(k) > 0`. No code change was needed.
- 2026-06-22: Added the public copy-case gap corollary
  `assertFilterPreservesNextGap(nextSeq, k)`. It reuses the verified
  next-position lemma and proves that when the immediate old successor survives
  the new front filter, the next gap is copied unchanged. Verification passed:
  `total: 7259 valid: 7259 invalid: 0 unknown: 0`.
- 2026-06-22: Audited the next ladder property, gap periodicity. It is already
  verified in `src/main/scala/v1/seq/sieve/SieveSequenceV0.scala` as
  `assertGapPeriodic(k, p)`. The lemma requires `apply(p) == head.value +
  filterModulus`, calls `assertBlockShift(k, p)` and
  `assertBlockShift(k + 1, p)`, and proves the adjacent gap repeats after one
  period.
- 2026-06-22: Audited the gap-period sum property. It is already verified in
  `src/main/scala/v1/seq/sieve/SieveSequenceV0.scala` as
  `assertGapSum(p)`. The lemma requires `apply(p) == head.value +
  filterModulus`, uses `assertSumGapTelescopes(0, p)`, and proves
  `sumGap(0, p) == filterModulus`.
- 2026-06-22: Tried to make `assertMergeLandsOnFirstSurvivor` reconstruct the
  first-survivor witness directly. The first attempt timed out because the alias
  had to rediscover the bounded-search preconditions before it could delegate:
  `p > 0`, `bound > k`, and `Calc.mod(apply(bound), p) != 0`.
- 2026-06-22: Added `assertPeriodBoundIsNonMultiple(nextSeq, k, period)` with an
  explicit postcondition exposing those endpoint facts. Verification passed:
  `total: 7321 valid: 7321 invalid: 0 unknown: 0`.
- 2026-06-22: Updated `assertMergeLandsOnFirstSurvivor` to consume the endpoint
  lemma, call `findFirstNonMultipleAfter`, and prove the landing equality
  directly. This confirms the alias is usable as a caller-facing property check.
  Verification passed: `total: 7340 valid: 7340 invalid: 0 unknown: 0`.
- 2026-06-22: Added `assertMergeGapEqualsOldGapSum(nextSeq, k, period)`, the
  public merge-gap corollary. It reuses the first-survivor landing alias,
  establishes `nextSeq(vIdx) == apply(k)`, telescopes `sumGap(k, m)`, and proves
  the next sequence's merged gap is exactly the sum of the old skipped gaps.
  Verification passed: `total: 7391 valid: 7391 invalid: 0 unknown: 0`.

## Open Work

1. Add a bounded prefix transformer that walks old indices and emits copied or
   merged gaps.
2. Prove the generated prefix is positive and non-empty.
3. Prove prefix equality against the next sequence's first generated values.
4. Only after the prefix theorem is green, lift it to a gap-cycle statement.

## Related Historical Tickets

These tickets are kept for proof logs and failed-attempt details, but should not
be used as the starting point for new implementation:

- `../superseded/v0-gap-properties.md`
- `../superseded/v0-skip-multiples-until-nonmultiple.md`
- `../superseded/v0-residue-cycle-proof.md`
- `../superseded/conditional-nextprime-gap-cycle-bridge.md`
- `../superseded/v0-filter-preserves-next-position.md`
- `../superseded/walk-based-pipeline.md`

## Validation

- Search `OBJECTS.md` first for the current verified lemma names.
- Use unit tests for concrete gap-list examples before adding proof code.
- For code changes, follow AGENTS.md green-to-green:
  run `just verify` before and after each non-markdown change.
  Keep one assertion, requirement, or lemma per verification cycle.
