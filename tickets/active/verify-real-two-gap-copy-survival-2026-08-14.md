# Verify Real Sieve Two-Gap Copy Survival

**Created:** 2026-08-14
**Updated:** 2026-08-14
**Status:** In progress — local real-sieve copy law verified and documented; cyclic aggregation remains
**Depends on:** `m-interval-density-and-sieve-sequence-v2.md` (verified arithmetic kernel and real-sequence survivor counting)

## START HERE

The local real-sequence law and its article documentation are complete. The
next micro-goal is to define the real cyclic 2-gap population over one
canonical period, including the wrap gap, and prove the aggregation bijection
between next-stage 2-gaps and surviving lifts of old-stage 2-gaps.

Do not start with the product recurrence. First establish the cyclic
population definition, the no-new-2-gap merge result, and the one-transition
bijection as separate verified changes.

## Related Tickets

- [`m-interval-density-and-sieve-sequence-v2.md`](m-interval-density-and-sieve-sequence-v2.md) — established the unique forbidden lift and exact one-removal count for each real residue fiber. Reuse this arithmetic kernel.
- [`add-draft-scala-three-representations-2026-08-03.md`](add-draft-scala-three-representations-2026-08-03.md) — records the unverified Scala sketches for the exact 2-gap properties; its placeholder theorem is not sufficient because it does not connect to a real sieve stage.
- [`../future/sieve-sequence-v2-gap-filter-properties.md`](../future/sieve-sequence-v2-gap-filter-properties.md) — records the verified copy/merge behavior needed to relate surviving endpoint pairs to next-stage gaps.
- [`fixed-lineage-cumulative-hazard-chart-2026-08-12.md`](fixed-lineage-cumulative-hazard-chart-2026-08-12.md) — separates deterministic real-sieve claims from toy-model/randomness claims in the associated article and diagrams.

## Goal

Add Stainless-verified properties for the deterministic real sieve sequence:
an old cyclic 2-gap has two distinct forbidden copy indices under the incoming
odd prime, exactly two of its complete block of lifted copies are destroyed,
and exactly `head - 2` copies survive. If the existing copy/merge machinery is
sufficient, lift this local result to the exact one-stage 2-gap recurrence and
its finite product iteration. Random toy-model claims are explicitly out of
scope.

## Strategy

Work bottom-up from the already verified real-fiber arithmetic. For an old
2-gap with endpoints `a` and `a + 2`, define the two forbidden offsets using
`BezoutUtils.coprimeStepZeroOffset(a, period, head)` and the same function at
`a + 2`. Existence and per-endpoint uniqueness are already postconditions.
First prove these witnesses differ. Then introduce the smallest recursive
counter needed to count the union of the two singleton forbidden-offset sets.
Only after that count is green should the result be connected to actual
surviving copied gaps and aggregated over the real cyclic period.

This route is preferred over a fresh CRT theorem because the codebase already
contains the exact modular-permutation kernel Stainless accepts. It is also
preferred over pipeline-list counting because the real sequence's acceptance
predicate and period-shift theorems are the mathematical abstraction intended
for Chapter 6.

## Current State

- Chapter 6's latest recorded regression is green: `4390 valid`, `0 invalid`,
  `0 unknown`.
- No Scala file has been changed for this ticket.
- `BezoutUtils.coprimeStepZeroOffset` returns the unique zero-making offset in
  `[0, p)` when the step is nonzero modulo prime `p`.
- `BezoutUtils.assertCoprimeStepZeroOffsetUnique` packages uniqueness.
- `SieveUtils.assertCountZeroOffsetsOne` proves exactly one zero-making offset
  in a complete `p`-offset fiber.
- `SpecSieveSeqSurvivorCountProperties` already proves exact real-sequence
  survivor counts, but for all accepted values rather than specifically for
  inherited 2-gaps.
- The 2026-08-14 baseline is green: `just test` passed all `230/230` tests;
  `just verify-ch 6` passed `4390/4390` VCs with `0` invalid and `0` unknown.
- `SpecSieveSeqTwoGapProperties.assertForbiddenLiftOffsetsDistinct` now proves
  the two unique forbidden lift offsets of a real linear 2-gap are distinct.
  Focused verification passed `41/41` VCs with no invalid or unknown results;
  Chapter 6 then passed `4431/4431`, increasing the valid count by `41`.
- `countDestroyedTwoGapCopies` now counts lift indices where either copied
  endpoint is divisible by the incoming prime, counting a copy only once even
  if both endpoint predicates were hypothetically true. Its focused gate
  passed `16/16`; Chapter 6 passed `4447/4447`.
- `assertDestroyedCountEqualsEndpointCounts` proves the two endpoint strike
  counts add without double-counting; focused verification passed `70/70` and
  Chapter 6 passed `4517/4517`.
- `assertExactlyTwoDestroyedCopies` is the real-sequence wrapper establishing
  the exact destroyed count; focused verification passed `61/61` and Chapter 6
  passed `4578/4578`.
- `assertExactlyHeadMinusTwoCopiesSurvive` proves the complementary survivor
  count is exactly `head - 2`; focused verification passed `15/15`.
- Final validation is green: Chapter 6 passed `4593/4593` and all `230/230`
  Scala tests passed.
- `articles/chapter6/sieve-sequence-v2.md` now owns the three representations
  of the verified local law: distinct forbidden offsets, exactly two destroyed
  lifts, and exactly `head - 2` endpoint-surviving lifts.
- `articles/chapter6/gap-dynamics-v2.md` now consumes that companion result and
  keeps only the stronger arbitrary finite-run ceiling bound marked pending.

## Expected State

The new Chapter 6 property object contains stateless `.holds` theorems whose
headline methods take `SpecSieveSequence` explicitly. At minimum, the distinct
forbidden-index theorem and exact `head - 2` descendant theorem pass focused
verification and the Chapter 6 regression with no invalid or unknown VCs.
Any stronger recurrence/product theorem is included only if its aggregation
bridge is also fully verified.

## What is Learned

- The problem is deterministic and finite; Spark is unnecessary for proof.
- Exact existence and uniqueness of the forbidden lift for one residue are
  already verified, including a witness-returning API.
- Exact one-residue zero counting is also already verified through
  `SieveUtils.countZeroOffsets`.
- The missing proof is not modular inversion. It is the two-endpoint union
  count and then the structural aggregation from old real 2-gaps to new real
  2-gaps.
- The existing overall survivor-count theorem must not be cited as a 2-gap
  theorem: it counts accepted values removed by the new head.
- A full-period recurrence additionally needs proof that filtering cannot
  create a new gap of value `2` through merging and that each surviving copied
  endpoint pair corresponds exactly to one next-stage cyclic 2-gap.
- Returning a Boolean claim after a contradiction-heavy case split can leave
  Stainless with a difficult outer postcondition even when every inner
  assertion is valid. Returning the claim directly from both branches keeps
  the branch facts local and verified immediately here.

## Failed Paths

- **Placeholder `allowedClassesPerOddPrime(q)` alone.** The draft merely shows
  `mod(2, q) != 0`; it does not mention a sieve stage, copy indices, existence,
  uniqueness, or counts. Retry only as a private arithmetic substep inside a
  theorem connected to `SpecSieveSequence`.
- **Treating `sameHeadSurvivorCount` as a 2-gap count.** It counts accepted
  values, not inherited gap copies, so it cannot establish the requested
  recurrence. Revisit only if paired with a new bijection between the relevant
  accepted values and 2-gap descendants.
- **Starting from a new generic CRT development.** Existing Bézout/offset
  lemmas already prove the required fiber permutation and uniqueness in a
  Stainless-friendly form. Revisit only if the aggregation theorem genuinely
  requires a multi-prime CRT bijection not obtainable by finite iteration.
- **Trailing result after the forbidden-offset case split.** The first source
  shape proved every internal assertion (`39/40` VCs) but timed out for 300
  seconds on the final `.holds` postcondition because the branch contradiction
  did not propagate cheaply to a trailing `leftOffset != rightOffset`.
  Returning that claim directly in each branch verified (`41/41`). Retry the
  trailing-result shape only if Stainless gains stronger branch propagation.

## Open Concerns

- The real cyclic 2-gap must be stated with precise wrap semantics. A linear
  endpoint `a + 2` is simplest for the first theorem; the wrap gap may require
  a canonical lifted representative.
- Distinct witnesses require an explicit proof that an odd prime dividing both
  endpoints would divide their difference `2`; the best existing modulo lemma
  for this final subtraction step still needs selection.
- Counting two forbidden offsets is straightforward mathematically but may
  need a dedicated recursive indicator counter to keep Stainless VCs small.
- The global recurrence requires a no-new-2-gap merge theorem and a bijection,
  not merely multiplication of the local descendant count.

## Assumptions

- The incoming head is prime and greater than `2`, as provided by a real
  post-base sieve stage.
- The real period/modulus is nonnegative and nonzero modulo the incoming head.
- Both old 2-gap endpoints are accepted by the current real sequence.
- Lift indices range over the complete half-open block `[0, head)`.

## Validation

1. Establish baseline with `just test` and `just verify-ch 6`.
2. For each single Scala theorem, run `just verify <functionName>`.
3. After each focused success, run `just verify-ch 6` before the next theorem.
4. Run `just test` again after the completed source changes.
5. Update `OBJECTS.md` and the article only after the source theorem is green.

## Implementation Plan

1. Prove distinct forbidden offsets for the endpoints of one real linear
   2-gap in a new Chapter 6 property object.
2. Add one exact two-endpoint offset counter and prove the destroyed count is
   `2` over `[0, head)`.
3. Derive the local surviving-copy count `head - 2`.
4. Connect surviving endpoint copies to real next-stage copied gaps and prove
   no merged run creates a new 2-gap.
5. Aggregate over one complete old period for the one-stage recurrence.
6. Iterate the recurrence over a finite list of subsequent real sieve stages.

## Next Action

Define the real cyclic 2-gap population over one canonical period, including
the wrap gap, then prove the aggregation bijection: every new-stage 2-gap is
exactly one surviving lift of one old-stage 2-gap. Only after that theorem is
green derive the one-stage recurrence and finite product.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-08-14 | Deep search found that existence, uniqueness, and exact one-zero counting for each lifted residue fiber are already verified. The missing boundary begins at combining the two endpoints of a genuine 2-gap and then aggregating descendants. | Create this ticket, run baseline gates, then prove distinct forbidden offsets as the first single change. |
| 2026-08-14 | Green baseline established: all `230` Scala tests passed and Chapter 6 verified `4390/4390` VCs with no invalid or unknown results. | Select the existing modulo-difference lemma, then propose the distinct-forbidden-offset theorem. |
| 2026-08-14 | First theorem shape timed out only on its trailing postcondition after all 39 internal VCs passed. A corrected direct branch-return shape passed focused verification `41/41`. | Run the Chapter 6 regression; if green, catalog the theorem and move to the two-endpoint count. |
| 2026-08-14 | Chapter 6 regression passed `4431/4431` with no invalid or unknown VCs, up `41` from baseline. The first deterministic real-sieve 2-gap property is fully green and cataloged in `OBJECTS.md`. | Search for an existing two-predicate/union counter before adding the next single proof unit. |
| 2026-08-14 | No existing disjoint-union counter was found. Added `countDestroyedTwoGapCopies`, whose OR predicate counts each destroyed copy index once. Focused verification passed `16/16`; Chapter 6 passed `4447/4447`. | Prove the counter equals the number of its two distinct witnesses remaining in the scan. |
| 2026-08-14 | Proved the destroyed-copy union count equals the sum of the two disjoint endpoint zero counts (`70/70` focused; `4517/4517` Chapter 6). | Compose it with the exact-one endpoint counts in a real-sequence wrapper. |
| 2026-08-14 | Proved exactly two copies are destroyed (`61/61` focused; `4578/4578` Chapter 6) and exactly `head - 2` copies survive (`15/15` focused). Final Chapter 6 is `4593/4593`; tests are `230/230`. | Local copy law complete. Next work is the distinct cyclic aggregation/bijection theorem required for the global recurrence and finite product. |
| 2026-08-14 | Added all three representations of the verified local law to the Sieve Sequence article. The 2-gap article now links to that proof and distinguishes the verified complete-block claim from its still-pending arbitrary finite-run bound. | Keep the global recurrence out of both verified summaries until cyclic wrap handling and the aggregation bijection are Stainless-verified. |
