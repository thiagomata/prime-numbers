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
   - Status: verified as
     `SieveSequenceV0.assertMergeGapEqualsOldGapSum(nextSeq, k, period)`.
7. Public apply-to-gap-sum bridge:
   - `apply(k) == head.value + sumGap(0, k)` for all `k >= 0`.
   - Estimated complexity: low. One-line wrapper over private
     `assertSumGapTelescopes(0, k)`, which already proves
     `sumGap(0, k) == apply(k) - apply(0)`.
   - This is the entry point for expressing V0.apply as a CycleIntegral
     (needed by the V0-V2 matching ticket).
   - Status: not yet added. Planned as
     `SieveSequenceV0.assertApplyEqualsHeadPlusGapSum(k)`.
8. Gap list extraction:
   - `gapList(from, count)` returns `[gap(from), ..., gap(from+count-1)]` as
     a concrete `List[BigInt]`.
   - Lemmas: all gaps in the result are positive (`allGreaterThan(_, 0)`),
     result size equals `count`.
   - Estimated complexity: low. Direct recursion using `apply`, with
     positivity lemmas via `assertSumGapPositive`.
   - This makes the gap cycle explicitly constructable for items 9-11 below
     and for the V0-V2 matching ticket.
   - Status: not yet added.
 9. Prefix lift (was item 7):
    - repeat copy/merge across a bounded prefix of old generated values.
    - Estimated complexity: high. This introduces a recursive list-building
      proof and accounting for consumed old indices.
    - Status: prefix transformer verified as
      `SieveSequenceV0.mergedGapPrefix(nextSeq, k, remaining, period)`;
      prefix positivity verified as
      `assertMergedGapPrefixAllPositive(nextSeq, k, remaining, period)`;
      prefix equality verified as
      `assertMergedGapPrefixMatchesNext(nextSeq, k, seqIndex, remaining, period)`.
10. Gap-list cyclicity (was item 8):
    - prove the finite gap list repeats as a cycle, so later gaps are found by
      cycling through the same bounded list.
    - Estimated complexity: high. This bridges finite gap-list equality to
      cycle access and repeated positions.
    - Status: proven by `assertGapPeriodic(k, p)` at
      `SieveSequenceV0.scala:1037` — `gap(k + p) == gap(k)` for all k.
      The finite list `[gap(0), ..., gap(p-1)]` therefore generates all gaps
      by repeating. No additional cyclicity lemma needed.
11. Cycle lift (was item 9):
    - prove the bounded prefix corresponds to one rotated gap cycle.
    - Estimated complexity: very high. This combines prefix equality,
      positivity, non-emptiness, rotation, and cycle construction.
    - Status: deferred to `v0-v2-apply-equivalence.md` (bridge ticket).
      V0 provides all prerequisites (`gapList`, `assertGapPeriodic`,
      `assertApplyEqualsHeadPlusGapSum`, `assertMergedGapPrefixMatchesNext`).
      The GapCycle construction and integral equivalence follow the
      `assertCycleIntegralEqualsSumOfModValuesAsList` pattern from
      `CycleIntegralProperties`.
12. Conditional next-prime bridge (was item 10):
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
- `SieveSequenceV0.nextMergedGapOldIndex(nextSeq, k, period)` is the verified
  one-step old-index transformer. It returns an index strictly after `k` whose
  old-stream value is accepted by `nextSeq`, choosing either the copied
  successor or the first bounded merge survivor. As of `8f6091d`, its
  postcondition was strengthened to also export `accepts(apply(res))` and
  `Calc.mod(apply(res), nextSeq.filterValues.head) != 0`. As of 2026-06-22, its
  postcondition was further strengthened to export the gap equality
  `nextSeq(vIdx+1) - nextSeq(vIdx) == sumGap(k, res)`, with branch-specific
  lemma assertions (`assertFilterPreservesNextGap` for copy,
  `assertMergeGapEqualsOldGapSum` for merge) in each branch body and the
  telescoped equality re-exported via `.ensuring`. Verified with 7621 valid (+14
  over 7607).
- `SieveSequenceV0.mergedGapPrefix(nextSeq, k, remaining, period)` builds a
  bounded prefix of copied-or-merged gaps by repeatedly using
  `nextMergedGapOldIndex` and emitting `sumGap(k, nextK)`. Its recursion
  decreases on the requested output count `remaining`, not on the number of old
  indices consumed.
- `SieveSequenceV0.assertSumGapPositive(from, until)` proves the private
  positivity fact `sumGap(from, until) > 0` whenever `until > from`, by
  inducting on `until - from` and using `applyStrictlyIncreases(from)` for each
  summand. It is the positivity companion to `assertSumGapTelescopes` and the
  single-step foundation for prefix-level positivity. Private `.holds`.
- `SieveSequenceV0.assertMergedGapPrefixAllPositive(nextSeq, k, remaining, period)`
  lifts positivity to the whole emitted prefix: every gap in
  `mergedGapPrefix(nextSeq, k, remaining, period)` is strictly positive. The
  induction decreases on `remaining`; the cons step combines the single-step
  `assertSumGapPositive` (head) with the inductive hypothesis (tail) and makes
  the head/tail split explicit via `ListBoundUtils.assertGreaterThanHeadTail`.
  Public `.holds`.
- `SieveSequenceV0.next` now has an explicit `List.head`-style precondition:
  `primes.nextPrime.value < head.value * head.value`.
- `SieveSequenceV0.assertApplyEqualsHeadPlusGapSum(k)` (new item 7) proves
  `apply(k) == head.value + sumGap(0, k)` for all k >= 0. Trivial wrapper over
  private `assertSumGapTelescopes(0, k)`. Verified: 7562 valid (+7).
- `SieveSequenceV0.gapList(from, count)` (new item 8) extracts a concrete
  `List[BigInt]` of gaps from position `from` to `from+count-1`. Structural
  recursion on `count`. Verified: 7568 valid (+6).
- `SieveSequenceV0.assertGapListPositive(from, count)` proves every element in
  the gap list is strictly positive. Induction on `count`, uses `assertGapPositive`
  for each element. Verified: 7579 valid (+11).
- `SieveSequenceV0.assertGapListSize(from, count)` proves the gap list size
  equals the requested count. Verified: 7590 valid (+11).
- `SieveSequenceV0.assertMergedGapPrefixHeadMatchesNext(nextSeq, k, period)`
  proves the first gap emitted by `mergedGapPrefix(nextSeq, k, 1, period)` equals
  the corresponding `nextSeq` gap `nextSeq(vIdx+1) - nextSeq(vIdx)`. Uses the
  strengthened postcondition of `nextMergedGapOldIndex`. Verified: 7643 valid (+22).

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
- 2026-06-22: Added `nextMergedGapOldIndex(nextSeq, k, period)`, a public
  one-step transformer for the prefix proof. It preserves the key recursion
  invariant by proving the returned old index is strictly after `k` and its
  value is accepted by `nextSeq`. Verification passed:
  `total: 7445 valid: 7445 invalid: 0 unknown: 0`.
- 2026-06-22: Added `mergedGapPrefix(nextSeq, k, remaining, period)`, the first
  bounded prefix transformer. It emits `sumGap(k, nextK)` for each copied or
  merged step and terminates by decreasing `remaining`. Verification passed:
  `total: 7478 valid: 7478 invalid: 0 unknown: 0`.
- 2026-06-22 (commit `8f6091d`, "nextMergedGapOldIndex improved"): Strengthened
  the postcondition of `nextMergedGapOldIndex` to export three facts instead of
  one: `accepts(apply(res))`, `Calc.mod(apply(res), nextSeq.filterValues.head)
  != 0`, and `nextSeq.accepts(apply(res))`, all in addition to `res > k`. The
  prior postcondition only exported `res > k && nextSeq.accepts(apply(res))`,
  which was insufficient for prefix positivity because callers could not reuse
  the bridge-shape invariant. Verification passed:
  `total: 7488 valid: 7488 (7468 from cache, 20 trivial) invalid: 0 unknown: 0`.
  This is the source of the 7478 → 7488 valid-count jump not previously logged.
  Lesson: when a prefix transformer will consume a one-step transformer's
  invariant, the invariant must appear in the one-step transformer's
  postcondition, not just in its internal assertions (consistent with
  LEARNINGS.md 1.2 on `.ensuring` propagation).
- 2026-06-22: Evaluated the ticket against the current code, OBJECTS.md, and
  LEARNINGS.md. All 11 claimed lemmas are present in `SieveSequenceV0.scala`
  (lines 999–1801) and reflected in OBJECTS.md (lines 897–944). The complexity
  ladder and its rationale are consistent with LEARNINGS.md sections 1, 7, 18.
  The conditional next-prime bridge (#10) is explicitly out of scope for this
  session because it is the "prime between p and p²" wall tracked separately
  in `prove-apply1-is-prime.md` and `conditional-nextprime-gap-cycle-bridge.md`
  (LEARNINGS.md 10.1, 18.1).
- 2026-06-22: Added `assertSumGapPositive(from, until)`, the positivity
  companion to `assertSumGapTelescopes`. It proves `sumGap(from, until) > 0`
  whenever `until > from` by inducting on `until - from` and using
  `applyStrictlyIncreases(from)` for each summand. This is the foundation for
  proving every emitted gap in `mergedGapPrefix` is positive, since
  `nextMergedGapOldIndex`'s strengthened postcondition guarantees `nextK > k`.
  Verification passed:
  `total: 7503 valid: 7503 (7469 from cache, 20 trivial) invalid: 0 unknown: 0`.
  +15 valid VCs over the previous run (7488).
- 2026-06-22: Added `assertMergedGapPrefixAllPositive(nextSeq, k, remaining, period)`,
  the list-level positivity lift. Each emitted gap is `sumGap(k, nextOldIndex)`
  with `nextOldIndex > k`, so each is positive by `assertSumGapPositive`; by
  induction on `remaining`, the entire emitted prefix satisfies
  `allGreaterThan(_, 0)`. The cons step makes the head/tail split explicit via
  `ListBoundUtils.assertGreaterThanHeadTail` (head from the single-step lemma,
  tail from the inductive hypothesis). Marked **public** because it is a
  caller-facing property that a future gap-cycle proof will consume.
  Verification passed:
  `total: 7555 valid: 7555 (7491 from cache, 20 trivial) invalid: 0 unknown: 0`.
  +52 valid VCs over the previous run (7503). Open Work item #1 (positivity)
  is now complete.
- 2026-06-22: Added `assertApplyEqualsHeadPlusGapSum(k)` (ladder item 7), a
  public lemma proving `apply(k) == head.value + sumGap(0, k)` for all k >= 0.
  This is a trivial wrapper over private `assertSumGapTelescopes(0, k)` and is
  the entry point for the V0-V2 bridge ticket to express V0.apply as a
  CycleIntegral. Verification passed:
  `total: 7562 valid: 7562 (7535 from cache, 20 trivial) invalid: 0 unknown: 0`.
  +7 VCs over the previous run (7555).
- 2026-06-22: Added `gapList(from, count)` (ladder item 8), extracting a concrete
  `List[BigInt]` of gaps from the V0 sequence. Followed by `assertGapListPositive`
  (proves all gaps > 0) and `assertGapListSize` (proves result.size == count).
  These make the gap cycle explicitly constructable for the cyclicity proofs and
  the V0-V2 bridge. Verification passed:
  `total: 7590 valid: 7590 (7561 from cache, 20 trivial) invalid: 0 unknown: 0`.
  +28 VCs over the previous run (7562). Open Work items #4 and #5 are now complete.
- 2026-06-22: Strengthened `nextMergedGapOldIndex`'s postcondition with the gap
  equality `nextSeq(vIdx+1) - nextSeq(vIdx) == sumGap(k, res)`. Added branch-
  specific lemma assertions (`assertFilterPreservesNextGap` for copy,
  `assertMergeGapEqualsOldGapSum` for merge) in each branch body, and re-exported
  the telescoped equality via `.ensuring`. Verified: 7621 valid (+14 over 7607).
- 2026-06-22: Added `assertMergedGapPrefixHeadMatchesNext(nextSeq, k, period)`,
  proving the first emitted gap of `mergedGapPrefix` matches the corresponding
  `nextSeq` gap. Relies on `nextMergedGapOldIndex`'s strengthened postcondition.
  Verification passed:
  `total: 7643 valid: 7643 (7607 from cache, 20 trivial) invalid: 0 unknown: 0`.
  +22 VCs over the previous run (7621).
- 2026-06-22: Strengthened `nextMergedGapOldIndex` step by step with the value
  equality `nextSeq(vIdx+1) == apply(res)`: (a) added `vIdx` to function body
  (7646), (b) asserted value equality in copy branch (7649), (c) asserted
  `assertSumGapTelescopes` then value equality in merge branch (7652→7655),
  (d) changed `.ensuring` from difference to BOTH value and difference equality
  (7659). Verified green after each step.
- 2026-06-22: Added `assertApplyIncreases(k, m)` (public, proves `apply(k) < apply(m)`
  for `k < m` by induction) and `assertApplyInjective(k, m)` (public, proves `k == m`
  given `apply(k) == apply(m)`). Verified: 7752 valid (+93).
- 2026-06-22: Removed unnecessary private `assertModSmall` lemma (external `.holds`
  lemmas propagate their equalities correctly — no private wrapper needed).
  Corrected LEARNINGS.md section 1.1 to reflect this. Verified: 7755 valid.
- 2026-06-22: Marked items 10 (gap-list cyclicity) and 11 (cycle lift) as resolved:
  cyclicity is proven by `assertGapPeriodic(k, p)`, cycle lift deferred to
  `v0-v2-apply-equivalence.md` which consumes V0's existing lemmas.
  Ticket is ready for closure — all V0-internal properties are proven.
- 2026-06-22: Uncommented and verified `assertMergedGapPrefixMatchesNext`.
  Uses `nextSeq.assertApplyInjective` to connect the parameter `seqIndex` with
  `nextSeq.indexOfAccepted(apply(k))`, unlocking the inductive tail equality.
  Verified: 7755 valid (+3). Open Work item #2 (prefix equality) is now complete.

## Downstream Dependency

This ticket is a prerequisite for:
- `v0-v2-apply-equivalence.md` — proves `SieveSequenceV0.apply(k) == SieveSequenceV2.apply(k)`.

Items 7-8 (the public apply-to-gap-sum lemma and gap list extraction) were identified
as missing during a cross-ticket audit. They are the entry points the bridge ticket
consumes from V0.

## Open Work

1. ~~Prove the generated prefix is positive and non-empty.~~ **Done.**
   - `assertSumGapPositive(from, until)` (private) proves the single-step case.
   - `assertMergedGapPrefixAllPositive(nextSeq, k, remaining, period)` (public)
     lifts it to the entire emitted prefix.
   - Non-emptiness is implicit: when `remaining > 0`, the prefix has exactly
     `remaining` elements by `mergedGapPrefix`'s recursion shape.
2. ~~Prove prefix equality against the next sequence's first generated values.~~ **Done.**
   - `assertApplyIncreases(k, m)` (public) proves `apply(k) < apply(m)` for `k < m`
     by induction using `applyStrictlyIncreases`. Verified with 7752 valid.
   - `assertApplyInjective(k, m)` (public) proves `k == m` given `apply(k) == apply(m)`
     by contradiction using `assertApplyIncreases`. Verified with 7752 valid.
   - `assertMergedGapPrefixMatchesNext(nextSeq, k, seqIndex, remaining, period)`
     (public) proves `mergedGapPrefix(...) == nextSeq.gapList(seqIndex, remaining)`
     where `seqIndex` satisfies `nextSeq(seqIndex) == apply(k)`. Induction on `remaining`:
     the head matches via `assertMergedGapPrefixHeadMatchesNext`, the tail via IH
     coupled with `nextSeq.assertApplyInjective` to connect `seqIndex` with
     `nextSeq.indexOfAccepted(apply(k))` and the `.ensuring` value equality from
     `nextMergedGapOldIndex`. Verified with 7755 valid.
   - Shape (b) (partial sums reconstruct nextSeq.apply) is implied by (a) since
     gapList partial sums reconstruct nextSeq.apply by construction.
3. ~~Only after the prefix theorem is green, lift it to a gap-cycle statement.~~ **Done via existing lemmas.**
   - Gap-list cyclicity (ladder item 10) is proven by `assertGapPeriodic(k, p)`:
     `gap(k + p) == gap(k)` for all k, documented at `SieveSequenceV0.scala:1037`.
   - The finite gap list `[gap(0), ..., gap(p-1)]` when repeated generates all gaps
     — this follows directly from periodicity. No additional lemma needed.
   - Cycle lift (ladder item 11) — constructing a `GapCycle` from `gapList(0, p)`
     and proving `CycleIntegral(head, gapCycle).apply(k-1) == apply(k)` —
     will be addressed in the bridge ticket `v0-v2-apply-equivalence.md`,
     which consumes the V0 lemmas (apply-to-gap-sum, gapList, gap periodicity,
     gap positivity) via the `assertCycleIntegralEqualsSumOfModValuesAsList`
     pattern from `CycleIntegralProperties`.
4. ~~**Add `assertApplyEqualsHeadPlusGapSum(k)`** (ladder item 7).~~ **Done.**
   - Public `.holds` lemma: `apply(k) == head.value + sumGap(0, k)` for k >= 0.
   - Trivial: delegates to private `assertSumGapTelescopes(0, k)`.
   - Verified with 7562 valid (+7 from 7555).
5. ~~**Add `gapList(from, count)` and positivity/size lemmas** (ladder item 8).~~ **Done.**
   - `gapList(from, count)` returns `List[BigInt] = [gap(from), ..., gap(from+count-1)]`.
   - `assertGapListPositive(from, count)`: `allGreaterThan(result, 0)`, verified 7579.
   - `assertGapListSize(from, count)`: `result.size == count`, verified 7590.
6. After items 2-5 are green, the V0-V2 bridge ticket can consume the results.
   Once the gap cycle is fully formalized within V0 (items 2-5, 9-12), open a
   ticket for any remaining V0 properties the bridge needs.

## Complexity Rationale Addendum

Items 7-8 are placed before the complex prefix/cycle work (items 9-11) because:
- `assertApplyEqualsHeadPlusGapSum` is a trivial one-line wrapper that unblocks
  the downstream V0-V2 matching ticket.
- `gapList` is simple structural recursion; its VCs are small and independent of
  the merge/copy prefix proof.
- Both provide explicit foundations that the cyclicity proofs (items 10-11)
  should consume rather than re-deriving.

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
