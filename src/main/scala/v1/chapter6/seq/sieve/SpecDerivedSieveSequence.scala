package v1.chapter6.seq.sieve

import stainless.collection.List
import stainless.lang.BooleanDecorations
import stainless.lang.decreases
import v1.chapter2.div.Calc
import v1.chapter4.cycle.gap.GapCycle
import v1.chapter4.cycle.integral.recursive.CycleIntegral
import v1.chapter4.cycle.memory.MemCycle
import v1.chapter5.prime.{AllPrimesSoFarList, Prime, PrimeUtils, SortedPrimeList}

/**
 * A `SpecDerivedCycleSieve` variant that stores `primes` as `AllPrimesSoFarList`
 * instead of `List[BigInt]`. This exposes the richer prime-type API for lemma
 * proofs — `nextPrime`, `noDivisorInRange`, primorial, etc. — all verified in
 * the prime chapter.
 *
 * The `cycle` field is a standard `CycleSieveSequence` (with `List[BigInt]`
 * primes, converted via `PrimeUtils.primeValues`). The APSFL version of the
 * prime list is available as `primesAPSFL` for proof use.
 *
 * Usage: construct from a `SpecSieveSequence` + `period`, then use the lemma
 * methods to discharge `nextFromWindow()` requires. Convert to `CycleSieveSequence`
 * via `cycle` when a concrete sequence is needed.
 */
case class SpecDerivedSieveSequence(
  spec: SpecSieveSequence,
  period: BigInt
) {
  require(period > BigInt(0))
  require(spec(period) == spec.head.value + spec.filterModulus)
  require(spec.primes.nextPrime.value < spec.head.value * spec.head.value)
  require(spec.primes.list.nonEmpty)
  require(
    Calc.mod(
      SieveUtils.product(spec.filterValues),
      spec.head.value
    ) != BigInt(0)
  )

  /** Gap cycle derived from the spec — same as SpecDerivedCycleSieve. */
  val gapCycle: GapCycle = spec.specGapCycle(period)

  /** Prime list as AllPrimesSoFarList — all lemmas from prime chapter available. */
  val primes: AllPrimesSoFarList = spec.primes

  /** Prime list as List[BigInt] for CycleSieveSequence construction. */
  val cyclePrimes: List[BigInt] = PrimeUtils.primeValues(primes.list.list)

  /** Standard CycleSieveSequence (for callers that need the concrete type). */
  val cycle: CycleSieveSequence = CycleSieveSequence(primes, gapCycle)

  /** Cycle integral — same as cycle.integral. */
  val integral: CycleIntegral = cycle.integral

  // ─── Spec-matching lemmas (bridge) ───────────────────────────────────────

  /**
   * Proves `cycle(k) == spec(k)` for all k — same as SpecDerivedCycleSieve's.
   * Delegates to the spec's certified gap cycle integral.
   */
  def assertApplyMatches(k: BigInt): Boolean = {
    require(k >= BigInt(0))
    if (k == BigInt(0)) {
      assert(cycle.head == spec.head.value)
      assert(spec(BigInt(0)) == spec.head.value)
      cycle(k) == spec(k)
    } else {
      assert(cycle.gapCycle.memCycle == gapCycle.memCycle)
      assert(cycle.integral ==
        v1.chapter4.cycle.integral.recursive.CycleIntegral(
          spec.head.value, gapCycle.memCycle))
      assert(spec.assertSpecGapCycleIntegralMatchesApply(period, k))
      cycle(k) == spec(k)
    }
  }.holds

  /**
   * Proves `cycle(1) == spec.next.head.value` — next head matches.
   * Mirrors SpecDerivedCycleSieve's version.
   */
  def assertNextHeadMatches(): Boolean = {
    assert(assertApplyMatches(BigInt(1)))
    assert(spec.assertApplyOneEqualsNextPrime())
    assert(cycle(BigInt(1)) == spec(BigInt(1)))
    assert(spec(BigInt(1)) == spec.primes.nextPrime.value)
    assert(spec.next.head.value == spec.primes.nextPrime.value)
    cycle(BigInt(1)) == spec.next.head.value
  }.holds

  /**
   * Proves `cycle(1) == spec(1)` and cycle's prime list matches spec's
   * filter values (for isCoprime compatibility).
   */
  def assertPrimesMatch(): Boolean = {
    assert(assertApplyMatches(BigInt(0)))
    assert(cycle.head == spec.head.value)
    assert(cyclePrimes == PrimeUtils.primeValues(primes.list.list))
    assert(primes.list.list == spec.primes.list.list)
    true
  }.holds

  /** Proves cycle(k) is coprime to all tail primes (by spec bridge). */
  def assertCycleValueCoprimeToTail(k: BigInt): Boolean = {
    require(k >= BigInt(0))
    assert(assertApplyMatches(k))
    assert(spec.accepts(spec(k)))
    SieveUtils.isCoprime(cycle(k), cyclePrimes.tail)
  }.holds

  /**
   * Proves cycle(1) is coprime to ALL primes (head + tail).
   * Uses AllPrimesSoFarList's noDivisorInRangeExcludesValue via the spec.
   */
  def assertNewHeadCoprimeToAllPrimes(): Boolean = {
    assert(assertCycleValueCoprimeToTail(BigInt(1)))
    assert(spec.assertApplyOneEqualsNextPrime())
    assert(assertApplyMatches(BigInt(1)))
    assert(Prime.isPrime(spec(BigInt(1))))
    assert(Prime.noDivisorInRangeExcludesValue(
      spec(BigInt(1)), BigInt(2), spec(BigInt(1)), spec.head.value))
    assert(Calc.mod(spec(BigInt(1)), spec.head.value) != BigInt(0))
    Calc.mod(cycle(BigInt(1)), cycle.head) != BigInt(0) &&
    SieveUtils.isCoprime(cycle(BigInt(1)), cyclePrimes)
  }.holds

  /**
   * Proves the cycle position k returns the (k+1)-th value coprime to all
   * tail primes.  Exclusion via assertCycleValueCoprimeToTail.
   * Inclusion via assertApplyMatches.
   */
  def assertCyclePositionMatchesSpec(k: BigInt): Boolean = {
    require(k >= BigInt(0))
    assert(assertCycleValueCoprimeToTail(k))
    assert(assertApplyMatches(k))
    assert(spec.accepts(spec(k)))
    assert(SieveUtils.isCoprime(cycle(k), cyclePrimes.tail))
    true
  }.holds

  /**
   * First survivor head matches spec.next(0).
   */
  def assertFirstSurvivorEqualsSpecNext0(): Boolean = {
    assert(assertNextHeadMatches())
    assert(cycle(BigInt(1)) == cycle.integral(BigInt(0)))
    assert(spec.next(BigInt(0)) == spec.next.head.value)
    cycle.integral(BigInt(0)) == spec.next.head.value
  }.holds

  /**
   * Per-index gap equality: survivor gap = spec.next gap.
   */
  def assertSurvivorGapEqualsSpecNextGap(nextPeriod: BigInt, k: BigInt): Boolean = {
    require(nextPeriod > BigInt(1))
    require(k >= BigInt(0))
    require(k + BigInt(1) < nextPeriod)
    require(spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus)
    assert(spec.assertNextValueAcceptedByThis(k))
    assert(spec.assertNextValueAcceptedByThis(k + BigInt(1)))
    val pos1 = spec.indexOfAccepted(spec.next(k))
    val pos2 = spec.indexOfAccepted(spec.next(k + BigInt(1)))
    assert(assertApplyMatches(pos1))
    assert(assertApplyMatches(pos2))
    assert(spec(pos1) == spec.next(k))
    assert(spec(pos2) == spec.next(k + BigInt(1)))
    spec.next(k + BigInt(1)) - spec.next(k) == cycle(pos2) - cycle(pos1)
  }.holds

  /**
   * Per-position: spec.next(k) == cycle(spec.indexOfAccepted(spec.next(k))).
   */
  def assertSpecNextIsKthSurvivor(nextPeriod: BigInt, k: BigInt): Boolean = {
    require(nextPeriod > BigInt(1))
    require(k >= BigInt(0))
    require(k < nextPeriod)
    require(spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus)
    decreases(k)
    if (k == BigInt(0)) {
      assertFirstSurvivorEqualsSpecNext0()
    } else {
      assertSpecNextIsKthSurvivor(nextPeriod, k - BigInt(1))
      if (k < nextPeriod - BigInt(1)) {
        assert(assertSurvivorGapEqualsSpecNextGap(nextPeriod, k - BigInt(1)))
      }
    }
    val pos = spec.indexOfAccepted(spec.next(k))
    assert(assertApplyMatches(pos))
    spec.next(k) == cycle(pos)
  }.holds

  /**
   * Top-level theorem: same-stage + next-stage head equality.
   */
  def assertFullEquivalence(nextPeriod: BigInt, k: BigInt): Boolean = {
    require(nextPeriod > BigInt(0))
    require(k >= BigInt(0))
    require(k < nextPeriod)
    require(spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus)
    assert(assertApplyMatches(k))
    assert(assertNextHeadMatches())
    assert(assertFirstSurvivorEqualsSpecNext0())
    cycle(k) == spec(k) && cycle(BigInt(1)) == spec.next.head.value
  }.holds

  /**
   * Canonical next-stage gap-cycle packaging.
   *
   * This lemma is intentionally about the Spec-certified next cycle, not about
   * the independent pipeline output. It records the construction fact that
   * `spec.next.specGapCycle(nextPeriod)` stores exactly
   * `spec.next.gapList(0, nextPeriod)` as its memory-cycle values. Keeping this
   * bridge explicit prevents future edits from mistaking the canonical
   * Spec-derived cycle proof for a proof about `nextRotatedGaps(cycle)`.
   */
  def assertNextGapCycleValuesEqualSpecNextGapList(nextPeriod: BigInt): Boolean = {
    require(nextPeriod > BigInt(0))
    require(spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus)

    spec.next.specGapCycle(nextPeriod).memCycle.values == spec.next.gapList(BigInt(0), nextPeriod)
  }.holds

  /**
   * Canonical next-stage apply equality.
   *
   * This is the current-stage `assertApplyMatches` lemma instantiated one stage
   * later: construct the Spec-derived wrapper for `spec.next`, then use that
   * wrapper's current-stage apply lemma. It proves a correct canonical next
   * cycle exists; it still does not claim the independent pipeline computed it.
   */
  def assertNextCycleApplyMatchesSpecNext(nextPeriod: BigInt, k: BigInt): Boolean = {
    require(nextPeriod > BigInt(0))
    require(k >= BigInt(0))
    require(spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus)
    require(spec.next.primes.nextPrime.value < spec.next.head.value * spec.next.head.value)
    require(spec.next.primes.list.nonEmpty)
    require(Calc.mod(SieveUtils.product(spec.next.filterValues), spec.next.head.value) != BigInt(0))

    val nextCanonical = SpecDerivedSieveSequence(spec.next, nextPeriod)
    assert(nextCanonical.assertApplyMatches(k))

    nextCanonical.cycle(k) == spec.next(k)
  }.holds

  /**
   * Canonical next-stage head equality.
   *
   * The next canonical wrapper is built from `spec.next`, so its cycle head is
   * the same prime head stored by `spec.next`. This is another construction
   * fact, intentionally separate from any independent pipeline claim.
   */
  def assertNextCycleHeadMatchesSpecNext(nextPeriod: BigInt): Boolean = {
    require(nextPeriod > BigInt(0))
    require(spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus)
    require(spec.next.primes.nextPrime.value < spec.next.head.value * spec.next.head.value)
    require(spec.next.primes.list.nonEmpty)
    require(Calc.mod(SieveUtils.product(spec.next.filterValues), spec.next.head.value) != BigInt(0))

    val nextCanonical = SpecDerivedSieveSequence(spec.next, nextPeriod)

    nextCanonical.cycle.head == spec.next.head.value
  }.holds

  /**
   * Canonical next-stage gap equality.
   *
   * The canonical wrapper for `spec.next` stores `spec.next.specGapCycle` as
   * its gap cycle. The earlier packaging lemma exposes that this gap cycle's
   * memory values are exactly `spec.next.gapList(0, nextPeriod)`.
   */
  def assertNextCycleGapsMatchSpecNext(nextPeriod: BigInt): Boolean = {
    require(nextPeriod > BigInt(0))
    require(spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus)
    require(spec.next.primes.nextPrime.value < spec.next.head.value * spec.next.head.value)
    require(spec.next.primes.list.nonEmpty)
    require(Calc.mod(SieveUtils.product(spec.next.filterValues), spec.next.head.value) != BigInt(0))

    val nextCanonical = SpecDerivedSieveSequence(spec.next, nextPeriod)
    val nextSpecGapCycle = spec.next.specGapCycle(nextPeriod)

    assert(nextCanonical.cycle.gapCycle == nextSpecGapCycle)
    assert(assertNextGapCycleValuesEqualSpecNextGapList(nextPeriod))

    nextCanonical.cycle.gapCycle.memCycle.values == spec.next.gapList(BigInt(0), nextPeriod)
  }.holds

  /**
   * Canonical next-stage gap positivity.
   *
   * This is the positivity side of the canonical next-cycle bridge. The next
   * spec stage already proves that `gapList(0, nextPeriod)` is strictly
   * positive because it is built from adjacent increasing `apply` values. This
   * lemma exposes the same fact through the canonical next cycle's stored gap
   * list, giving the independent pipeline proof a precise equality target:
   * first prove the pipeline gaps equal these canonical gaps, then reuse this
   * positivity theorem for `GapCycle(newGaps)`.
   */
  def assertNextCycleGapsPositive(nextPeriod: BigInt): Boolean = {
    require(nextPeriod > BigInt(0))
    require(spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus)
    require(spec.next.primes.nextPrime.value < spec.next.head.value * spec.next.head.value)
    require(spec.next.primes.list.nonEmpty)
    require(Calc.mod(SieveUtils.product(spec.next.filterValues), spec.next.head.value) != BigInt(0))

    val nextCanonical = SpecDerivedSieveSequence(spec.next, nextPeriod)

    assert(assertNextCycleGapsMatchSpecNext(nextPeriod))
    assert(spec.next.assertSpecGapPeriodPositive(nextPeriod))

    v1.chapter3.list.ListBoundUtils.allGreaterThan(
      nextCanonical.cycle.gapCycle.memCycle.values,
      BigInt(0)
    )
  }.holds

  /**
   * Builds the next-stage gap list directly from adjacent `spec.next` values.
   *
   * This is a canonical target for producer proofs, not an independent
   * producer. Its recursion deliberately mirrors `SpecSieveSequence.gapList`:
   * the `from` parameter slides forward and each step conses the next adjacent
   * difference. Keeping the same forward order avoids the reversed-builder
   * timeout that older attempts hit.
   */
  def nextGapList(from: BigInt, count: BigInt): List[BigInt] = {
    require(from >= BigInt(0))
    require(count >= BigInt(0))
    decreases(count)
    if (count == BigInt(0)) {
      List.empty[BigInt]
    } else {
      (spec.next(from + BigInt(1)) - spec.next(from)) ::
        nextGapList(from + BigInt(1), count - BigInt(1))
    }
  }

  /**
   * Proves the direct adjacent-difference target equals `spec.next.gapList`.
   *
   * Future independent pipeline or walk proofs should target this list, or the
   * equivalent `spec.next.gapList`, when proving next-stage equality. This
   * lemma is intentionally small: it only aligns two canonical descriptions of
   * the same next-stage gaps and does not assert that the pipeline produced
   * them.
   */
  def assertNextGapListMatchesSpecNext(from: BigInt, count: BigInt): Boolean = {
    require(from >= BigInt(0))
    require(count >= BigInt(0))
    decreases(count)

    if (count == BigInt(0)) {
      nextGapList(from, BigInt(0)) == spec.next.gapList(from, BigInt(0))
    } else {
      assert(spec.next.assertGapListFirstEqualsGap(from, count))
      assert(assertNextGapListMatchesSpecNext(from + BigInt(1), count - BigInt(1)))
      nextGapList(from, count) == spec.next.gapList(from, count)
    }
  }.holds

  /**
   * Canonical next-stage structural identity.
   *
   * Packages the separately verified canonical facts: the wrapper built from
   * `spec.next` has the same head and stored gap list as `spec.next`, and its
   * apply behavior is available through `assertNextCycleApplyMatchesSpecNext`.
   * This is the migrated "correct next cycle exists" theorem, still distinct
   * from proving that the independent pipeline produced that cycle.
   */
  def assertNextCycleMatchesSpecNext(nextPeriod: BigInt): Boolean = {
    require(nextPeriod > BigInt(0))
    require(spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus)
    require(spec.next.primes.nextPrime.value < spec.next.head.value * spec.next.head.value)
    require(spec.next.primes.list.nonEmpty)
    require(Calc.mod(SieveUtils.product(spec.next.filterValues), spec.next.head.value) != BigInt(0))

    assert(assertNextCycleHeadMatchesSpecNext(nextPeriod))
    assert(assertNextCycleGapsMatchSpecNext(nextPeriod))

    true
  }.holds

  /**
   * Packages the current and canonical next-stage apply equalities.
   *
   * This names the main equality spine for the three-representation proof:
   * the current `cycle` stored by this derived wrapper agrees with `spec`, and
   * the canonical next wrapper built from `spec.next` agrees with `spec.next`.
   * It deliberately does not claim that the independent pipeline produced the
   * next wrapper's gap cycle; that producer theorem remains the separate
   * `nextFromCycle` obligation.
   */
  def assertCurrentAndCanonicalNextApplyMatches(nextPeriod: BigInt, k: BigInt): Boolean = {
    require(nextPeriod > BigInt(0))
    require(k >= BigInt(0))
    require(spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus)
    require(spec.next.primes.nextPrime.value < spec.next.head.value * spec.next.head.value)
    require(spec.next.primes.list.nonEmpty)
    require(Calc.mod(SieveUtils.product(spec.next.filterValues), spec.next.head.value) != BigInt(0))

    assert(assertApplyMatches(k))
    assert(assertNextCycleApplyMatchesSpecNext(nextPeriod, k))

    cycle(k) == spec(k) &&
      SpecDerivedSieveSequence(spec.next, nextPeriod).cycle(k) == spec.next(k)
  }.holds

  /**
   * Pipeline precondition: the cycle modulus is positive.
   *
   * `SieveSequenceNextLevel` operates on the tail-prime modulus. For a
   * Spec-derived cycle this is exactly the primorial of `primes.list.tail`,
   * and chapter 5 already proves every primorial is strictly positive.
   */
  def assertModulusPositive(): Boolean = {
    assert(PrimeUtils.primorialPositive(primes.list.tail.list))
    cycle.modulus > BigInt(0)
  }.holds

  /**
   * Pipeline precondition: every tail-prime value is positive.
   *
   * `PrimeUtils.primeValues` is the single bridge from `List[Prime]` to
   * `List[BigInt]`; its postcondition already exports positivity. Keeping this
   * as a named lemma prevents future pipeline proofs from duplicating the same
   * list/value reasoning.
   */
  def assertPrimesTailValuesPositive(): Boolean = {
    assert(cycle.primesTailValues == PrimeUtils.primeValues(primes.list.tail.list))
    v1.chapter3.list.ListUtils.checkAllPositive(cycle.primesTailValues)
  }.holds

  /**
   * Pipeline precondition: the current head prime is positive.
   */
  def assertHeadPositive(): Boolean = {
    cycle.head > BigInt(0)
  }.holds

  /**
   * Pipeline precondition: the expanded next-stage modulus is positive.
   *
   * This combines the two independent positive factors required by
   * `SieveSequenceNextLevel.nextGaps`: the current tail modulus and the current
   * head prime.
   */
  def assertModulusTimesHeadPositive(): Boolean = {
    assert(assertModulusPositive())
    assert(assertHeadPositive())
    cycle.modulus * cycle.head > BigInt(0)
  }.holds

  /**
   * Computes the independent next-stage rotated gap list from B's own cycle.
   *
   * This is the producer half of `nextFromCycle`, isolated before the
   * `GapCycle` constructor. Keeping it as a plain list lets us prove equality
   * against the canonical target first; only after that equality is available
   * should callers reuse canonical positivity to build `GapCycle(newGaps)`.
   */
  def nextPipelineGaps(): List[BigInt] = {
    assert(assertModulusPositive())
    assert(assertPrimesTailValuesPositive())
    assert(assertHeadPositive())
    assert(assertModulusTimesHeadPositive())

    SieveSequenceNextLevel.nextRotatedGaps(cycle)
  }

  /**
   * Conditional bridge from the future producer equality to gap positivity.
   *
   * The hard theorem is the equality in the precondition: the independent
   * pipeline must produce the same rotated gap list as the canonical next spec
   * period. Once that equality is available, positivity is immediate from the
   * existing apply/gap invariant on `spec.next`.
   */
  def assertNextPipelineGapsPositiveFromSpec(nextPeriod: BigInt): Boolean = {
    require(nextPeriod > BigInt(0))
    require(spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus)
    require(nextPipelineGaps() == spec.next.gapList(BigInt(0), nextPeriod))

    assert(spec.next.assertSpecGapPeriodPositive(nextPeriod))
    v1.chapter3.list.ListBoundUtils.allGreaterThan(nextPipelineGaps(), BigInt(0))
  }.holds

  /**
   * Builds the independent pipeline gap cycle once producer equality is known.
   *
   * The equality precondition is intentionally the only hard fact here. It lets
   * this method reuse the canonical next period for both constructor facts:
   * non-emptiness follows from `nextPeriod > 0` and `gapList` size, while
   * positivity follows from `assertNextPipelineGapsPositiveFromSpec`.
   */
  def nextPipelineGapCycleIfMatchesSpec(nextPeriod: BigInt): GapCycle = {
    require(nextPeriod > BigInt(0))
    require(spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus)
    require(nextPipelineGaps() == spec.next.gapList(BigInt(0), nextPeriod))

    val gaps = nextPipelineGaps()
    val specGaps = spec.next.gapList(BigInt(0), nextPeriod)

    assert(gaps == specGaps)
    assert(spec.next.assertGapListSize(BigInt(0), nextPeriod))
    assert(specGaps.size == nextPeriod)
    assert(specGaps.nonEmpty)
    assert(gaps.nonEmpty)
    assert(assertNextPipelineGapsPositiveFromSpec(nextPeriod))

    GapCycle(gaps)
  }.ensuring(result => result.memCycle.values == nextPipelineGaps())

//  /**
//   * Computes the next stage gap cycle independently from B's own cycle,
//   * then wraps A.next to match.
//   *
//   * The gap computation uses `nextRotatedGaps` (pure cycle math, no A.next data).
//   * Precondition discharge uses A (available to B) — this is separate from the
//   * gap computation itself.
//   */
//  def nextFromCycle(): CycleSieveSequence = {
//    assert(assertModulusPositive())
//    assert(assertPrimesTailValuesPositive())
//    assert(assertHeadPositive())
//    assert(assertModulusTimesHeadPositive())
//    assert(SieveSequenceNextLevel.assertNextGapsNonEmpty(cycle))
//
//    val newGaps = SieveSequenceNextLevel.nextRotatedGaps(cycle)
//    val newGapCycle = GapCycle(newGaps)
//
//    CycleSieveSequence(primes.next, newGapCycle)
//  }

  def nextVerified(nextPeriod: BigInt): SpecDerivedSieveSequence = {
    require(nextPeriod > BigInt(0))
    require(spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus)
    require(spec.next.primes.nextPrime.value < spec.next.head.value * spec.next.head.value)
    require(Calc.mod(SieveUtils.product(spec.next.filterValues), spec.next.head.value) != BigInt(0))
    SpecDerivedSieveSequence(spec.next, nextPeriod)
  }
}
