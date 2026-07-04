package v1.chapter6.seq.sieve

import stainless.collection.List
import stainless.lang.BooleanDecorations
import stainless.lang.decreases
import v1.chapter2.div.Calc
import v1.chapter2.div.properties.ModOperations
import v1.chapter3.list.{ListBoundUtils, ListUtils}
import v1.chapter3.list.properties.ListRepeatProperties
import v1.chapter4.cycle.gap.GapCycle
import v1.chapter4.cycle.integral.recursive.CycleIntegral
import v1.chapter4.cycle.integral.recursive.properties.{
  CycleIntegralFilterProperties,
  CycleIntegralProperties,
  GapProperties
}
import v1.chapter4.cycle.memory.MemCycle
import v1.chapter4.cycle.memory.properties.MemCycleProperties
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

  /** Proves `cycle.head == spec.head.value` — S1 alias. */
  def assertCycleHeadMatchesSpecHead(): Boolean = {
    assert(assertApplyMatches(BigInt(0)))
    cycle.head == spec.head.value
  }.holds

  /** S1 alias: `cycle.primesTailValues == spec.filterValues`. */
  def assertCyclePrimesTailEqualsSpecFilterValues(): Boolean = {
    cycle.primesTailValues == spec.filterValues
  }.holds

  /**
   * Proves `primorial(primeList) == SieveUtils.product(primeValues(primeList))`
   * for any prime list.
   *
   * Made public on 2026-07-05 so that the expansion-bridge lemmas in
   * `SpecDerivedBySurvivors` can derive the precondition
   * `modulus == product(primes)` required by `assertModPreservesCoprime`
   * (in `SpecCycleSieveEquivalence`). Previously this fact was only available
   * as an inline `assert(...)` inside private lemmas, which left no public
   * route to the product form of the modulus.
   */
  def primorialMatchesProduct(primeList: List[Prime]): Boolean = {
    decreases(primeList.size)
    if (primeList.isEmpty) {
      PrimeUtils.primorial(primeList) == SieveUtils.product(PrimeUtils.primeValues(primeList))
    } else {
      primorialMatchesProduct(primeList.tail)
      PrimeUtils.primorial(primeList) == SieveUtils.product(PrimeUtils.primeValues(primeList))
    }
  }.holds

  /** S1 alias: `cycle.modulus == spec.filterModulus`. */
  def assertCycleModulusEqualsSpecFilterModulus(): Boolean = {
    assert(primorialMatchesProduct(spec.primes.list.tail.list))
    cycle.modulus == spec.filterModulus
  }.holds

  /** S1 alias: `nextPipelineGaps() == nextRotatedGaps(cycle)` (definitional). */
  def assertNextPipelineGapsIsNextRotatedGaps(): Boolean = {
    assert(assertModulusPositive())
    assert(assertPrimesTailValuesPositive())
    assert(assertHeadPositive())
    assert(assertModulusTimesHeadPositive())
    nextPipelineGaps() == SieveSequenceNextLevel.nextRotatedGaps(cycle)
  }.holds

  /** S1 alias: `cycle.gapCycle == spec.specGapCycle(period)`. */
  def assertCycleGapCycleEqualsSpecGapCycle(): Boolean = {
    cycle.gapCycle == spec.specGapCycle(period)
  }.holds

  /**
   * Keep/drop predicate transfer (S2/S3 bridge).
   *
   * cycle(k) == spec(k) and cycle.head == spec.next.filterValues.head
   * ==> Calc.mod(cycle(k), cycle.head) != 0 ==
   *     Calc.mod(spec(k), spec.next.filterValues.head) != 0
   *
   * Same value, same divisor, same decision. Prevents downstream survivor
   * proofs from repeatedly reconstructing the equality through
   * assertApplyMatches, head aliases, and Calc.mod.
   */
  def assertCycleSpecNextFilterDecisionMatches(k: BigInt): Boolean = {
    require(k >= BigInt(0))
    assert(assertApplyMatches(k))
    assert(assertCycleHeadMatchesSpecHead())

    val nextSeq = spec.next
    assert(nextSeq.filterPrimes == spec.primes.list.list)
    assert(nextSeq.filterValues == PrimeUtils.primeValues(nextSeq.filterPrimes))
    assert(nextSeq.filterValues.head == spec.head.value)
    assert(cycle.head == spec.next.filterValues.head)

    (Calc.mod(cycle(k), cycle.head) != BigInt(0)) ==
      (Calc.mod(spec(k), spec.next.filterValues.head) != BigInt(0))
  }.holds

  /** S7 alias: `cycle(k) == integral(k-1)` for k > 0 (apply-vs-integral lowering). */
  def assertCycleApplyLowersToIntegral(k: BigInt): Boolean = {
    require(k > BigInt(0))
    cycle(k) == cycle.integral(k - BigInt(1))
  }.holds

  /** S4 alias: the cycle's gap list is non-empty. */
  def assertCycleGapListNonEmpty(): Boolean = {
    cycle.gapCycle.memCycle.values.nonEmpty
  }.holds

  /** The next prime list's head value equals cycle(1). */
  def assertNextPrimesHeadMatchesCycleApplyOne(): Boolean = {
    assert(assertPrimesMatch())
    assert(assertApplyMatches(BigInt(1)))
    assert(spec.assertApplyOneEqualsNextPrime())
    primes.next.head.value == cycle(BigInt(1))
  }.holds

  /** `cycle(k) <= spec.searchBound(k) = head + k * filterModulus`. */
  def assertCycleApplyUpperBound(k: BigInt): Boolean = {
    require(k >= BigInt(0))
    assert(assertApplyMatches(k))
    cycle(k) <= spec.searchBound(k)
  }.holds

  /** `cycle.apply(spec.indexOfAccepted(value)) == value` for valid values. */
  def assertCycleIndexOf(value: BigInt): Boolean = {
    require(value >= cycle.head)
    require(SieveUtils.isCoprime(value, cycle.primesTailValues))
    assert(assertCyclePrimesTailEqualsSpecFilterValues())
    val idx = spec.indexOfAccepted(value)
    assert(assertApplyMatches(idx))
    cycle.apply(idx) == value
  }.holds

  /** Copy of spec's expandedCoprimePreservesFilter: returns isCoprime directly. */
  private def expandedCoprime(r: BigInt, i: BigInt, modulus: BigInt, values: List[BigInt], prefixProd: BigInt): Boolean = {
    require(i >= BigInt(0))
    require(modulus > BigInt(0))
    require(prefixProd > BigInt(0))
    require(ListUtils.checkAllPositive(values))
    require(modulus == prefixProd * SieveUtils.product(values))
    require(SieveUtils.isCoprime(r, values))
    decreases(values.size)
    if (values.isEmpty) {
      SieveUtils.isCoprime(r + i * modulus, values)
    } else {
      val p = values.head
      val factor = prefixProd * SieveUtils.product(values.tail)
      assert(SieveUtils.assertProductNonNegative(values.tail))
      assert(SieveUtils.product(values.tail) >= BigInt(0))
      assert(factor >= BigInt(0))
      assert(SieveUtils.assertMultipleModZero(factor, p))
      assert(Calc.mod(modulus, p) == BigInt(0))
      assert(SieveUtils.assertIsCoprimeForAll(r, values))
      assert(Calc.mod(r, p) != BigInt(0))
      assert(SieveUtils.assertMultiplePreservesDivisible(i, modulus, p))
      assert(Calc.mod(i * modulus, p) == BigInt(0))
      assert(SieveUtils.assertAddPreservesNotZeroMod(r, p, i * modulus))
      assert(Calc.mod(r + i * modulus, p) != BigInt(0))
      assert(expandedCoprime(r, i, modulus, values.tail, prefixProd * p))
      assert(SieveUtils.isCoprime(r + i * modulus, values.tail))
      SieveUtils.isCoprime(r + i * modulus, values)
    }
  }.holds

  /** Upper bound: `cycle(1) + cycle.modulus` is never filtered out. */
  def assertNewHeadPlusModulusCoprime(): Boolean = {
    assert(assertModulusPositive())
    assert(assertPrimesTailValuesPositive())
    assert(assertCycleValueCoprimeToTail(BigInt(1)))
    assert(primorialMatchesProduct(spec.primes.list.tail.list))
    assert(SieveUtils.product(cycle.primesTailValues) == cycle.modulus)
    assert(expandedCoprime(
      cycle(BigInt(1)), BigInt(1), cycle.modulus, cycle.primesTailValues, BigInt(1)
    ))
    true
  }.holds

  /**
   * The first value in the next old period is not removed by the new front
   * filter.
   *
   * The front filter of `spec.next` is the current head prime. The constructor
   * assumption says the current filter modulus is not a multiple of that head.
   * Adding one full head preserves the same non-zero remainder.
   *
   * Math:
   *
   *   spec.next.filterValues.head = spec.head.value
   *   mod(spec.filterModulus, spec.head.value) != 0
   *   mod(spec.head.value, spec.head.value) = 0
   *   ------------------------------------------------------------
   *   mod(spec.head.value + spec.filterModulus,
   *       spec.next.filterValues.head) != 0
   */
  def assertHeadPlusFilterModulusNotFrontMultiple(): Boolean = {
    assert(assertHeadPositive())
    assert(primorialMatchesProduct(spec.primes.list.tail.list))
    assert(spec.filterModulus == SieveUtils.product(spec.filterValues))
    assert(Calc.mod(spec.filterModulus, spec.head.value) != BigInt(0))
    assert(SieveUtils.assertModZero(spec.head.value))
    assert(Calc.mod(spec.head.value, spec.head.value) == BigInt(0))
    assert(SieveUtils.assertAddPreservesNotZeroMod(
      spec.filterModulus,
      spec.head.value,
      spec.head.value))
    assert(Calc.mod(spec.filterModulus + spec.head.value, spec.head.value) != BigInt(0))
    assert(spec.filterModulus + spec.head.value == spec.head.value + spec.filterModulus)
    assert(Calc.mod(spec.head.value + spec.filterModulus, spec.head.value) != BigInt(0))
    assert(spec.next.filterPrimes == spec.primes.list.list)
    assert(spec.next.filterValues == PrimeUtils.primeValues(spec.next.filterPrimes))
    assert(spec.next.filterValues.head == spec.head.value)
    Calc.mod(
      spec.head.value + spec.filterModulus,
      spec.next.filterValues.head
    ) != BigInt(0)
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
   * Cycle-side survivor scan starts at the spec next head.
   *
   * The current cycle integral is indexed one step behind `cycle.apply`:
   * `integral(0) == cycle(1)`. The value `cycle(1)` is the next prime and is
   * not divisible by the old head, so no prefix is skipped and the survivor
   * scan splits immediately at position 0.
   *
   * Math:
   *
   *   integral(0) = cycle(1) = spec.next.head.value
   *   mod(integral(0), cycle.head) != 0
   *   ------------------------------------------------------------
   *   survivorValues(integral, cycle.head, 0, count)
   *     = spec.next.head.value :: survivorValues(integral, cycle.head, 1, count - 1)
   */
  def assertCycleSurvivorValuesStartAtSpecNextHead(count: BigInt): Boolean = {
    require(count > BigInt(0))

    assert(assertFirstSurvivorEqualsSpecNext0())
    assert(assertNewHeadCoprimeToAllPrimes())
    assert(cycle(BigInt(1)) == cycle.integral(BigInt(0)))
    assert(Calc.mod(cycle(BigInt(1)), cycle.head) != BigInt(0))
    assert(Calc.mod(cycle.integral(BigInt(0)), cycle.head) != BigInt(0))
    assert(GapProperties.assertSurvivorValuesSplitAtFirstPosition(
      cycle.integral, cycle.head, BigInt(0), count, BigInt(0)))

    CycleIntegralFilterProperties.survivorValues(
      cycle.integral, cycle.head, BigInt(0), count) ==
      spec.next.head.value :: CycleIntegralFilterProperties.survivorValues(
        cycle.integral, cycle.head, BigInt(1), count - BigInt(1))
  }.holds

//  def assertCycleSurvivorHeadMatchesSpecNext0(count: BigInt): Boolean = {
//    require(count > BigInt(0))
//
//    assert(assertCycleSurvivorValuesStartAtSpecNextHead(count))
//    assert(spec.next(BigInt(0)) == spec.next.head.value)
//
//    CycleIntegralFilterProperties.survivorValues(
//      cycle.integral, cycle.head, BigInt(0), count).head ==
//      spec.next(BigInt(0))
//  }.holds

  /**
   * Spec skipped-old-index facts as cycle-integral skipped-prefix facts.
   *
   * If `currentOldIndex` is aligned with `spec.next`, then
   * `spec.nextAcceptedOldIndex(spec.next, currentOldIndex, period)` is the next
   * old-stream index emitted by `spec.next`. Every old index strictly between
   * those two is a multiple of the new front filter. Since
   * `cycle.integral(pos) == cycle(pos + 1) == spec(pos + 1)`, the skipped old
   * indices `(currentOldIndex, nextOldIndex)` are exactly the integral
   * positions `[currentOldIndex, nextOldIndex - 1)`.
   *
   * Math:
   *
   *   currentOldIndex <= from <= until <= nextOldIndex - 1
   *   ------------------------------------------------------------
   *   allMultiplesInRange(cycle.integral, cycle.head, from, until)
   */
  def assertCycleIntegralSkippedRangeAllMultiples(
    currentOldIndex: BigInt,
    fromPos: BigInt,
    untilPos: BigInt
  ): Boolean = {
    require(currentOldIndex >= BigInt(0))
    require(fromPos >= currentOldIndex)
    require(untilPos >= fromPos)
    require(spec(currentOldIndex) >= spec.next.head.value)
    require(spec.next.filterValues.nonEmpty)
    require(spec.next.filterValues.tail == spec.filterValues)
    require(spec.next.head.value == spec.head.value)
    require(Calc.mod(
      spec.head.value + spec.filterModulus,
      spec.next.filterValues.head
    ) != BigInt(0))
    require(spec.next.accepts(spec(currentOldIndex)))
    require(untilPos <=
      spec.nextAcceptedOldIndex(spec.next, currentOldIndex, period) - BigInt(1))
    decreases(untilPos - fromPos)

    val nextSeq = spec.next
    val nextOldIndex = spec.nextAcceptedOldIndex(nextSeq, currentOldIndex, period)

    assert(nextSeq.filterPrimes == spec.primes.list.list)
    assert(nextSeq.filterValues == PrimeUtils.primeValues(nextSeq.filterPrimes))
    assert(nextSeq.filterValues.head == spec.head.value)
    assert(nextSeq.filterValues.tail == spec.filterValues)
    assert(nextSeq.head.value == spec.head.value)
    assert(assertCycleHeadMatchesSpecHead())
    assert(cycle.head == nextSeq.filterValues.head)

    if (fromPos == untilPos) {
      GapProperties.allMultiplesInRange(
        cycle.integral, cycle.head, fromPos, untilPos)
    } else {
      val skippedOldIndex = fromPos + BigInt(1)

      assert(skippedOldIndex > currentOldIndex)
      assert(skippedOldIndex < nextOldIndex)
      assert(spec.assertSkippedBeforeNextAcceptedOldIndexIsMultiple(
        nextSeq, currentOldIndex, skippedOldIndex, period))
      assert(Calc.mod(spec(skippedOldIndex), nextSeq.filterValues.head) == BigInt(0))
      assert(assertApplyMatches(skippedOldIndex))
      assert(cycle(skippedOldIndex) == spec(skippedOldIndex))
      assert(assertCycleApplyLowersToIntegral(skippedOldIndex))
      assert(cycle(skippedOldIndex) == cycle.integral(fromPos))
      assert(Calc.mod(cycle.integral(fromPos), cycle.head) == BigInt(0))
      assert(assertCycleIntegralSkippedRangeAllMultiples(
        currentOldIndex, fromPos + BigInt(1), untilPos))
      GapProperties.allMultiplesInRange(
        cycle.integral, cycle.head, fromPos, untilPos)
    }
  }.holds

  /**
   * Splits the cycle survivor scan at the next spec-accepted old index.
   *
   * `nextAcceptedOldIndex` gives the next old-stream value emitted by
   * `spec.next`. The previous lemma translates all skipped old indices into an
   * all-multiple cycle-integral prefix, so the chapter-4 ordered split can peel
   * exactly that next survivor from the cycle scan.
   *
   * Math:
   *
   *   j = nextAcceptedOldIndex(spec.next, currentOldIndex, period)
   *   pos = j - 1
   *   allMultiplesInRange(cycle.integral, cycle.head, currentOldIndex, pos)
   *   mod(cycle.integral(pos), cycle.head) != 0
   *   ------------------------------------------------------------
   *   survivorValues(cycle.integral, cycle.head, currentOldIndex, count)
   *     = cycle.integral(pos) ::
   *       survivorValues(cycle.integral, cycle.head, j,
   *         currentOldIndex + count - j)
   */
  def assertCycleSurvivorValuesSplitAtNextAccepted(
    currentOldIndex: BigInt,
    count: BigInt
  ): Boolean = {
    require(currentOldIndex >= BigInt(0))
    require(count > BigInt(0))
    require(spec(currentOldIndex) >= spec.next.head.value)
    require(spec.next.filterValues.nonEmpty)
    require(spec.next.filterValues.tail == spec.filterValues)
    require(spec.next.head.value == spec.head.value)
    require(Calc.mod(
      spec.head.value + spec.filterModulus,
      spec.next.filterValues.head
    ) != BigInt(0))
    require(spec.next.accepts(spec(currentOldIndex)))
    require(
      spec.nextAcceptedOldIndex(spec.next, currentOldIndex, period) - BigInt(1) <
        currentOldIndex + count)

    val nextSeq = spec.next
    val nextOldIndex = spec.nextAcceptedOldIndex(nextSeq, currentOldIndex, period)
    val survivorPos = nextOldIndex - BigInt(1)
    val remaining = currentOldIndex + count - nextOldIndex

    assert(nextOldIndex > currentOldIndex)
    assert(survivorPos >= currentOldIndex)
    assert(survivorPos < currentOldIndex + count)
    assert(assertCycleIntegralSkippedRangeAllMultiples(
      currentOldIndex, currentOldIndex, survivorPos))
    assert(GapProperties.allMultiplesInRange(
      cycle.integral, cycle.head, currentOldIndex, survivorPos))
    assert(assertApplyMatches(nextOldIndex))
    assert(cycle(nextOldIndex) == spec(nextOldIndex))
    assert(assertCycleApplyLowersToIntegral(nextOldIndex))
    assert(cycle(nextOldIndex) == cycle.integral(survivorPos))
    assert(Calc.mod(spec(nextOldIndex), nextSeq.filterValues.head) != BigInt(0))
    assert(Calc.mod(cycle.integral(survivorPos), cycle.head) != BigInt(0))
    assert(GapProperties.assertSurvivorValuesSplitAtFirstPosition(
      cycle.integral, cycle.head, currentOldIndex, count, survivorPos))

    CycleIntegralFilterProperties.survivorValues(
      cycle.integral, cycle.head, currentOldIndex, count) ==
      cycle.integral(survivorPos) ::
        CycleIntegralFilterProperties.survivorValues(
          cycle.integral, cycle.head, nextOldIndex, remaining)
  }.holds

  /**
   * The survivor peeled by `nextAcceptedOldIndex` is the next spec value.
   *
   * This is the value-level companion to the survivor split above. It connects
   * the cycle-integral position `nextOldIndex - 1` back to the already verified
   * spec search postcondition:
   *
   * Math:
   *
   *   j = nextAcceptedOldIndex(spec.next, currentOldIndex, period)
   *   s = spec.next.indexOfAccepted(spec(currentOldIndex))
   *   cycle.integral(j - 1) = cycle(j) = spec(j)
   *   spec.next(s + 1) = spec(j)
   *   ------------------------------------------------------------
   *   cycle.integral(j - 1) = spec.next(s + 1)
   */
  def assertCycleNextAcceptedSurvivorMatchesSpecNext(
    currentOldIndex: BigInt
  ): Boolean = {
    require(currentOldIndex >= BigInt(0))
    require(spec(currentOldIndex) >= spec.next.head.value)
    require(spec.next.filterValues.nonEmpty)
    require(spec.next.filterValues.tail == spec.filterValues)
    require(spec.next.head.value == spec.head.value)
    require(Calc.mod(
      spec.head.value + spec.filterModulus,
      spec.next.filterValues.head
    ) != BigInt(0))
    require(spec.next.accepts(spec(currentOldIndex)))

    val nextSeq = spec.next
    val nextOldIndex = spec.nextAcceptedOldIndex(nextSeq, currentOldIndex, period)
    val nextSeqIndex = nextSeq.indexOfAccepted(spec(currentOldIndex))
    val survivorPos = nextOldIndex - BigInt(1)

    assert(nextOldIndex > currentOldIndex)
    assert(assertApplyMatches(nextOldIndex))
    assert(cycle(nextOldIndex) == spec(nextOldIndex))
    assert(assertCycleApplyLowersToIntegral(nextOldIndex))
    assert(cycle.integral(survivorPos) == cycle(nextOldIndex))
    assert(nextSeq(nextSeqIndex + BigInt(1)) == spec(nextOldIndex))

    cycle.integral(survivorPos) == nextSeq(nextSeqIndex + BigInt(1))
  }.holds

//  def assertCycleSurvivorTailHeadMatchesSpecNext(
//    currentOldIndex: BigInt,
//    count: BigInt
//  ): Boolean = {
//    require(currentOldIndex >= BigInt(0))
//    require(count > BigInt(0))
//    require(spec(currentOldIndex) >= spec.next.head.value)
//    require(spec.next.filterValues.nonEmpty)
//    require(spec.next.filterValues.tail == spec.filterValues)
//    require(spec.next.filterValues.head == spec.head.value)
//    require(Calc.mod(
//      spec.head.value + spec.filterModulus,
//      spec.next.filterValues.head
//    ) != BigInt(0))
//    require(spec.next.accepts(spec(currentOldIndex)))
//    require(
//      spec.nextAcceptedOldIndex(spec.next, currentOldIndex, period) - BigInt(1) <
//        currentOldIndex + count)
//
//    val nextSeq = spec.next
//    val nextSeqIndex = nextSeq.indexOfAccepted(spec(currentOldIndex))
//
//    assert(assertCycleSurvivorValuesSplitAtNextAccepted(currentOldIndex, count))
//    assert(assertCycleNextAcceptedSurvivorMatchesSpecNext(currentOldIndex))
//
//    CycleIntegralFilterProperties.survivorValues(
//      cycle.integral, cycle.head, currentOldIndex, count).head ==
//      nextSeq(nextSeqIndex + BigInt(1))
//  }.holds

  /**
   * Head equality for an explicitly indexed aligned survivor window.
   *
   * This is the caller-friendly form of
   * `assertCycleSurvivorTailHeadMatchesSpecNext`. The tail-head lemma names the
   * previous next-stage position as
   * `spec.next.indexOfAccepted(spec(currentOldIndex))`; this wrapper lets the
   * recursive ordered-survivor proof carry that position as the explicit
   * `specIndex` parameter instead. The only extra work is an injectivity bridge
   * showing that the carried `specIndex` is the same index returned by
   * `indexOfAccepted`.
   *
   * Math:
   *
   *   spec(currentOldIndex) = spec.next(specIndex)
   *   s = spec.next.indexOfAccepted(spec(currentOldIndex))
   *   spec.next(s) = spec(currentOldIndex)
   *   spec.next(specIndex) = spec(currentOldIndex)
   *   ------------------------------------------------------------
   *   survivorValues(cycle.integral, cycle.head, currentOldIndex, count).head
   *     = spec.next(specIndex + 1)
   */
//  def assertCycleSurvivorWindowHeadMatchesSpecNext(
//    specIndex: BigInt,
//    currentOldIndex: BigInt,
//    count: BigInt
//  ): Boolean = {
//    require(specIndex >= BigInt(0))
//    require(currentOldIndex >= BigInt(0))
//    require(count > BigInt(0))
//    require(spec(currentOldIndex) == spec.next(specIndex))
//    require(spec(currentOldIndex) >= spec.next.head.value)
//    require(spec.next.filterValues.nonEmpty)
//    require(spec.next.filterValues.tail == spec.filterValues)
//    require(spec.next.filterValues.head == spec.head.value)
//    require(Calc.mod(
//      spec.head.value + spec.filterModulus,
//      spec.next.filterValues.head
//    ) != BigInt(0))
//    require(spec.next.accepts(spec(currentOldIndex)))
//    require(
//      spec.nextAcceptedOldIndex(spec.next, currentOldIndex, period) - BigInt(1) <
//        currentOldIndex + count)
//
//    val nextSeq = spec.next
//    val computedIndex = nextSeq.indexOfAccepted(spec(currentOldIndex))
//
//    assert(nextSeq(specIndex) == spec(currentOldIndex))
//    assert(nextSeq(computedIndex) == spec(currentOldIndex))
//    assert(nextSeq.assertApplyInjective(specIndex, computedIndex))
//    assert(specIndex == computedIndex)
//    assert(assertCycleSurvivorTailHeadMatchesSpecNext(currentOldIndex, count))
//
//    CycleIntegralFilterProperties.survivorValues(
//      cycle.integral, cycle.head, currentOldIndex, count).head ==
//      nextSeq(specIndex + BigInt(1))
//  }.holds

  /**
   * Raw-window coverage for ordered survivor recursion.
   *
   * The recursive survivor equality consumes retained values, but `count`
   * measures raw old integral positions. This predicate records the exact
   * bridge between those coordinate systems: every next accepted old index
   * needed for `offset` recursive survivor steps remains inside the current
   * raw scan window.
   *
   * Math:
   *
   *   covers(s, k, c, 0)
   *     := nextAcceptedOldIndex(spec.next, k, period) - 1 < k + c
   *
   *   covers(s, k, c, n + 1)
   *     := j = nextAcceptedOldIndex(spec.next, k, period)
   *        j < k + c
   *        covers(s + 1, j, k + c - j, n)
   */
//  def survivorWindowCovers(
//    specIndex: BigInt,
//    currentOldIndex: BigInt,
//    count: BigInt,
//    offset: BigInt
//  ): Boolean = {
//    require(specIndex >= BigInt(0))
//    require(currentOldIndex >= BigInt(0))
//    require(count > BigInt(0))
//    require(offset >= BigInt(0))
//    require(spec(currentOldIndex) == spec.next(specIndex))
//    require(spec(currentOldIndex) >= spec.next.head.value)
//    require(spec.next.filterValues.nonEmpty)
//    require(spec.next.filterValues.tail == spec.filterValues)
//    require(spec.next.filterValues.head == spec.head.value)
//    require(Calc.mod(
//      spec.head.value + spec.filterModulus,
//      spec.next.filterValues.head
//    ) != BigInt(0))
//    require(spec.next.accepts(spec(currentOldIndex)))
//    decreases(offset)
//
//    val nextSeq = spec.next
//    val nextOldIndex = spec.nextAcceptedOldIndex(nextSeq, currentOldIndex, period)
//
//    if (offset == BigInt(0)) {
//      nextOldIndex - BigInt(1) < currentOldIndex + count
//    } else {
//      val computedIndex = nextSeq.indexOfAccepted(spec(currentOldIndex))
//      val remaining = currentOldIndex + count - nextOldIndex
//
//      assert(nextSeq(specIndex) == spec(currentOldIndex))
//      assert(nextSeq(computedIndex) == spec(currentOldIndex))
//      assert(nextSeq.assertApplyInjective(specIndex, computedIndex))
//      assert(specIndex == computedIndex)
//      assert(nextSeq(computedIndex + BigInt(1)) == spec(nextOldIndex))
//      assert(spec(nextOldIndex) == nextSeq(specIndex + BigInt(1)))
//      assert(nextSeq.accepts(spec(nextOldIndex)))
//
//      nextOldIndex < currentOldIndex + count &&
//        survivorWindowCovers(
//          specIndex + BigInt(1),
//          nextOldIndex,
//          remaining,
//          offset - BigInt(1))
//    }
//  }

  /**
   * Indexed ordered survivor equality for an aligned non-initial window.
   *
   * This is the recursive form used after the initial survivor has been peeled:
   * `currentOldIndex` is the old-stream index for `spec.next(specIndex)`, and
   * the `offset`-th retained value in the remaining cycle survivor scan is the
   * following next-stage value `spec.next(specIndex + offset + 1)`.
   *
   * Math:
   *
   *   spec(currentOldIndex) = spec.next(specIndex)
   *   covers(specIndex, currentOldIndex, count, offset)
   *   ------------------------------------------------------------
   *   survivorValues(cycle.integral, cycle.head, currentOldIndex, count)(offset)
   *     = spec.next(specIndex + offset + 1)
   */
//  def assertCycleSurvivorWindowAtMatchesSpecNext(
//    specIndex: BigInt,
//    offset: BigInt,
//    currentOldIndex: BigInt,
//    count: BigInt
//  ): Boolean = {
//    require(specIndex >= BigInt(0))
//    require(offset >= BigInt(0))
//    require(currentOldIndex >= BigInt(0))
//    require(count > BigInt(0))
//    require(spec(currentOldIndex) == spec.next(specIndex))
//    require(spec(currentOldIndex) >= spec.next.head.value)
//    require(spec.next.filterValues.nonEmpty)
//    require(spec.next.filterValues.tail == spec.filterValues)
//    require(spec.next.filterValues.head == spec.head.value)
//    require(Calc.mod(
//      spec.head.value + spec.filterModulus,
//      spec.next.filterValues.head
//    ) != BigInt(0))
//    require(spec.next.accepts(spec(currentOldIndex)))
//    require(survivorWindowCovers(specIndex, currentOldIndex, count, offset))
//    require(CycleIntegralFilterProperties.survivorValues(
//      cycle.integral, cycle.head, currentOldIndex, count).size > offset)
//    decreases(offset)
//
//    val nextSeq = spec.next
//    val survivors = CycleIntegralFilterProperties.survivorValues(
//      cycle.integral, cycle.head, currentOldIndex, count)
//
//    if (offset == BigInt(0)) {
//      assert(assertCycleSurvivorWindowHeadMatchesSpecNext(
//        specIndex, currentOldIndex, count))
//      survivors(offset) == nextSeq(specIndex + BigInt(1))
//    } else {
//      val nextOldIndex = spec.nextAcceptedOldIndex(nextSeq, currentOldIndex, period)
//      val remaining = currentOldIndex + count - nextOldIndex
//      val tailSurvivors = CycleIntegralFilterProperties.survivorValues(
//        cycle.integral, cycle.head, nextOldIndex, remaining)
//      val computedIndex = nextSeq.indexOfAccepted(spec(currentOldIndex))
//
//      assert(nextSeq(specIndex) == spec(currentOldIndex))
//      assert(nextSeq(computedIndex) == spec(currentOldIndex))
//      assert(nextSeq.assertApplyInjective(specIndex, computedIndex))
//      assert(specIndex == computedIndex)
//      assert(nextSeq(computedIndex + BigInt(1)) == spec(nextOldIndex))
//      assert(spec(nextOldIndex) == nextSeq(specIndex + BigInt(1)))
//      assert(nextSeq.accepts(spec(nextOldIndex)))
//      assert(survivorWindowCovers(
//        specIndex + BigInt(1),
//        nextOldIndex,
//        remaining,
//        offset - BigInt(1)))
//      assert(assertCycleSurvivorValuesSplitAtNextAccepted(currentOldIndex, count))
//      assert(survivors == cycle.integral(nextOldIndex - BigInt(1)) :: tailSurvivors)
//      assert(survivors.tail == tailSurvivors)
//      assert(tailSurvivors.size > offset - BigInt(1))
//      assert(assertCycleSurvivorWindowAtMatchesSpecNext(
//        specIndex + BigInt(1),
//        offset - BigInt(1),
//        nextOldIndex,
//        remaining))
//
//      survivors(offset) == nextSeq(specIndex + offset + BigInt(1))
//    }
//  }.holds

  /**
   * Raw-window coverage for the initial survivor scan.
   *
   * The first retained value is `spec.next(0)`, and the remaining scan starts
   * at old integral position 1. For non-zero offsets, the tail coverage is
   * exactly `survivorWindowCovers(0, 1, count - 1, offset - 1)`.
   */
//  def initialSurvivorWindowCovers(
//    count: BigInt,
//    offset: BigInt
//  ): Boolean = {
//    require(count > BigInt(0))
//    require(offset >= BigInt(0))
//
//    if (offset == BigInt(0)) {
//      true
//    } else if (count <= BigInt(1)) {
//      false
//    } else {
//      assert(assertFirstSurvivorEqualsSpecNext0())
//      assert(spec(BigInt(1)) == spec.next(BigInt(0)))
//      assert(spec(BigInt(1)) >= spec.next.head.value)
//      assert(spec.next.accepts(spec(BigInt(1))))
//      survivorWindowCovers(
//        BigInt(0),
//        BigInt(1),
//        count - BigInt(1),
//        offset - BigInt(1))
//    }
//  }

  /**
   * Indexed ordered survivor equality for the initial cycle scan.
   *
   * This packages the initial head case and the aligned tail-window recursion
   * into the direct statement needed by gap equality: the `offset`-th value
   * retained from the current cycle integral is exactly `spec.next(offset)`.
   *
   * Math:
   *
   *   initialSurvivorWindowCovers(count, offset)
   *   ------------------------------------------------------------
   *   survivorValues(cycle.integral, cycle.head, 0, count)(offset)
   *     = spec.next(offset)
   */
//  def assertCycleSurvivorAtMatchesSpecNext(
//    offset: BigInt,
//    count: BigInt
//  ): Boolean = {
//    require(offset >= BigInt(0))
//    require(count > BigInt(0))
//    require(initialSurvivorWindowCovers(count, offset))
//    require(CycleIntegralFilterProperties.survivorValues(
//      cycle.integral, cycle.head, BigInt(0), count).size > offset)
//    decreases(offset)
//
//    val survivors = CycleIntegralFilterProperties.survivorValues(
//      cycle.integral, cycle.head, BigInt(0), count)
//
//    if (offset == BigInt(0)) {
//      assert(assertCycleSurvivorHeadMatchesSpecNext0(count))
//      survivors(offset) == spec.next(offset)
//    } else {
//      val tailSurvivors = CycleIntegralFilterProperties.survivorValues(
//        cycle.integral, cycle.head, BigInt(1), count - BigInt(1))
//
//      assert(assertCycleSurvivorValuesStartAtSpecNextHead(count))
//      assert(survivors == spec.next.head.value :: tailSurvivors)
//      assert(survivors.tail == tailSurvivors)
//      assert(tailSurvivors.size > offset - BigInt(1))
//      assert(assertFirstSurvivorEqualsSpecNext0())
//      assert(spec.assertApplyOneEqualsNextPrime())
//      assert(spec(BigInt(1)) == spec.primes.nextPrime.value)
//      assert(spec.next.head.value == spec.primes.nextPrime.value)
//      assert(spec.next(BigInt(0)) == spec.next.head.value)
//      assert(spec(BigInt(1)) == spec.next(BigInt(0)))
//      assert(spec(BigInt(1)) >= spec.next.head.value)
//      assert(spec.next.filterPrimes == spec.primes.list.list)
//      assert(spec.next.filterValues == PrimeUtils.primeValues(spec.next.filterPrimes))
//      assert(spec.next.filterValues.head == spec.head.value)
//      assert(spec.next.filterValues.tail == spec.filterValues)
//      assert(spec.next.filterValues.head == spec.head.value)
//      assert(spec.next.accepts(spec(BigInt(1))))
//      assert(assertHeadPlusFilterModulusNotFrontMultiple())
//      assert(survivorWindowCovers(
//        BigInt(0),
//        BigInt(1),
//        count - BigInt(1),
//        offset - BigInt(1)))
//      assert(assertCycleSurvivorWindowAtMatchesSpecNext(
//        BigInt(0),
//        offset - BigInt(1),
//        BigInt(1),
//        count - BigInt(1)))
//
//      survivors(offset) == spec.next(offset)
//    }
//  }.holds

  /**
   * Adjacent survivor gaps match adjacent `spec.next` gaps.
   *
   * The ordered survivor bridge proves equality pointwise:
   * `survivors(k) = spec.next(k)` and
   * `survivors(k + 1) = spec.next(k + 1)`. Taking the adjacent difference on
   * both sides gives the gap equality needed before moving to list-level
   * `gapsFromValues` proofs.
   *
   * Math:
   *
   *   S(k) = spec.next(k)
   *   S(k + 1) = spec.next(k + 1)
   *   ------------------------------------------------------------
   *   S(k + 1) - S(k) = spec.next(k + 1) - spec.next(k)
   */
//  def assertInitialSurvivorGapMatchesSpecNextGap(
//    k: BigInt,
//    count: BigInt
//  ): Boolean = {
//    require(k >= BigInt(0))
//    require(count > BigInt(0))
//    require(initialSurvivorWindowCovers(count, k))
//    require(initialSurvivorWindowCovers(count, k + BigInt(1)))
//    require(CycleIntegralFilterProperties.survivorValues(
//      cycle.integral, cycle.head, BigInt(0), count).size > k + BigInt(1))
//
//    val survivors = CycleIntegralFilterProperties.survivorValues(
//      cycle.integral, cycle.head, BigInt(0), count)
//
//    assert(assertCycleSurvivorAtMatchesSpecNext(k, count))
//    assert(assertCycleSurvivorAtMatchesSpecNext(k + BigInt(1), count))
//    assert(survivors(k) == spec.next(k))
//    assert(survivors(k + BigInt(1)) == spec.next(k + BigInt(1)))
//
//    survivors(k + BigInt(1)) - survivors(k) ==
//      spec.next(k + BigInt(1)) - spec.next(k)
//  }.holds

  /**
   * The gap list computed from ordered survivors matches the adjacent
   * `spec.next` gap at index `k`.
   *
   * This is the list-facing form of
   * `assertInitialSurvivorGapMatchesSpecNextGap`: chapter 4 proves that
   * `gapsFromValues(S)(k)` is the adjacent difference `S(k + 1) - S(k)`,
   * while the local survivor bridge proves those two survivor values are
   * `spec.next(k)` and `spec.next(k + 1)`.
   *
   * Math:
   *
   *   gapsFromValues(S)(k) = S(k + 1) - S(k)
   *   S(k + 1) - S(k) = spec.next(k + 1) - spec.next(k)
   *   ------------------------------------------------------------
   *   gapsFromValues(S)(k) = spec.next(k + 1) - spec.next(k)
   */
//  def assertInitialSurvivorGapsFromValuesAtMatchesSpecNextGap(
//    k: BigInt,
//    count: BigInt
//  ): Boolean = {
//    require(k >= BigInt(0))
//    require(count > BigInt(0))
//    require(initialSurvivorWindowCovers(count, k))
//    require(initialSurvivorWindowCovers(count, k + BigInt(1)))
//    require(CycleIntegralFilterProperties.survivorValues(
//      cycle.integral, cycle.head, BigInt(0), count).size > k + BigInt(1))
//
//    val survivors = CycleIntegralFilterProperties.survivorValues(
//      cycle.integral, cycle.head, BigInt(0), count)
//
//    assert(!survivors.isEmpty)
//    assert(CycleIntegralFilterProperties.assertGapsFromValuesAtIndex(survivors, k))
//    assert(assertInitialSurvivorGapMatchesSpecNextGap(k, count))
//
//    CycleIntegralFilterProperties.gapsFromValues(survivors)(k) ==
//      spec.next(k + BigInt(1)) - spec.next(k)
//  }.holds

  /**
   * The survivor-derived gap list matches `spec.next.gapList` at index `k`.
   *
   * This adds only the final spec-list projection to
   * `assertInitialSurvivorGapsFromValuesAtMatchesSpecNextGap`. The spec
   * sequence already proves that `gapList(0, nextPeriod)(k)` is the adjacent
   * next-stage difference.
   *
   * Math:
   *
   *   gapsFromValues(S)(k) = spec.next(k + 1) - spec.next(k)
   *   spec.next.gapList(0, P)(k) = spec.next(k + 1) - spec.next(k)
   *   ------------------------------------------------------------
   *   gapsFromValues(S)(k) = spec.next.gapList(0, P)(k)
   */
//  def assertInitialSurvivorGapListAtMatchesSpecNextGapList(
//    k: BigInt,
//    count: BigInt,
//    nextPeriod: BigInt
//  ): Boolean = {
//    require(k >= BigInt(0))
//    require(count > BigInt(0))
//    require(nextPeriod > BigInt(0))
//    require(k < nextPeriod)
//    require(initialSurvivorWindowCovers(count, k))
//    require(initialSurvivorWindowCovers(count, k + BigInt(1)))
//    require(CycleIntegralFilterProperties.survivorValues(
//      cycle.integral, cycle.head, BigInt(0), count).size > k + BigInt(1))
//
//    val survivors = CycleIntegralFilterProperties.survivorValues(
//      cycle.integral, cycle.head, BigInt(0), count)
//
//    assert(assertInitialSurvivorGapsFromValuesAtMatchesSpecNextGap(k, count))
//    assert(spec.next.assertGapListApplyEqualsGapAtPosition(BigInt(0), nextPeriod, k))
//
//    CycleIntegralFilterProperties.gapsFromValues(survivors)(k) ==
//      spec.next.gapList(BigInt(0), nextPeriod)(k)
//  }.holds

  /**
   * Coverage predicate for a consecutive survivor-gap prefix.
   *
   * A gap at position `from` needs two survivor values: `from` and `from + 1`.
   * Recursing over `gapCount` records exactly that adjacent-pair coverage for
   * every gap in the prefix.
   */
//  def initialSurvivorGapListCovers(
//    scanCount: BigInt,
//    from: BigInt,
//    gapCount: BigInt
//  ): Boolean = {
//    require(scanCount > BigInt(0))
//    require(from >= BigInt(0))
//    require(gapCount >= BigInt(0))
//    decreases(gapCount)
//
//    if (gapCount == BigInt(0)) {
//      true
//    } else {
//      initialSurvivorWindowCovers(scanCount, from) &&
//        initialSurvivorWindowCovers(scanCount, from + BigInt(1)) &&
//        initialSurvivorGapListCovers(scanCount, from + BigInt(1), gapCount - BigInt(1))
//    }
//  }

  /**
   * Forward gap prefix built from the initial ordered survivor values.
   *
   * This is intentionally shaped like `nextGapList`: each step emits the
   * adjacent survivor difference at `from`, then recurses at `from + 1`.
   */
//  def initialSurvivorGapList(
//    from: BigInt,
//    gapCount: BigInt,
//    scanCount: BigInt
//  ): List[BigInt] = {
//    require(scanCount > BigInt(0))
//    require(from >= BigInt(0))
//    require(gapCount >= BigInt(0))
//    require(initialSurvivorGapListCovers(scanCount, from, gapCount))
//    require(CycleIntegralFilterProperties.survivorValues(
//      cycle.integral, cycle.head, BigInt(0), scanCount).size > from + gapCount)
//    decreases(gapCount)
//
//    if (gapCount == BigInt(0)) {
//      List.empty[BigInt]
//    } else {
//      val survivors = CycleIntegralFilterProperties.survivorValues(
//        cycle.integral, cycle.head, BigInt(0), scanCount)
//
//      (survivors(from + BigInt(1)) - survivors(from)) ::
//        initialSurvivorGapList(from + BigInt(1), gapCount - BigInt(1), scanCount)
//    }
//  }

  /**
   * The forward survivor-gap prefix equals the canonical adjacent next-gap
   * prefix.
   *
   * Both lists recurse in the same direction. The head equality is exactly
   * `assertInitialSurvivorGapMatchesSpecNextGap`; the tail equality is the
   * induction hypothesis over `from + 1`.
   *
   * Math:
   *
   *   survivorGap(from) = spec.next(from + 1) - spec.next(from)
   *   initialSurvivorGapList(from + 1, n - 1, scan)
   *     = nextGapList(from + 1, n - 1)
   *   ------------------------------------------------------------
   *   initialSurvivorGapList(from, n, scan) = nextGapList(from, n)
   */
//  def assertInitialSurvivorGapListMatchesNextGapList(
//    from: BigInt,
//    gapCount: BigInt,
//    scanCount: BigInt
//  ): Boolean = {
//    require(scanCount > BigInt(0))
//    require(from >= BigInt(0))
//    require(gapCount >= BigInt(0))
//    require(initialSurvivorGapListCovers(scanCount, from, gapCount))
//    require(CycleIntegralFilterProperties.survivorValues(
//      cycle.integral, cycle.head, BigInt(0), scanCount).size > from + gapCount)
//    decreases(gapCount)
//
//    if (gapCount == BigInt(0)) {
//      initialSurvivorGapList(from, BigInt(0), scanCount) ==
//        nextGapList(from, BigInt(0))
//    } else {
//      assert(initialSurvivorWindowCovers(scanCount, from))
//      assert(initialSurvivorWindowCovers(scanCount, from + BigInt(1)))
//      assert(initialSurvivorGapListCovers(
//        scanCount, from + BigInt(1), gapCount - BigInt(1)))
//      assert(assertInitialSurvivorGapMatchesSpecNextGap(from, scanCount))
//      assert(assertInitialSurvivorGapListMatchesNextGapList(
//        from + BigInt(1), gapCount - BigInt(1), scanCount))
//
//      initialSurvivorGapList(from, gapCount, scanCount) ==
//        nextGapList(from, gapCount)
//    }
//  }.holds

  /**
   * The forward survivor-gap prefix equals `spec.next.gapList`.
   *
   * This composes the survivor-prefix equality with the canonical
   * `nextGapList == spec.next.gapList` bridge. It gives the next pipeline proof
   * a list-level target without reopening either recursion.
   */
//  def assertInitialSurvivorGapListMatchesSpecNextGapList(
//    from: BigInt,
//    gapCount: BigInt,
//    scanCount: BigInt
//  ): Boolean = {
//    require(scanCount > BigInt(0))
//    require(from >= BigInt(0))
//    require(gapCount >= BigInt(0))
//    require(initialSurvivorGapListCovers(scanCount, from, gapCount))
//    require(CycleIntegralFilterProperties.survivorValues(
//      cycle.integral, cycle.head, BigInt(0), scanCount).size > from + gapCount)
//
//    assert(assertInitialSurvivorGapListMatchesNextGapList(from, gapCount, scanCount))
//    assert(assertNextGapListMatchesSpecNext(from, gapCount))
//
//    initialSurvivorGapList(from, gapCount, scanCount) ==
//      spec.next.gapList(from, gapCount)
//  }.holds

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

  /**
   * Builds the same B cycle with its gap period repeated `times` times.
   *
   * Math:
   *
   *   B      = cycle
   *   G      = B.gapCycle.memCycle.values
   *   times  > 0
   *   G^times = repeat(G, times)
   *
   *   repeatedCycle(times) = CycleSieveSequence(primes, GapCycle(G^times))
   *
   * Repeating the stored gap list does not change the semantic cycle: it only
   * changes the physical period length. This constructor is isolated so later
   * lemmas can compare the original and repeated cycles without reopening
   * `GapCycle` positivity/non-emptiness obligations.
   */
  def repeatedCycle(times: BigInt): CycleSieveSequence = {
    require(times > BigInt(0))

    val gaps = cycle.gapCycle.memCycle.values
    val repeatedGaps = ListRepeatProperties.repeat(gaps, times)

    assert(GapCycle.assertMemCycleValuesPositive(cycle.gapCycle))
    assert(ListRepeatProperties.assertRepeatAllGreaterThan(gaps, times, BigInt(0)))
    assert(ListRepeatProperties.assertRepeatSize(gaps, times))
    assert(repeatedGaps.size == gaps.size * times)
    assert(gaps.nonEmpty)
    assert(repeatedGaps.nonEmpty)
    assert(ListBoundUtils.allGreaterThan(repeatedGaps, BigInt(0)))

    CycleSieveSequence(primes, GapCycle(repeatedGaps))
  }

  /**
   * Bounded-index equality for B's repeated gap period.
   *
   * Math:
   *
   *   G = cycle.gapCycle.memCycle.values
   *   R = repeat(G, times)
   *
   *   times > 0
   *   0 <= index < size(G) * times
   *
   *   R(index) = G(mod(index, size(G)))
   *
   * If we physically repeat B's stored gap list `times` times, any index inside
   * that repeated list reads the same gap as the original list at the modulo
   * position. This is the list-level seed for proving the repeated cycle has
   * the same `apply` behavior as B.
   */
  def assertRepeatedGapListIndexMatches(times: BigInt, index: BigInt): Boolean = {
    require(times > BigInt(0))
    require(index >= BigInt(0))

    val gaps = cycle.gapCycle.memCycle.values
    require(index < gaps.size * times)

    val repeatedGaps = ListRepeatProperties.repeat(gaps, times)

    assert(GapCycle.assertMemCycleValuesPositive(cycle.gapCycle))
    assert(ListRepeatProperties.assertRepeatSize(gaps, times))
    assert(ListRepeatProperties.assertRepeatedIndex(gaps, times, index))

    repeatedGaps(index) == gaps(Calc.mod(index, gaps.size))
  }.holds

  /**
   * Repeating B's physical gap storage does not change B's gap cycle lookup.
   *
   * Math:
   *
   *   B      = cycle
   *   B_t    = repeatedCycle(times)
   *   G      = B.gapCycle.memCycle.values
   *   R      = repeat(G, times)
   *   n      = size(G)
   *   period = n * times
   *
   *   B_t.gap(position)
   *     = R(mod(position, period))
   *     = G(mod(mod(position, period), n))
   *     = G(mod(position, n))
   *     = B.gap(position)
   *
   * The repeated cycle has a larger memory period (`oldSize * times`), so its
   * raw position is first reduced by that larger period. The chapter-2 modular
   * bridge then reduces that index back to the same old-period index used by
   * B's original `MemCycle`. This is the exact fact future `apply` proofs need:
   * repeated storage is an implementation detail, not a semantic change.
   */
  def assertRepeatedCycleGapMatches(times: BigInt, position: BigInt): Boolean = {
    require(times > BigInt(0))
    require(position >= BigInt(0))

    val gaps = cycle.gapCycle.memCycle.values
    val repeated = repeatedCycle(times)
    val repeatedGaps = ListRepeatProperties.repeat(gaps, times)

    assert(GapCycle.assertMemCycleValuesPositive(cycle.gapCycle))
    assert(gaps.nonEmpty)
    assert(gaps.size > BigInt(0))
    assert(ListRepeatProperties.assertRepeatSize(gaps, times))
    assert(repeatedGaps.size == gaps.size * times)
    assert(repeated.gapCycle.memCycle.values == repeatedGaps)
    assert(repeated.gapCycle.memCycle.size == gaps.size * times)

    assert(MemCycleProperties.assertRepeatedValuesCycleMatches(
      cycle.gapCycle.memCycle,
      repeated.gapCycle.memCycle,
      times,
      position
    ))

    repeated.gapCycle.memCycle(position) == cycle.gapCycle.memCycle(position)
  }.holds

  /**
   * Repeating B's gap storage preserves B's cumulative integral.
   *
   * Math:
   *
   *   B   = cycle
   *   B_t = repeatedCycle(times)
   *
   *   integral_B(0)   = head(B)   + gap_B(0)
   *   integral_B(k)   = integral_B(k - 1)   + gap_B(k)
   *   integral_Bt(0)  = head(B_t) + gap_Bt(0)
   *   integral_Bt(k)  = integral_Bt(k - 1)  + gap_Bt(k)
   *
   *   head(B_t) = head(B)
   *   gap_Bt(k) = gap_B(k)
   *
   *   Therefore, by the generic repeated-values integral lemma:
   *
   *   integral_Bt(k) = integral_B(k)
   */
  def assertRepeatedCycleIntegralMatches(times: BigInt, position: BigInt): Boolean = {
    require(times > BigInt(0))
    require(position >= BigInt(0))

    val gaps = cycle.gapCycle.memCycle.values
    val repeated = repeatedCycle(times)
    val repeatedGaps = ListRepeatProperties.repeat(gaps, times)

    assert(GapCycle.assertMemCycleValuesPositive(cycle.gapCycle))
    assert(gaps.size > BigInt(0))
    assert(ListRepeatProperties.assertRepeatSize(gaps, times))
    assert(repeated.gapCycle.memCycle.values == repeatedGaps)
    assert(repeated.integral.initialValue == cycle.integral.initialValue)
    assert(CycleIntegralProperties.assertRepeatedValuesIntegralMatches(
      cycle.integral,
      repeated.integral,
      times,
      position
    ))

    repeated.integral(position) == cycle.integral(position)
  }.holds

  /**
   * Repeating B's gap period preserves B's sequence value at every position.
   * The proof is intentionally staged by lowering a positive sequence index
   * `k` to the strictly smaller integral index `k - 1`.
   *
   * Math:
   *
   *   B   = cycle
   *   B_t = repeatedCycle(times)
   *   times > 0, k >= 0
   *
   *   B(0)   = head(B)
   *   B_t(0) = head(B_t) = head(B)
   *
   *   For k > 0:
   *
   *   j      = k - 1, so 0 <= j < k
   *   B(k)   = integral_B(k - 1)
   *   B_t(k) = integral_Bt(k - 1)
   *          = integral_B(k - 1)
   *          = B(k)
   *
   * Therefore:
   *
   *   repeatedCycle(times)(k) = cycle(k)
   *
   * This is the semantic version of the repeated-storage fact: repeating a
   * physical gap period changes the memory representation only, not the
   * generated sequence.
   */
  def assertRepeatedCycleApplyMatches(times: BigInt, k: BigInt): Boolean = {
    require(times > BigInt(0))
    require(k >= BigInt(0))

    val repeated = repeatedCycle(times)

    if (k == BigInt(0)) {
      assert(repeated.head == cycle.head)
      assert(repeated(k) == repeated.head)
      assert(cycle(k) == cycle.head)
      assert(repeated(k) == cycle(k))

      repeated(k) == cycle(k)
    } else {
      val previousPosition = k - BigInt(1)
      assert(previousPosition >= BigInt(0))
      assert(previousPosition < k)
      assert(assertRepeatedCycleIntegralMatches(times, previousPosition))
      val repeatedValue = repeated(k)
      val originalValue = cycle(k)
      val repeatedIntegral = repeated.integral(previousPosition)
      val originalIntegral = cycle.integral(previousPosition)

      assert(repeatedIntegral == originalIntegral)
      assert(repeatedValue == repeatedIntegral)
      assert(originalValue == originalIntegral)
      assert(repeatedValue == originalValue)
      assert(repeated(k) == cycle(k))

      repeated(k) == cycle(k)
    }
  }.holds

  /**
   * Builds the next `CycleSieveSequence` independently (no spec delegation).
   *
   * Uses the residue pipeline (`nextRotatedGaps`) to compute survivor gaps.
   * Positivity follows from the gap-merge argument: filtering out multiples
   * of `head` only merges adjacent positive gaps, preserving positivity.
   */
  def nextFromCycle(): CycleSieveSequence = {
    require(ListBoundUtils.allGreaterThan(
      SieveSequenceNextLevel.nextRotatedGaps(cycle), BigInt(0)))
    require(SieveSequenceNextLevel.nextRotatedGaps(cycle).nonEmpty)
    assert(assertModulusPositive())
    assert(assertPrimesTailValuesPositive())
    assert(assertHeadPositive())
    assert(assertModulusTimesHeadPositive())
    assert(assertNewHeadPlusModulusCoprime())

    val newGaps = SieveSequenceNextLevel.nextRotatedGaps(cycle)
    val newGapCycle = GapCycle(newGaps)

    CycleSieveSequence(primes.next, newGapCycle)
  }

  def nextVerified(nextPeriod: BigInt): SpecDerivedSieveSequence = {
    require(nextPeriod > BigInt(0))
    require(spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus)
    require(spec.next.primes.nextPrime.value < spec.next.head.value * spec.next.head.value)
    require(Calc.mod(SieveUtils.product(spec.next.filterValues), spec.next.head.value) != BigInt(0))
    SpecDerivedSieveSequence(spec.next, nextPeriod)
  }

  def assertNextHeadLessThanNewModulus(): Boolean = {
    require(spec.head.value >= 3)
    require(spec.filterModulus >= 2)

    assert(assertApplyMatches(BigInt(1)))
    assert(assertCycleModulusEqualsSpecFilterModulus())
    assert(spec(BigInt(1)) <= spec.searchBound(BigInt(1)))
    assert(spec.head.value * spec.filterModulus > spec.head.value + spec.filterModulus)
    cycle(BigInt(1)) < cycle.head * cycle.modulus
  }.holds

  def assertNextHeadLessThanHeadSquared(): Boolean = {
    assert(assertNextHeadMatches())
    cycle(BigInt(1)) < spec.head.value * spec.head.value
  }.holds
}
