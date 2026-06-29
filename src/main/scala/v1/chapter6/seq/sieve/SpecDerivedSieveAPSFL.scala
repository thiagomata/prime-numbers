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
case class SpecDerivedSieveAPSFL(
  spec: SpecSieveSequence,
  period: BigInt
) {
  require(period > BigInt(0))
  require(spec(period) == spec.head.value + spec.filterModulus)
  require(spec.primes.nextPrime.value < spec.head.value * spec.head.value)
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
  val cycle: CycleSieveSequence = CycleSieveSequence(cyclePrimes, gapCycle)

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
   * tail primes.  Exclusion (no false positives) via assertCycleValueCoprimeToTail.
   * Inclusion (no omissions) via assertApplyMatches — the spec enumerates every
   * accepted value at the correct position, and the cycle matches the spec.
   */
  def assertCyclePositionMatchesSpec(k: BigInt): Boolean = {
    require(k >= BigInt(0))
    assert(assertCycleValueCoprimeToTail(k))
    assert(assertApplyMatches(k))
    assert(spec.accepts(spec(k)))
    assert(SieveUtils.isCoprime(cycle(k), cyclePrimes.tail))
    true
  }.holds
}
