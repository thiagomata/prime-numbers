package v1.chapter6.seq.sieve

import stainless.collection.List
import stainless.lang.*
import v1.chapter2.div.Calc
import v1.chapter3.list.{ListBoundUtils, ListUtils}
import v1.chapter5.prime.{Prime, PrimeUtils}

/**
 * Canonical correspondence between one specification sieve stage and its
 * cycle-based representation.
 *
 * `SpecSieveSequence` remains the mathematical source of truth. It defines the
 * accepted values, proves the gap sequence, and packages one verified period as
 * `specGapCycle(period)`. `CycleSieveSequence` remains responsible only for
 * generic cycle mechanics and invariants that apply to every valid cycle.
 *
 * This intermediate representation owns the relationship between those two
 * classes. It receives a Spec stage, extracts the exact prime values and gap
 * cycle certified by that stage, and constructs the corresponding Cycle stage.
 * All later alignment lemmas should live here so neither underlying sequence
 * needs to know how the other one is represented.
 *
 * The constructor requirements state the current proof boundary:
 *
 *  - `period` identifies one positive Spec gap period;
 *  - the period returns to the same tail-filter residue;
 *  - the direct next prime is below the current head squared, which is the
 *    conditional number-theory assumption used by `SpecSieveSequence.next`;
 *  - the current tail product is not divisible by the current head, matching
 *    the structural requirement of `CycleSieveSequence`.
 *
 * Once constructed, `cycle` is not an independently supplied optimized state.
 * It is derived from `spec` itself, so its prime list and stored gaps have one
 * canonical origin.
 */
case class CanonicalCycleSieve(
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

  /**
   * The exact Cycle representation extracted from `spec`.
   *
   * The raw prime list contains every current Spec prime value in the same
   * order. The gap cycle is `spec.specGapCycle(period)`, not a separately
   * discovered or caller-provided cycle. The assertions below translate the
   * Spec facts into the generic structural obligations required by
   * `CycleSieveSequence`.
   */
  val cycle: CycleSieveSequence = {
    val cyclePrimes = PrimeUtils.primeValues(spec.primes.list.list)
    val gapCycle = spec.specGapCycle(period)
    val firstNext = spec(BigInt(1))

    assert(cyclePrimes.head == spec.head.value)
    assert(cyclePrimes.tail == spec.filterValues)
    assert(ListUtils.checkAllPositive(cyclePrimes))
    assert(ListUtils.checkAllBiggerThanValue(cyclePrimes, BigInt(1)))
    assert(SieveUtils.assertProductEqualOrBiggerThanElements(cyclePrimes.tail))
    assert(SieveUtils.isCoprime(cyclePrimes.head, cyclePrimes.tail))

    assert(spec.assertMemCycleGapMatch(BigInt(0), period))
    assert(gapCycle.memCycle(BigInt(0)) == firstNext - spec.head.value)
    assert(cyclePrimes.head + gapCycle.memCycle(BigInt(0)) == firstNext)
    assert(firstNext > spec.head.value)
    assert(spec.accepts(firstNext))
    assert(SieveUtils.isCoprime(firstNext, cyclePrimes.tail))

    assert(spec.assertApplyOneEqualsNextPrime())
    assert(Prime.isPrime(firstNext))
    assert(
      Prime.noDivisorInRangeExcludesValue(
        firstNext,
        BigInt(2),
        firstNext,
        spec.head.value
      )
    )
    assert(Calc.mod(firstNext, spec.head.value) != BigInt(0))
    assert(
      Calc.mod(
        SieveUtils.product(cyclePrimes.tail),
        cyclePrimes.head
      ) != BigInt(0)
    )

    CycleSieveSequence(cyclePrimes, gapCycle)
  }

  /**
   * Proves the extracted Cycle representation generates exactly the Spec
   * stream at every non-negative index.
   *
   * Index zero is the shared head. At a positive index, the Cycle sequence uses
   * `CycleIntegral` over the exact `specGapCycle(period)` stored by this bridge,
   * while `SpecSieveSequence.assertSpecGapCycleIntegralMatchesApply` proves that
   * the same integral reconstructs `spec(k)`.
   */
  def assertApplyMatches(k: BigInt): Boolean = {
    require(k >= BigInt(0))

    if (k == BigInt(0)) {
      assert(cycle.head == spec.head.value)
      assert(spec(BigInt(0)) == spec.head.value)
      cycle(k) == spec(k)
    } else {
      val gapCycle = spec.specGapCycle(period)
      assert(cycle.gapCycle.memCycle == gapCycle.memCycle)
      assert(
        cycle.integral ==
          v1.chapter4.cycle.integral.recursive.CycleIntegral(
            spec.head.value,
            gapCycle.memCycle
          )
      )
      assert(spec.assertSpecGapCycleIntegralMatchesApply(period, k))
      cycle(k) == spec(k)
    }
  }.holds

  /**
   * Exposes that the canonical Cycle starts at the Spec head.
   */
  def assertHeadMatches(): Boolean = {
    cycle.head == spec.head.value
  }.holds

  /**
   * Exposes that the canonical Cycle stores exactly the Spec prime values.
   */
  def assertPrimesMatch(): Boolean = {
    cycle.primes == PrimeUtils.primeValues(spec.primes.list.list)
  }.holds

  /**
   * Exposes that the canonical Cycle stores the exact Spec-derived gap cycle.
   */
  def assertGapCycleMatches(): Boolean = {
    cycle.gapCycle.memCycle == spec.specGapCycle(period).memCycle
  }.holds

  /**
   * Proves the canonical Cycle chooses the same next head as `spec.next`.
   */
  def assertNextHeadMatches(): Boolean = {
    val nextSpec = spec.next

    assert(assertApplyMatches(BigInt(1)))
    assert(spec.assertApplyOneEqualsNextPrime())
    assert(cycle(BigInt(1)) == spec(BigInt(1)))
    assert(spec(BigInt(1)) == spec.primes.nextPrime.value)
    assert(nextSpec.head.value == spec.primes.nextPrime.value)

    cycle(BigInt(1)) == nextSpec.head.value
  }.holds

  /**
   * Proves `spec.next` accepts exactly the values coprime to the canonical
   * Cycle's current prime list.
   */
  def assertNextAcceptsMatches(value: BigInt): Boolean = {
    require(value >= spec.next.head.value)

    val nextSpec = spec.next

    assert(assertPrimesMatch())
    assert(nextSpec.primes.list.tail.list == spec.primes.list.list)
    assert(nextSpec.filterPrimes == nextSpec.primes.list.tail.list)
    assert(nextSpec.filterValues == PrimeUtils.primeValues(nextSpec.filterPrimes))
    assert(nextSpec.filterValues == PrimeUtils.primeValues(spec.primes.list.list))
    assert(nextSpec.filterValues == cycle.primes)
    assert(
      nextSpec.accepts(value) ==
        SieveUtils.isCoprime(value, nextSpec.filterValues)
    )

    nextSpec.accepts(value) == SieveUtils.isCoprime(value, cycle.primes)
  }.holds

  /**
   * Proves the raw prime list produced by a canonical Cycle next stage matches
   * the prime values stored by `spec.next`.
   */
  def assertNextPrimesMatch(): Boolean = {
    val nextSpec = spec.next

    assert(assertNextHeadMatches())
    assert(assertPrimesMatch())
    assert(cycle(BigInt(1)) == nextSpec.head.value)
    assert(cycle.primes == PrimeUtils.primeValues(spec.primes.list.list))
    assert(nextSpec.primes.list.tail.list == spec.primes.list.list)

    cycle(BigInt(1)) :: cycle.primes ==
      PrimeUtils.primeValues(nextSpec.primes.list.list)
  }.holds

  /**
   * Proves the walk decision condition is equivalent to next-stage acceptance.
   *
   * For k >= 1, the walk `collectGaps` keeps `cycle(k)` exactly when
   * `Calc.mod(cycle(k), cycle.head) != 0`. The next stage accepts `cycle(k)`
   * exactly when it is coprime to `cycle.primes`. Since `cycle(k)` already
   * passes the tail filter (because `spec(k)` passes it), coprimality to
   * `cycle.primes` reduces to the non-divisibility by `cycle.head`.
   *
   * This bridges the walk's branch condition to Spec.next's acceptance
   * predicate, enabling a later recursive gap equality proof.
   */
  def assertWalkDecisionMatchesNextAccept(k: BigInt): Boolean = {
    require(k >= BigInt(1))

    val v = cycle(k)

    assert(assertApplyMatches(k))
    assert(spec(k) == v)
    assert(spec.assertApplyMonotonic(BigInt(1), k))
    assert(spec(BigInt(1)) <= spec(k))
    assert(assertApplyMatches(BigInt(1)))
    assert(spec(BigInt(1)) == cycle(BigInt(1)))
    assert(assertNextHeadMatches())
    assert(cycle(BigInt(1)) == spec.next.head.value)
    assert(spec(BigInt(1)) == spec.next.head.value)
    assert(v >= spec.next.head.value)
    assert(spec(k) >= spec.head.value)
    assert(spec.accepts(spec(k)))
    assert(SieveUtils.isCoprime(spec(k), spec.filterValues))
    assert(assertPrimesMatch())
    assert(PrimeUtils.primeValues(spec.primes.list.list).tail ==
      PrimeUtils.primeValues(spec.primes.list.list.tail))
    assert(spec.filterValues == PrimeUtils.primeValues(spec.filterPrimes))
    assert(spec.filterPrimes == spec.primes.list.list.tail)
    assert(cycle.primes.tail == spec.filterValues)
    assert(SieveUtils.isCoprime(v, cycle.primes.tail))
    assert(assertNextAcceptsMatches(v))
    assert(spec.next.accepts(v) == SieveUtils.isCoprime(v, cycle.primes))

    val modNonZero = Calc.mod(v, cycle.head) != BigInt(0)

    modNonZero == spec.next.accepts(v)
  }.holds

  /**
   * Proves the canonical next-stage gap cycle values equal `spec.next.gapList`.
   *
   * This is true by construction: `specGapCycle(period)` creates a `GapCycle`
   * from `gapList(0, period)`. For the next stage, `spec.next.specGapCycle(nextPeriod)`
   * stores `gapList(0, nextPeriod)` as its values. Exposing this as a lemma
   * makes it available for downstream alignment proofs.
   */
  def assertNextGapCycleValuesEqualSpecNextGapList(nextPeriod: BigInt): Boolean = {
    require(nextPeriod > BigInt(0))
    require(spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus)

    spec.next.specGapCycle(nextPeriod).memCycle.values == spec.next.gapList(BigInt(0), nextPeriod)
  }.holds

  /**
   * Proves the canonical next-stage apply matches `spec.next.apply(k)`.
   *
   * `spec.next.assertSpecGapCycleIntegralMatchesApply(nextPeriod, k)` proves
   * that the integral reconstruction using `specGapCycle(nextPeriod)` at index
   * `k` equals `spec.next(k)`. This integral reconstruction IS the canonical
   * cycle apply for the next stage (for positive indices), so this lemma
   * establishes the apply match without constructing a new
   * `CanonicalCycleSieve` instance.
   */
  def assertNextApplyMatches(nextPeriod: BigInt, k: BigInt): Boolean = {
    require(nextPeriod > BigInt(0))
    require(spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus)
    require(k > BigInt(0))

    spec.next.assertSpecGapCycleIntegralMatchesApply(nextPeriod, k)
  }.holds

  /**
   * Proves each next-stage gap equals the sum of consecutive current gaps.
   *
   * For any i < nextPeriod-1, the gap spec.next(i+1) - spec.next(i) equals
   * spec(k_{i+1}) - spec(k_i), where k_i = spec.indexOfAccepted(spec.next(i))
   * and k_{i+1} = spec.indexOfAccepted(spec.next(i+1)). The difference
   * spec(k_{i+1}) - spec(k_i) is exactly the sum of current gapList values
   * from k_i through k_{i+1} - 1.
   *
   * This is the single-gap merge property: adding the head as a new filter
   * merges consecutive current gaps whose intermediate values are multiples
   * of head. The proof uses indexOfAccepted's cached postcondition instead
   * of scanning positions, avoiding the timeout from the full merge lemmas.
   */
  def assertNextGapEqualsCurrentGapSum(nextPeriod: BigInt, i: BigInt): Boolean = {
    require(nextPeriod > BigInt(1))
    require(i >= BigInt(0))
    require(i + BigInt(1) < nextPeriod)
    require(
      spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus
    )

    val v1 = spec.next(i)
    val v2 = spec.next(i + BigInt(1))

    // v1 >= spec.head.value
    assert(assertNextHeadMatches())
    assert(cycle(BigInt(1)) == spec.next.head.value)
    assert(spec.next(BigInt(0)) == spec.next.head.value)
    assert(spec.next.assertApplyMonotonic(BigInt(0), i))
    assert(spec.next(BigInt(0)) <= spec.next(i))
    assert(v1 >= spec.head.value)

    // spec.accepts(v1) via the acceptance bridge
    assert(spec.next.accepts(v1))
    assert(assertNextAcceptsMatches(v1))
    assert(spec.next.accepts(v1) == SieveUtils.isCoprime(v1, cycle.primes))
    assert(assertPrimesMatch())
    assert(PrimeUtils.primeValues(spec.primes.list.list).tail ==
      PrimeUtils.primeValues(spec.primes.list.list.tail))
    assert(spec.filterValues == PrimeUtils.primeValues(spec.filterPrimes))
    assert(spec.filterPrimes == spec.primes.list.list.tail)
    assert(cycle.primes.tail == spec.filterValues)
    assert(SieveUtils.isCoprime(v1, spec.filterValues))
    assert(spec.accepts(v1))

    // Same for v2
    assert(spec.next.assertApplyMonotonic(i, i + BigInt(1)))
    assert(spec.next(i) <= spec.next(i + BigInt(1)))
    assert(v2 >= spec.head.value)
    assert(spec.next.accepts(v2))
    assert(SieveUtils.isCoprime(v2, spec.filterValues))
    assert(spec.accepts(v2))

    val k1 = spec.indexOfAccepted(v1)
    val k2 = spec.indexOfAccepted(v2)

    assert(spec(k1) == v1)
    assert(spec(k2) == v2)

    val nextGap = v2 - v1
    val currentSum = spec(k2) - spec(k1)

    nextGap == currentSum
  }.holds
//
//  /**
//   * [NEVER INDEPENDENTLY VERIFIED — helper for timed-out lemmas]
//   *
//   * Merges current gaps into next gaps by scanning the canonical gap cycle.
//   *
//   * Iterates `head * gapCycle.size` positions of the cycle, accumulating the
//   * cumulative value by adding successive gaps. At each position:
//   *
//   * - If the cumulative value is NOT a multiple of head: the value survives
//   *   the head filter. Emit the gap from the last survivor to this value.
//   * - If the cumulative value IS a multiple of head: skip it (future gaps
//   *   will merge with this one).
//   *
//   * `memCycle(pos)` provides the gap at each position with automatic
//   *   wrapping modulo `gapCycle.size`, so the scan covers the necessary
//   *   `head` full repetitions of the gap cycle without explicit list
//   *   concatenation.
//   *
//   * This function was written as a building block for
//   * assertMergeGapsMatchesSpecNext and assertMergeGapsIntegralMatchesSpecNext,
//   * both of which timed out (3 attempts). It was never verified standalone.
//   * Do NOT uncomment without a new strategy for the gap equality proof.
//   */
//  def mergeGaps(
//    pos: BigInt,
//    remaining: BigInt,
//    cumulative: BigInt,
//    lastSurvivor: BigInt,
//    emitted: List[BigInt]
//  ): List[BigInt] = {
//    require(remaining >= BigInt(0))
//    require(pos >= BigInt(1))
//    require(cycle.head > BigInt(0))
//    decreases(remaining)
//
//    if (remaining == BigInt(0)) {
//      emitted.reverse
//    } else {
//      val g = cycle.gapCycle.memCycle(pos)
//      val nextVal = cumulative + g
//      if (Calc.mod(nextVal, cycle.head) != BigInt(0)) {
//        val gap = nextVal - lastSurvivor
//        mergeGaps(
//          pos + BigInt(1), remaining - BigInt(1),
//          nextVal, nextVal,
//          gap :: emitted
//        )
//      } else {
//        mergeGaps(
//          pos + BigInt(1), remaining - BigInt(1),
//          nextVal, lastSurvivor,
//          emitted
//        )
//      }
//    }
//  }
//
  /**
   * Proves each spec.next value appears at some cycle position.
   *
   * For any k >= 0, `spec.next(k) == cycle(pos)` where
   * `pos = spec.indexOfAccepted(spec.next(k))`. The proof uses
   * `indexOfAccepted.ensuring(res => spec(res) == spec.next(k))`
   * and `assertApplyMatches(pos)` to bridge to the canonical cycle.
   *
   * This is the value-level correspondence between the next Spec stage
   * and the current canonical cycle, independent of any merge or walk.
   */
  def assertNextValueMatchesCyclePosition(k: BigInt): Boolean = {
    require(k >= BigInt(0))

    val v = spec.next(k)

    // v >= spec.head.value (needed for accepts / indexOfAccepted)
    assert(assertNextHeadMatches())
    assert(cycle(BigInt(1)) == spec.next.head.value)
    assert(spec.next.assertApplyMonotonic(BigInt(0), k))
    assert(spec.next(BigInt(0)) <= spec.next(k))
    assert(v >= spec.next.head.value)
    assert(v >= spec.head.value)

    // spec.accepts(v) (needed for indexOfAccepted)
    assert(spec.next.accepts(v))
    assert(assertNextAcceptsMatches(v))
    assert(spec.next.accepts(v) == SieveUtils.isCoprime(v, cycle.primes))
    assert(assertPrimesMatch())
    assert(PrimeUtils.primeValues(spec.primes.list.list).tail ==
      PrimeUtils.primeValues(spec.primes.list.list.tail))
    assert(spec.filterValues == PrimeUtils.primeValues(spec.filterPrimes))
    assert(spec.filterPrimes == spec.primes.list.list.tail)
    assert(cycle.primes.tail == spec.filterValues)
    assert(SieveUtils.isCoprime(v, spec.filterValues))
    assert(spec.accepts(v))

    val pos = spec.indexOfAccepted(v)

    assert(spec(pos) == v)
    assert(assertApplyMatches(pos))
    assert(cycle(pos) == spec(pos))

    spec.next(k) == cycle(pos)
  }.holds
//
//  /**
//  * [NEVER INDEPENDENTLY VERIFIED — helper for timed-out lemma]
//  *
//  * Recursive predicate: all positions in [from, to) are multiples of head.
//  *
//  * Used as the postcondition of `findNextNonMultiple` to guarantee that the
//  * returned position is the FIRST non-multiple in the search range.
//  *
//  * This predicate was written as a building block for
//  * assertNonMultipleMatchesSpecNext, which timed out (3 attempts).
//  * It was never verified standalone. Do NOT uncomment without a new strategy.
//  */
// def noNonMultipleInRange(from: BigInt, to: BigInt): Boolean = {
//   require(to >= from)
//   decreases(to - from)
//   if (from >= to) true
//   else Calc.mod(cycle(from), cycle.head) == BigInt(0) &&
//     noNonMultipleInRange(from + BigInt(1), to)
// }
////
// /**
//  * [NEVER INDEPENDENTLY VERIFIED — helper for timed-out lemma]
//  *
//  * Extracts a value from `noNonMultipleInRange`: if `v` is in [from, to),
//  * then `cycle(v) % head == 0` (i.e., `v` is a multiple).
//  *
//  * Mirror of `AllPrimesSoFarList.noPrimesBetweenExcludesValue` for the
//  * no-non-multiples predicate.
//  *
//  * This lemma was written as a building block for
//  * assertNonMultipleMatchesSpecNext, which timed out (3 attempts).
//  * It was never verified standalone. Do NOT uncomment without a new strategy.
//  */
// def noNonMultipleExcludesValue(from: BigInt, to: BigInt, v: BigInt): Boolean = {
//   require(noNonMultipleInRange(from, to))
//   require(v >= from)
//   require(v < to)
//   decreases(to - v)
////
//   if (from == v) {
//     Calc.mod(cycle(v), cycle.head) == BigInt(0)
//   } else {
//     assert(noNonMultipleInRange(from + BigInt(1), to))
//     noNonMultipleExcludesValue(from + BigInt(1), to, v)
//   }
// }.holds
////
// /**
//  * [NEVER INDEPENDENTLY VERIFIED — helper for timed-out lemma]
//  *
//  * Bounded search for the first non-multiple position in [startPos, bound].
//  *
//  * Mirrors `SpecSieveSequence.searchNext` but operates on cycle positions.
//  * Returns `bound + 1` if no non-multiple found in range.
//  *
//  * @ensuring `noNonMultipleInRange(startPos, res)` guarantees all skipped
//  * positions are multiples — the returned position is the FIRST non-multiple.
//  *
//  * This function was written as a building block for
//  * assertNonMultipleMatchesSpecNext, which timed out (3 attempts).
//  * It was never verified standalone. Do NOT uncomment without a new strategy.
//  */
// def findNextNonMultiple(startPos: BigInt, bound: BigInt): BigInt = {
//   require(startPos >= BigInt(1))
//   require(bound >= startPos)
//   require(cycle.head > BigInt(0))
//   decreases(bound - startPos + BigInt(1))
////
//   if (Calc.mod(cycle(startPos), cycle.head) != BigInt(0)) {
//     startPos
//   } else if (startPos == bound) {
//     bound + BigInt(1)
//   } else {
//     findNextNonMultiple(startPos + BigInt(1), bound)
//   }
// }.ensuring(res =>
//   res >= startPos &&
//   (!(res <= bound) || Calc.mod(cycle(res), cycle.head) != BigInt(0)) &&
//   noNonMultipleInRange(startPos, res)
// )
////
// /**
//  * [NEVER INDEPENDENTLY VERIFIED — helper for timed-out lemma]
//  *
//  * Returns the position of the k-th non-multiple of head in the cycle.
//  *
//  * Defined inductively like `SpecSieveSequence.apply(k)`: base case (k=1)
//  * returns position 1 (= new head), and each step calls `findNextNonMultiple`
//  * to skip past multiples. The search bound is the full scan range.
//  *
//  * This function was written as a building block for
//  * assertNonMultipleMatchesSpecNext, which timed out (3 attempts).
//  * It was never verified standalone. Do NOT uncomment without a new strategy.
//  */
// def nonMultiplePosition(k: BigInt): BigInt = {
//   require(k >= BigInt(1))
//   require(cycle.head > BigInt(0))
//   decreases(k)
////
//   if (k == BigInt(1)) {
//     BigInt(1)
//   } else {
//     val prevPos = nonMultiplePosition(k - BigInt(1))
//     findNextNonMultiple(
//       prevPos + BigInt(1),
//       prevPos + cycle.head * cycle.gapCycle.size
//     )
//   }
// }
//
// /**
//  * [TIMED OUT — 3 attempts exhausted, per stop-and-ask rule]
//  *
//  * Bounded-search proof that the k-th non-multiple in the canonical cycle
//  * equals spec.next(k-1). Uses findNextNonMultiple with .ensuring for
//  * noNonMultipleInRange guarantee and nextDoesNotPassAcceptedValue for
//  * Spec minimality.
//  *
//  * Root cause: The critical step requires proving there is no accepted
//  * value between lastSurvivor and the current position. This needs a
//  * FORALL over all intermediate walk positions (∀t ∈ (lastPos, walkPos).
//  * !accepted(cycle(t+1))). Stainless cannot express this quantifier as a
//  * recursive function parameter, and the aux lemma's sequential assertion
//  * chain does not imply a FORALL to the solver.
//  *
//  * Do NOT retry without a fundamentally new approach (e.g., recursive
//  * accumulator parameter carrying the FORALL, or a different strategy).
//  * Commented out rather than deleted per never-destroy rule.
//  */
// def assertNonMultipleMatchesSpecNext(
//   k: BigInt, nextPeriod: BigInt
// ): Boolean = {
//   require(k >= BigInt(1))
//   require(k <= nextPeriod)
//   require(nextPeriod > BigInt(0))
//   require(spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus)
//   decreases(k)
//
//   val pos = nonMultiplePosition(k)
//
//   if (k == BigInt(1)) {
//     assert(pos == BigInt(1))
//     assert(assertNextHeadMatches())
//     assert(cycle(pos) == spec.next(BigInt(0)))
//     cycle(pos) == spec.next(k - BigInt(1))
//   } else {
//     assert(assertNonMultipleMatchesSpecNext(k - BigInt(1), nextPeriod))
//     val prevPos = nonMultiplePosition(k - BigInt(1))
//     assert(cycle(prevPos) == spec.next(k - BigInt(2)))
//     assert(assertWalkDecisionMatchesNextAccept(prevPos))
//     assert(assertWalkDecisionMatchesNextAccept(pos))
//     assert(spec.next.accepts(cycle(pos)))
//     assert(spec.next(k - BigInt(2)) < cycle(pos))
//     assert(spec.next.accepts(cycle(pos)))
//     assert(spec.next.nextDoesNotPassAcceptedValue(k - BigInt(2), cycle(pos)))
//     assert(spec.next(k - BigInt(1)) <= cycle(pos))
//     assert(noNonMultipleInRange(prevPos + BigInt(1), pos))
//     val specPos = spec.indexOfAccepted(spec.next(k - BigInt(1)))
//     if (specPos < pos) {
//       assert(noNonMultipleExcludesValue(prevPos + BigInt(1), pos, specPos))
//       assert(Calc.mod(cycle(specPos), cycle.head) == BigInt(0))
//       assert(false)
//     }
//     cycle(pos) == spec.next(k - BigInt(1))
//   }
// }.holds
//
// /**
//  * [TIMED OUT — 3 attempts exhausted, per stop-and-ask rule]
//  *
//  * Full list equality between mergeGaps output and spec.next.gapList.
//  * Timed out at 121s (Attempt 1 — Direct list comparison).
//  *
//  * Root cause: The walk's collectGaps recursively scans head * period
//  * positions, and the SMT solver cannot symbolically execute this many
//  * iterations. nextGapsWalk is fundamentally opaque from outside .holds
//  * contexts — its .ensuring exports positivity but not length or element
//  * values.
//  *
//  * Do NOT retry without a fundamentally new approach (e.g., strengthening
//  * collectGaps postconditions, or a non-walk-based comparison).
//  * Commented out rather than deleted per never-destroy rule.
//  */
// def assertMergeGapsMatchesSpecNext(nextPeriod: BigInt): Boolean = {
//   require(nextPeriod > BigInt(0))
//   require(spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus)
//   val steps = cycle.head * cycle.gapCycle.size
//   val walked = mergeGaps(BigInt(1), steps, cycle(BigInt(1)), cycle(BigInt(1)), List.empty[BigInt])
//   val specGaps = spec.next.gapList(BigInt(0), nextPeriod)
//   walked == specGaps
// }.holds
//
// /**
//  * [TIMED OUT — 3 attempts exhausted, per stop-and-ask rule]
//  *
//  * Integral comparison between mergeGaps output and spec.next values.
//  * Timed out at 121s (Attempt 3 — Even walkedGaps.nonEmpty confirmed
//  * nextGapsWalk is fundamentally opaque).
//  *
//  * Root cause: Same as assertMergeGapsMatchesSpecNext — the walk's
//  * output is opaque to external lemmas. No structural information about
//  * element values or list length is exported by collectGaps.ensuring.
//  *
//  * Do NOT retry without a fundamentally new approach.
//  * Commented out rather than deleted per never-destroy rule.
//  */
// def assertMergeGapsIntegralMatchesSpecNext(nextPeriod: BigInt, k: BigInt): Boolean = {
//   require(nextPeriod > BigInt(0))
//   require(k > BigInt(0))
//   require(k <= nextPeriod)
//   require(spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus)
//
//   val steps = cycle.head * cycle.gapCycle.size
//   val walked = mergeGaps(BigInt(1), steps, cycle(BigInt(1)), cycle(BigInt(1)), List.empty[BigInt])
//   val walkedIntegral = CycleIntegral(spec.next.head.value, walked)
//   walkedIntegral(k - BigInt(1)) == spec.next(k)
// }.holds
}
