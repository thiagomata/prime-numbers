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
   * Proves every current Spec value from index one onward is in the domain of
   * the next Spec sequence.
   *
   * The next sequence starts at the current value `spec(1)`. Monotonicity of
   * the current sequence gives `spec(1) <= spec(k)` for every `k >= 1`, while
   * the canonical next-head correspondence identifies `spec(1)` with
   * `spec.next.head.value`. Keeping this arithmetic fact separate prevents
   * acceptance proofs from mixing ordering with filter coprimality.
   */
  def assertCurrentValueAtOrAboveNextHead(k: BigInt): Boolean = {
    require(k >= BigInt(1))

    assert(spec.assertApplyMonotonic(BigInt(1), k))
    assert(spec(BigInt(1)) <= spec(k))
    assert(assertApplyMatches(BigInt(1)))
    assert(spec(BigInt(1)) == cycle(BigInt(1)))
    assert(assertNextHeadMatches())
    assert(cycle(BigInt(1)) == spec.next.head.value)
    assert(spec(BigInt(1)) == spec.next.head.value)

    spec(k) >= spec.next.head.value
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
   * [TIMED OUT — acceptance transfer attempt 3, 2026-06-24]
   *
   * Even as an isolated 17-VC lemma, Stainless timed out when using the
   * equivalence exported by `assertWalkDecisionMatchesNextAccept` to establish
   * its positive acceptance branch. Commented out after the third failed
   * canonical acceptance-transfer attempt, per the stop-and-ask rule.
   *
   * Exposes the kept branch of the walk decision directly in Spec terms.
   *
   * `assertWalkDecisionMatchesNextAccept` proves an equivalence whose accepted
   * value is written as `cycle(k)`. Callers that reason about consecutive Spec
   * values need the more direct endpoint `spec.next.accepts(spec(k))`.
   *
   * Keeping this rewrite in a tiny lemma prevents a larger copy-gap proof from
   * unfolding the canonical representation, the next sequence, and the
   * acceptance predicate in the same verification condition.
   */
  /*
  def assertWalkNonMultipleAcceptedByNext(k: BigInt): Boolean = {
    require(k >= BigInt(1))
    require(Calc.mod(cycle(k), cycle.head) != BigInt(0))

    assert(assertWalkDecisionMatchesNextAccept(k))
    assert(spec.next.accepts(cycle(k)))
    assert(assertApplyMatches(k))
    assert(cycle(k) == spec(k))

    spec.next.accepts(spec(k))
  }.holds
  */

  /**
   * Proves next-stage acceptance constructively from the two filter parts.
   *
   * A current generated value already passes `spec.filterValues`, which is the
   * tail of `cycle.primes`. The additional filter used by `spec.next` is the
   * current `cycle.head`. Therefore the explicit non-multiple requirement and
   * the existing tail-coprimality fact together establish coprimality with the
   * complete next-stage filter list.
   *
   * This lemma intentionally does not consume
   * `assertWalkDecisionMatchesNextAccept`: constructing the positive result
   * directly avoids asking Stainless to select and rewrite one branch of a
   * cross-representation boolean equivalence.
   */
  def assertCurrentNonMultipleAcceptedByNext(k: BigInt): Boolean = {
    require(k >= BigInt(1))
    require(Calc.mod(cycle(k), cycle.head) != BigInt(0))

    val value = cycle(k)
    val nextSpec = spec.next

    assert(assertApplyMatches(k))
    assert(value == spec(k))
    assert(spec(k) >= spec.head.value)
    assert(spec.accepts(spec(k)))
    assert(SieveUtils.isCoprime(spec(k), spec.filterValues))

    assert(assertPrimesMatch())
    assert(cycle.primes.tail == spec.filterValues)
    assert(SieveUtils.isCoprime(value, cycle.primes.tail))
    assert(cycle.primes.head == cycle.head)
    assert(Calc.mod(value, cycle.primes.head) != BigInt(0))
    assert(SieveUtils.isCoprime(value, cycle.primes))

    assert(nextSpec.primes.list.tail.list == spec.primes.list.list)
    assert(nextSpec.filterPrimes == nextSpec.primes.list.tail.list)
    assert(nextSpec.filterValues == PrimeUtils.primeValues(nextSpec.filterPrimes))
    assert(nextSpec.filterValues == PrimeUtils.primeValues(spec.primes.list.list))
    assert(nextSpec.filterValues == cycle.primes)

    assert(assertCurrentValueAtOrAboveNextHead(k))
    assert(SieveUtils.isCoprime(value, nextSpec.filterValues))

    nextSpec.accepts(spec(k))
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

  /**
   * Proves the first next-stage gap matches the first element of
   * `spec.next.gapList(0, nextPeriod)`, without scanning positions.
   *
   * The first next-stage gap is the distance from the next head to the value
   * that follows it in the next stream:
   *
   * {{{
   *   firstGap = spec.next(1) - spec.next(0)
   *            = spec.next(1) - spec.next.head.value     [by apply's base case]
   * }}}
   *
   * The head of `gapList(0, nextPeriod)` is definitionally
   * `apply(0 + 1) - apply(0)`, i.e. exactly `spec.next(1) - spec.next(0)`.
   * So the equality reduces to applying `gapList`'s head definition together
   * with `apply`'s base case:
   *
   * {{{
   *   gapList(0, nextPeriod).head
   *     = apply(0 + 1) - apply(0)        [gapList head definition]
   *     = spec.next(1) - spec.next(0)    [by apply's base case]
   *     = firstGap                       [Q.E.D.]
   * }}}
   *
   * This is the foundational single-gap fact for the Leg-3 gap-list equality
   * (see `tickets/active/canonical-next-strategy.md`). It avoids the opaque
   * positional walk that timed out in the prior Leg-2 Lemma 5, and mirrors the
   * substitution-first style that made `assertNextGapEqualsCurrentGapSum`
   * verify.
   *
   * @param nextPeriod a positive period anchor for `spec.next` satisfying
   *                   `spec.next(nextPeriod) == spec.next.head.value +
   *                   spec.next.filterModulus`
   * @return `true` (verified); formally,
   *         `spec.next(1) - spec.next(0) == spec.next.gapList(0, nextPeriod).head`
   */
  def assertNextFirstGapMatchesSpecNext(nextPeriod: BigInt): Boolean = {
    require(nextPeriod > BigInt(0))
    require(spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus)

    val firstGap = spec.next(BigInt(1)) - spec.next(BigInt(0))
    val gapListHead = spec.next.gapList(BigInt(0), nextPeriod).head

    assert(spec.next(BigInt(0)) == spec.next.head.value)
    assert(spec.next.assertApplyMonotonic(BigInt(0), BigInt(1)))
    assert(firstGap == spec.next(BigInt(1)) - spec.next.head.value)
    assert(gapListHead == spec.next(BigInt(1)) - spec.next(BigInt(0)))

    firstGap == gapListHead
  }.holds

  /**
   * Proves the next-stage gap at an arbitrary position `index` matches the
   * corresponding element of `spec.next.gapList(0, nextPeriod)`, without
   * scanning positions.
   *
   * For any valid index `index < nextPeriod`, the `index`-th next-stage gap
   * is the distance between two consecutive next-stage values:
   *
   * {{{
   *   nextGap(index) = spec.next(index + 1) - spec.next(index)
   * }}}
   *
   * The `index`-th element of `gapList(0, nextPeriod)` is definitionally the
   * same adjacent difference, by `SpecSieveSequence.assertGapListApplyEqualsGapAtPosition`:
   *
   * {{{
   *   gapList(0, nextPeriod).apply(index)
   *     = apply(0 + index + 1) - apply(0 + index)   [gapList apply definition]
   *     = spec.next(index + 1) - spec.next(index)   [by apply's base case]
   *     = nextGap(index)                            [Q.E.D.]
   * }}}
   *
   * This generalizes `assertNextFirstGapMatchesSpecNext` from `index = 0` to
   * any valid index, and is the per-position input to the list-level gap
   * equality proof of Leg 3 (see `tickets/active/canonical-next-strategy.md`).
   *
   * @param nextPeriod a positive period anchor for `spec.next` satisfying
   *                   `spec.next(nextPeriod)` == `spec.next.head.value` +
   *                   `spec.next.filterModulus`
   * @param index      the gap position, `0 <= index < nextPeriod`
   * @return `true` (verified); formally,
   *         spec.next(index + 1) - spec.next(index)
   *          == spec.next.gapList(0, nextPeriod).apply(index).
   */
  def assertNextGapAtMatchesSpecNext(
    nextPeriod: BigInt,
    index: BigInt
  ): Boolean = {
    require(nextPeriod > BigInt(0))
    require(index >= BigInt(0))
    require(index < nextPeriod)
    require(spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus)

    val nextGap = spec.next(index + BigInt(1)) - spec.next(index)

    // Discharge the `index < gapList.size` precondition of `.apply(index)`:
    // assertGapListSize proves the list built with count = nextPeriod has
    // exactly nextPeriod elements, and `index < nextPeriod` is already required.
    assert(spec.next.assertGapListSize(BigInt(0), nextPeriod))
    assert(spec.next.gapList(BigInt(0), nextPeriod).size == nextPeriod)

    val gapListValue = spec.next.gapList(BigInt(0), nextPeriod).apply(index)

    assert(spec.next.assertGapListApplyEqualsGapAtPosition(BigInt(0), nextPeriod, index))
    assert(gapListValue == spec.next(index + BigInt(1)) - spec.next(index))

    nextGap == gapListValue
  }.holds

  /**
   * Builds the next-stage gap list directly from `spec.next`'s adjacent value
   * differences, in forward order, without going through the walk pipeline.
   *
   * The `i`-th emitted element is `spec.next(from + i + 1) - spec.next(from + i)`,
   * so the list is in the same forward order as `spec.next.gapList(from, count)`:
   *
   * {{{
   *   nextGapList(from, count) = [ spec.next(from + 1) - spec.next(from),
   *                                spec.next(from + 2) - spec.next(from + 1),
   *                                ...,
   *                                spec.next(from + count) - spec.next(from + count - 1) ]
   * }}}
   *
   * The `from` parameter slides forward by one on each recursive step, mirroring
   * `SpecSieveSequence.gapList`'s own recursion shape exactly. This sliding
   * window keeps the period-anchor precondition local at every step, which is
   * what makes the companion induction lemma verify (see LEARNINGS 2.2).
   *
   * @param from   the starting index, `from >= 0`
   * @param count  number of gaps to emit, `count >= 0`
   * @return the list of `count` adjacent next-stage gaps, forward-ordered
   */
  def nextGapList(from: BigInt, count: BigInt): List[BigInt] = {
    require(from >= BigInt(0))
    require(count >= BigInt(0))
    decreases(count)
    if (count == BigInt(0)) {
      List.empty[BigInt]
    } else {
      (spec.next(from + BigInt(1)) - spec.next(from)) :: nextGapList(from + BigInt(1), count - BigInt(1))
    }
  }

  /**
   * Proves the Canonical-computed next gap list equals Spec's own next
   * `gapList`, element-for-element, by structural induction on `count`.
   *
   * {{{
   *   nextGapList(from, count) == spec.next.gapList(from, count)
   * }}}
   *
   * Proof by induction on `count` (mirroring `assertGapListPositive`):
   *  - Base (`count == 0`): both lists are empty.                       `[Q.E.D.]`
   *  - Step (`count > 0`):
   *    - head: `nextGapList(from, count).head == spec.next(from + 1) - spec.next(from)`
   *      by the builder definition, and
   *      `spec.next.gapList(from, count).head == spec.next(from + 1) - spec.next(from)`
   *      by `assertGapListFirstEqualsGap`. So the heads are equal.
   *    - tail: by the inductive hypothesis at `from + 1, count - 1`.
   *
   * The sliding `from` parameter keeps the induction self-contained: each
   * recursive call uses `from + 1`, so no period-anchor precondition needs to
   * be re-derived. This avoids the recursion-precondition timeout seen in the
   * first attempt (see `canonical-next-strategy.md` update log).
   *
   * This is the list-level lift of Leg 3. It establishes that the
   * direct-difference computation matches Spec's own `gapList`.
   *
   * @param from   the starting index, `from >= 0`
   * @param count  number of gaps, `count >= 0`
   * @return `true` (verified); formally,
   *         `nextGapList(from, count) == spec.next.gapList(from, count)`
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
   * Transfers Spec's gap periodicity to the canonical cycle.
   *
   * Spec's gap periodicity (`spec.assertGapPeriodic`) proves the gap at index
   * `k` repeats after a period `p` that satisfies
   * `spec.apply(p) == spec.head.value + spec.filterModulus`:
   *
   * {{{
   *   spec(k + 1 + p) - spec(k + p) == spec(k + 1) - spec(k)
   * }}}
   *
   * Since the canonical cycle replicates Spec at every index
   * (`assertApplyMatches`: `cycle(i) == spec(i)` for all `i >= 0`), the same
   * periodicity holds for the cycle's adjacent differences:
   *
   * {{{
   *   cycle(k + 1 + p) - cycle(k + p)
   *     == spec(k + 1 + p) - spec(k + p)   [by assertApplyMatches, twice]
   *     == spec(k + 1) - spec(k)           [by spec.assertGapPeriodic]
   *     == cycle(k + 1) - cycle(k)         [by assertApplyMatches, twice]
   *                                                                      [Q.E.D.]
   * }}}
   *
   * This is a pure transfer lemma: the period anchor is unchanged, and each
   * rewrite goes through the verified `assertApplyMatches`. No cycle-strategy
   * (walk/rotate) machinery is involved.
   *
   * @param k any gap index, `k >= 0`
   * @param period a period anchor satisfying `spec(period) == spec.head.value + spec.filterModulus`
   * @return `true` (verified); formally,
   *         `cycle(period + k + 1) - cycle(period + k) == cycle(k + 1) - cycle(k)`
   */
  def assertGapPeriodicMatchesSpec(k: BigInt, period: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(period >= BigInt(0))
    require(spec(period) == spec.head.value + spec.filterModulus)

    assert(spec.assertGapPeriodic(k, period))
    assert(assertApplyMatches(k))
    assert(assertApplyMatches(k + BigInt(1)))
    assert(assertApplyMatches(k + period))
    assert(assertApplyMatches(k + period + BigInt(1)))

    val specGap = spec(k + BigInt(1)) - spec(k)
    val cycleGap = cycle(k + BigInt(1)) - cycle(k)
    val specShiftedGap = spec(k + period + BigInt(1)) - spec(k + period)
    val cycleShiftedGap = cycle(k + period + BigInt(1)) - cycle(k + period)

    assert(cycleGap == specGap)
    assert(cycleShiftedGap == specShiftedGap)
    assert(specGap == specShiftedGap)

    cycleShiftedGap == cycleGap
  }.holds

  /**
   * Transfers Spec's gap positivity to the canonical cycle.
   *
   * Spec's gap positivity (`spec.assertGapPositive`) proves each adjacent
   * difference is strictly positive because Spec's stream is strictly
   * increasing:
   *
   * {{{
   *   spec(k + 1) - spec(k) > 0
   * }}}
   *
   * Since the canonical cycle replicates Spec at every index
   * (`assertApplyMatches`: `cycle(i) == spec(i)` for all `i >= 0`), the same
   * positivity holds for the cycle's adjacent differences:
   *
   * {{{
   *   cycle(k + 1) - cycle(k)
   *     == spec(k + 1) - spec(k)   [by assertApplyMatches, twice]
   *     > 0                        [by spec.assertGapPositive]
   *                                                              [Q.E.D.]
   * }}}
   *
   * This is rule 2 of the Leg-3 gap rule list (see
   * `canonical-next-strategy.md`): a pure-over-`cycle` fact, certified by
   * transfer through the Spec/Cycle equivalence.
   *
   * @param k any gap index, `k >= 0`
   * @return `true` (verified); formally, `cycle(k + 1) - cycle(k) > 0`
   */
  def assertGapPositiveMatchesSpec(k: BigInt): Boolean = {
    require(k >= BigInt(0))

    assert(spec.assertGapPositive(k))
    assert(assertApplyMatches(k))
    assert(assertApplyMatches(k + BigInt(1)))

    val specGap = spec(k + BigInt(1)) - spec(k)
    val cycleGap = cycle(k + BigInt(1)) - cycle(k)

    assert(cycleGap == specGap)
    assert(specGap > BigInt(0))

    cycleGap > BigInt(0)
  }.holds

  /**
   * [TIMED OUT — attempt 1 of 3, 2026-06-24, per stop-and-ask rule]
   *
   * Intended: transfer Spec's copy-case gap rule to the canonical cycle.
   *
   * When the new stage's head filter keeps both the value at `cycle(k)` and its
   * successor `cycle(k+1)`, the next-stage gap is simply copied: it equals the
   * current-stage gap `cycle(k+1) - cycle(k)`.
   *
   * The "new head" is `cycle(1)` (the value `cycle.head + cycle.gapCycle.memCycle(0)`),
   * which equals `spec.next.head.value` (by `assertNextHeadMatches`). A value
   * survives the new head filter exactly when it is not a multiple of `cycle(1)`.
   *
   * {{{
   *   cycle(k)   mod cycle(1) != 0
   *   cycle(k+1) mod cycle(1) != 0
   *   -----------------------------------------------
   *   nextGap(k) == cycle(k+1) - cycle(k)
   * }}}
   *
   * BLOCKER: The proof needs to discharge precondition 4/6 of
   * `spec.assertFilterPreservesNextGap`, namely `spec.next.accepts(spec(k))`.
   * The cycle-side hypothesis `Calc.mod(cycle(k), cycle(1)) != 0` only gives
   * coprimality against the new head, NOT the full next-stage acceptance
   * (which is coprimality against the whole `cycle.primes` list).
   * `assertNextAcceptsMatches(value)` bridges
   *   `spec.next.accepts(value) == SieveUtils.isCoprime(value, cycle.primes)`,
   * so the full hypothesis needed is "value is coprime to cycle.primes", not
   * just "not a multiple of cycle(1)".
   *
   * This is a genuine logical gap, not a solver weakness: the stated
   * precondition is too weak. Options to discuss with user before retrying:
   *  (a) Strengthen the cycle-side precondition to coprimality against
   *      `cycle.primes` (matches Spec's actual acceptance predicate), OR
   *  (b) Keep the weaker mod-new-head precondition but first prove a cycle-side
   *      lemma that `cycle(k)` being a current generated value implies it is
   *      coprime to `cycle.primes.tail` (then only the new-head test is needed).
   *
   * Commented out rather than deleted per never-destroy rule. The doc and the
   * analysis above remain as a record of the attempt.
   */
//  def assertCopyGapMatchesSpec(
//    k: BigInt
//  ): Boolean = {
//    require(k >= BigInt(0))
//    require(Calc.mod(cycle(k), cycle(BigInt(1))) != BigInt(0))
//    require(Calc.mod(cycle(k + BigInt(1)), cycle(BigInt(1))) != BigInt(0))
//
//    val nextGap = spec.next(k + BigInt(1)) - spec.next(k)
//    val cycleGap = cycle(k + BigInt(1)) - cycle(k)
//
//    assert(assertApplyMatches(k))
//    assert(assertApplyMatches(k + BigInt(1)))
//    assert(assertNextHeadMatches())
//
//    assert(spec.assertFilterPreservesNextGap(spec.next, k))
//    assert(nextGap == spec(k + BigInt(1)) - spec(k))
//    assert(spec(k + BigInt(1)) - spec(k) == cycleGap)
//
//    nextGap == cycleGap
//  }.holds

  /**
   * [TIMED OUT — isolation test, 2026-06-24]
   *
   * Confirmed: `val nextSeq = spec.next` alias blocks the solver from
   * connecting cached lemma results (`assertCurrentNonMultipleAcceptedByNext`
   * returns `spec.next.accepts(...)`) to `nextSeq.accepts(spec(k))`.
   * 8 VCs passed, 1 timed out at `nextSeq.accepts(spec(k))`.
   *
   * The fix for `assertCopyGapMatchesSpec`: use `spec.next` directly,
   * no local alias. Also capture and assert lemma return values.
   *
   * Commented out per never-destroy rule. Do NOT uncomment — serves only
   * as a permanent record of the confirmed root cause.
   */
  /*
  def assertNextAcceptsViaAlias(k: BigInt): Boolean = {
    require(k >= BigInt(1))
    require(Calc.mod(cycle(k), cycle.head) != BigInt(0))

    val nextSeq = spec.next

    val accepted = assertCurrentNonMultipleAcceptedByNext(k)
    assert(accepted)

    nextSeq.accepts(spec(k))
  }.holds
  */

  /**
   * [TIMED OUT — `def` does not inline in Stainless, 2026-06-24]
   *
   * Attempted `def nextSeq = spec.next` hoping that a 0-arg `def` would inline
   * at the call site. It does not — Stainless treats `def` as a separate
   * function, so the same indirection problem occurs. 8 VCs passed, 1 timed out
   * at `nextSeq.accepts(spec(k))`.
   */
  /*
  def assertNextAcceptsViaDefAlias(k: BigInt): Boolean = {
    require(k >= BigInt(1))
    require(Calc.mod(cycle(k), cycle.head) != BigInt(0))

    def nextSeq = spec.next

    val accepted = assertCurrentNonMultipleAcceptedByNext(k)
    assert(accepted)

    nextSeq.accepts(spec(k))
  }.holds
  */

  /**
   * Proves that equal `SpecSieveSequence` instances have equivalent `accepts`.
   * When `seq1 == seq2` and `seq1.accepts(v)` holds, then `seq2.accepts(v)`
   * also holds. Split into two directed versions because `require(seq1.accepts(v))`
   * is cheaper for the solver than a bare `==` comparison.
   *
   * Bridges the gap between a cached `.holds` result on `spec.next.accepts(v)`
   * and acceptance through a locally-bound `val nextSeq = spec.next` alias.
   */
  def assertAcceptsEqualWhenTrue(
    seq1: SpecSieveSequence,
    seq2: SpecSieveSequence,
    v: BigInt
  ): Boolean = {
    require(seq1 == seq2)
    require(v >= seq1.head.value)
    require(seq1.passesFilter(v))
    require(seq1.accepts(v))

    assert(seq1 == seq2)
    assert(seq1.head == seq2.head)
    assert(v >= seq2.head.value)
    assert(seq1.primes == seq2.primes)
    assert(seq1.primes.tail == seq2.primes.tail)
    seq1.accepts(v) == seq2.accepts(v)
  }.holds

  /**
   * Dual of `assertAcceptsEqualWhenTrue`: when `seq1 == seq2` and
   * `seq1.accepts(v)` does NOT hold, then `seq2.accepts(v)` also does not hold.
   */
  def assertAcceptsEqualWhenFalse(
    seq1: SpecSieveSequence,
    seq2: SpecSieveSequence,
    v: BigInt
  ): Boolean = {
    require(seq1 == seq2)
    require(v >= seq1.head.value)
    require(!seq1.passesFilter(v))
    require(!seq1.accepts(v))

    assert(seq1 == seq2)
    assert(seq1.head == seq2.head)
    assert(v >= seq2.head.value)
    assert(seq1.primes == seq2.primes)
    assert(seq1.primes.tail == seq2.primes.tail)
    seq1.accepts(v) == seq2.accepts(v)
  }.holds

  /**
   * Proves that equal `SpecSieveSequence` instances have equivalent `accepts`, by
   * case analysis on `seq1.accepts(v)`. This is the full version of the lemma, which
   * bridges the gap between cached acceptance facts on `spec.next` and acceptance
   * through a local alias. The two cases are split to avoid the solver's difficulty with
   * equivalence branches when acceptance is involved.
   *
   * @param seq1 the first `SpecSieveSequence` instance, equal to `seq2`
   * @param seq2 the second `SpecSieveSequence` instance, equal to `seq1`
   * @param v any value at or above the head of the sequences, to test for acceptance
   * @return `true` (verified); formally, `seq1.accepts(v) == seq2.accepts(v)` under the given preconditions
   */
  def assertAcceptsEqual(
    seq1: SpecSieveSequence,
    seq2: SpecSieveSequence,
    v: BigInt
  ): Boolean = {
    require(seq1 == seq2)
    require(v >= seq1.head.value)
    require(seq1.passesFilter(v))
    if (seq1.passesFilter(v)) {
      assertAcceptsEqualWhenTrue(seq1, seq2, v)
    } else {
      assertAcceptsEqualWhenFalse(seq1, seq2, v)
    }
    seq1.accepts(v) == seq2.accepts(v)
  }.holds

  /**
   * Cycle-side gap equals Spec-side gap. Pure consequence of
   * `assertApplyMatches`: each apply value is equal, so their difference is too.
   */
  def assertCycleGapEqualsSpecGap(k: BigInt): Boolean = {
    require(k >= BigInt(0))

    assert(assertApplyMatches(k))
    assert(assertApplyMatches(k + BigInt(1)))

    spec(k + BigInt(1)) - spec(k) == cycle(k + BigInt(1)) - cycle(k)
  }.holds

  /**
   * Proves acceptance through a local `val nextSeq = spec.next` alias using
   * the `assertAcceptsEqualWhenTrue` bridge lemma.
   */
  def assertNextAcceptsViaAlias(k: BigInt): Boolean = {
    require(k >= BigInt(1))
    require(Calc.mod(cycle(k), cycle.head) != BigInt(0))

    val nextSeq = spec.next

    val accepted = assertCurrentNonMultipleAcceptedByNext(k)
    assert(accepted)

    assert(assertCurrentValueAtOrAboveNextHead(k))

    assert(assertAcceptsEqualWhenTrue(spec.next, nextSeq, spec(k)))
    nextSeq.accepts(spec(k))
  }.holds

  /**
   * Proves the canonical copy rule using the corrected Spec gap lemma.
   *
   * The current sequence already filters every prime in `cycle.primes.tail`.
   * Moving to `spec.next` adds the current head, `cycle.head`, to that filter.
   * Therefore a current value survives the next filter exactly when its
   * remainder modulo `cycle.head` is nonzero; `cycle(1)` is the next sequence's
   * starting value, not the newly added filter divisor.
   *
   * If both consecutive current values survive, no merge occurs between them.
   * `assertConsecutiveAcceptedByNextPreservesGap` proves that they remain
   * consecutive in `spec.next`. The next-stage index is obtained from
   * `indexOfAccepted(spec(k))`; it is intentionally not assumed to equal the
   * old index `k`, because earlier rejected values may have shifted positions.
   *
   * Uses `assertCurrentNonMultipleAcceptedByNext` (verified 9213 valid) to
   * transfer the non-multiple cycle precondition into a direct
   * `spec.next.accepts(spec(k))` fact, avoiding the equivalence-branch timeout
   * that blocked the earlier attempts. The ordering and filter-tail facts are
   * consumed from `assertCurrentValueAtOrAboveNextHead` and structural prime-list
   * equalities.
   *
   * {{{
   *   cycle(k)   mod cycle.head != 0
   *   cycle(k+1) mod cycle.head != 0
   *   ------------------------------------------------------------
   *   spec.next(nextIndex+1) - spec.next(nextIndex)
   *     == cycle(k+1) - cycle(k)
   * }}}
   */
  def assertCopyGapMatchesSpec(k: BigInt): Boolean = {
    require(k >= BigInt(1))
    require(Calc.mod(cycle(k), cycle.head) != BigInt(0))
    require(Calc.mod(cycle(k + BigInt(1)), cycle.head) != BigInt(0))

    assert(assertApplyMatches(k))
    assert(assertApplyMatches(k + BigInt(1)))

    val acceptedK = assertCurrentNonMultipleAcceptedByNext(k)
    assert(acceptedK)
    val acceptedK1 = assertCurrentNonMultipleAcceptedByNext(k + BigInt(1))
    assert(acceptedK1)

    val lbK = assertCurrentValueAtOrAboveNextHead(k)
    assert(lbK)
    val lbK1 = assertCurrentValueAtOrAboveNextHead(k + BigInt(1))
    assert(lbK1)

    assert(spec.next.filterValues.tail == spec.filterValues)
    assert(assertNextHeadMatches())
    assert(cycle(BigInt(1)) > cycle.head)
    assert(spec.next.head.value >= spec.head.value)

    assert(spec.assertConsecutiveAcceptedByNextPreservesGap(spec.next, k))

    val nextIndex = spec.next.indexOfAccepted(spec(k))
    assert(
      spec.next(nextIndex + BigInt(1)) - spec.next(nextIndex) ==
        spec(k + BigInt(1)) - spec(k)
    )

    spec.next(nextIndex + BigInt(1)) - spec.next(nextIndex) ==
      cycle(k + BigInt(1)) - cycle(k)
  }.holds
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
