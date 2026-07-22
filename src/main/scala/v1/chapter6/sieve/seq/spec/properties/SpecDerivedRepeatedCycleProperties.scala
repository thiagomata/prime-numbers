package v1.chapter6.sieve.seq.spec.properties

import stainless.lang.*
import v1.chapter2.div.Calc
import v1.chapter3.list.ListBoundUtils
import v1.chapter3.list.properties.ListRepeatProperties
import v1.chapter4.cycle.gap.GapCycle
import v1.chapter4.cycle.integral.recursive.CycleIntegral
import v1.chapter4.cycle.integral.recursive.properties.{CycleIntegralFilterProperties, CycleIntegralProperties, RepeatedGapIntegralProperties}
import v1.chapter4.cycle.memory.MemCycle
import v1.chapter5.prime.Prime
import v1.chapter5.prime.properties.FilterPreservesPrimesProperties
import v1.chapter6.sieve.seq.spec.SpecSieveSequence

/**
 * Lemmas about the gap cycle that is repeated `head` times before filtering.
 *
 * Proof chain position (Goal 3 revision, flat step numbering):
 *   Step 1:  spec == cycle                          (SpecSieveSeqPeriodProperties)
 *   Step 2:  specRepeatedCycleIntegral constructor  (HERE)
 *   Step 3:  period = period * head                 (HERE)
 *   Step 4:  repeatedCI(k) == baseCI(k)             (HERE)
 *   Step 5:  filter equality                        (HERE)
 *   ...
 *
 * Architecture: stateless object, no chapter6 imports, depends only on
 * chapter3/4 and chapter6's own SpecSieveSequence + PeriodProperties.
 */
object SpecDerivedRepeatedCycleProperties {

  /**
   * Constructs the CycleIntegral that repeats the spec's gap cycle `head` times.
   *
   * This covers exactly one period of `spec.next` (primorial = tailPrimorial * head).
   * The ensuring clause exports the two facts needed by all downstream lemmas:
   *   (a) initialValue == seq.head.value
   *   (b) cycle.values == repeat(specGapCycle.memCycle.values, head)
   */
  def specRepeatedCycleIntegral(seq: SpecSieveSequence, period: BigInt): CycleIntegral = {
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)

    val gapCycle = SpecSieveSeqPeriodProperties.specGapCycle(seq, period)

    // base gaps are positive and non-empty (GapCycle invariant)
    assert(GapCycle.assertMemCycleValuesPositive(gapCycle))
    assert(ListBoundUtils.allGreaterThan(gapCycle.memCycle.values, BigInt(0)))
    assert(gapCycle.memCycle.values.nonEmpty)

    // all primes are >= 2, so head > 0
    assert(seq.head.value > BigInt(0))

    // repeat preserves the positivity bound element-wise
    val repeatedGaps = ListRepeatProperties.repeat(gapCycle.memCycle.values, seq.head.value)
    assert(ListRepeatProperties.assertRepeatAllGreaterThan(
      gapCycle.memCycle.values, seq.head.value, BigInt(0)))
    assert(ListBoundUtils.allGreaterThan(repeatedGaps, BigInt(0)))

    // size = values.size * head > 0, so non-empty
    assert(ListRepeatProperties.assertRepeatSize(gapCycle.memCycle.values, seq.head.value))
    assert(repeatedGaps.size == gapCycle.memCycle.values.size * seq.head.value)
    assert(repeatedGaps.nonEmpty)

    // bridge allGreaterThan(> 0) → checkPositiveOrZero (required by MemCycle constructor)
    assert(GapCycle.assertAllGreaterThanImpliesCheckPositiveOrZero(repeatedGaps))

    CycleIntegral(seq.head.value, MemCycle(repeatedGaps))
  }.ensuring(result =>
    result.initialValue == seq.head.value &&
    result.cycle.values == ListRepeatProperties.repeat(
      SpecSieveSeqPeriodProperties.specGapCycle(seq, period).memCycle.values,
      seq.head.value
    )
  )

  /**
   * The repeated cycle has period = original period * head.
   *
   * This must be stated as its own lemma **before** the filter step.
   * The survivor-count argument (T' = T*(head-1)) counts elements within
   * a window of `period * head` positions — without this explicit period fact
   * the verifier has no anchor for the window size and cannot confirm the
   * filtered element count.
   */
  def assertSpecRepeatedCyclePeriodIsHeadTimesPeriod(
    seq: SpecSieveSequence,
    period: BigInt
  ): Boolean = {
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)

    val gapCycle   = SpecSieveSeqPeriodProperties.specGapCycle(seq, period)
    val repeatedCI = specRepeatedCycleIntegral(seq, period)

    // gapCycle.memCycle.values.size == period
    // (specGapCycle ensuring: memCycle.values == gapList(seq,0,period);
    //  assertGapListSize: gapList.size == period)
    assert(SpecSieveSeqPeriodProperties.assertGapListSize(seq, BigInt(0), period))

    // all primes >= 2, so head > 0
    assert(seq.head.value > BigInt(0))

    // repeat(..., head).size == values.size * head == period * head
    assert(ListRepeatProperties.assertRepeatSize(gapCycle.memCycle.values, seq.head.value))

    // repeatedCI.cycle.values == repeat(gapCycle.memCycle.values, head) [from ensuring]
    // repeatedCI.period       == repeatedCI.cycle.values.size           [by definition]
    //                         == period * head
    repeatedCI.period == period * seq.head.value
  }.holds

  /**
   * Step 4: pointwise value equality — repeated CI and base CI agree at every position.
   *
   * `specRepeatedCycleIntegral` repeats `gapCycle.memCycle` `head` times with the
   * same initial value; `assertRepeatedValuesIntegralMatches` (ch4) proves that
   * repeating does not change the integral values.
   */
  def assertSpecRepeatedCycleIntegralMatchesBase(
    seq: SpecSieveSequence,
    period: BigInt,
    k: BigInt
  ): Boolean = {
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(k >= BigInt(0))

    val gapCycle   = SpecSieveSeqPeriodProperties.specGapCycle(seq, period)
    val baseCI     = CycleIntegral(seq.head.value, gapCycle.memCycle)
    val repeatedCI = specRepeatedCycleIntegral(seq, period)

    // base cycle period > 0
    assert(GapCycle.assertMemCyclePeriodPositive(gapCycle))

    // head > 0 (prime)
    assert(seq.head.value > BigInt(0))

    // delegate to ch4 generic lemma:
    // requires repeated.initialValue == original.initialValue  ← both seq.head.value (from ensuring)
    // requires repeated.cycle.values == repeat(original.cycle.values, head)
    //          ← ensuring gives repeat(gapCycle.memCycle.values, head)
    //            and baseCI.cycle == gapCycle.memCycle so baseCI.cycle.values == gapCycle.memCycle.values
    assert(RepeatedGapIntegralProperties.assertRepeatedValuesIntegralMatches(
      baseCI, repeatedCI, seq.head.value, k
    ))

    repeatedCI(k) == baseCI(k)
  }.holds

  /**
   * Step 3: the survivor lists of the base CI and the repeated CI are identical.
   *
   * Because `repeatedCI(k) == baseCI(k)` at every position, each step of
   * `survivorValues` takes the same branch in both integrals, giving equal lists.
   * This must be proven before the filter — it is the bridge from value equality
   * to list equality that feeds the next stage's gap construction.
   */
  def assertSpecBaseAndRepeatedSurvivorValuesMatch(
    seq: SpecSieveSequence,
    period: BigInt,
    startPos: BigInt,
    count: BigInt
  ): Boolean = {
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(startPos >= BigInt(0))
    require(count >= BigInt(0))
    decreases(count)

    val gapCycle   = SpecSieveSeqPeriodProperties.specGapCycle(seq, period)
    val baseCI     = CycleIntegral(seq.head.value, gapCycle.memCycle)
    val repeatedCI = specRepeatedCycleIntegral(seq, period)

    assert(seq.head.value > BigInt(0))

    if (count == BigInt(0)) {
      CycleIntegralFilterProperties.survivorValues(
        repeatedCI, seq.head.value, startPos, count) ==
      CycleIntegralFilterProperties.survivorValues(
        baseCI, seq.head.value, startPos, count)
    } else {
      assert(assertSpecRepeatedCycleIntegralMatchesBase(seq, period, startPos))
      assert(repeatedCI(startPos) == baseCI(startPos))
      assert(assertSpecBaseAndRepeatedSurvivorValuesMatch(
        seq, period, startPos + BigInt(1), count - BigInt(1)))
      CycleIntegralFilterProperties.survivorValues(
        repeatedCI, seq.head.value, startPos, count) ==
      CycleIntegralFilterProperties.survivorValues(
        baseCI, seq.head.value, startPos, count)
    }
  }.holds

  /**
   * Step 4: gaps of the survivor lists are equal.
   *
   * Direct corollary of Step 3: equal lists → equal gapsFromValues output.
   */
  def assertSpecBaseAndRepeatedGapListMatch(
    seq: SpecSieveSequence,
    period: BigInt
  ): Boolean = {
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)

    val gapCycle   = SpecSieveSeqPeriodProperties.specGapCycle(seq, period)
    val baseCI     = CycleIntegral(seq.head.value, gapCycle.memCycle)
    val repeatedCI = specRepeatedCycleIntegral(seq, period)
    val count      = period * seq.head.value

    assert(seq.head.value > BigInt(0))

    val baseSurvivors = CycleIntegralFilterProperties.survivorValues(
      baseCI, seq.head.value, BigInt(0), count)
    val repSurvivors  = CycleIntegralFilterProperties.survivorValues(
      repeatedCI, seq.head.value, BigInt(0), count)

    assert(assertSpecBaseAndRepeatedSurvivorValuesMatch(seq, period, BigInt(0), count))
    assert(baseSurvivors == repSurvivors)

    if (baseSurvivors.isEmpty) {
      baseSurvivors == repSurvivors
    } else {
      assert(repSurvivors.nonEmpty)
      CycleIntegralFilterProperties.gapsFromValues(baseSurvivors) ==
        CycleIntegralFilterProperties.gapsFromValues(repSurvivors)
    }
  }.holds

  /**
   * Step 7: the base CI at position k equals seq.apply(k+1).
   *
   * This is the shift lemma: `CycleIntegral(head, gapCycle.memCycle)(k) == seq.apply(k+1)`.
   * Direct corollary of `assertSpecGapCycleIntegralMatchesApply` (which concludes
   * `integral(k-1) == seq.apply(k)` for k > 0, equivalently `integral(k) == seq.apply(k+1)`).
   */
  def assertBaseCIEqualsSeqApplyShifted(
    seq: SpecSieveSequence,
    period: BigInt,
    k: BigInt
  ): Boolean = {
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(k >= BigInt(0))

    val gapCycle = SpecSieveSeqPeriodProperties.specGapCycle(seq, period)
    val baseCI   = CycleIntegral(seq.head.value, gapCycle.memCycle)

    assert(SpecSieveSeqPeriodProperties.assertSpecGapCycleIntegralMatchesApply(
      seq, period, k + BigInt(1)))

    baseCI(k) == seq.apply(k + BigInt(1))
  }.holds

  /**
   * Step 8: the first survivor of baseCI equals nextSeq.head.value.
   *
   * `seq.apply(1)` is the next prime after seq.head.value (from assertApplyOneEqualsNextPrime).
   * Distinct primes are not divisible by each other, so `seq.apply(1) % head != 0`.
   * Therefore `baseCI(0) = seq.apply(1)` is the first survivor.
   * And `nextSeq.head.value = seq.apply(1)` = `nextSeq.apply(0)`.
   */
  def assertFirstSurvivorMatchesNextSeqHead(
    seq: SpecSieveSequence,
    nextSeq: SpecSieveSequence,
    period: BigInt
  ): Boolean = {
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(seq.primes.nextPrime.value < seq.head.value * seq.head.value)
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.head == seq.head.value)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(nextSeq.head.value == seq.apply(BigInt(1)))

    val gapCycle  = SpecSieveSeqPeriodProperties.specGapCycle(seq, period)
    val baseCI    = CycleIntegral(seq.head.value, gapCycle.memCycle)
    val count     = period * seq.head.value

    // baseCI(0) = seq.apply(1)
    assert(assertBaseCIEqualsSeqApplyShifted(seq, period, BigInt(0)))
    assert(baseCI(BigInt(0)) == seq.apply(BigInt(1)))

    // seq.apply(1) is a prime different from seq.head.value → not a multiple of it
    assert(SpecSieveSeqHeadIsPrime.assertApplyOneEqualsNextPrime(seq))
    assert(Prime.isPrime(seq.apply(BigInt(1))))
    assert(seq.apply(BigInt(1)) > seq.head.value)
    assert(seq.apply(BigInt(1)) != seq.head.value)
    assert(Prime.isPrime(seq.head.value))
    assert(FilterPreservesPrimesProperties.assertPrimeNotDivisibleByDistinctPrime(
      seq.apply(BigInt(1)), seq.head.value))
    assert(Calc.mod(seq.apply(BigInt(1)), seq.head.value) != BigInt(0))
    assert(Calc.mod(baseCI(BigInt(0)), seq.head.value) != BigInt(0))

    // count > 0, so survivorValues is non-trivial; first element = baseCI(0)
    assert(count > BigInt(0))

    val survivors = CycleIntegralFilterProperties.survivorValues(
      baseCI, seq.head.value, BigInt(0), count)

    // nextSeq.apply(0) = nextSeq.head.value = seq.apply(1) = baseCI(0) = survivors.head
    assert(nextSeq.apply(BigInt(0)) == nextSeq.head.value)
    assert(nextSeq.head.value == seq.apply(BigInt(1)))

    survivors.head == nextSeq.apply(BigInt(0))
  }.holds

}
