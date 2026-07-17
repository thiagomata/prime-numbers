package v1.chapter60.sieve.seq.spec.properties

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
import v1.chapter60.sieve.seq.spec.SpecSieveSequence

/**
 * Lemmas about the gap cycle that is repeated `head` times before filtering.
 *
 * Proof chain position (Goal 3 revision):
 *   Step 1: spec == cycle                (SpecSieveSeqPeriodProperties)
 *   Step 2: spec == repeated(cycle,head) (HERE — period established before filter)
 *   Step 3: filter(spec) == filter(repeated(cycle,head))
 *   ...
 *
 * Architecture: stateless object, no chapter6 imports, depends only on
 * chapter3/4 and chapter60's own SpecSieveSequence + PeriodProperties.
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
   * Step 2c: pointwise value equality — repeated CI and base CI agree at every position.
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
   * Step 5a: the base CI at position k equals seq.apply(k+1).
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
   * Step 5b: the first survivor of baseCI equals nextSeq.head.value.
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

  /**
   * Step 5c helper: from structural requirements on nextSeq,
   * seq.passesFilter(v) + v % head != 0 + v >= nextSeq.head.value
   *   → nextSeq.accepts(v).
   *
   * Proof: nextSeq.filterValues = head :: seq.filterValues (from structural requires).
   * By the recursive definition of isCoprime:
   *   isCoprime(v, head :: rest) = (v % head != 0) && isCoprime(v, rest)
   * So nextSeq.passesFilter(v) = (v % head != 0) && seq.passesFilter(v).
   */
  def assertAcceptedByNextGivenStructure(
    seq: SpecSieveSequence,
    nextSeq: SpecSieveSequence,
    v: BigInt
  ): Boolean = {
    require(v >= nextSeq.head.value)
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.head == seq.head.value)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(seq.passesFilter(v))
    require(Calc.mod(v, seq.head.value) != BigInt(0))

    nextSeq.accepts(v)
  }.holds

  // ── Step 5c helpers ───────────────────────────────────────────────────

  /**
   * Lemma A: every survivor is seq-accepted.
   *
   * Mirrors assertSurvivorAtNotMultiple (ch4) but proves seq.accepts instead
   * of non-divisibility. The base case uses assertFirstSurvivorHead +
   * assertBaseCIEqualsSeqApplyShifted + the .ensuring clause of apply.
   */
  def assertSurvivorAtIsSeqAccepted(
    seq: SpecSieveSequence,
    period: BigInt,
    startPos: BigInt,
    count: BigInt,
    index: BigInt
  ): Boolean = {
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(startPos >= BigInt(0))
    require(count >= BigInt(0))
    require(index >= BigInt(0))
    val gapCycle  = SpecSieveSeqPeriodProperties.specGapCycle(seq, period)
    val baseCI    = CycleIntegral(seq.head.value, gapCycle.memCycle)
    val survivors = CycleIntegralFilterProperties.survivorValues(
      baseCI, seq.head.value, startPos, count)
    require(index < survivors.size)
    decreases(count)

    if (count == BigInt(0)) {
      true
    } else if (Calc.mod(baseCI(startPos), seq.head.value) != BigInt(0)) {
      if (index == BigInt(0)) {
        assert(CycleIntegralFilterProperties.assertFirstSurvivorHead(
          baseCI, seq.head.value, startPos, count))
        assert(assertBaseCIEqualsSeqApplyShifted(seq, period, startPos))
        val applyAtNext = seq.apply(startPos + BigInt(1))
        assert(seq.accepts(applyAtNext))
        assert(survivors.head == applyAtNext)
      } else {
        assertSurvivorAtIsSeqAccepted(
          seq, period, startPos + BigInt(1), count - BigInt(1), index - BigInt(1))
      }
    } else {
      assertSurvivorAtIsSeqAccepted(
        seq, period, startPos + BigInt(1), count - BigInt(1), index)
    }
    seq.accepts(survivors(index))
  }.holds

  /**
   * Lemma B: every survivor value is >= baseCI at the scan start.
   *
   * Uses assertCycleIntegralIncreasing: since all gap values are positive,
   * CI is strictly increasing, so any CI value at position >= startPos is
   * >= CI(startPos). The base case (index=0) gives equality.
   */
  def assertSurvivorGEQStartCI(
    seq: SpecSieveSequence,
    period: BigInt,
    startPos: BigInt,
    count: BigInt,
    index: BigInt
  ): Boolean = {
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(startPos >= BigInt(0))
    require(count >= BigInt(0))
    require(index >= BigInt(0))
    val gapCycle  = SpecSieveSeqPeriodProperties.specGapCycle(seq, period)
    val baseCI    = CycleIntegral(seq.head.value, gapCycle.memCycle)
    val survivors = CycleIntegralFilterProperties.survivorValues(
      baseCI, seq.head.value, startPos, count)
    require(index < survivors.size)
    decreases(count)

    assert(GapCycle.assertMemCycleValuesPositive(gapCycle))
    assert(ListBoundUtils.allGreaterThan(gapCycle.memCycle.values, BigInt(0)))
    assert(gapCycle.memCycle.values.nonEmpty)
    assert(seq.head.value > BigInt(0))
    assert(GapCycle.assertMemCyclePeriodPositive(gapCycle))

    if (count == BigInt(0)) {
      true
    } else if (Calc.mod(baseCI(startPos), seq.head.value) != BigInt(0)) {
      if (index == BigInt(0)) {
        assert(CycleIntegralFilterProperties.assertFirstSurvivorHead(
          baseCI, seq.head.value, startPos, count))
      } else {
        assert(assertSurvivorGEQStartCI(
          seq, period, startPos + BigInt(1), count - BigInt(1), index - BigInt(1)))
        assert(CycleIntegralProperties.assertCycleIntegralIncreasing(
          baseCI, startPos, startPos + BigInt(1)))
      }
    } else {
      assert(assertSurvivorGEQStartCI(
        seq, period, startPos + BigInt(1), count - BigInt(1), index))
      assert(CycleIntegralProperties.assertCycleIntegralIncreasing(
        baseCI, startPos, startPos + BigInt(1)))
    }
    baseCI(startPos) <= survivors(index)
  }.holds

  /**
   * Lemma C: every survivor value is <= baseCI at the scan end position.
   *
   * Since survivors are CI values at positions in [startPos, startPos+count),
   * and CI is strictly increasing, each survivor is <= the last CI value
   * in the scan window (at position startPos + count - 1).
   */
  def assertSurvivorLEQEndCI(
    seq: SpecSieveSequence,
    period: BigInt,
    startPos: BigInt,
    count: BigInt,
    index: BigInt
  ): Boolean = {
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(startPos >= BigInt(0))
    require(count >= BigInt(0))
    require(index >= BigInt(0))
    val gapCycle  = SpecSieveSeqPeriodProperties.specGapCycle(seq, period)
    val baseCI    = CycleIntegral(seq.head.value, gapCycle.memCycle)
    val survivors = CycleIntegralFilterProperties.survivorValues(
      baseCI, seq.head.value, startPos, count)
    require(index < survivors.size)
    decreases(count)

    assert(GapCycle.assertMemCycleValuesPositive(gapCycle))
    assert(ListBoundUtils.allGreaterThan(gapCycle.memCycle.values, BigInt(0)))
    assert(gapCycle.memCycle.values.nonEmpty)
    assert(seq.head.value > BigInt(0))
    assert(GapCycle.assertMemCyclePeriodPositive(gapCycle))

    if (count == BigInt(0)) {
      true
    } else if (Calc.mod(baseCI(startPos), seq.head.value) != BigInt(0)) {
      if (index == BigInt(0)) {
        assert(CycleIntegralFilterProperties.assertFirstSurvivorHead(
          baseCI, seq.head.value, startPos, count))
        if (count > BigInt(1)) {
          assert(CycleIntegralProperties.assertCycleIntegralIncreasing(
            baseCI, startPos, startPos + count - BigInt(1)))
        }
      } else {
        assert(assertSurvivorLEQEndCI(
          seq, period, startPos + BigInt(1), count - BigInt(1), index - BigInt(1)))
      }
    } else {
      assert(assertSurvivorLEQEndCI(
        seq, period, startPos + BigInt(1), count - BigInt(1), index))
    }
    survivors(index) <= baseCI(startPos + count - BigInt(1))
  }.holds

  /**
   * Lemma D: every survivor of baseCI is accepted by nextSeq = seq.next.
   *
   * Combines Lemma A (seq-accepted) + assertSurvivorAtNotMultiple (not head-multiple)
   * + Lemma B (value >= nextSeq.head.value) to call
   * assertOldAcceptedHeadNonMultipleAcceptedByNext.
   */
  def assertSurvivorIsNextSeqAccepted(
    seq: SpecSieveSequence,
    period: BigInt,
    index: BigInt
  ): Boolean = {
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(seq.primes.nextPrime.value < seq.head.value * seq.head.value)
    require(index >= BigInt(0))
    val gapCycle  = SpecSieveSeqPeriodProperties.specGapCycle(seq, period)
    val baseCI    = CycleIntegral(seq.head.value, gapCycle.memCycle)
    val count     = period * seq.head.value
    val survivors = CycleIntegralFilterProperties.survivorValues(
      baseCI, seq.head.value, BigInt(0), count)
    require(index < survivors.size)

    val nextSeq = seq.next

    // survivors(index) is seq-accepted (Lemma A)
    assert(assertSurvivorAtIsSeqAccepted(seq, period, BigInt(0), count, index))
    assert(seq.accepts(survivors(index)))

    // survivors(index) % head != 0 (ch4 lemma)
    assert(CycleIntegralFilterProperties.assertSurvivorAtNotMultiple(
      baseCI, seq.head.value, BigInt(0), count, index))
    assert(Calc.mod(survivors(index), seq.head.value) != BigInt(0))

    // survivors(index) >= baseCI(0) = seq.apply(1) = nextSeq.head.value (Lemma B)
    assert(assertSurvivorGEQStartCI(seq, period, BigInt(0), count, index))
    assert(baseCI(BigInt(0)) <= survivors(index))
    assert(assertBaseCIEqualsSeqApplyShifted(seq, period, BigInt(0)))
    assert(baseCI(BigInt(0)) == seq.apply(BigInt(1)))
    assert(seq.apply(BigInt(1)) == nextSeq.head.value)
    assert(survivors(index) >= nextSeq.head.value)

    // Combine via assertOldAcceptedHeadNonMultipleAcceptedByNext
    assert(SpecSieveSeqNextProperties.assertOldAcceptedHeadNonMultipleAcceptedByNext(
      seq, survivors(index)))

    nextSeq.accepts(survivors(index))
  }.holds

  /**
   * Lemma E: survivor list is strictly increasing.
   *
   * Since CI is strictly increasing and survivors are CI values at strictly
   * increasing positions, consecutive survivors are strictly ordered.
   */
  def assertSurvivorStrictlyIncreases(
    seq: SpecSieveSequence,
    period: BigInt,
    startPos: BigInt,
    count: BigInt,
    index: BigInt
  ): Boolean = {
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(startPos >= BigInt(0))
    require(count >= BigInt(0))
    require(index >= BigInt(0))
    val gapCycle  = SpecSieveSeqPeriodProperties.specGapCycle(seq, period)
    val baseCI    = CycleIntegral(seq.head.value, gapCycle.memCycle)
    val survivors = CycleIntegralFilterProperties.survivorValues(
      baseCI, seq.head.value, startPos, count)
    require(index + BigInt(1) < survivors.size)
    decreases(count)

    assert(GapCycle.assertMemCycleValuesPositive(gapCycle))
    assert(ListBoundUtils.allGreaterThan(gapCycle.memCycle.values, BigInt(0)))
    assert(gapCycle.memCycle.values.nonEmpty)
    assert(seq.head.value > BigInt(0))
    assert(GapCycle.assertMemCyclePeriodPositive(gapCycle))

    if (Calc.mod(baseCI(startPos), seq.head.value) != BigInt(0)) {
      if (index == BigInt(0)) {
        // survivors(0) = baseCI(startPos), survivors(1) = tail(0) >= baseCI(startPos+1) > baseCI(startPos)
        assert(CycleIntegralFilterProperties.assertFirstSurvivorHead(
          baseCI, seq.head.value, startPos, count))
        // survivors.head == baseCI(startPos)
        assert(assertSurvivorGEQStartCI(
          seq, period, startPos + BigInt(1), count - BigInt(1), BigInt(0)))
        // baseCI(startPos+1) <= tail(0) = survivors(1)
        assert(CycleIntegralProperties.assertCycleIntegralIncreasing(
          baseCI, startPos, startPos + BigInt(1)))
        // baseCI(startPos) < baseCI(startPos+1)
      } else {
        // survivors(index) = tail(index-1), survivors(index+1) = tail(index)
        assert(assertSurvivorStrictlyIncreases(
          seq, period, startPos + BigInt(1), count - BigInt(1), index - BigInt(1)))
      }
    } else {
      // survivors = tail: survivors(index) = tail(index), survivors(index+1) = tail(index+1)
      assert(assertSurvivorStrictlyIncreases(
        seq, period, startPos + BigInt(1), count - BigInt(1), index))
    }
    survivors(index) < survivors(index + BigInt(1))
  }.holds

  /**
   * Step 5c forward lemma: nextSeq.apply(i) <= survivors(i).
   *
   * Forward induction. Base: survivors(0) == nextSeq.apply(0) (Step 5b).
   * Step: IH gives nextSeq.apply(i-1) <= survivors(i-1) < survivors(i);
   * since nextSeq.accepts(survivors(i)) and nextSeq.apply(i-1) < survivors(i),
   * nextDoesNotPassAcceptedValue gives nextSeq.apply(i) <= survivors(i).
   */
  def assertNextSeqApplyLEQSurvivor(
    seq: SpecSieveSequence,
    period: BigInt,
    nextPeriod: BigInt,
    i: BigInt
  ): Boolean = {
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(seq.primes.nextPrime.value < seq.head.value * seq.head.value)
    require(nextPeriod > BigInt(0))
    require(i >= BigInt(0))
    require(i < nextPeriod)
    val gapCycle  = SpecSieveSeqPeriodProperties.specGapCycle(seq, period)
    val baseCI    = CycleIntegral(seq.head.value, gapCycle.memCycle)
    val count     = period * seq.head.value
    val survivors = CycleIntegralFilterProperties.survivorValues(
      baseCI, seq.head.value, BigInt(0), count)
    require(i < survivors.size)
    decreases(i)

    val nextSeq = seq.next

    if (i == BigInt(0)) {
      // Establish structural facts about seq.next (required by assertFirstSurvivorMatchesNextSeqHead)
      assert(nextSeq.filterValues.head == seq.head.value)
      assert(nextSeq.filterValues.tail == seq.filterValues)
      assert(nextSeq.filterValues.nonEmpty)
      assert(SpecSieveSeqHeadIsPrime.assertApplyOneEqualsNextPrime(seq))
      assert(nextSeq.head.value == seq.apply(BigInt(1)))
      assert(assertFirstSurvivorMatchesNextSeqHead(seq, nextSeq, period))
      assert(survivors.head == nextSeq.apply(BigInt(0)))
    } else {
      // IH: nextSeq.apply(i-1) <= survivors(i-1)
      assert(assertNextSeqApplyLEQSurvivor(seq, period, nextPeriod, i - BigInt(1)))
      assert(nextSeq.apply(i - BigInt(1)) <= survivors(i - BigInt(1)))

      // survivors(i-1) < survivors(i) by strict increase
      assert(assertSurvivorStrictlyIncreases(seq, period, BigInt(0), count, i - BigInt(1)))
      assert(survivors(i - BigInt(1)) < survivors(i))

      // survivors(i) >= nextSeq.head.value (Lemma B)
      assert(assertSurvivorGEQStartCI(seq, period, BigInt(0), count, i))
      assert(assertBaseCIEqualsSeqApplyShifted(seq, period, BigInt(0)))
      assert(survivors(i) >= nextSeq.head.value)

      // nextSeq.accepts(survivors(i)) (Lemma D)
      assert(assertSurvivorIsNextSeqAccepted(seq, period, i))
      assert(nextSeq.accepts(survivors(i)))

      // nextSeq.apply(i-1) < survivors(i), so nextDoesNotPassAcceptedValue gives nextSeq.apply(i) <= survivors(i)
      assert(nextSeq.nextDoesNotPassAcceptedValue(i - BigInt(1), survivors(i)))
    }
    nextSeq.apply(i) <= survivors(i)
  }.holds

  /**
   * Step 5c: survivors(i) == nextSeq.apply(i) for all i in [0, nextPeriod).
   *
   * Backward induction. The lower bound comes from assertNextSeqApplyLEQSurvivor.
   * For the upper bound:
   *   - inductive step: survivors(i) < survivors(i+1) = nextSeq.apply(i+1)
   *     (strict increase + backward IH), so if survivors(i) > nextSeq.apply(i)
   *     we'd have nextSeq.apply(i) < survivors(i) < nextSeq.apply(i+1),
   *     contradicting !nextSeq.accepts(survivors(i)).
   *   - base case i = nextPeriod-1: survivors(i) <= baseCI(count-1) = seq.apply(count)
   *     = seq.head.value + head*tailPrimorial < nextSeq.head.value + nextSeq.tailPrimorial
   *     = nextSeq.apply(nextPeriod), so assertNoAcceptedValueBetweenGeneratedValues gives equality.
   *
   * Precondition nextSeq.tailPrimorial == seq.head.value * seq.tailPrimorial lets us prove
   * that seq.apply(count) < nextSeq.apply(nextPeriod).
   */
  def assertSurvivorAtIndexMatchesNextSeqApply(
    seq: SpecSieveSequence,
    period: BigInt,
    nextPeriod: BigInt,
    i: BigInt
  ): Boolean = {
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(seq.primes.nextPrime.value < seq.head.value * seq.head.value)
    require(nextPeriod > BigInt(0))
    require(i >= BigInt(0))
    require(i < nextPeriod)
    val gapCycle  = SpecSieveSeqPeriodProperties.specGapCycle(seq, period)
    val baseCI    = CycleIntegral(seq.head.value, gapCycle.memCycle)
    val count     = period * seq.head.value
    val survivors = CycleIntegralFilterProperties.survivorValues(
      baseCI, seq.head.value, BigInt(0), count)
    require(i < survivors.size)
    require(nextPeriod <= survivors.size)
    val nextSeq = seq.next
    require(nextSeq.apply(nextPeriod) == nextSeq.head.value + nextSeq.tailPrimorial)
    require(nextSeq.tailPrimorial == seq.head.value * seq.tailPrimorial)
    decreases(nextPeriod - i)

    // Lower bound: nextSeq.apply(i) <= survivors(i)
    assert(assertNextSeqApplyLEQSurvivor(seq, period, nextPeriod, i))
    assert(nextSeq.apply(i) <= survivors(i))

    // nextSeq.accepts(survivors(i))
    assert(assertSurvivorIsNextSeqAccepted(seq, period, i))
    assert(nextSeq.accepts(survivors(i)))

    // survivors(i) >= nextSeq.head.value (needed for assertNoAcceptedValueBetweenGeneratedValues)
    assert(assertSurvivorGEQStartCI(seq, period, BigInt(0), count, i))
    assert(assertBaseCIEqualsSeqApplyShifted(seq, period, BigInt(0)))
    assert(baseCI(BigInt(0)) <= survivors(i))
    assert(baseCI(BigInt(0)) == seq.apply(BigInt(1)))
    assert(SpecSieveSeqHeadIsPrime.assertApplyOneEqualsNextPrime(seq))
    assert(nextSeq.head.value == seq.apply(BigInt(1)))
    assert(survivors(i) >= nextSeq.head.value)

    if (i == nextPeriod - BigInt(1)) {
      // Base case: establish survivors(i) < nextSeq.apply(i+1) = nextSeq.apply(nextPeriod)
      assert(assertSurvivorLEQEndCI(seq, period, BigInt(0), count, i))
      assert(survivors(i) <= baseCI(count - BigInt(1)))
      assert(assertBaseCIEqualsSeqApplyShifted(seq, period, count - BigInt(1)))
      assert(baseCI(count - BigInt(1)) == seq.apply(count))
      assert(SpecSieveSeqSurvivorCountProperties.assertExpandedOldAcceptedCount(seq, period))
      assert(seq.apply(count) == seq.head.value + seq.head.value * seq.tailPrimorial)
      // nextSeq.apply(nextPeriod) = seq.apply(1) + head*tailPrimorial > head + head*tailPrimorial
      assert(nextSeq.apply(nextPeriod) == nextSeq.head.value + nextSeq.tailPrimorial)
      assert(nextSeq.tailPrimorial == seq.head.value * seq.tailPrimorial)
      assert(seq.apply(BigInt(1)) > seq.head.value)
      assert(survivors(i) < nextSeq.apply(nextPeriod))
      // Case split: equality or contradiction via assertNoAcceptedValueBetweenGeneratedValues
      if (nextSeq.apply(i) < survivors(i)) {
        // survivors(i) is strictly between apply(i) and apply(nextPeriod) = apply(i+1)
        assert(nextSeq.assertNoAcceptedValueBetweenGeneratedValues(i, survivors(i)))
        // gives !nextSeq.accepts(survivors(i)) — contradicts nextSeq.accepts(survivors(i))
      }
    } else {
      // Step case: backward IH for i+1
      assert(assertSurvivorAtIndexMatchesNextSeqApply(seq, period, nextPeriod, i + BigInt(1)))
      assert(survivors(i + BigInt(1)) == nextSeq.apply(i + BigInt(1)))
      // survivors(i) < survivors(i+1) = nextSeq.apply(i+1)
      assert(assertSurvivorStrictlyIncreases(seq, period, BigInt(0), count, i))
      assert(survivors(i) < survivors(i + BigInt(1)))
      assert(survivors(i) < nextSeq.apply(i + BigInt(1)))
      // Case split: equality or contradiction
      if (nextSeq.apply(i) < survivors(i)) {
        // survivors(i) is strictly between apply(i) and apply(i+1)
        assert(nextSeq.assertNoAcceptedValueBetweenGeneratedValues(i, survivors(i)))
        // gives !nextSeq.accepts(survivors(i)) — contradicts nextSeq.accepts(survivors(i))
      }
    }
    nextSeq.apply(i) == survivors(i)
  }.holds

}
