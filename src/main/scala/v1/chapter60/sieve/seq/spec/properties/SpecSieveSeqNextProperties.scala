package v1.chapter60.sieve.seq.spec.properties

import stainless.collection.List
import stainless.lang.*
import v1.chapter2.div.Calc
import v1.chapter2.div.properties.AdditionAndMultiplication
import v1.chapter3.list.{ListBoundUtils, ListUtils}
import v1.chapter5.prime.*
import v1.chapter60.sieve.seq.spec.SieveUtils
import v1.chapter60.sieve.seq.spec.SpecSieveSequence

object SpecSieveSeqNextProperties {

  // ── Headline theorems ─────────────────────────────────────────────────

  def nextAcceptedOldIndex(
    seq: SpecSieveSequence,
    nextSeq: SpecSieveSequence,
    k: BigInt,
    period: BigInt
  ): BigInt = {
    require(k >= BigInt(0))
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(seq.head.value <= nextSeq.head.value)
    require(nextSeq.accepts(seq.apply(k)))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(Calc.mod(seq.head.value + seq.tailPrimorial, nextSeq.filterValues.head) != BigInt(0))

    nextMergedGapOldIndex(seq, nextSeq, k, period)
  }.ensuring(result =>
    result > k &&
      seq.accepts(seq.apply(result)) &&
      Calc.mod(seq.apply(result), nextSeq.filterValues.head) != BigInt(0) &&
      nextSeq.accepts(seq.apply(result)) && {
      val computedNextSeqIndex = nextSeq.indexOfAccepted(seq.apply(k))
      nextSeq(computedNextSeqIndex + BigInt(1)) == seq.apply(result)
    }
  )


  def assertFilterPreservesNextGap(
    seq: SpecSieveSequence,
    nextSeq: SpecSieveSequence,
    k: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(seq.head.value <= nextSeq.head.value)
    require(nextSeq.accepts(seq.apply(k)))
    require(Calc.mod(seq.apply(k + BigInt(1)), nextSeq.filterValues.head) != BigInt(0))

    val v = seq.apply(k)
    val w = seq.apply(k + BigInt(1))
    val vIdx = nextSeq.indexOfAccepted(v)

    assert(nextSeq(vIdx) == v)
    assert(assertFilterPreservesNextPosition(seq, nextSeq, k))
    assert(nextSeq(vIdx + BigInt(1)) == w)

    nextSeq(vIdx + BigInt(1)) - nextSeq(vIdx) == w - v
  }.holds


  def mergedGapPrefix(
    seq: SpecSieveSequence,
    nextSeq: SpecSieveSequence,
    k: BigInt,
    remaining: BigInt,
    period: BigInt
  ): List[BigInt] = {
    require(k >= BigInt(0))
    require(remaining >= BigInt(0))
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(seq.head.value <= nextSeq.head.value)
    require(nextSeq.accepts(seq.apply(k)))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(Calc.mod(seq.head.value + seq.tailPrimorial, nextSeq.filterValues.head) != BigInt(0))
    decreases(remaining)

    if (remaining == BigInt(0)) {
      List.empty[BigInt]
    } else {
      val nextK = nextMergedGapOldIndex(seq, nextSeq, k, period)

      assert(nextK > k)
      assert(nextK >= k)
      assert(nextK >= BigInt(0))
      assert(nextSeq.accepts(seq.apply(nextK)))
      SpecSieveSeqPeriodProperties.sumGap(seq, k, nextK) :: mergedGapPrefix(seq, nextSeq, nextK, remaining - BigInt(1), period)
    }
  }

  def assertMergedGapPrefixMatchesNext(
    seq: SpecSieveSequence,
    nextSeq: SpecSieveSequence,
    k: BigInt,
    seqIndex: BigInt,
    remaining: BigInt,
    period: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(seqIndex >= BigInt(0))
    require(remaining >= BigInt(0))
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(seq.head.value <= nextSeq.head.value)
    require(nextSeq.accepts(seq.apply(k)))
    require(nextSeq(seqIndex) == seq.apply(k))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(Calc.mod(seq.head.value + seq.tailPrimorial, nextSeq.filterValues.head) != BigInt(0))
    decreases(remaining)

    val prefix = mergedGapPrefix(seq, nextSeq, k, remaining, period)

    if (remaining == BigInt(0)) {
      prefix == SpecSieveSeqPeriodProperties.gapList(nextSeq, seqIndex, BigInt(0))
    } else {
      val nextOldIndex = nextMergedGapOldIndex(seq, nextSeq, k, period)
      val computedSeqIndex = nextSeq.indexOfAccepted(seq.apply(k))

      assert(nextSeq.assertApplyInjective(seqIndex, computedSeqIndex))
      assert(assertMergedGapPrefixHeadMatchesNext(seq, nextSeq, k, period))
      assert(assertMergedGapPrefixMatchesNext(seq, nextSeq, nextOldIndex, seqIndex + BigInt(1), remaining - BigInt(1), period))

      prefix == SpecSieveSeqPeriodProperties.gapList(nextSeq, seqIndex, remaining)
    }
  }.holds


  def assertSurvivorAcceptedByNext(seq: SpecSieveSequence, v: BigInt): Boolean = {
    require(v >= seq.head.value)
    require(seq.accepts(v))
    require(Calc.mod(v, seq.head.value) != BigInt(0))
    require(seq.primes.nextPrime.value < seq.head.value * seq.head.value)

    val nextSeq = seq.next
    assert(nextSeq.filterValues.head == seq.head.value)
    assert(nextSeq.filterValues.tail == seq.filterValues)
    nextSeq.passesFilter(v)
  }.holds

  def findFirstNonMultipleAfter(
    seq: SpecSieveSequence,
    k: BigInt, p: BigInt,
    bound: BigInt): BigInt = {
    require(k >= BigInt(0))
    require(p > BigInt(0))
    require(bound > k)
    require(Calc.mod(seq.apply(bound), p) != BigInt(0))
    decreases(bound - k)
    if (Calc.mod(seq.apply(k + BigInt(1)), p) != BigInt(0)) k + BigInt(1)
    else {
      assert(bound > k + BigInt(1))
      findFirstNonMultipleAfter(seq, k + BigInt(1), p, bound)
    }
  }.ensuring(res => res >= k + BigInt(1) && res <= bound && Calc.mod(seq.apply(res), p) != BigInt(0))



  def assertOldAcceptedRejectedByNextIsHeadMultiple(seq: SpecSieveSequence, v: BigInt): Boolean = {
    require(seq.primes.nextPrime.value < seq.head.value * seq.head.value)
    require(v >= seq.next.head.value)
    require(seq.accepts(v))
    require(!seq.next.accepts(v))

    val nextSeq = seq.next

    assert(assertNextAcceptsMatchesHeadFilterForAcceptedValue(seq,v))
    assert(nextSeq.accepts(v) == (Calc.mod(v, seq.head.value) != BigInt(0)))
    assert(Calc.mod(v, seq.head.value) == BigInt(0))

    Calc.mod(v, seq.head.value) == BigInt(0)
  }.holds


  def assertNextAcceptsMatchesHeadFilterForAcceptedValue(seq: SpecSieveSequence, v: BigInt): Boolean = {
    require(seq.primes.nextPrime.value < seq.head.value * seq.head.value)
    require(v >= seq.next.head.value)
    require(seq.accepts(v))

    val nextSeq = seq.next
    assert(nextSeq.filterValues.head == seq.head.value)
    assert(nextSeq.filterValues.tail == seq.filterValues)

    if (Calc.mod(v, seq.head.value) == BigInt(0)) {
      assert(Calc.mod(v, nextSeq.filterValues.head) == BigInt(0))
      assert(!CoprimeUtils.isCoprime(v, nextSeq.filterValues))
      assert(!nextSeq.passesFilter(v))
      assert(!nextSeq.accepts(v))
    } else {
      assert(assertSurvivorAcceptedByNext(seq,v))
      assert(nextSeq.passesFilter(v))
      assert(nextSeq.accepts(v))
    }

    nextSeq.accepts(v) == (Calc.mod(v, seq.head.value) != BigInt(0))
  }.holds

  // ── Private helpers ───────────────────────────────────────────────────

  private def nextMergedGapOldIndex(
    seq: SpecSieveSequence, nextSeq: SpecSieveSequence, k: BigInt, period: BigInt
  ): BigInt = {
    require(k >= BigInt(0))
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(seq.head.value <= nextSeq.head.value)
    require(nextSeq.accepts(seq.apply(k)))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(Calc.mod(seq.head.value + seq.tailPrimorial, nextSeq.filterValues.head) != BigInt(0))

    val frontFilterPrime = nextSeq.filterValues.head
    val nextSeqIndex = nextSeq.indexOfAccepted(seq.apply(k))

    if (Calc.mod(seq.apply(k + BigInt(1)), frontFilterPrime) != BigInt(0)) {
      assert(seq.accepts(seq.apply(k + BigInt(1))))
      assert(seq.apply(k) >= nextSeq.head.value)
      assert(seq.applyStrictlyIncreases(k))
      assert(seq.apply(k + BigInt(1)) > seq.apply(k))
      assert(seq.apply(k + BigInt(1)) >= nextSeq.head.value)
      assert(assertAcceptedByNextWhenOldAcceptedAndNewHeadNonMultiple(seq, nextSeq, seq.apply(k + BigInt(1))))
      assert(assertFilterPreservesNextGap(seq, nextSeq, k))
      assert(nextSeq(nextSeqIndex + BigInt(1)) == seq.apply(k + BigInt(1)))
      k + BigInt(1)
    } else {
      val searchUpperBound = k + frontFilterPrime * period

      assert(assertPeriodBoundIsNonMultiple(seq, nextSeq, k, period))
      val firstSurvivorOldIndex = findFirstNonMultipleAfter(seq, k, frontFilterPrime, searchUpperBound)
      assert(firstSurvivorOldIndex > k)
      assert(seq.accepts(seq.apply(firstSurvivorOldIndex)))
      assert(Calc.mod(seq.apply(firstSurvivorOldIndex), frontFilterPrime) != BigInt(0))
      assert(seq.apply(k) >= nextSeq.head.value)
      assert(seq.applyIndexStrictlyPreservesValues(k, firstSurvivorOldIndex))
      assert(seq.apply(firstSurvivorOldIndex) > seq.apply(k))
      assert(seq.apply(firstSurvivorOldIndex) >= nextSeq.head.value)
      assert(assertAcceptedByNextWhenOldAcceptedAndNewHeadNonMultiple(seq, nextSeq, seq.apply(firstSurvivorOldIndex)))
      assert(assertMergeGapEqualsOldGapSum(seq, nextSeq, k, period))
      assert(SpecSieveSeqPeriodProperties.assertSumGapTelescopes(seq, k, firstSurvivorOldIndex))
      assert(nextSeq(nextSeqIndex + BigInt(1)) == seq.apply(firstSurvivorOldIndex))
      firstSurvivorOldIndex
    }
  }.ensuring(result =>
    result > k &&
      seq.accepts(seq.apply(result)) &&
      Calc.mod(seq.apply(result), nextSeq.filterValues.head) != BigInt(0) &&
      nextSeq.accepts(seq.apply(result)) && {
      val computedNextSeqIndex = nextSeq.indexOfAccepted(seq.apply(k))
      nextSeq(computedNextSeqIndex + BigInt(1)) == seq.apply(result) &&
        nextSeq(computedNextSeqIndex + BigInt(1)) - nextSeq(computedNextSeqIndex) == SpecSieveSeqPeriodProperties.sumGap(seq, k, result)
    }
  )

  private def assertAcceptedByNextWhenOldAcceptedAndNewHeadNonMultiple(
    seq: SpecSieveSequence,
    nextSeq: SpecSieveSequence,
    value: BigInt
  ): Boolean = {
    require(value >= nextSeq.head.value)
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(seq.head.value <= nextSeq.head.value)
    require(seq.accepts(value))
    require(Calc.mod(value, nextSeq.filterValues.head) != BigInt(0))

    assert(SieveUtils.isCoprime(value, seq.filterValues))
    assert(SieveUtils.isCoprime(value, nextSeq.filterValues.tail))
    assert(SieveUtils.isCoprime(value, nextSeq.filterValues))
    nextSeq.accepts(value)
  }.holds

  private def assertNextAcceptedImpliesOldAcceptedAndNewHeadNonMultiple(
    seq: SpecSieveSequence,
    nextSeq: SpecSieveSequence,
    value: BigInt
  ): Boolean = {
    require(value >= nextSeq.head.value)
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(seq.head.value <= nextSeq.head.value)
    require(nextSeq.accepts(value))

    assert(value >= seq.head.value) // value >= nextSeq.head.value >= seq.head.value
    assert(SieveUtils.isCoprime(value, nextSeq.filterValues))
    assert(SieveUtils.assertIsCoprimeSound(value, nextSeq.filterValues))
    assert(Calc.mod(value, nextSeq.filterValues.head) != BigInt(0))
    assert(SieveUtils.isCoprime(value, nextSeq.filterValues.tail))
    assert(SieveUtils.isCoprime(value, seq.filterValues))
    seq.accepts(value) && Calc.mod(value, nextSeq.filterValues.head) != BigInt(0)
  }.holds

  private def assertRejectedByNextWhenNewHeadMultiple(
    seq: SpecSieveSequence,
    nextSeq: SpecSieveSequence,
    value: BigInt,
    p: BigInt
  ): Boolean = {
    require(value >= nextSeq.head.value)
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.head == p)
    require(Calc.mod(value, p) == BigInt(0))

    assert(Calc.mod(value, nextSeq.filterValues.head) == BigInt(0))
    assert(!SieveUtils.isCoprime(value, nextSeq.filterValues))
    assert(!nextSeq.passesFilter(value))
    !nextSeq.accepts(value)
  }.holds

  private def assertFilterPreservesNextPosition(
    seq: SpecSieveSequence,
    nextSeq: SpecSieveSequence,
    k: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(seq.head.value <= nextSeq.head.value)
    require(nextSeq.accepts(seq.apply(k)))
    require(Calc.mod(seq.apply(k + BigInt(1)), nextSeq.filterValues.head) != BigInt(0))
    true
  }.ensuring(res => {
    val V = seq.apply(k)
    val W = seq.apply(k + BigInt(1))
    val vIdx = nextSeq.indexOfAccepted(V)

    assert(V >= nextSeq.head.value)
    assert(seq.applyStrictlyIncreases(k))
    assert(W > V)
    assert(W >= nextSeq.head.value)
    assert(seq.accepts(W))
    assert(assertAcceptedByNextWhenOldAcceptedAndNewHeadNonMultiple(seq, nextSeq, W))
    assert(nextSeq.accepts(W))

    assert(seq.applySkipsNoAcceptedBetween(k + BigInt(1)))
    assert(seq.noAcceptedBetween(V + BigInt(1), W))

    assert(nextSeq.applyStrictlyIncreases(vIdx))
    assert(nextSeq(vIdx + BigInt(1)) > V)
    val z = nextSeq(vIdx + BigInt(1))
    assert(z >= nextSeq.head.value)
    assert(z >= seq.head.value)
    assert(SieveUtils.isCoprime(z, seq.filterValues))
    assert(seq.accepts(z))
    assert(seq.nextDoesNotPassAcceptedValue(k, z))
    assert(W <= z)

    assert(nextSeq.accepts(W))
    assert(nextSeq.nextDoesNotPassAcceptedValue(vIdx, W))
    assert(z <= W)

    res && nextSeq(vIdx + BigInt(1)) == W
  })

  private def assertFirstNonMultipleIsAtOrBefore(
    seq: SpecSieveSequence,
    k: BigInt,
    zIdx: BigInt,
    p: BigInt,
    bound: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(zIdx > k)
    require(zIdx <= bound)
    require(p > BigInt(0))
    require(Calc.mod(seq.apply(zIdx), p) != BigInt(0))
    require(Calc.mod(seq.apply(bound), p) != BigInt(0))
    decreases(bound - k)
    val m = findFirstNonMultipleAfter(seq, k, p, bound)
    if (k + BigInt(1) == m) {
      m <= zIdx
    } else {
      assert(k + BigInt(1) < m)
      assert(Calc.mod(seq.apply(k + BigInt(1)), p) == BigInt(0))
      assert(zIdx > k + BigInt(1))
      assert(assertFirstNonMultipleIsAtOrBefore(seq, k + BigInt(1), zIdx, p, bound))
      m <= zIdx
    }
  }.holds

  private def assertSkippedIndexBeforeFirstIsMultiple(
    seq: SpecSieveSequence,
    k: BigInt,
    idx: BigInt,
    p: BigInt,
    bound: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(p > BigInt(0))
    require(bound > k)
    require(Calc.mod(seq.apply(bound), p) != BigInt(0))
    require(idx > k)
    require(idx < findFirstNonMultipleAfter(seq, k, p, bound))
    decreases(idx - k)

    val m = findFirstNonMultipleAfter(seq, k, p, bound)
    assert(k + BigInt(1) <= idx)
    assert(k + BigInt(1) < m)

    if (Calc.mod(seq.apply(k + BigInt(1)), p) != BigInt(0)) {
      assert(m == k + BigInt(1))
      assert(false)
      Calc.mod(seq.apply(idx), p) == BigInt(0)
    } else if (idx == k + BigInt(1)) {
      Calc.mod(seq.apply(idx), p) == BigInt(0)
    } else {
      assert(idx > k + BigInt(1))
      assert(bound > k + BigInt(1))
      val nextM = findFirstNonMultipleAfter(seq, k + BigInt(1), p, bound)
      assert(m == nextM)
      assert(idx < nextM)
      assert(assertSkippedIndexBeforeFirstIsMultiple(seq, k + BigInt(1), idx, p, bound))
      Calc.mod(seq.apply(idx), p) == BigInt(0)
    }
  }.holds

  private def assertNextAnchorBeforeFirstSurvivor(
    seq: SpecSieveSequence,
    nextSeq: SpecSieveSequence,
    k: BigInt,
    p: BigInt,
    bound: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(p > BigInt(0))
    require(bound > k)
    require(Calc.mod(seq.apply(bound), p) != BigInt(0))
    require(seq.head.value <= nextSeq.head.value)
    require(nextSeq.accepts(seq.apply(k)))

    val vIdx = nextSeq.indexOfAccepted(seq.apply(k))
    val m = findFirstNonMultipleAfter(seq, k, p, bound)

    assert(m >= k + BigInt(1))
    assert(m > k)
    assert(seq.applyIndexStrictlyPreservesValues(k, m))
    assert(seq.apply(k) < seq.apply(m))
    assert(nextSeq(vIdx) == seq.apply(k))
    nextSeq(vIdx) < seq.apply(m)
  }.holds


  private def assertNextValueAtOrBeforeFirstSurvivor(
    seq: SpecSieveSequence,
    nextSeq: SpecSieveSequence,
    k: BigInt,
    p: BigInt,
    bound: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(p > BigInt(0))
    require(bound > k)
    require(Calc.mod(seq.apply(bound), p) != BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.head == p)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(seq.head.value <= nextSeq.head.value)
    require(nextSeq.accepts(seq.apply(k)))

    val vIdx = nextSeq.indexOfAccepted(seq.apply(k))
    val m = findFirstNonMultipleAfter(seq, k, p, bound)

    assert(m >= k + BigInt(1))
    assert(m >= BigInt(0))
    assert(Calc.mod(seq.apply(m), p) != BigInt(0))
    assert(Calc.mod(seq.apply(m), nextSeq.filterValues.head) != BigInt(0))
    assert(seq.accepts(seq.apply(m)))
    assert(seq.apply(k) >= nextSeq.head.value)
    assert(seq.applyIndexStrictlyPreservesValues(k, m))
    assert(seq.apply(m) > seq.apply(k))
    assert(seq.apply(m) >= nextSeq.head.value)
    assert(assertAcceptedByNextWhenOldAcceptedAndNewHeadNonMultiple(seq, nextSeq, seq.apply(m)))
    assert(nextSeq.accepts(seq.apply(m)))
    assert(assertNextAnchorBeforeFirstSurvivor(seq, nextSeq, k, p, bound))
    assert(nextSeq.nextDoesNotPassAcceptedValue(vIdx, seq.apply(m)))
    nextSeq(vIdx + BigInt(1)) <= seq.apply(m)
  }.holds

  private def assertNextSuccessorOldIndexAfterAnchor(
    seq: SpecSieveSequence,
    nextSeq: SpecSieveSequence,
    k: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(seq.head.value <= nextSeq.head.value)
    require(nextSeq.accepts(seq.apply(k)))

    val vIdx = nextSeq.indexOfAccepted(seq.apply(k))
    assert(vIdx >= BigInt(0))
    assert(nextSeq(vIdx) == seq.apply(k))
    assert(nextSeq.applyStrictlyIncreases(vIdx))

    val z = nextSeq(vIdx + BigInt(1))
    assert(z > seq.apply(k))
    assert(nextSeq.accepts(z))
    assert(z >= nextSeq.head.value)
    assert(assertNextAcceptedImpliesOldAcceptedAndNewHeadNonMultiple(seq, nextSeq, z))
    assert(seq.accepts(z))

    val zIdx = seq.indexOfAccepted(z)
    assert(zIdx >= BigInt(0))
    assert(seq.apply(zIdx) == z)

    if (zIdx > k) {
      true
    } else {
      assert(zIdx <= k)
      assert(seq.applyIndexOrderPreservesValues(zIdx, k))
      assert(seq.apply(zIdx) <= seq.apply(k))
      assert(z <= seq.apply(k))
      zIdx > k
    }
  }.holds

  private def assertNextSuccessorOldIndexWithinBound(
    seq: SpecSieveSequence,
    nextSeq: SpecSieveSequence,
    k: BigInt,
    p: BigInt,
    bound: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(p > BigInt(0))
    require(bound > k)
    require(Calc.mod(seq.apply(bound), p) != BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.head == p)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(seq.head.value <= nextSeq.head.value)
    require(nextSeq.accepts(seq.apply(k)))

    val vIdx = nextSeq.indexOfAccepted(seq.apply(k))
    val z = nextSeq(vIdx + BigInt(1))
    assert(z >= nextSeq.head.value)
    assert(nextSeq.accepts(z))
    assert(assertNextAcceptedImpliesOldAcceptedAndNewHeadNonMultiple(seq, nextSeq, z))
    assert(seq.accepts(z))
    val zIdx = seq.indexOfAccepted(z)
    val m = findFirstNonMultipleAfter(seq, k, p, bound)

    assert(assertNextValueAtOrBeforeFirstSurvivor(seq, nextSeq, k, p, bound))
    assert(z <= seq.apply(m))
    assert(m <= bound)
    assert(m >= BigInt(0))
    assert(seq.applyIndexOrderPreservesValues(m, bound))
    assert(seq.apply(m) <= seq.apply(bound))
    assert(z <= seq.apply(bound))
    assert(seq.apply(zIdx) == z)
    assert(seq.valueBoundImpliesIndexBound(zIdx, bound))
    zIdx <= bound
  }.holds

  private def assertFirstSurvivorAtOrBeforeNextValue(
    seq: SpecSieveSequence,
    nextSeq: SpecSieveSequence,
    k: BigInt,
    p: BigInt,
    bound: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(p > BigInt(0))
    require(bound > k)
    require(Calc.mod(seq.apply(bound), p) != BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.head == p)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(seq.head.value <= nextSeq.head.value)
    require(nextSeq.accepts(seq.apply(k)))

    val vIdx = nextSeq.indexOfAccepted(seq.apply(k))
    val z = nextSeq(vIdx + BigInt(1))
    assert(z >= nextSeq.head.value)
    assert(nextSeq.accepts(z))
    assert(assertNextAcceptedImpliesOldAcceptedAndNewHeadNonMultiple(seq, nextSeq, z))
    assert(seq.accepts(z))
    val zIdx = seq.indexOfAccepted(z)
    val m = findFirstNonMultipleAfter(seq, k, p, bound)

    assert(assertNextSuccessorOldIndexAfterAnchor(seq, nextSeq, k))
    assert(zIdx > k)
    assert(assertNextSuccessorOldIndexWithinBound(seq, nextSeq, k, p, bound))
    assert(zIdx <= bound)
    assert(Calc.mod(z, p) != BigInt(0))
    assert(seq.apply(zIdx) == z)
    assert(Calc.mod(seq.apply(zIdx), p) != BigInt(0))
    assert(assertFirstNonMultipleIsAtOrBefore(seq, k, zIdx, p, bound))
    assert(m <= zIdx)
    assert(seq.applyIndexOrderPreservesValues(m, zIdx))
    assert(seq.apply(m) <= seq.apply(zIdx))
    seq.apply(m) <= z
  }.holds

  private def assertNextSuccessorIsFirstSurvivor(
    seq: SpecSieveSequence,
    nextSeq: SpecSieveSequence,
    k: BigInt,
    p: BigInt,
    bound: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(p > BigInt(0))
    require(bound > k)
    require(Calc.mod(seq.apply(bound), p) != BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.head == p)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(seq.head.value <= nextSeq.head.value)
    require(nextSeq.accepts(seq.apply(k)))

    val vIdx = nextSeq.indexOfAccepted(seq.apply(k))
    val m = findFirstNonMultipleAfter(seq, k, p, bound)

    assert(assertNextValueAtOrBeforeFirstSurvivor(seq, nextSeq, k, p, bound))
    assert(nextSeq(vIdx + BigInt(1)) <= seq.apply(m))
    assert(assertFirstSurvivorAtOrBeforeNextValue(seq, nextSeq, k, p, bound))
    assert(seq.apply(m) <= nextSeq(vIdx + BigInt(1)))
    nextSeq(vIdx + BigInt(1)) == seq.apply(m)
  }.holds

  private def assertPeriodBoundIsNonMultiple(
    seq: SpecSieveSequence,
    nextSeq: SpecSieveSequence,
    k: BigInt, period: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(seq.head.value <= nextSeq.head.value)
    require(nextSeq.accepts(seq.apply(k)))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(Calc.mod(seq.head.value + seq.tailPrimorial, nextSeq.filterValues.head) != BigInt(0))

    val p = nextSeq.filterValues.head
    val bound = k + p * period

    seq.primorialMatchesSieveProduct(seq.filterPrimes)
    assert(seq.tailPrimorial == SieveUtils.product(seq.filterValues))
    assert(p > BigInt(0))
    assert(bound > k)
    assert(SpecSieveSeqPeriodProperties.assertBlockShiftMultiple(seq, k, p, period))
    assert(seq.apply(bound) == seq.apply(k) + p * seq.tailPrimorial)
    assert(seq.apply(k) >= nextSeq.head.value)
    assert(assertNextAcceptedImpliesOldAcceptedAndNewHeadNonMultiple(seq, nextSeq, seq.apply(k)))
    assert(Calc.mod(seq.apply(k), p) != BigInt(0))
    assert(AdditionAndMultiplication.ATimesBSameMod(seq.apply(k), p, seq.tailPrimorial))
    assert(Calc.mod(seq.apply(k) + p * seq.tailPrimorial, p) == Calc.mod(seq.apply(k), p))

    Calc.mod(seq.apply(bound), p) != BigInt(0)
  }.ensuring(res => {
    val p = nextSeq.filterValues.head
    val bound = k + p * period
    res && p > BigInt(0) && bound > k && Calc.mod(seq.apply(bound), p) != BigInt(0)
  })

  private def assertSkipUntilNonMultiple(
    seq: SpecSieveSequence, nextSeq: SpecSieveSequence, k: BigInt, period: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(seq.head.value <= nextSeq.head.value)
    require(nextSeq.accepts(seq.apply(k)))
    require(Calc.mod(seq.apply(k + BigInt(1)), nextSeq.filterValues.head) == BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(Calc.mod(seq.head.value + seq.tailPrimorial, nextSeq.filterValues.head) != BigInt(0))

    val p = nextSeq.filterValues.head
    val vIdx = nextSeq.indexOfAccepted(seq.apply(k))
    val bound = k + p * period

    seq.primorialMatchesSieveProduct(seq.filterPrimes)
    assert(seq.tailPrimorial == SieveUtils.product(seq.filterValues))
    assert(p > BigInt(0))
    assert(bound > k)
    assert(SpecSieveSeqPeriodProperties.assertBlockShiftMultiple(seq, k, p, period))
    assert(seq.apply(bound) == seq.apply(k) + p * seq.tailPrimorial)
    assert(seq.apply(k) >= nextSeq.head.value)
    assert(assertNextAcceptedImpliesOldAcceptedAndNewHeadNonMultiple(seq, nextSeq, seq.apply(k)))
    assert(Calc.mod(seq.apply(k), p) != BigInt(0))
    assert(AdditionAndMultiplication.ATimesBSameMod(seq.apply(k), p, seq.tailPrimorial))
    assert(Calc.mod(seq.apply(k) + p * seq.tailPrimorial, p) == Calc.mod(seq.apply(k), p))
    assert(Calc.mod(seq.apply(bound), p) != BigInt(0))
    val m = findFirstNonMultipleAfter(seq, k, p, bound)
    assert(assertNextSuccessorIsFirstSurvivor(seq, nextSeq, k, p, bound))

    nextSeq(vIdx + BigInt(1)) == seq.apply(m)
  }.holds

  private def assertMergeLandsOnFirstSurvivor(
    seq: SpecSieveSequence, nextSeq: SpecSieveSequence, k: BigInt, period: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(seq.head.value <= nextSeq.head.value)
    require(nextSeq.accepts(seq.apply(k)))
    require(Calc.mod(seq.apply(k + BigInt(1)), nextSeq.filterValues.head) == BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(Calc.mod(seq.head.value + seq.tailPrimorial, nextSeq.filterValues.head) != BigInt(0))

    val p = nextSeq.filterValues.head
    val vIdx = nextSeq.indexOfAccepted(seq.apply(k))
    val bound = k + p * period

    assert(assertPeriodBoundIsNonMultiple(seq, nextSeq, k, period))
    val m = findFirstNonMultipleAfter(seq, k, p, bound)
    assert(assertSkipUntilNonMultiple(seq, nextSeq, k, period))

    nextSeq(vIdx + BigInt(1)) == seq.apply(m)
  }.holds

  private def assertMergeGapEqualsOldGapSum(
    seq: SpecSieveSequence, nextSeq: SpecSieveSequence, k: BigInt, period: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(seq.head.value <= nextSeq.head.value)
    require(nextSeq.accepts(seq.apply(k)))
    require(Calc.mod(seq.apply(k + BigInt(1)), nextSeq.filterValues.head) == BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(Calc.mod(seq.head.value + seq.tailPrimorial, nextSeq.filterValues.head) != BigInt(0))

    val p = nextSeq.filterValues.head
    val vIdx = nextSeq.indexOfAccepted(seq.apply(k))
    val bound = k + p * period

    assert(assertPeriodBoundIsNonMultiple(seq, nextSeq, k, period))
    val m = findFirstNonMultipleAfter(seq, k, p, bound)
    assert(m >= k)
    assert(assertMergeLandsOnFirstSurvivor(seq, nextSeq, k, period))
    assert(nextSeq(vIdx) == seq.apply(k))
    assert(nextSeq(vIdx + BigInt(1)) == seq.apply(m))
    assert(SpecSieveSeqPeriodProperties.assertSumGapTelescopes(seq, k, m))

    nextSeq(vIdx + BigInt(1)) - nextSeq(vIdx) == SpecSieveSeqPeriodProperties.sumGap(seq, k, m)
  }.holds

  private def assertMergedGapPrefixAllPositive(
    seq: SpecSieveSequence,
    nextSeq: SpecSieveSequence,
    k: BigInt,
    remaining: BigInt,
    period: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(remaining >= BigInt(0))
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(seq.head.value <= nextSeq.head.value)
    require(nextSeq.accepts(seq.apply(k)))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(Calc.mod(seq.head.value + seq.tailPrimorial, nextSeq.filterValues.head) != BigInt(0))
    decreases(remaining)

    val prefix = mergedGapPrefix(seq, nextSeq, k, remaining, period)
    if (remaining == BigInt(0)) {
      ListBoundUtils.allGreaterThan(prefix, BigInt(0))
    } else {
      val nextOldIndex = nextMergedGapOldIndex(seq, nextSeq, k, period)
      val tailPrefix = mergedGapPrefix(seq, nextSeq, nextOldIndex, remaining - BigInt(1), period)

      assert(SpecSieveSeqPeriodProperties.assertSumGapPositive(seq, k, nextOldIndex))
      assert(assertMergedGapPrefixAllPositive(seq, nextSeq, nextOldIndex, remaining - BigInt(1), period))
      assert(ListBoundUtils.assertGreaterThanHeadTail(prefix, BigInt(0)))
      ListBoundUtils.allGreaterThan(prefix, BigInt(0))
    }
  }.holds

  private def assertMergedGapPrefixHeadMatchesNext(
    seq: SpecSieveSequence,
    nextSeq: SpecSieveSequence,
    k: BigInt,
    period: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(seq.head.value <= nextSeq.head.value)
    require(nextSeq.accepts(seq.apply(k)))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(Calc.mod(seq.head.value + seq.tailPrimorial, nextSeq.filterValues.head) != BigInt(0))

    val prefix = mergedGapPrefix(seq, nextSeq, k, BigInt(1), period)
    val nextSeqIndex = nextSeq.indexOfAccepted(seq.apply(k))

    prefix.head == nextSeq(nextSeqIndex + BigInt(1)) - nextSeq(nextSeqIndex)
  }.holds
}
