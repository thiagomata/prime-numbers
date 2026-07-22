package v1.chapter6.sieve.seq.spec.properties

import stainless.lang.*
import v1.chapter2.div.Calc
import v1.chapter2.div.properties.AdditionAndMultiplication
import v1.chapter5.prime.*
import v1.chapter6.sieve.seq.spec.SieveUtils
import v1.chapter6.sieve.seq.spec.SpecSieveSequence

object SpecSieveSeqSurvivorCountProperties {

  // ── Headline theorems ─────────────────────────────────────────────────

  def sameHeadSurvivorCount(seq: SpecSieveSequence, period: BigInt): BigInt = {
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(Calc.mod(seq.tailPrimorial, seq.head.value) != BigInt(0))

    val expandedEnd = seq.head.value + seq.head.value * seq.tailPrimorial
    countAcceptedHeadNonMultiplesBetween(seq, seq.head.value, expandedEnd)
  }.ensuring(count => {
    assertSameHeadExtendedFilterCount(seq, period)
    count == period * (seq.head.value - BigInt(1))
  })

  def assertSameHeadExtendedFilterCount(seq: SpecSieveSequence, period: BigInt): Boolean = {
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(Calc.mod(seq.tailPrimorial, seq.head.value) != BigInt(0))

    val expandedIndex = period * seq.head.value
    val expandedEnd = seq.head.value + seq.head.value * seq.tailPrimorial

    assert(seq.head.value > BigInt(1))
    assert(expandedIndex >= BigInt(0))
    assert(assertGeneratedHeadMultiplesPrefixExpandedCount(seq, period))
    assert(countGeneratedHeadMultiplesPrefix(seq, expandedIndex) == period)
    assert(assertExpandedHeadMultipleCountFromGeneratedCount(seq, period))
    assert(countAcceptedHeadMultiplesBetween(seq, seq.head.value, expandedEnd) == period)
    assert(assertSameHeadExtendedFilterCountFromRemovedCount(seq, period))
    countAcceptedHeadNonMultiplesBetween(seq, seq.head.value, expandedEnd) ==
      period * (seq.head.value - BigInt(1))
  }.holds

  def assertExpandedOldAcceptedCount(seq: SpecSieveSequence, period: BigInt): Boolean = {
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)

    val expandedIndex = period * seq.head.value
    val expandedEnd = seq.head.value + seq.head.value * seq.tailPrimorial

    assert(seq.head.value > BigInt(1))
    assert(expandedIndex >= BigInt(0))
    assert(assertBlockShiftMultiple(seq, BigInt(0), seq.head.value, period))
    assert(seq.apply(expandedIndex) == expandedEnd)
    assert(assertGeneratedPrefixCount(seq, expandedIndex))
    countAcceptedBetween(seq, seq.head.value, expandedEnd) == expandedIndex
  }.holds

  def assertGeneratedPrefixCount(seq: SpecSieveSequence, k: BigInt): Boolean = {
    require(k >= BigInt(0))
    decreases(k)

    if (k == BigInt(0)) {
      assert(seq.apply(BigInt(0)) == seq.head.value)
      countAcceptedBetween(seq, seq.head.value, seq.apply(k)) == k
    } else {
      val previousIndex = k - BigInt(1)
      val previous = seq.apply(previousIndex)
      val current = seq.apply(k)

      assertGeneratedPrefixCount(seq, previousIndex)
      assert(countAcceptedBetween(seq, seq.head.value, previous) == previousIndex)
      assert(seq.applyStrictlyIncreases(previousIndex))
      assert(previous < current)
      assert(previous + BigInt(1) <= current)
      assert(seq.applySkipsNoAcceptedBetween(k))
      assert(seq.noAcceptedBetween(previous + BigInt(1), current))
      assert(countNoAcceptedBetween(seq, previous + BigInt(1), current))
      assert(countAcceptedBetween(seq, previous + BigInt(1), current) == BigInt(0))
      assert(seq.accepts(previous))
      assert(countAcceptedBetween(seq, previous, current) == BigInt(1))
      assert(assertCountAcceptedBetweenAppend(seq, seq.head.value, previous, current))
      countAcceptedBetween(seq, seq.head.value, current) == k
    }
  }.holds

  def assertGeneratedHeadMultiplePrefixCount(seq: SpecSieveSequence, k: BigInt): Boolean = {
    require(k >= BigInt(0))
    decreases(k)

    if (k == BigInt(0)) {
      assert(seq.apply(BigInt(0)) == seq.head.value)
      countAcceptedHeadMultiplesBetween(seq, seq.head.value, seq.apply(k)) ==
        countGeneratedHeadMultiplesPrefix(seq, k)
    } else {
      val previousIndex = k - BigInt(1)
      val previous = seq.apply(previousIndex)
      val current = seq.apply(k)

      assertGeneratedHeadMultiplePrefixCount(seq, previousIndex)
      assert(countAcceptedHeadMultiplesBetween(seq, seq.head.value, previous) ==
        countGeneratedHeadMultiplesPrefix(seq, previousIndex))
      assert(seq.applyStrictlyIncreases(previousIndex))
      assert(previous < current)
      assert(previous + BigInt(1) <= current)
      assert(seq.applySkipsNoAcceptedBetween(k))
      assert(seq.noAcceptedBetween(previous + BigInt(1), current))
      assert(countNoAcceptedHeadMultiplesBetween(seq, previous + BigInt(1), current))
      assert(countAcceptedHeadMultiplesBetween(seq, previous + BigInt(1), current) == BigInt(0))
      assert(seq.accepts(previous))

      if (Calc.mod(previous, seq.head.value) == BigInt(0)) {
        assert(countAcceptedHeadMultiplesBetween(seq, previous, current) == BigInt(1))
        assert(countGeneratedHeadMultiplesPrefix(seq, k) ==
          countGeneratedHeadMultiplesPrefix(seq, previousIndex) + BigInt(1))
      } else {
        assert(countAcceptedHeadMultiplesBetween(seq, previous, current) == BigInt(0))
        assert(countGeneratedHeadMultiplesPrefix(seq, k) ==
          countGeneratedHeadMultiplesPrefix(seq, previousIndex))
      }

      assert(assertCountAcceptedHeadMultiplesBetweenAppend(seq, seq.head.value, previous, current))
      countAcceptedHeadMultiplesBetween(seq, seq.head.value, current) ==
        countGeneratedHeadMultiplesPrefix(seq, k)
    }
  }.holds

  def assertExpandedHeadMultipleCountFromGeneratedCount(seq: SpecSieveSequence, period: BigInt): Boolean = {
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)

    val expandedIndex = period * seq.head.value
    val expandedEnd = seq.head.value + seq.head.value * seq.tailPrimorial

    require(countGeneratedHeadMultiplesPrefix(seq, expandedIndex) == period)

    assert(seq.head.value > BigInt(1))
    assert(expandedIndex >= BigInt(0))
    assert(assertBlockShiftMultiple(seq, BigInt(0), seq.head.value, period))
    assert(seq.apply(expandedIndex) == expandedEnd)
    assert(assertGeneratedHeadMultiplePrefixCount(seq, expandedIndex))
    countAcceptedHeadMultiplesBetween(seq, seq.head.value, expandedEnd) == period
  }.holds

  def assertSameHeadExtendedFilterCountFromRemovedCount(seq: SpecSieveSequence, period: BigInt): Boolean = {
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)

    val expandedEnd = seq.head.value + seq.head.value * seq.tailPrimorial

    require(countAcceptedHeadMultiplesBetween(seq, seq.head.value, expandedEnd) == period)

    assert(assertExpandedOldAcceptedCount(seq, period))
    assert(countAcceptedBetween(seq, seq.head.value, expandedEnd) == period * seq.head.value)
    assert(assertAcceptedCountSplitByHead(seq, seq.head.value, expandedEnd))
    assert(countAcceptedBetween(seq, seq.head.value, expandedEnd) ==
      countAcceptedHeadMultiplesBetween(seq, seq.head.value, expandedEnd) +
        countAcceptedHeadNonMultiplesBetween(seq, seq.head.value, expandedEnd))
    countAcceptedHeadNonMultiplesBetween(seq, seq.head.value, expandedEnd) ==
      period * (seq.head.value - BigInt(1))
  }.holds

  def assertGeneratedHeadMultiplesPrefixExpandedCount(
    seq: SpecSieveSequence,
    period: BigInt
  ): Boolean = {
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(Calc.mod(seq.tailPrimorial, seq.head.value) != BigInt(0))

    val expandedIndex = period * seq.head.value

    assert(seq.head.value > BigInt(0))
    assert(expandedIndex >= BigInt(0))
    assert(assertGeneratedHeadMultiplesRangeMatchesStrideOffsets(seq, period))
    assert(
      countGeneratedHeadMultiplesRange(seq, BigInt(0), expandedIndex) ==
        countGeneratedHeadMultiplesByStrideOffsets(seq, BigInt(0), period)
    )
    assert(assertGeneratedHeadMultiplesByStrideOffsetsCount(seq, BigInt(0), period))
    assert(countGeneratedHeadMultiplesByStrideOffsets(seq, BigInt(0), period) == period)
    assert(assertGeneratedHeadMultiplesPrefixMatchesRange(seq, expandedIndex))
    countGeneratedHeadMultiplesPrefix(seq, expandedIndex) == period
  }.holds



  // ── Public counting functions ─────────────────────────────────────────

  def countAcceptedBetween(seq: SpecSieveSequence, from: BigInt, until: BigInt): BigInt = {
    require(from >= seq.head.value)
    require(from <= until)
    decreases(until - from)

    if (from == until) {
      BigInt(0)
    } else if (seq.accepts(from)) {
      BigInt(1) + countAcceptedBetween(seq, from + BigInt(1), until)
    } else {
      countAcceptedBetween(seq, from + BigInt(1), until)
    }
  }.ensuring(res => res >= BigInt(0) && res <= until - from)

  def countAcceptedHeadMultiplesBetween(seq: SpecSieveSequence, from: BigInt, until: BigInt): BigInt = {
    require(from >= seq.head.value)
    require(from <= until)
    decreases(until - from)

    if (from == until) {
      BigInt(0)
    } else if (seq.accepts(from) && Calc.mod(from, seq.head.value) == BigInt(0)) {
      BigInt(1) + countAcceptedHeadMultiplesBetween(seq, from + BigInt(1), until)
    } else {
      countAcceptedHeadMultiplesBetween(seq, from + BigInt(1), until)
    }
  }.ensuring(res => res >= BigInt(0) && res <= until - from)

  def countAcceptedHeadNonMultiplesBetween(seq: SpecSieveSequence, from: BigInt, until: BigInt): BigInt = {
    require(from >= seq.head.value)
    require(from <= until)
    decreases(until - from)

    if (from == until) {
      BigInt(0)
    } else if (seq.accepts(from) && Calc.mod(from, seq.head.value) != BigInt(0)) {
      BigInt(1) + countAcceptedHeadNonMultiplesBetween(seq, from + BigInt(1), until)
    } else {
      countAcceptedHeadNonMultiplesBetween(seq, from + BigInt(1), until)
    }
  }.ensuring(res => res >= BigInt(0) && res <= until - from)

  def generatedHeadMultipleIndicator(seq: SpecSieveSequence, index: BigInt): BigInt = {
    require(index >= BigInt(0))

    assert(seq.head.value != BigInt(0))
    if (Calc.mod(seq.apply(index), seq.head.value) == BigInt(0)) {
      BigInt(1)
    } else {
      BigInt(0)
    }
  }.ensuring(res => res >= BigInt(0) && res <= BigInt(1))

  def countGeneratedHeadMultiplesPrefix(seq: SpecSieveSequence, k: BigInt): BigInt = {
    require(k >= BigInt(0))
    decreases(k)

    if (k == BigInt(0)) {
      BigInt(0)
    } else {
      val previous = k - BigInt(1)
      val rest = countGeneratedHeadMultiplesPrefix(seq, previous)

      assert(seq.head.value != BigInt(0))
      if (Calc.mod(seq.apply(previous), seq.head.value) == BigInt(0)) {
        rest + BigInt(1)
      } else {
        rest
      }
    }
  }.ensuring(res => res >= BigInt(0) && res <= k)

  def countGeneratedHeadMultiplesRange(seq: SpecSieveSequence, from: BigInt, count: BigInt): BigInt = {
    require(from >= BigInt(0))
    require(count >= BigInt(0))
    decreases(count)

    if (count == BigInt(0)) {
      BigInt(0)
    } else {
      val previousCount = count - BigInt(1)
      val current = from + previousCount
      val rest = countGeneratedHeadMultiplesRange(seq, from, previousCount)

      assert(seq.head.value != BigInt(0))
      assert(current >= BigInt(0))
      if (Calc.mod(seq.apply(current), seq.head.value) == BigInt(0)) {
        rest + BigInt(1)
      } else {
        rest
      }
    }
  }.ensuring(res => res >= BigInt(0) && res <= count)

  // ── Private helpers ───────────────────────────────────────────────────

  private def assertBlockShiftMultiple(seq: SpecSieveSequence, k: BigInt, n: BigInt, period: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(n >= BigInt(0))
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    SpecSieveSeqPeriodProperties.assertBlockShiftMultiple(seq, k, n, period)
  }.holds

  private def assertGeneratedHeadMultiplesRangeFront(
    seq: SpecSieveSequence,
    from: BigInt,
    count: BigInt
  ): Boolean = {
    require(from >= BigInt(0))
    require(count > BigInt(0))
    decreases(count)

    val tailFrom = from + BigInt(1)
    val tailCount = count - BigInt(1)

    if (count == BigInt(1)) {
      assert(tailCount == BigInt(0))
      if (Calc.mod(seq.apply(from), seq.head.value) == BigInt(0)) {
        assert(generatedHeadMultipleIndicator(seq, from) == BigInt(1))
        assert(countGeneratedHeadMultiplesRange(seq, from, count) == BigInt(1))
      } else {
        assert(generatedHeadMultipleIndicator(seq, from) == BigInt(0))
        assert(countGeneratedHeadMultiplesRange(seq, from, count) == BigInt(0))
      }
      countGeneratedHeadMultiplesRange(seq, from, count) ==
        generatedHeadMultipleIndicator(seq, from) +
          countGeneratedHeadMultiplesRange(seq, tailFrom, tailCount)
    } else {
      val previousCount = count - BigInt(1)
      val previousTailCount = previousCount - BigInt(1)
      val last = from + previousCount

      assert(previousCount > BigInt(0))
      assert(previousTailCount >= BigInt(0))
      assert(last >= BigInt(0))
      assert(assertGeneratedHeadMultiplesRangeFront(seq, from, previousCount))
      assert(
        countGeneratedHeadMultiplesRange(seq, from, previousCount) ==
          generatedHeadMultipleIndicator(seq, from) +
            countGeneratedHeadMultiplesRange(seq, tailFrom, previousTailCount)
      )

      if (Calc.mod(seq.apply(last), seq.head.value) == BigInt(0)) {
        assert(generatedHeadMultipleIndicator(seq, last) == BigInt(1))
        assert(countGeneratedHeadMultiplesRange(seq, from, count) ==
          countGeneratedHeadMultiplesRange(seq, from, previousCount) + BigInt(1))
        assert(countGeneratedHeadMultiplesRange(seq, tailFrom, tailCount) ==
          countGeneratedHeadMultiplesRange(seq, tailFrom, previousTailCount) + BigInt(1))
      } else {
        assert(generatedHeadMultipleIndicator(seq, last) == BigInt(0))
        assert(countGeneratedHeadMultiplesRange(seq, from, count) ==
          countGeneratedHeadMultiplesRange(seq, from, previousCount))
        assert(countGeneratedHeadMultiplesRange(seq, tailFrom, tailCount) ==
          countGeneratedHeadMultiplesRange(seq, tailFrom, previousTailCount))
      }

      countGeneratedHeadMultiplesRange(seq, from, count) ==
        generatedHeadMultipleIndicator(seq, from) +
          countGeneratedHeadMultiplesRange(seq, tailFrom, tailCount)
    }
  }.holds

  private def assertGeneratedHeadMultiplesRangeAppend(
    seq: SpecSieveSequence,
    from: BigInt,
    left: BigInt,
    right: BigInt
  ): Boolean = {
    require(from >= BigInt(0))
    require(left >= BigInt(0))
    require(right >= BigInt(0))
    decreases(right)

    if (right == BigInt(0)) {
      countGeneratedHeadMultiplesRange(seq, from, left + right) ==
        countGeneratedHeadMultiplesRange(seq, from, left) +
          countGeneratedHeadMultiplesRange(seq, from + left, right)
    } else {
      val previousRight = right - BigInt(1)
      val previousTotal = left + previousRight
      val current = from + previousTotal

      assert(previousRight >= BigInt(0))
      assert(previousTotal >= BigInt(0))
      assert(current >= BigInt(0))
      assert(assertGeneratedHeadMultiplesRangeAppend(seq, from, left, previousRight))
      assert(
        countGeneratedHeadMultiplesRange(seq, from, left + previousRight) ==
          countGeneratedHeadMultiplesRange(seq, from, left) +
            countGeneratedHeadMultiplesRange(seq, from + left, previousRight)
      )

      if (Calc.mod(seq.apply(current), seq.head.value) == BigInt(0)) {
        assert(countGeneratedHeadMultiplesRange(seq, from, left + right) ==
          countGeneratedHeadMultiplesRange(seq, from, left + previousRight) + BigInt(1))
        assert(countGeneratedHeadMultiplesRange(seq, from + left, right) ==
          countGeneratedHeadMultiplesRange(seq, from + left, previousRight) + BigInt(1))
      } else {
        assert(countGeneratedHeadMultiplesRange(seq, from, left + right) ==
          countGeneratedHeadMultiplesRange(seq, from, left + previousRight))
        assert(countGeneratedHeadMultiplesRange(seq, from + left, right) ==
          countGeneratedHeadMultiplesRange(seq, from + left, previousRight))
      }

      countGeneratedHeadMultiplesRange(seq, from, left + right) ==
        countGeneratedHeadMultiplesRange(seq, from, left) +
          countGeneratedHeadMultiplesRange(seq, from + left, right)
    }
  }.holds

  private def countGeneratedHeadMultiplesStrideFrom(
    seq: SpecSieveSequence,
    offset: BigInt,
    i: BigInt,
    period: BigInt
  ): BigInt = {
    require(offset >= BigInt(0))
    require(i >= BigInt(0))
    require(i <= seq.head.value)
    require(period > BigInt(0))
    decreases(seq.head.value - i)

    if (i == seq.head.value) {
      BigInt(0)
    } else {
      val current = offset + i * period
      val rest = countGeneratedHeadMultiplesStrideFrom(seq, offset, i + BigInt(1), period)

      assert(seq.head.value != BigInt(0))
      assert(current >= BigInt(0))
      if (Calc.mod(seq.apply(current), seq.head.value) == BigInt(0)) {
        rest + BigInt(1)
      } else {
        rest
      }
    }
  }.ensuring(res => res >= BigInt(0) && res <= seq.head.value - i)

  private def countGeneratedHeadMultiplesStrideUntil(
    seq: SpecSieveSequence,
    offset: BigInt,
    i: BigInt,
    limit: BigInt,
    period: BigInt
  ): BigInt = {
    require(offset >= BigInt(0))
    require(i >= BigInt(0))
    require(limit >= BigInt(0))
    require(i <= limit)
    require(limit <= seq.head.value)
    require(period > BigInt(0))
    decreases(limit - i)

    if (i == limit) {
      BigInt(0)
    } else {
      val current = offset + i * period
      val rest = countGeneratedHeadMultiplesStrideUntil(
        seq, offset, i + BigInt(1), limit, period
      )

      assert(seq.head.value != BigInt(0))
      assert(current >= BigInt(0))
      if (Calc.mod(seq.apply(current), seq.head.value) == BigInt(0)) {
        rest + BigInt(1)
      } else {
        rest
      }
    }
  }.ensuring(res => res >= BigInt(0) && res <= limit - i)

  private def assertGeneratedHeadMultiplesStrideUntilStep(
    seq: SpecSieveSequence,
    offset: BigInt,
    i: BigInt,
    limit: BigInt,
    period: BigInt
  ): Boolean = {
    require(offset >= BigInt(0))
    require(i >= BigInt(0))
    require(limit >= BigInt(0))
    require(i <= limit)
    require(limit < seq.head.value)
    require(period > BigInt(0))
    decreases(limit - i)

    val newLimit = limit + BigInt(1)
    val newIndex = offset + limit * period

    assert(newLimit <= seq.head.value)
    assert(newIndex >= BigInt(0))

    if (i == limit) {
      if (Calc.mod(seq.apply(newIndex), seq.head.value) == BigInt(0)) {
        assert(generatedHeadMultipleIndicator(seq, newIndex) == BigInt(1))
        assert(countGeneratedHeadMultiplesStrideUntil(seq, offset, i, newLimit, period) == BigInt(1))
      } else {
        assert(generatedHeadMultipleIndicator(seq, newIndex) == BigInt(0))
        assert(countGeneratedHeadMultiplesStrideUntil(seq, offset, i, newLimit, period) == BigInt(0))
      }
      countGeneratedHeadMultiplesStrideUntil(seq, offset, i, newLimit, period) ==
        countGeneratedHeadMultiplesStrideUntil(seq, offset, i, limit, period) +
          generatedHeadMultipleIndicator(seq, newIndex)
    } else {
      val current = offset + i * period

      assert(current >= BigInt(0))
      assert(assertGeneratedHeadMultiplesStrideUntilStep(
        seq, offset, i + BigInt(1), limit, period
      ))
      if (Calc.mod(seq.apply(current), seq.head.value) == BigInt(0)) {
        assert(countGeneratedHeadMultiplesStrideUntil(seq, offset, i, newLimit, period) ==
          countGeneratedHeadMultiplesStrideUntil(seq, offset, i + BigInt(1), newLimit, period) + BigInt(1))
        assert(countGeneratedHeadMultiplesStrideUntil(seq, offset, i, limit, period) ==
          countGeneratedHeadMultiplesStrideUntil(seq, offset, i + BigInt(1), limit, period) + BigInt(1))
      } else {
        assert(countGeneratedHeadMultiplesStrideUntil(seq, offset, i, newLimit, period) ==
          countGeneratedHeadMultiplesStrideUntil(seq, offset, i + BigInt(1), newLimit, period))
        assert(countGeneratedHeadMultiplesStrideUntil(seq, offset, i, limit, period) ==
          countGeneratedHeadMultiplesStrideUntil(seq, offset, i + BigInt(1), limit, period))
      }
      countGeneratedHeadMultiplesStrideUntil(seq, offset, i, newLimit, period) ==
        countGeneratedHeadMultiplesStrideUntil(seq, offset, i, limit, period) +
          generatedHeadMultipleIndicator(seq, newIndex)
    }
  }.holds

  private def assertGeneratedHeadMultiplesStrideFromMatchesUntil(
    seq: SpecSieveSequence,
    offset: BigInt,
    i: BigInt,
    period: BigInt
  ): Boolean = {
    require(offset >= BigInt(0))
    require(i >= BigInt(0))
    require(i <= seq.head.value)
    require(period > BigInt(0))
    decreases(seq.head.value - i)

    if (i == seq.head.value) {
      countGeneratedHeadMultiplesStrideFrom(seq, offset, i, period) ==
        countGeneratedHeadMultiplesStrideUntil(seq, offset, i, seq.head.value, period)
    } else {
      assert(assertGeneratedHeadMultiplesStrideFromMatchesUntil(
        seq, offset, i + BigInt(1), period
      ))
      countGeneratedHeadMultiplesStrideFrom(seq, offset, i, period) ==
        countGeneratedHeadMultiplesStrideUntil(seq, offset, i, seq.head.value, period)
    }
  }.holds

  private def assertGeneratedHeadMultiplesStrideMatchesZeroOffsets(
    seq: SpecSieveSequence,
    offset: BigInt,
    i: BigInt,
    period: BigInt
  ): Boolean = {
    require(offset >= BigInt(0))
    require(i >= BigInt(0))
    require(i <= seq.head.value)
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    decreases(seq.head.value - i)

    if (i == seq.head.value) {
      countGeneratedHeadMultiplesStrideFrom(seq, offset, i, period) ==
        SieveUtils.countZeroOffsets(seq.apply(offset), seq.tailPrimorial, seq.head.value, i)
    } else {
      val current = offset + i * period

      assert(current >= BigInt(0))
      assert(assertBlockShiftMultiple(seq, offset, i, period))
      assert(seq.apply(current) == seq.apply(offset) + i * seq.tailPrimorial)
      assert(assertGeneratedHeadMultiplesStrideMatchesZeroOffsets(
        seq, offset, i + BigInt(1), period
      ))
      countGeneratedHeadMultiplesStrideFrom(seq, offset, i, period) ==
        SieveUtils.countZeroOffsets(seq.apply(offset), seq.tailPrimorial, seq.head.value, i)
    }
  }.holds

  private def assertGeneratedHeadMultiplesStrideOne(
    seq: SpecSieveSequence,
    offset: BigInt,
    period: BigInt
  ): Boolean = {
    require(offset >= BigInt(0))
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(Calc.mod(seq.tailPrimorial, seq.head.value) != BigInt(0))

    assert(Prime.isPrime(seq.head.value))
    assert(seq.head.value >= BigInt(2))
    assertGeneratedHeadMultiplesStrideMatchesZeroOffsets(seq, offset, BigInt(0), period)
    SieveUtils.assertCountZeroOffsetsOne(seq.apply(offset), seq.tailPrimorial, seq.head.value)
    countGeneratedHeadMultiplesStrideFrom(seq, offset, BigInt(0), period) == BigInt(1)
  }.holds

  private def countGeneratedHeadMultiplesByStrideOffsets(
    seq: SpecSieveSequence,
    offset: BigInt,
    period: BigInt
  ): BigInt = {
    require(offset >= BigInt(0))
    require(offset <= period)
    require(period > BigInt(0))
    decreases(period - offset)

    if (offset == period) {
      BigInt(0)
    } else {
      val current = countGeneratedHeadMultiplesStrideFrom(seq, offset, BigInt(0), period)
      val rest = countGeneratedHeadMultiplesByStrideOffsets(seq, offset + BigInt(1), period)

      current + rest
    }
  }.ensuring(res => res >= BigInt(0) && res <= (period - offset) * seq.head.value)

  private def countGeneratedHeadMultiplesByStrideOffsetsUntil(
    seq: SpecSieveSequence,
    offset: BigInt,
    limit: BigInt,
    period: BigInt
  ): BigInt = {
    require(offset >= BigInt(0))
    require(offset <= period)
    require(limit >= BigInt(0))
    require(limit <= seq.head.value)
    require(period > BigInt(0))
    decreases(period - offset)

    if (offset == period) {
      BigInt(0)
    } else {
      val current = countGeneratedHeadMultiplesStrideUntil(
        seq, offset, BigInt(0), limit, period
      )
      val rest = countGeneratedHeadMultiplesByStrideOffsetsUntil(
        seq, offset + BigInt(1), limit, period
      )

      current + rest
    }
  }.ensuring(res => res >= BigInt(0) && res <= (period - offset) * limit)

  private def assertGeneratedHeadMultiplesByStrideOffsetsMatchesUntil(
    seq: SpecSieveSequence,
    offset: BigInt,
    period: BigInt
  ): Boolean = {
    require(offset >= BigInt(0))
    require(offset <= period)
    require(period > BigInt(0))
    decreases(period - offset)

    if (offset == period) {
      countGeneratedHeadMultiplesByStrideOffsets(seq, offset, period) ==
        countGeneratedHeadMultiplesByStrideOffsetsUntil(seq, offset, seq.head.value, period)
    } else {
      assert(assertGeneratedHeadMultiplesStrideFromMatchesUntil(
        seq, offset, BigInt(0), period
      ))
      assert(assertGeneratedHeadMultiplesByStrideOffsetsMatchesUntil(
        seq, offset + BigInt(1), period
      ))
      countGeneratedHeadMultiplesByStrideOffsets(seq, offset, period) ==
        countGeneratedHeadMultiplesByStrideOffsetsUntil(seq, offset, seq.head.value, period)
    }
  }.holds

  private def assertGeneratedHeadMultiplesByStrideOffsetsUntilStep(
    seq: SpecSieveSequence,
    offset: BigInt,
    limit: BigInt,
    period: BigInt
  ): Boolean = {
    require(offset >= BigInt(0))
    require(offset <= period)
    require(limit >= BigInt(0))
    require(limit < seq.head.value)
    require(period > BigInt(0))
    decreases(period - offset)

    val newLimit = limit + BigInt(1)
    val rowStart = limit * period + offset
    val rowCount = period - offset

    assert(newLimit <= seq.head.value)
    assert(rowStart >= BigInt(0))
    assert(rowCount >= BigInt(0))

    if (offset == period) {
      assert(rowCount == BigInt(0))
      countGeneratedHeadMultiplesByStrideOffsetsUntil(seq, offset, newLimit, period) ==
        countGeneratedHeadMultiplesByStrideOffsetsUntil(seq, offset, limit, period) +
          countGeneratedHeadMultiplesRange(seq, rowStart, rowCount)
    } else {
      val nextOffset = offset + BigInt(1)
      val rowTailStart = limit * period + nextOffset
      val rowTailCount = period - nextOffset

      assert(nextOffset <= period)
      assert(rowCount > BigInt(0))
      assert(rowTailCount >= BigInt(0))
      assert(rowTailStart == rowStart + BigInt(1))
      assert(assertGeneratedHeadMultiplesStrideUntilStep(
        seq, offset, BigInt(0), limit, period
      ))
      assert(assertGeneratedHeadMultiplesByStrideOffsetsUntilStep(
        seq, nextOffset, limit, period
      ))
      assert(assertGeneratedHeadMultiplesRangeFront(seq, rowStart, rowCount))
      assert(
        countGeneratedHeadMultiplesRange(seq, rowStart, rowCount) ==
          generatedHeadMultipleIndicator(seq, rowStart) +
            countGeneratedHeadMultiplesRange(seq, rowTailStart, rowTailCount)
      )
      assert(rowStart == offset + limit * period)
      countGeneratedHeadMultiplesByStrideOffsetsUntil(seq, offset, newLimit, period) ==
        countGeneratedHeadMultiplesByStrideOffsetsUntil(seq, offset, limit, period) +
          countGeneratedHeadMultiplesRange(seq, rowStart, rowCount)
    }
  }.holds

  private def assertGeneratedHeadMultiplesByStrideOffsetsUntilZero(
    seq: SpecSieveSequence,
    offset: BigInt,
    period: BigInt
  ): Boolean = {
    require(offset >= BigInt(0))
    require(offset <= period)
    require(period > BigInt(0))
    decreases(period - offset)

    if (offset == period) {
      countGeneratedHeadMultiplesByStrideOffsetsUntil(seq, offset, BigInt(0), period) ==
        BigInt(0)
    } else {
      assert(countGeneratedHeadMultiplesStrideUntil(
        seq, offset, BigInt(0), BigInt(0), period
      ) == BigInt(0))
      assert(assertGeneratedHeadMultiplesByStrideOffsetsUntilZero(
        seq, offset + BigInt(1), period
      ))
      countGeneratedHeadMultiplesByStrideOffsetsUntil(seq, offset, BigInt(0), period) ==
        BigInt(0)
    }
  }.holds

  private def assertGeneratedHeadMultiplesRangeMatchesStrideOffsetsUntil(
    seq: SpecSieveSequence,
    limit: BigInt,
    period: BigInt
  ): Boolean = {
    require(limit >= BigInt(0))
    require(limit <= seq.head.value)
    require(period > BigInt(0))
    decreases(limit)

    val total = period * limit

    assert(total >= BigInt(0))
    if (limit == BigInt(0)) {
      assert(assertGeneratedHeadMultiplesByStrideOffsetsUntilZero(seq, BigInt(0), period))
      countGeneratedHeadMultiplesRange(seq, BigInt(0), total) ==
        countGeneratedHeadMultiplesByStrideOffsetsUntil(seq, BigInt(0), limit, period)
    } else {
      val previousLimit = limit - BigInt(1)
      val previousTotal = period * previousLimit

      assert(previousLimit >= BigInt(0))
      assert(previousLimit < seq.head.value)
      assert(previousTotal >= BigInt(0))
      assert(total == previousTotal + period)
      assert(assertGeneratedHeadMultiplesRangeMatchesStrideOffsetsUntil(
        seq, previousLimit, period
      ))
      assert(
        countGeneratedHeadMultiplesRange(seq, BigInt(0), previousTotal) ==
          countGeneratedHeadMultiplesByStrideOffsetsUntil(
            seq, BigInt(0), previousLimit, period
          )
      )
      assert(assertGeneratedHeadMultiplesRangeAppend(
        seq, BigInt(0), previousTotal, period
      ))
      assert(
        countGeneratedHeadMultiplesRange(seq, BigInt(0), total) ==
          countGeneratedHeadMultiplesRange(seq, BigInt(0), previousTotal) +
            countGeneratedHeadMultiplesRange(seq, previousTotal, period)
      )
      assert(assertGeneratedHeadMultiplesByStrideOffsetsUntilStep(
        seq, BigInt(0), previousLimit, period
      ))
      assert(
        countGeneratedHeadMultiplesByStrideOffsetsUntil(seq, BigInt(0), limit, period) ==
          countGeneratedHeadMultiplesByStrideOffsetsUntil(
            seq, BigInt(0), previousLimit, period
          ) +
            countGeneratedHeadMultiplesRange(seq, previousTotal, period)
      )

      countGeneratedHeadMultiplesRange(seq, BigInt(0), total) ==
        countGeneratedHeadMultiplesByStrideOffsetsUntil(seq, BigInt(0), limit, period)
    }
  }.holds

  private def assertGeneratedHeadMultiplesByStrideOffsetsCount(
    seq: SpecSieveSequence,
    offset: BigInt,
    period: BigInt
  ): Boolean = {
    require(offset >= BigInt(0))
    require(offset <= period)
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(Calc.mod(seq.tailPrimorial, seq.head.value) != BigInt(0))
    decreases(period - offset)

    if (offset == period) {
      countGeneratedHeadMultiplesByStrideOffsets(seq, offset, period) ==
        period - offset
    } else {
      assertGeneratedHeadMultiplesStrideOne(seq, offset, period)
      assert(countGeneratedHeadMultiplesStrideFrom(seq, offset, BigInt(0), period) == BigInt(1))
      assertGeneratedHeadMultiplesByStrideOffsetsCount(seq, offset + BigInt(1), period)
      countGeneratedHeadMultiplesByStrideOffsets(seq, offset, period) ==
        period - offset
    }
  }.holds

  private def assertGeneratedHeadMultiplesRangeMatchesStrideOffsets(
    seq: SpecSieveSequence,
    period: BigInt
  ): Boolean = {
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(Calc.mod(seq.tailPrimorial, seq.head.value) != BigInt(0))

    val expandedIndex = period * seq.head.value

    assert(seq.head.value > BigInt(0))
    assert(expandedIndex >= BigInt(0))
    assert(assertGeneratedHeadMultiplesRangeMatchesStrideOffsetsUntil(seq, seq.head.value, period))
    assert(
      countGeneratedHeadMultiplesRange(seq, BigInt(0), expandedIndex) ==
        countGeneratedHeadMultiplesByStrideOffsetsUntil(seq, BigInt(0), seq.head.value, period)
    )
    assert(assertGeneratedHeadMultiplesByStrideOffsetsMatchesUntil(seq, BigInt(0), period))
    assertGeneratedHeadMultiplesPrefixMatchesRange(seq, expandedIndex)
    assertGeneratedHeadMultiplesByStrideOffsetsCount(seq, BigInt(0), period)
    countGeneratedHeadMultiplesRange(seq, BigInt(0), expandedIndex) ==
      countGeneratedHeadMultiplesByStrideOffsets(seq, BigInt(0), period)
  }.holds

  private def assertGeneratedHeadMultiplesPrefixMatchesRange(seq: SpecSieveSequence, k: BigInt): Boolean = {
    require(k >= BigInt(0))
    decreases(k)

    if (k == BigInt(0)) {
      countGeneratedHeadMultiplesPrefix(seq, k) ==
        countGeneratedHeadMultiplesRange(seq, BigInt(0), k)
    } else {
      val previous = k - BigInt(1)

      assertGeneratedHeadMultiplesPrefixMatchesRange(seq, previous)
      countGeneratedHeadMultiplesPrefix(seq, k) ==
        countGeneratedHeadMultiplesRange(seq, BigInt(0), k)
    }
  }.holds

  private def countNoAcceptedBetween(seq: SpecSieveSequence, from: BigInt, until: BigInt): Boolean = {
    require(from >= seq.head.value)
    require(from <= until)
    require(seq.noAcceptedBetween(from, until))
    decreases(until - from)

    if (from == until) {
      countAcceptedBetween(seq, from, until) == BigInt(0)
    } else {
      assert(!seq.accepts(from))
      assert(seq.noAcceptedBetween(from + BigInt(1), until))
      assert(countNoAcceptedBetween(seq, from + BigInt(1), until))
      countAcceptedBetween(seq, from, until) == BigInt(0)
    }
  }.holds

  private def countNoAcceptedHeadMultiplesBetween(seq: SpecSieveSequence, from: BigInt, until: BigInt): Boolean = {
    require(from >= seq.head.value)
    require(from <= until)
    require(seq.noAcceptedBetween(from, until))
    decreases(until - from)

    if (from == until) {
      countAcceptedHeadMultiplesBetween(seq, from, until) == BigInt(0)
    } else {
      assert(!seq.accepts(from))
      assert(seq.noAcceptedBetween(from + BigInt(1), until))
      assert(countNoAcceptedHeadMultiplesBetween(seq, from + BigInt(1), until))
      countAcceptedHeadMultiplesBetween(seq, from, until) == BigInt(0)
    }
  }.holds

  private def assertAcceptedCountSplitByHead(
    seq: SpecSieveSequence,
    from: BigInt,
    until: BigInt
  ): Boolean = {
    require(from >= seq.head.value)
    require(from <= until)
    decreases(until - from)

    if (from == until) {
      countAcceptedBetween(seq, from, until) ==
        countAcceptedHeadMultiplesBetween(seq, from, until) +
          countAcceptedHeadNonMultiplesBetween(seq, from, until)
    } else {
      val next = from + BigInt(1)

      assert(assertAcceptedCountSplitByHead(seq, next, until))

      if (seq.accepts(from)) {
        val remainder = Calc.mod(from, seq.head.value)

        if (remainder == BigInt(0)) {
          assert(Calc.mod(from, seq.head.value) == BigInt(0))
        } else {
          assert(Calc.mod(from, seq.head.value) != BigInt(0))
        }
      }

      countAcceptedBetween(seq, from, until) ==
        countAcceptedHeadMultiplesBetween(seq, from, until) +
          countAcceptedHeadNonMultiplesBetween(seq, from, until)
    }
  }.holds

  private def assertCountAcceptedBetweenAppend(
    seq: SpecSieveSequence,
    from: BigInt,
    middle: BigInt,
    until: BigInt
  ): Boolean = {
    require(from >= seq.head.value)
    require(from <= middle)
    require(middle <= until)
    decreases(middle - from)

    if (from == middle) {
      countAcceptedBetween(seq, from, until) ==
        countAcceptedBetween(seq, from, middle) + countAcceptedBetween(seq, middle, until)
    } else {
      assert(from < middle)
      assert(from + BigInt(1) <= middle)
      assert(assertCountAcceptedBetweenAppend(seq, from + BigInt(1), middle, until))
      countAcceptedBetween(seq, from, until) ==
        countAcceptedBetween(seq, from, middle) + countAcceptedBetween(seq, middle, until)
    }
  }.holds

  private def assertCountAcceptedHeadMultiplesBetweenAppend(
    seq: SpecSieveSequence,
    from: BigInt,
    middle: BigInt,
    until: BigInt
  ): Boolean = {
    require(from >= seq.head.value)
    require(from <= middle)
    require(middle <= until)
    decreases(middle - from)

    if (from == middle) {
      countAcceptedHeadMultiplesBetween(seq, from, until) ==
        countAcceptedHeadMultiplesBetween(seq, from, middle) +
          countAcceptedHeadMultiplesBetween(seq, middle, until)
    } else {
      assert(from < middle)
      assert(from + BigInt(1) <= middle)
      assert(assertCountAcceptedHeadMultiplesBetweenAppend(seq, from + BigInt(1), middle, until))
      countAcceptedHeadMultiplesBetween(seq, from, until) ==
        countAcceptedHeadMultiplesBetween(seq, from, middle) +
          countAcceptedHeadMultiplesBetween(seq, middle, until)
    }
  }.holds

  private def assertCountAcceptedHeadNonMultiplesBetweenAppend(
    seq: SpecSieveSequence,
    from: BigInt,
    middle: BigInt,
    until: BigInt
  ): Boolean = {
    require(from >= seq.head.value)
    require(from <= middle)
    require(middle <= until)
    decreases(middle - from)

    if (from == middle) {
      countAcceptedHeadNonMultiplesBetween(seq, from, until) ==
        countAcceptedHeadNonMultiplesBetween(seq, from, middle) +
          countAcceptedHeadNonMultiplesBetween(seq, middle, until)
    } else {
      assert(from < middle)
      assert(from + BigInt(1) <= middle)
      assert(assertCountAcceptedHeadNonMultiplesBetweenAppend(seq, from + BigInt(1), middle, until))
      countAcceptedHeadNonMultiplesBetween(seq, from, until) ==
        countAcceptedHeadNonMultiplesBetween(seq, from, middle) +
          countAcceptedHeadNonMultiplesBetween(seq, middle, until)
    }
  }.holds
}
