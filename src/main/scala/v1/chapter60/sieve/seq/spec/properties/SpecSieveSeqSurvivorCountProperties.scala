package v1.chapter60.sieve.seq.spec.properties

import stainless.annotation.extern
import stainless.collection.List
import stainless.lang.*
import v1.chapter2.div.Calc
import v1.chapter2.div.properties.{AdditionAndMultiplication, ModIdempotence, ModOperations}
import v1.chapter3.list.{ListBoundUtils, ListUtils}
import v1.chapter4.cycle.gap.GapCycle
import v1.chapter4.cycle.integral.recursive.CycleIntegral
import v1.chapter4.cycle.integral.recursive.properties.CycleIntegralProperties
import v1.chapter4.cycle.memory.properties.MemCycleProperties
import v1.chapter5.prime.*
import v1.chapter5.prime.properties.PrimeProperties
import v1.chapter6.seq.sieve.SieveUtils
import v1.chapter60.sieve.seq.spec.SpecSieveSequence

import scala.annotation.tailrec

final case class SpecSieveSeqSurvivorCountProperties(seq: SpecSieveSequence) {
  import seq.*

  def countAcceptedBetween(from: BigInt, until: BigInt): BigInt = {
    require(from >= head.value)
    require(from <= until)
    decreases(until - from)

    if (from == until) {
      BigInt(0)
    } else if (accepts(from)) {
      BigInt(1) + countAcceptedBetween(from + BigInt(1), until)
    } else {
      countAcceptedBetween(from + BigInt(1), until)
    }
  }.ensuring(res => res >= BigInt(0) && res <= until - from)

  def countAcceptedHeadMultiplesBetween(from: BigInt, until: BigInt): BigInt = {
    require(from >= head.value)
    require(from <= until)
    decreases(until - from)

    if (from == until) {
      BigInt(0)
    } else if (accepts(from) && Calc.mod(from, head.value) == BigInt(0)) {
      BigInt(1) + countAcceptedHeadMultiplesBetween(from + BigInt(1), until)
    } else {
      countAcceptedHeadMultiplesBetween(from + BigInt(1), until)
    }
  }.ensuring(res => res >= BigInt(0) && res <= until - from)

  def countAcceptedHeadNonMultiplesBetween(from: BigInt, until: BigInt): BigInt = {
    require(from >= head.value)
    require(from <= until)
    decreases(until - from)

    if (from == until) {
      BigInt(0)
    } else if (accepts(from) && Calc.mod(from, head.value) != BigInt(0)) {
      BigInt(1) + countAcceptedHeadNonMultiplesBetween(from + BigInt(1), until)
    } else {
      countAcceptedHeadNonMultiplesBetween(from + BigInt(1), until)
    }
  }.ensuring(res => res >= BigInt(0) && res <= until - from)

  def generatedHeadMultipleIndicator(index: BigInt): BigInt = {
    require(index >= BigInt(0))

    assert(head.value != BigInt(0))
    if (Calc.mod(apply(index), head.value) == BigInt(0)) {
      BigInt(1)
    } else {
      BigInt(0)
    }
  }.ensuring(res => res >= BigInt(0) && res <= BigInt(1))

  def countGeneratedHeadMultiplesPrefix(k: BigInt): BigInt = {
    require(k >= BigInt(0))
    decreases(k)

    if (k == BigInt(0)) {
      BigInt(0)
    } else {
      val previous = k - BigInt(1)
      val rest = countGeneratedHeadMultiplesPrefix(previous)

      assert(head.value != BigInt(0))
      if (Calc.mod(apply(previous), head.value) == BigInt(0)) {
        rest + BigInt(1)
      } else {
        rest
      }
    }
  }.ensuring(res => res >= BigInt(0) && res <= k)

  def countGeneratedHeadMultiplesRange(from: BigInt, count: BigInt): BigInt = {
    require(from >= BigInt(0))
    require(count >= BigInt(0))
    decreases(count)

    if (count == BigInt(0)) {
      BigInt(0)
    } else {
      val previousCount = count - BigInt(1)
      val current = from + previousCount
      val rest = countGeneratedHeadMultiplesRange(from, previousCount)

      assert(head.value != BigInt(0))
      assert(current >= BigInt(0))
      if (Calc.mod(apply(current), head.value) == BigInt(0)) {
        rest + BigInt(1)
      } else {
        rest
      }
    }
  }.ensuring(res => res >= BigInt(0) && res <= count)

  private def assertGeneratedHeadMultiplesRangeFront(
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
      if (Calc.mod(apply(from), head.value) == BigInt(0)) {
        assert(generatedHeadMultipleIndicator(from) == BigInt(1))
        assert(countGeneratedHeadMultiplesRange(from, count) == BigInt(1))
      } else {
        assert(generatedHeadMultipleIndicator(from) == BigInt(0))
        assert(countGeneratedHeadMultiplesRange(from, count) == BigInt(0))
      }
      countGeneratedHeadMultiplesRange(from, count) ==
        generatedHeadMultipleIndicator(from) +
          countGeneratedHeadMultiplesRange(tailFrom, tailCount)
    } else {
      val previousCount = count - BigInt(1)
      val previousTailCount = previousCount - BigInt(1)
      val last = from + previousCount

      assert(previousCount > BigInt(0))
      assert(previousTailCount >= BigInt(0))
      assert(last >= BigInt(0))
      assert(assertGeneratedHeadMultiplesRangeFront(from, previousCount))
      assert(
        countGeneratedHeadMultiplesRange(from, previousCount) ==
          generatedHeadMultipleIndicator(from) +
            countGeneratedHeadMultiplesRange(tailFrom, previousTailCount)
      )

      if (Calc.mod(apply(last), head.value) == BigInt(0)) {
        assert(generatedHeadMultipleIndicator(last) == BigInt(1))
        assert(countGeneratedHeadMultiplesRange(from, count) ==
          countGeneratedHeadMultiplesRange(from, previousCount) + BigInt(1))
        assert(countGeneratedHeadMultiplesRange(tailFrom, tailCount) ==
          countGeneratedHeadMultiplesRange(tailFrom, previousTailCount) + BigInt(1))
      } else {
        assert(generatedHeadMultipleIndicator(last) == BigInt(0))
        assert(countGeneratedHeadMultiplesRange(from, count) ==
          countGeneratedHeadMultiplesRange(from, previousCount))
        assert(countGeneratedHeadMultiplesRange(tailFrom, tailCount) ==
          countGeneratedHeadMultiplesRange(tailFrom, previousTailCount))
      }

      countGeneratedHeadMultiplesRange(from, count) ==
        generatedHeadMultipleIndicator(from) +
          countGeneratedHeadMultiplesRange(tailFrom, tailCount)
    }
  }.holds

  private def assertGeneratedHeadMultiplesRangeAppend(
    from: BigInt,
    left: BigInt,
    right: BigInt
  ): Boolean = {
    require(from >= BigInt(0))
    require(left >= BigInt(0))
    require(right >= BigInt(0))
    decreases(right)

    if (right == BigInt(0)) {
      countGeneratedHeadMultiplesRange(from, left + right) ==
        countGeneratedHeadMultiplesRange(from, left) +
          countGeneratedHeadMultiplesRange(from + left, right)
    } else {
      val previousRight = right - BigInt(1)
      val previousTotal = left + previousRight
      val current = from + previousTotal

      assert(previousRight >= BigInt(0))
      assert(previousTotal >= BigInt(0))
      assert(current >= BigInt(0))
      assert(assertGeneratedHeadMultiplesRangeAppend(from, left, previousRight))
      assert(
        countGeneratedHeadMultiplesRange(from, left + previousRight) ==
          countGeneratedHeadMultiplesRange(from, left) +
            countGeneratedHeadMultiplesRange(from + left, previousRight)
      )

      if (Calc.mod(apply(current), head.value) == BigInt(0)) {
        assert(countGeneratedHeadMultiplesRange(from, left + right) ==
          countGeneratedHeadMultiplesRange(from, left + previousRight) + BigInt(1))
        assert(countGeneratedHeadMultiplesRange(from + left, right) ==
          countGeneratedHeadMultiplesRange(from + left, previousRight) + BigInt(1))
      } else {
        assert(countGeneratedHeadMultiplesRange(from, left + right) ==
          countGeneratedHeadMultiplesRange(from, left + previousRight))
        assert(countGeneratedHeadMultiplesRange(from + left, right) ==
          countGeneratedHeadMultiplesRange(from + left, previousRight))
      }

      countGeneratedHeadMultiplesRange(from, left + right) ==
        countGeneratedHeadMultiplesRange(from, left) +
          countGeneratedHeadMultiplesRange(from + left, right)
    }
  }.holds

  private def countGeneratedHeadMultiplesStrideFrom(
    offset: BigInt,
    i: BigInt,
    period: BigInt
  ): BigInt = {
    require(offset >= BigInt(0))
    require(i >= BigInt(0))
    require(i <= head.value)
    require(period > BigInt(0))
    decreases(head.value - i)

    if (i == head.value) {
      BigInt(0)
    } else {
      val current = offset + i * period
      val rest = countGeneratedHeadMultiplesStrideFrom(offset, i + BigInt(1), period)

      assert(head.value != BigInt(0))
      assert(current >= BigInt(0))
      if (Calc.mod(apply(current), head.value) == BigInt(0)) {
        rest + BigInt(1)
      } else {
        rest
      }
    }
  }.ensuring(res => res >= BigInt(0) && res <= head.value - i)

  private def countGeneratedHeadMultiplesStrideUntil(
    offset: BigInt,
    i: BigInt,
    limit: BigInt,
    period: BigInt
  ): BigInt = {
    require(offset >= BigInt(0))
    require(i >= BigInt(0))
    require(limit >= BigInt(0))
    require(i <= limit)
    require(limit <= head.value)
    require(period > BigInt(0))
    decreases(limit - i)

    if (i == limit) {
      BigInt(0)
    } else {
      val current = offset + i * period
      val rest = countGeneratedHeadMultiplesStrideUntil(
        offset,
        i + BigInt(1),
        limit,
        period
      )

      assert(head.value != BigInt(0))
      assert(current >= BigInt(0))
      if (Calc.mod(apply(current), head.value) == BigInt(0)) {
        rest + BigInt(1)
      } else {
        rest
      }
    }
  }.ensuring(res => res >= BigInt(0) && res <= limit - i)

  private def assertGeneratedHeadMultiplesStrideUntilStep(
    offset: BigInt,
    i: BigInt,
    limit: BigInt,
    period: BigInt
  ): Boolean = {
    require(offset >= BigInt(0))
    require(i >= BigInt(0))
    require(limit >= BigInt(0))
    require(i <= limit)
    require(limit < head.value)
    require(period > BigInt(0))
    decreases(limit - i)

    val newLimit = limit + BigInt(1)
    val newIndex = offset + limit * period

    assert(newLimit <= head.value)
    assert(newIndex >= BigInt(0))

    if (i == limit) {
      if (Calc.mod(apply(newIndex), head.value) == BigInt(0)) {
        assert(generatedHeadMultipleIndicator(newIndex) == BigInt(1))
        assert(countGeneratedHeadMultiplesStrideUntil(offset, i, newLimit, period) == BigInt(1))
      } else {
        assert(generatedHeadMultipleIndicator(newIndex) == BigInt(0))
        assert(countGeneratedHeadMultiplesStrideUntil(offset, i, newLimit, period) == BigInt(0))
      }
      countGeneratedHeadMultiplesStrideUntil(offset, i, newLimit, period) ==
        countGeneratedHeadMultiplesStrideUntil(offset, i, limit, period) +
          generatedHeadMultipleIndicator(newIndex)
    } else {
      val current = offset + i * period

      assert(current >= BigInt(0))
      assert(assertGeneratedHeadMultiplesStrideUntilStep(
        offset,
        i + BigInt(1),
        limit,
        period
      ))
      if (Calc.mod(apply(current), head.value) == BigInt(0)) {
        assert(countGeneratedHeadMultiplesStrideUntil(offset, i, newLimit, period) ==
          countGeneratedHeadMultiplesStrideUntil(offset, i + BigInt(1), newLimit, period) + BigInt(1))
        assert(countGeneratedHeadMultiplesStrideUntil(offset, i, limit, period) ==
          countGeneratedHeadMultiplesStrideUntil(offset, i + BigInt(1), limit, period) + BigInt(1))
      } else {
        assert(countGeneratedHeadMultiplesStrideUntil(offset, i, newLimit, period) ==
          countGeneratedHeadMultiplesStrideUntil(offset, i + BigInt(1), newLimit, period))
        assert(countGeneratedHeadMultiplesStrideUntil(offset, i, limit, period) ==
          countGeneratedHeadMultiplesStrideUntil(offset, i + BigInt(1), limit, period))
      }
      countGeneratedHeadMultiplesStrideUntil(offset, i, newLimit, period) ==
        countGeneratedHeadMultiplesStrideUntil(offset, i, limit, period) +
          generatedHeadMultipleIndicator(newIndex)
    }
  }.holds

  private def assertGeneratedHeadMultiplesStrideFromMatchesUntil(
    offset: BigInt,
    i: BigInt,
    period: BigInt
  ): Boolean = {
    require(offset >= BigInt(0))
    require(i >= BigInt(0))
    require(i <= head.value)
    require(period > BigInt(0))
    decreases(head.value - i)

    if (i == head.value) {
      countGeneratedHeadMultiplesStrideFrom(offset, i, period) ==
        countGeneratedHeadMultiplesStrideUntil(offset, i, head.value, period)
    } else {
      assert(assertGeneratedHeadMultiplesStrideFromMatchesUntil(
        offset,
        i + BigInt(1),
        period
      ))
      countGeneratedHeadMultiplesStrideFrom(offset, i, period) ==
        countGeneratedHeadMultiplesStrideUntil(offset, i, head.value, period)
    }
  }.holds

  private def assertGeneratedHeadMultiplesStrideMatchesZeroOffsets(
    offset: BigInt,
    i: BigInt,
    period: BigInt
  ): Boolean = {
    require(offset >= BigInt(0))
    require(i >= BigInt(0))
    require(i <= head.value)
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)
    decreases(head.value - i)

    if (i == head.value) {
      countGeneratedHeadMultiplesStrideFrom(offset, i, period) ==
        SieveUtils.countZeroOffsets(apply(offset), tailPrimorial, head.value, i)
    } else {
      val current = offset + i * period

      assert(current >= BigInt(0))
      assert(assertBlockShiftMultiple(offset, i, period))
      assert(apply(current) == apply(offset) + i * tailPrimorial)
      assert(assertGeneratedHeadMultiplesStrideMatchesZeroOffsets(
        offset,
        i + BigInt(1),
        period
      ))
      countGeneratedHeadMultiplesStrideFrom(offset, i, period) ==
        SieveUtils.countZeroOffsets(apply(offset), tailPrimorial, head.value, i)
    }
  }.holds

  private def assertGeneratedHeadMultiplesStrideOne(
    offset: BigInt,
    period: BigInt
  ): Boolean = {
    require(offset >= BigInt(0))
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)
    require(Calc.mod(tailPrimorial, head.value) != BigInt(0))

    assert(Prime.isPrime(head.value))
    assert(head.value >= BigInt(2))
    assertGeneratedHeadMultiplesStrideMatchesZeroOffsets(offset, BigInt(0), period)
    SieveUtils.assertCountZeroOffsetsOne(apply(offset), tailPrimorial, head.value)
    countGeneratedHeadMultiplesStrideFrom(offset, BigInt(0), period) == BigInt(1)
  }.holds

  private def countGeneratedHeadMultiplesByStrideOffsets(
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
      val current = countGeneratedHeadMultiplesStrideFrom(offset, BigInt(0), period)
      val rest = countGeneratedHeadMultiplesByStrideOffsets(offset + BigInt(1), period)

      current + rest
    }
  }.ensuring(res => res >= BigInt(0) && res <= (period - offset) * head.value)

  private def countGeneratedHeadMultiplesByStrideOffsetsUntil(
    offset: BigInt,
    limit: BigInt,
    period: BigInt
  ): BigInt = {
    require(offset >= BigInt(0))
    require(offset <= period)
    require(limit >= BigInt(0))
    require(limit <= head.value)
    require(period > BigInt(0))
    decreases(period - offset)

    if (offset == period) {
      BigInt(0)
    } else {
      val current = countGeneratedHeadMultiplesStrideUntil(
        offset,
        BigInt(0),
        limit,
        period
      )
      val rest = countGeneratedHeadMultiplesByStrideOffsetsUntil(
        offset + BigInt(1),
        limit,
        period
      )

      current + rest
    }
  }.ensuring(res => res >= BigInt(0) && res <= (period - offset) * limit)

  private def assertGeneratedHeadMultiplesByStrideOffsetsMatchesUntil(
    offset: BigInt,
    period: BigInt
  ): Boolean = {
    require(offset >= BigInt(0))
    require(offset <= period)
    require(period > BigInt(0))
    decreases(period - offset)

    if (offset == period) {
      countGeneratedHeadMultiplesByStrideOffsets(offset, period) ==
        countGeneratedHeadMultiplesByStrideOffsetsUntil(offset, head.value, period)
    } else {
      assert(assertGeneratedHeadMultiplesStrideFromMatchesUntil(
        offset,
        BigInt(0),
        period
      ))
      assert(assertGeneratedHeadMultiplesByStrideOffsetsMatchesUntil(
        offset + BigInt(1),
        period
      ))
      countGeneratedHeadMultiplesByStrideOffsets(offset, period) ==
        countGeneratedHeadMultiplesByStrideOffsetsUntil(offset, head.value, period)
    }
  }.holds

  private def assertGeneratedHeadMultiplesByStrideOffsetsUntilStep(
    offset: BigInt,
    limit: BigInt,
    period: BigInt
  ): Boolean = {
    require(offset >= BigInt(0))
    require(offset <= period)
    require(limit >= BigInt(0))
    require(limit < head.value)
    require(period > BigInt(0))
    decreases(period - offset)

    val newLimit = limit + BigInt(1)
    val rowStart = limit * period + offset
    val rowCount = period - offset

    assert(newLimit <= head.value)
    assert(rowStart >= BigInt(0))
    assert(rowCount >= BigInt(0))

    if (offset == period) {
      assert(rowCount == BigInt(0))
      countGeneratedHeadMultiplesByStrideOffsetsUntil(offset, newLimit, period) ==
        countGeneratedHeadMultiplesByStrideOffsetsUntil(offset, limit, period) +
          countGeneratedHeadMultiplesRange(rowStart, rowCount)
    } else {
      val nextOffset = offset + BigInt(1)
      val rowTailStart = limit * period + nextOffset
      val rowTailCount = period - nextOffset

      assert(nextOffset <= period)
      assert(rowCount > BigInt(0))
      assert(rowTailCount >= BigInt(0))
      assert(rowTailStart == rowStart + BigInt(1))
      assert(assertGeneratedHeadMultiplesStrideUntilStep(
        offset,
        BigInt(0),
        limit,
        period
      ))
      assert(assertGeneratedHeadMultiplesByStrideOffsetsUntilStep(
        nextOffset,
        limit,
        period
      ))
      assert(assertGeneratedHeadMultiplesRangeFront(rowStart, rowCount))
      assert(
        countGeneratedHeadMultiplesRange(rowStart, rowCount) ==
          generatedHeadMultipleIndicator(rowStart) +
            countGeneratedHeadMultiplesRange(rowTailStart, rowTailCount)
      )
      assert(rowStart == offset + limit * period)
      countGeneratedHeadMultiplesByStrideOffsetsUntil(offset, newLimit, period) ==
        countGeneratedHeadMultiplesByStrideOffsetsUntil(offset, limit, period) +
          countGeneratedHeadMultiplesRange(rowStart, rowCount)
    }
  }.holds

  private def assertGeneratedHeadMultiplesByStrideOffsetsUntilZero(
    offset: BigInt,
    period: BigInt
  ): Boolean = {
    require(offset >= BigInt(0))
    require(offset <= period)
    require(period > BigInt(0))
    decreases(period - offset)

    if (offset == period) {
      countGeneratedHeadMultiplesByStrideOffsetsUntil(offset, BigInt(0), period) ==
        BigInt(0)
    } else {
      assert(countGeneratedHeadMultiplesStrideUntil(
        offset,
        BigInt(0),
        BigInt(0),
        period
      ) == BigInt(0))
      assert(assertGeneratedHeadMultiplesByStrideOffsetsUntilZero(
        offset + BigInt(1),
        period
      ))
      countGeneratedHeadMultiplesByStrideOffsetsUntil(offset, BigInt(0), period) ==
        BigInt(0)
    }
  }.holds

  private def assertGeneratedHeadMultiplesRangeMatchesStrideOffsetsUntil(
    limit: BigInt,
    period: BigInt
  ): Boolean = {
    require(limit >= BigInt(0))
    require(limit <= head.value)
    require(period > BigInt(0))
    decreases(limit)

    val total = period * limit

    assert(total >= BigInt(0))
    if (limit == BigInt(0)) {
      assert(assertGeneratedHeadMultiplesByStrideOffsetsUntilZero(BigInt(0), period))
      countGeneratedHeadMultiplesRange(BigInt(0), total) ==
        countGeneratedHeadMultiplesByStrideOffsetsUntil(BigInt(0), limit, period)
    } else {
      val previousLimit = limit - BigInt(1)
      val previousTotal = period * previousLimit

      assert(previousLimit >= BigInt(0))
      assert(previousLimit < head.value)
      assert(previousTotal >= BigInt(0))
      assert(total == previousTotal + period)
      assert(assertGeneratedHeadMultiplesRangeMatchesStrideOffsetsUntil(
        previousLimit,
        period
      ))
      assert(
        countGeneratedHeadMultiplesRange(BigInt(0), previousTotal) ==
          countGeneratedHeadMultiplesByStrideOffsetsUntil(
            BigInt(0),
            previousLimit,
            period
          )
      )
      assert(assertGeneratedHeadMultiplesRangeAppend(
        BigInt(0),
        previousTotal,
        period
      ))
      assert(
        countGeneratedHeadMultiplesRange(BigInt(0), total) ==
          countGeneratedHeadMultiplesRange(BigInt(0), previousTotal) +
            countGeneratedHeadMultiplesRange(previousTotal, period)
      )
      assert(assertGeneratedHeadMultiplesByStrideOffsetsUntilStep(
        BigInt(0),
        previousLimit,
        period
      ))
      assert(
        countGeneratedHeadMultiplesByStrideOffsetsUntil(BigInt(0), limit, period) ==
          countGeneratedHeadMultiplesByStrideOffsetsUntil(
            BigInt(0),
            previousLimit,
            period
          ) +
            countGeneratedHeadMultiplesRange(previousTotal, period)
      )

      countGeneratedHeadMultiplesRange(BigInt(0), total) ==
        countGeneratedHeadMultiplesByStrideOffsetsUntil(BigInt(0), limit, period)
    }
  }.holds

  private def assertGeneratedHeadMultiplesByStrideOffsetsCount(
    offset: BigInt,
    period: BigInt
  ): Boolean = {
    require(offset >= BigInt(0))
    require(offset <= period)
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)
    require(Calc.mod(tailPrimorial, head.value) != BigInt(0))
    decreases(period - offset)

    if (offset == period) {
      countGeneratedHeadMultiplesByStrideOffsets(offset, period) ==
        period - offset
    } else {
      assertGeneratedHeadMultiplesStrideOne(offset, period)
      assert(countGeneratedHeadMultiplesStrideFrom(offset, BigInt(0), period) == BigInt(1))
      assertGeneratedHeadMultiplesByStrideOffsetsCount(offset + BigInt(1), period)
      countGeneratedHeadMultiplesByStrideOffsets(offset, period) ==
        period - offset
    }
  }.holds

  private def assertGeneratedHeadMultiplesRangeMatchesStrideOffsets(
    period: BigInt
  ): Boolean = {
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)
    require(Calc.mod(tailPrimorial, head.value) != BigInt(0))

    val expandedIndex = period * head.value

    assert(head.value > BigInt(0))
    assert(expandedIndex >= BigInt(0))
    assert(assertGeneratedHeadMultiplesRangeMatchesStrideOffsetsUntil(head.value, period))
    assert(
      countGeneratedHeadMultiplesRange(BigInt(0), expandedIndex) ==
        countGeneratedHeadMultiplesByStrideOffsetsUntil(BigInt(0), head.value, period)
    )
    assert(assertGeneratedHeadMultiplesByStrideOffsetsMatchesUntil(BigInt(0), period))
    assertGeneratedHeadMultiplesPrefixMatchesRange(expandedIndex)
    assertGeneratedHeadMultiplesByStrideOffsetsCount(BigInt(0), period)
    countGeneratedHeadMultiplesRange(BigInt(0), expandedIndex) ==
      countGeneratedHeadMultiplesByStrideOffsets(BigInt(0), period)
  }.holds

  def assertGeneratedHeadMultiplesPrefixExpandedCount(
    period: BigInt
  ): Boolean = {
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)
    require(Calc.mod(tailPrimorial, head.value) != BigInt(0))

    val expandedIndex = period * head.value

    assert(head.value > BigInt(0))
    assert(expandedIndex >= BigInt(0))
    assert(assertGeneratedHeadMultiplesRangeMatchesStrideOffsets(period))
    assert(
      countGeneratedHeadMultiplesRange(BigInt(0), expandedIndex) ==
        countGeneratedHeadMultiplesByStrideOffsets(BigInt(0), period)
    )
    assert(assertGeneratedHeadMultiplesByStrideOffsetsCount(BigInt(0), period))
    assert(countGeneratedHeadMultiplesByStrideOffsets(BigInt(0), period) == period)
    assert(assertGeneratedHeadMultiplesPrefixMatchesRange(expandedIndex))
    countGeneratedHeadMultiplesPrefix(expandedIndex) == period
  }.holds

  def assertExpandedGeneratedHeadMultipleCount(period: BigInt): Boolean = {
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)
    require(Calc.mod(tailPrimorial, head.value) != BigInt(0))

    val expandedIndex = period * head.value

    assert(assertGeneratedHeadMultiplesPrefixExpandedCount(period))
    countGeneratedHeadMultiplesPrefix(expandedIndex) == period
  }.holds

  private def assertGeneratedHeadMultiplesPrefixMatchesRange(k: BigInt): Boolean = {
    require(k >= BigInt(0))
    decreases(k)

    if (k == BigInt(0)) {
      countGeneratedHeadMultiplesPrefix(k) ==
        countGeneratedHeadMultiplesRange(BigInt(0), k)
    } else {
      val previous = k - BigInt(1)

      assertGeneratedHeadMultiplesPrefixMatchesRange(previous)
      countGeneratedHeadMultiplesPrefix(k) ==
        countGeneratedHeadMultiplesRange(BigInt(0), k)
    }
  }.holds

  private def countNoAcceptedBetween(from: BigInt, until: BigInt): Boolean = {
    require(from >= head.value)
    require(from <= until)
    require(noAcceptedBetween(from, until))
    decreases(until - from)

    if (from == until) {
      countAcceptedBetween(from, until) == BigInt(0)
    } else {
      assert(!accepts(from))
      assert(noAcceptedBetween(from + BigInt(1), until))
      assert(countNoAcceptedBetween(from + BigInt(1), until))
      countAcceptedBetween(from, until) == BigInt(0)
    }
  }.holds

  private def countNoAcceptedHeadMultiplesBetween(from: BigInt, until: BigInt): Boolean = {
    require(from >= head.value)
    require(from <= until)
    require(noAcceptedBetween(from, until))
    decreases(until - from)

    if (from == until) {
      countAcceptedHeadMultiplesBetween(from, until) == BigInt(0)
    } else {
      assert(!accepts(from))
      assert(noAcceptedBetween(from + BigInt(1), until))
      assert(countNoAcceptedHeadMultiplesBetween(from + BigInt(1), until))
      countAcceptedHeadMultiplesBetween(from, until) == BigInt(0)
    }
  }.holds

  private def assertAcceptedCountSplitByHead(
    from: BigInt,
    until: BigInt
  ): Boolean = {
    require(from >= head.value)
    require(from <= until)
    decreases(until - from)

    if (from == until) {
      countAcceptedBetween(from, until) ==
        countAcceptedHeadMultiplesBetween(from, until) +
          countAcceptedHeadNonMultiplesBetween(from, until)
    } else {
      val next = from + BigInt(1)

      assert(assertAcceptedCountSplitByHead(next, until))

      if (accepts(from)) {
        val remainder = Calc.mod(from, head.value)

        if (remainder == BigInt(0)) {
          assert(Calc.mod(from, head.value) == BigInt(0))
        } else {
          assert(Calc.mod(from, head.value) != BigInt(0))
        }
      }

      countAcceptedBetween(from, until) ==
        countAcceptedHeadMultiplesBetween(from, until) +
          countAcceptedHeadNonMultiplesBetween(from, until)
    }
  }.holds

  private def assertCountAcceptedBetweenAppend(
    from: BigInt,
    middle: BigInt,
    until: BigInt
  ): Boolean = {
    require(from >= head.value)
    require(from <= middle)
    require(middle <= until)
    decreases(middle - from)

    if (from == middle) {
      countAcceptedBetween(from, until) ==
        countAcceptedBetween(from, middle) + countAcceptedBetween(middle, until)
    } else {
      assert(from < middle)
      assert(from + BigInt(1) <= middle)
      assert(assertCountAcceptedBetweenAppend(from + BigInt(1), middle, until))
      countAcceptedBetween(from, until) ==
        countAcceptedBetween(from, middle) + countAcceptedBetween(middle, until)
    }
  }.holds

  private def assertCountAcceptedHeadMultiplesBetweenAppend(
    from: BigInt,
    middle: BigInt,
    until: BigInt
  ): Boolean = {
    require(from >= head.value)
    require(from <= middle)
    require(middle <= until)
    decreases(middle - from)

    if (from == middle) {
      countAcceptedHeadMultiplesBetween(from, until) ==
        countAcceptedHeadMultiplesBetween(from, middle) +
          countAcceptedHeadMultiplesBetween(middle, until)
    } else {
      assert(from < middle)
      assert(from + BigInt(1) <= middle)
      assert(assertCountAcceptedHeadMultiplesBetweenAppend(from + BigInt(1), middle, until))
      countAcceptedHeadMultiplesBetween(from, until) ==
        countAcceptedHeadMultiplesBetween(from, middle) +
          countAcceptedHeadMultiplesBetween(middle, until)
    }
  }.holds

  private def assertCountAcceptedHeadNonMultiplesBetweenAppend(
    from: BigInt,
    middle: BigInt,
    until: BigInt
  ): Boolean = {
    require(from >= head.value)
    require(from <= middle)
    require(middle <= until)
    decreases(middle - from)

    if (from == middle) {
      countAcceptedHeadNonMultiplesBetween(from, until) ==
        countAcceptedHeadNonMultiplesBetween(from, middle) +
          countAcceptedHeadNonMultiplesBetween(middle, until)
    } else {
      assert(from < middle)
      assert(from + BigInt(1) <= middle)
      assert(assertCountAcceptedHeadNonMultiplesBetweenAppend(from + BigInt(1), middle, until))
      countAcceptedHeadNonMultiplesBetween(from, until) ==
        countAcceptedHeadNonMultiplesBetween(from, middle) +
          countAcceptedHeadNonMultiplesBetween(middle, until)
    }
  }.holds

  def assertGeneratedPrefixCount(k: BigInt): Boolean = {
    require(k >= BigInt(0))
    decreases(k)

    if (k == BigInt(0)) {
      assert(apply(BigInt(0)) == head.value)
      countAcceptedBetween(head.value, apply(k)) == k
    } else {
      val previousIndex = k - BigInt(1)
      val previous = apply(previousIndex)
      val current = apply(k)

      assertGeneratedPrefixCount(previousIndex)
      assert(countAcceptedBetween(head.value, previous) == previousIndex)
      assert(applyStrictlyIncreases(previousIndex))
      assert(previous < current)
      assert(previous + BigInt(1) <= current)
      assert(applySkipsNoAcceptedBetween(k))
      assert(noAcceptedBetween(previous + BigInt(1), current))
      assert(countNoAcceptedBetween(previous + BigInt(1), current))
      assert(countAcceptedBetween(previous + BigInt(1), current) == BigInt(0))
      assert(accepts(previous))
      assert(countAcceptedBetween(previous, current) == BigInt(1))
      assert(assertCountAcceptedBetweenAppend(head.value, previous, current))
      countAcceptedBetween(head.value, current) == k
    }
  }.holds

  def assertGeneratedHeadMultiplePrefixCount(k: BigInt): Boolean = {
    require(k >= BigInt(0))
    decreases(k)

    if (k == BigInt(0)) {
      assert(apply(BigInt(0)) == head.value)
      countAcceptedHeadMultiplesBetween(head.value, apply(k)) ==
        countGeneratedHeadMultiplesPrefix(k)
    } else {
      val previousIndex = k - BigInt(1)
      val previous = apply(previousIndex)
      val current = apply(k)

      assertGeneratedHeadMultiplePrefixCount(previousIndex)
      assert(countAcceptedHeadMultiplesBetween(head.value, previous) ==
        countGeneratedHeadMultiplesPrefix(previousIndex))
      assert(applyStrictlyIncreases(previousIndex))
      assert(previous < current)
      assert(previous + BigInt(1) <= current)
      assert(applySkipsNoAcceptedBetween(k))
      assert(noAcceptedBetween(previous + BigInt(1), current))
      assert(countNoAcceptedHeadMultiplesBetween(previous + BigInt(1), current))
      assert(countAcceptedHeadMultiplesBetween(previous + BigInt(1), current) == BigInt(0))
      assert(accepts(previous))

      if (Calc.mod(previous, head.value) == BigInt(0)) {
        assert(countAcceptedHeadMultiplesBetween(previous, current) == BigInt(1))
        assert(countGeneratedHeadMultiplesPrefix(k) ==
          countGeneratedHeadMultiplesPrefix(previousIndex) + BigInt(1))
      } else {
        assert(countAcceptedHeadMultiplesBetween(previous, current) == BigInt(0))
        assert(countGeneratedHeadMultiplesPrefix(k) ==
          countGeneratedHeadMultiplesPrefix(previousIndex))
      }

      assert(assertCountAcceptedHeadMultiplesBetweenAppend(head.value, previous, current))
      countAcceptedHeadMultiplesBetween(head.value, current) ==
        countGeneratedHeadMultiplesPrefix(k)
    }
  }.holds

  def assertExpandedOldAcceptedCount(period: BigInt): Boolean = {
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)

    val expandedIndex = period * head.value
    val expandedEnd = head.value + head.value * tailPrimorial

    assert(head.value > BigInt(1))
    assert(expandedIndex >= BigInt(0))
    assert(assertBlockShiftMultiple(BigInt(0), head.value, period))
    assert(apply(expandedIndex) == expandedEnd)
    assert(assertGeneratedPrefixCount(expandedIndex))
    countAcceptedBetween(head.value, expandedEnd) == expandedIndex
  }.holds

  def assertExpandedHeadMultipleCountFromGeneratedCount(period: BigInt): Boolean = {
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)

    val expandedIndex = period * head.value
    val expandedEnd = head.value + head.value * tailPrimorial

    require(countGeneratedHeadMultiplesPrefix(expandedIndex) == period)

    assert(head.value > BigInt(1))
    assert(expandedIndex >= BigInt(0))
    assert(assertBlockShiftMultiple(BigInt(0), head.value, period))
    assert(apply(expandedIndex) == expandedEnd)
    assert(assertGeneratedHeadMultiplePrefixCount(expandedIndex))
    countAcceptedHeadMultiplesBetween(head.value, expandedEnd) == period
  }.holds

  def assertSameHeadExtendedFilterCountFromRemovedCount(period: BigInt): Boolean = {
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)

    val expandedEnd = head.value + head.value * tailPrimorial

    require(countAcceptedHeadMultiplesBetween(head.value, expandedEnd) == period)

    assert(assertExpandedOldAcceptedCount(period))
    assert(countAcceptedBetween(head.value, expandedEnd) == period * head.value)
    assert(assertAcceptedCountSplitByHead(head.value, expandedEnd))
    assert(countAcceptedBetween(head.value, expandedEnd) ==
      countAcceptedHeadMultiplesBetween(head.value, expandedEnd) +
        countAcceptedHeadNonMultiplesBetween(head.value, expandedEnd))
    countAcceptedHeadNonMultiplesBetween(head.value, expandedEnd) ==
      period * (head.value - BigInt(1))
  }.holds

  def assertSameHeadExtendedFilterCount(period: BigInt): Boolean = {
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)
    require(Calc.mod(tailPrimorial, head.value) != BigInt(0))

    val expandedIndex = period * head.value
    val expandedEnd = head.value + head.value * tailPrimorial

    assert(head.value > BigInt(1))
    assert(expandedIndex >= BigInt(0))
    assert(assertGeneratedHeadMultiplesPrefixExpandedCount(period))
    assert(countGeneratedHeadMultiplesPrefix(expandedIndex) == period)
    assert(assertExpandedHeadMultipleCountFromGeneratedCount(period))
    assert(countAcceptedHeadMultiplesBetween(head.value, expandedEnd) == period)
    assert(assertSameHeadExtendedFilterCountFromRemovedCount(period))
    countAcceptedHeadNonMultiplesBetween(head.value, expandedEnd) ==
      period * (head.value - BigInt(1))
  }.holds

  /**
   * Computes the actual count of accepted values in [head, head + head*M)
   * that are NOT multiples of the head, then proves it equals the closed form.
   */
  def sameHeadSurvivorCount(period: BigInt): BigInt = {
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)
    require(Calc.mod(tailPrimorial, head.value) != BigInt(0))

    val expandedEnd = head.value + head.value * tailPrimorial
    countAcceptedHeadNonMultiplesBetween(head.value, expandedEnd)
  }.ensuring(count => {
    assertSameHeadExtendedFilterCount(period)
    count == period * (head.value - BigInt(1))
  })

  def assertSameHeadShiftedWindowCount(period: BigInt): Boolean = {
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)
    require(Calc.mod(tailPrimorial, head.value) != BigInt(0))

    val expandedEnd = head.value + head.value * tailPrimorial
    val shiftedStart = head.value + BigInt(1)
    val shiftedUntil = expandedEnd + BigInt(1)

    assert(head.value > BigInt(1))
    assert(tailPrimorial > BigInt(0))
    assert(head.value < expandedEnd)
    assert(shiftedStart <= expandedEnd)
    assert(expandedEnd <= shiftedUntil)
    assert(assertSameHeadExtendedFilterCount(period))
    assert(countAcceptedHeadNonMultiplesBetween(head.value, expandedEnd) ==
      period * (head.value - BigInt(1)))

    assert(AdditionAndMultiplication.ATimesBSameMod(BigInt(0), head.value, BigInt(1)))
    assert(Calc.mod(head.value, head.value) == BigInt(0))
    assert(countAcceptedHeadNonMultiplesBetween(head.value, expandedEnd) ==
      countAcceptedHeadNonMultiplesBetween(shiftedStart, expandedEnd))

    assert(assertBlockShiftMultiple(BigInt(0), head.value, period))
    assert(apply(period * head.value) == expandedEnd)
    assert(AdditionAndMultiplication.ATimesBSameMod(BigInt(0), head.value, BigInt(1) + tailPrimorial))
    assert(Calc.mod(expandedEnd, head.value) == BigInt(0))
    assert(countAcceptedHeadNonMultiplesBetween(expandedEnd, shiftedUntil) == BigInt(0))
    assert(assertCountAcceptedHeadNonMultiplesBetweenAppend(shiftedStart, expandedEnd, shiftedUntil))
    assert(countAcceptedHeadNonMultiplesBetween(shiftedStart, shiftedUntil) ==
      countAcceptedHeadNonMultiplesBetween(shiftedStart, expandedEnd) +
        countAcceptedHeadNonMultiplesBetween(expandedEnd, shiftedUntil))

    countAcceptedHeadNonMultiplesBetween(shiftedStart, shiftedUntil) ==
      period * (head.value - BigInt(1))
  }.holds

  /**
   * Extracts the rejection fact for one value inside a skipped interval.
   *
   * `noAcceptedBetween(from, until)` is recursive over the interval start, so
   * Stainless does not automatically know what it says about an arbitrary
   * interior value. This helper walks from `from` to `value`, carrying the
   * interval proof forward one candidate at a time. When it reaches `value`,
   * the unfolded predicate gives the exact fact needed by completeness:
   * `value` cannot be accepted.
   */
}
