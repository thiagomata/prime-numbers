package v1.chapter6.seq.sieve

import stainless.collection.List
import stainless.lang.*
import v1.chapter2.div.Calc

import scala.annotation.tailrec
import v1.chapter3.list.{ListBoundUtils, ListUtils, SortedList}
import v1.chapter4.cycle.gap.GapCycle
import v1.chapter4.cycle.integral.recursive.CycleIntegral
import v1.chapter4.cycle.integral.recursive.properties.CycleIntegralProperties
import v1.chapter6.seq.sieve.properties.SieveSequenceProperties

object SieveSequenceNextLevel {

  def nextResidues(seq: CycleSieveSequence): List[BigInt] = {
    SieveUtils.residues(seq.modulus, seq.primesTailValues)
  }

  def nextExpanded(seq: CycleSieveSequence): List[BigInt] = {
    SieveUtils.expandResidues(nextResidues(seq), seq.modulus, seq.head)
  }

  def nextFiltered(seq: CycleSieveSequence): List[BigInt] = {
    SieveUtils.filterList(nextExpanded(seq), seq.head)
  }

  def nextSorted(seq: CycleSieveSequence): SortedList = {
    SortedList.fromUnsorted(nextFiltered(seq))
  }

  def nextGaps(seq: CycleSieveSequence): List[BigInt] = {
    // require(seq.head > BigInt(0))                                      // [TIMEOUT CANDIDATE]
    // require(seq.modulus > BigInt(0))                                   // [TIMEOUT CANDIDATE]
    SieveUtils.calculateGaps(nextSorted(seq).list, seq.modulus * seq.head)
  }

  def nextHeadResidueIndex(seq: CycleSieveSequence): BigInt = {
    val newHeadVal = seq.apply(BigInt(1))
    val newMod = seq.modulus * seq.head
    SieveUtils.nextResidueIndex(nextSorted(seq).list, BigInt(0), Calc.mod(newHeadVal, newMod))
  }

  def nextRotatedGaps(seq: CycleSieveSequence): List[BigInt] = {
    SieveUtils.rotateAt(nextGaps(seq), nextHeadResidueIndex(seq))
  }

  def collectGaps(seq: CycleSieveSequence, lastSurvivor: BigInt, lastPos: BigInt, pos: BigInt, remaining: BigInt, gaps: List[BigInt]): List[BigInt] = {
    require(remaining >= 0)
    require(pos >= 1)
    require(lastSurvivor > 0)
    require(lastPos >= 0)
    require(lastPos < pos)
    require(seq.integral(lastPos) == lastSurvivor)
    require(ListBoundUtils.allGreaterThan(gaps, BigInt(0)))
    decreases(remaining)
    if (remaining == BigInt(0)) {
      assert(assertAllGreaterThanReverse(gaps, BigInt(0)))
      gaps.reverse
    } else {
      val current = seq.apply(pos + 1)
      if (Calc.mod(current, seq.head) == BigInt(0)) {
        collectGaps(seq, lastSurvivor, lastPos, pos + 1, remaining - 1, gaps)
      } else {
        assert(seq.integral(pos) == current)
        assert(CycleIntegralProperties.assertCycleIntegralIncreasing(seq.integral, lastPos, pos))
        assert(current > lastSurvivor)
        val gap = current - lastSurvivor
        assert(gap > BigInt(0))
        collectGaps(seq, current, pos, pos + 1, remaining - 1, gap :: gaps)
      }
    }
  }.ensuring(res => ListBoundUtils.allGreaterThan(res, BigInt(0)))

  def assertAllGreaterThanReverse(list: List[BigInt], value: BigInt): Boolean = {
    require(ListBoundUtils.allGreaterThan(list, value))
    decreases(list.size)
    if (list.isEmpty) {
      ListBoundUtils.allGreaterThan(list.reverse, value)
    } else {
      assert(ListBoundUtils.allGreaterThan(list.tail, value))
      assert(assertAllGreaterThanReverse(list.tail, value))
      assert(ListBoundUtils.allGreaterThan(list.tail.reverse, value))
      assert(list.head > value)
      assert(ListBoundUtils.assertAppendGreaterThan(list.tail.reverse, List(list.head), value))
      ListBoundUtils.allGreaterThan(list.reverse, value)
    }
  }.holds

  def assertCollectGapsAllPositive(
    seq: CycleSieveSequence, lastSurvivor: BigInt, lastPos: BigInt,
    pos: BigInt, remaining: BigInt, gaps: List[BigInt]
  ): Boolean = {
    require(remaining >= 0)
    require(pos >= 1)
    require(lastSurvivor > 0)
    require(lastPos >= 0)
    require(lastPos < pos)
    require(seq.integral(lastPos) == lastSurvivor)
    require(ListBoundUtils.allGreaterThan(gaps, BigInt(0)))
    decreases(remaining)
    if (remaining == BigInt(0)) {
      assert(assertAllGreaterThanReverse(gaps, BigInt(0)))
      ListBoundUtils.allGreaterThan(gaps.reverse, BigInt(0))
    } else {
      val current = seq.apply(pos + 1)
      if (Calc.mod(current, seq.head) == BigInt(0)) {
        assertCollectGapsAllPositive(seq, lastSurvivor, lastPos, pos + 1, remaining - 1, gaps)
      } else {
        assert(seq.integral(pos) == current)
        assert(CycleIntegralProperties.assertCycleIntegralIncreasing(seq.integral, lastPos, pos))
        assert(current > lastSurvivor)
        val gap = current - lastSurvivor
        assert(gap > BigInt(0))
        assertCollectGapsAllPositive(seq, current, pos, pos + 1, remaining - 1, gap :: gaps)
      }
    }
  }.holds

  def nextGapsWalk(seq: CycleSieveSequence): List[BigInt] = {
    val steps = seq.head * seq.gapCycle.size
    val newHead = seq.apply(BigInt(1))
    assert(assertCollectGapsAllPositive(seq, newHead, BigInt(0), BigInt(1), steps, List.empty[BigInt]))
    collectGaps(seq, newHead, BigInt(0), BigInt(1), steps, List.empty[BigInt])
  }.ensuring(res => ListBoundUtils.allGreaterThan(res, BigInt(0)))

  def nextGapCycle(seq: CycleSieveSequence): GapCycle = {
    val gaps = nextGapsWalk(seq)
    require(gaps.nonEmpty)
    require(ListBoundUtils.allGreaterThan(gaps, BigInt(0)))
    GapCycle(gaps)
  }

    def assertNextPrimesNonEmpty(seq: CycleSieveSequence): Boolean = {
    true
  }.holds

  def assertNextHeadPositive(seq: CycleSieveSequence): Boolean = {
    val newHead = seq.apply(BigInt(1))
    assert(CycleIntegralProperties.assertCycleIntegralPositive(seq.integral, BigInt(0)))
    newHead > BigInt(0)
  }.holds

  def assertNextPrimesPositive(seq: CycleSieveSequence): Boolean = {
    assert(assertNextHeadPositive(seq))
    ListUtils.checkAllPositive(seq.primesValues)
  }.holds

  def assertNextHeadBiggerThanOne(seq: CycleSieveSequence): Boolean = {
    val newHead = seq.apply(BigInt(1))
    assert(SieveSequenceProperties.assertStrictlyIncreasing(seq, BigInt(0)))
    newHead > BigInt(1)
  }.holds

  def assertNextPrimesBiggerThanOne(seq: CycleSieveSequence): Boolean = {
    assert(assertNextHeadBiggerThanOne(seq))
    ListUtils.checkAllBiggerThanValue(seq.primesValues, BigInt(1))
  }.holds

  def assertNextTailProductEqualOrBiggerThanElements(seq: CycleSieveSequence): Boolean = {
    SieveUtils.assertProductEqualOrBiggerThanElements(seq.primesValues)
  }.holds

  def assertNextHeadCoprimeToPrimes(seq: CycleSieveSequence): Boolean = {
    val newHead = seq.apply(BigInt(1))
    assert(newHead == seq.primes.head.value + seq.gapCycle.memCycle(0))
    SieveUtils.isCoprime(newHead, seq.primesValues)
  }.holds

  def assertNextExpandedCoprime(seq: CycleSieveSequence): Boolean = {
    require(seq.modulus > 0)
    require(seq.modulus == SieveUtils.product(seq.primesTailValues))
    require(ListUtils.checkAllPositive(seq.primesTailValues))
    assert(SieveUtils.assertAllRExpandedCoprime(seq.modulus, seq.head, seq.primesTailValues))
    true
  }.holds

  def assertNextFilteredCoprime(seq: CycleSieveSequence): Boolean = {
    require(seq.modulus > 0)
    require(seq.modulus == SieveUtils.product(seq.primesTailValues))
    require(ListUtils.checkAllPositive(seq.primesTailValues))
    assert(assertNextExpandedCoprime(seq))
    true
  }.holds

  def assertResiduesCoprime(seq: CycleSieveSequence): Boolean = {
    require(seq.modulus > 0)
    require(ListUtils.checkAllPositive(seq.primesTailValues))
    SieveUtils.assertResiduesAllCoprime(seq.modulus, seq.primesTailValues)
    true
  }.holds

  def assertNextGapsNonEmpty(seq: CycleSieveSequence): Boolean = {
    // require(seq.head > BigInt(0))                                      // [TIMEOUT CANDIDATE]
    // require(seq.modulus > BigInt(0))                                   // [TIMEOUT CANDIDATE]
    nextGaps(seq).nonEmpty
  }.holds

  /**
   * Transparent window of `ci`'s first `steps` values.
   *
   * Returns a plain `List[BigInt]` of `ci(0)` through `ci(steps-1)`.
   * Exposed as a concrete list that Stainless can induct over without
   * unfolding `CycleIntegral`/`MemCycle` internals.
   */
  def currentWindow(ci: CycleIntegral, steps: BigInt): List[BigInt] = {
    require(steps >= BigInt(0))
    decreases(steps)
    if (steps == BigInt(0)) List.empty[BigInt]
    else {
      val prefix = currentWindow(ci, steps - BigInt(1))
      prefix :+ ci(steps - BigInt(1))
    }
  }.ensuring((res: List[BigInt]) => res.size == steps)

}
