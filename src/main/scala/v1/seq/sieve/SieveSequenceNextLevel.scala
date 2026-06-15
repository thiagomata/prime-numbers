package v1.seq.sieve

import stainless.collection.List
import stainless.lang.*
import scala.annotation.tailrec
import v1.Calc
import v1.cycle.gap.GapCycle
import v1.cycle.integral.recursive.properties.CycleIntegralProperties
import v1.list.ListBoundUtils
import v1.list.ListUtils
import v1.list.SortedList

object SieveSequenceNextLevel {

  def nextResiduesV2(seq: SieveSequenceV2): List[BigInt] = {
    SieveUtils.residues(seq.modulus, seq.primes.tail)
  }

  def nextExpandedV2(seq: SieveSequenceV2): List[BigInt] = {
    SieveUtils.expandResidues(nextResiduesV2(seq), seq.modulus, seq.head)
  }

  def nextFilteredV2(seq: SieveSequenceV2): List[BigInt] = {
    SieveUtils.filterList(nextExpandedV2(seq), seq.head)
  }

  def nextSortedV2(seq: SieveSequenceV2): SortedList = {
    SortedList.fromUnsorted(nextFilteredV2(seq))
  }

  def nextGapsV2(seq: SieveSequenceV2): List[BigInt] = {
    SieveUtils.calculateGaps(nextSortedV2(seq).list, seq.modulus * seq.head)
  }

  def nextHeadResidueIndexV2(seq: SieveSequenceV2): BigInt = {
    val newHeadVal = seq.apply(BigInt(1))
    val newMod = seq.modulus * seq.head
    SieveUtils.nextResidueIndex(nextSortedV2(seq).list, BigInt(0), Calc.mod(newHeadVal, newMod))
  }

  def nextRotatedGapsV2(seq: SieveSequenceV2): List[BigInt] = {
    SieveUtils.rotateAt(nextGapsV2(seq), nextHeadResidueIndexV2(seq))
  }

  def collectGapsV2(seq: SieveSequenceV2, lastSurvivor: BigInt, lastPos: BigInt, pos: BigInt, remaining: BigInt, gaps: List[BigInt]): List[BigInt] = {
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
        collectGapsV2(seq, lastSurvivor, lastPos, pos + 1, remaining - 1, gaps)
      } else {
        assert(seq.integral(pos) == current)
        assert(CycleIntegralProperties.assertCycleIntegralIncreasing(seq.integral, lastPos, pos))
        assert(current > lastSurvivor)
        val gap = current - lastSurvivor
        assert(gap > BigInt(0))
        collectGapsV2(seq, current, pos, pos + 1, remaining - 1, gap :: gaps)
      }
    }
  }

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

  def assertCollectGapsV2AllPositive(
    seq: SieveSequenceV2, lastSurvivor: BigInt, lastPos: BigInt,
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
        assertCollectGapsV2AllPositive(seq, lastSurvivor, lastPos, pos + 1, remaining - 1, gaps)
      } else {
        assert(seq.integral(pos) == current)
        assert(CycleIntegralProperties.assertCycleIntegralIncreasing(seq.integral, lastPos, pos))
        assert(current > lastSurvivor)
        val gap = current - lastSurvivor
        assert(gap > BigInt(0))
        assertCollectGapsV2AllPositive(seq, current, pos, pos + 1, remaining - 1, gap :: gaps)
      }
    }
  }.holds

  def nextGapsWalkV2(seq: SieveSequenceV2): List[BigInt] = {
    val steps = seq.head * seq.gapCycle.size
    val newHead = seq.apply(BigInt(1))
    assert(assertCollectGapsV2AllPositive(seq, newHead, BigInt(0), BigInt(1), steps, List.empty[BigInt]))
    collectGapsV2(seq, newHead, BigInt(0), BigInt(1), steps, List.empty[BigInt])
  }

  def nextGapCycleV2(seq: SieveSequenceV2): GapCycle = {
    val gaps = nextGapsWalkV2(seq)
    require(gaps.nonEmpty)
    require(ListBoundUtils.allGreaterThan(gaps, BigInt(0)))
    GapCycle(gaps)
  }

  def assertNextExpandedCoprime(seq: SieveSequenceV2): Boolean = {
    require(seq.modulus > 0)
    require(seq.modulus == SieveUtils.product(seq.primes.tail))
    require(ListUtils.checkAllPositive(seq.primes.tail))
    assert(SieveUtils.assertAllRExpandedCoprime(seq.modulus, seq.head, seq.primes.tail))
    true
  }.holds

  def assertNextFilteredCoprime(seq: SieveSequenceV2): Boolean = {
    require(seq.modulus > 0)
    require(seq.modulus == SieveUtils.product(seq.primes.tail))
    require(ListUtils.checkAllPositive(seq.primes.tail))
    assert(assertNextExpandedCoprime(seq))
    true
  }.holds

  def assertResiduesCoprime(seq: SieveSequenceV2): Boolean = {
    require(seq.modulus > 0)
    require(ListUtils.checkAllPositive(seq.primes.tail))
    SieveUtils.assertResiduesAllCoprime(seq.modulus, seq.primes.tail)
    true
  }.holds

  def assertNextGapsNonEmptyV2(seq: SieveSequenceV2): Boolean = {
    nextGapsV2(seq).nonEmpty
  }.holds

}
