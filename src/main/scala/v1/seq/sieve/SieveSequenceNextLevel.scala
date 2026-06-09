package v1.seq.sieve

import stainless.collection.List
import stainless.lang.*
import scala.annotation.tailrec
import v1.Calc
import v1.cycle.gap.GapCycle
import v1.cycle.integral.recursive.properties.CycleIntegralProperties
import v1.list.ListBoundUtils
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
    decreases(remaining)
    if (remaining == BigInt(0)) {
      gaps.reverse
    } else {
      val current = seq.apply(pos + 1)
      if (Calc.mod(current, seq.head) == BigInt(0)) {
        collectGapsV2(seq, lastSurvivor, lastPos, pos + 1, remaining - 1, gaps)
      } else {
        assert(CycleIntegralProperties.assertCycleIntegralPositive(seq.integral, pos))
        assert(CycleIntegralProperties.assertCycleValuePositive(seq.integral, pos + 1))
        assert(CycleIntegralProperties.assertDiffEqualsCycleValue(seq.integral, pos))
        assert(CycleIntegralProperties.assertCycleIntegralIncreasing(seq.integral, lastPos, pos))
        val gap = current - lastSurvivor
        collectGapsV2(seq, current, pos, pos + 1, remaining - 1, gap :: gaps)
      }
    }
  }

//  def assertCollectGapsV2AllPositive(
//    seq: SieveSequenceV2, lastSurvivor: BigInt, lastPos: BigInt,
//    pos: BigInt, remaining: BigInt, gaps: List[BigInt]
//  ): Boolean = {
//    require(remaining >= 0)
//    require(pos >= 1)
//    require(lastSurvivor > 0)
//    require(lastPos >= 0)
//    require(lastPos < pos)
//    require(ListBoundUtils.allGreaterThan(gaps, BigInt(0)))
//    decreases(remaining)
//    if (remaining == BigInt(0)) {
//      ListBoundUtils.allGreaterThan(gaps.reverse, BigInt(0))
//    } else {
//      val current = seq.apply(pos + 1)
//      if (current % seq.head == BigInt(0)) {
//        assertCollectGapsV2AllPositive(seq, lastSurvivor, lastPos, pos + 1, remaining - 1, gaps)
//      } else {
//        assert(CycleIntegralProperties.assertCycleIntegralIncreasing(seq.integral, lastPos, pos))
////        assert(current > lastSurvivor)
////        assert(current - lastSurvivor > BigInt(0))
//        assertCollectGapsV2AllPositive(seq, current, pos, pos + 1, remaining - 1, (current - lastSurvivor) :: gaps)
//      }
//    }
//  }.holds

  def nextGapsWalkV2(seq: SieveSequenceV2): List[BigInt] = {
    val steps = seq.head * seq.gapCycle.size
    val newHead = seq.apply(BigInt(1))
    collectGapsV2(seq, newHead, BigInt(0), BigInt(1), steps, List.empty[BigInt])
  }

  def nextGapCycleV2(seq: SieveSequenceV2): GapCycle = {
    val gaps = nextGapsWalkV2(seq)
    require(gaps.nonEmpty)
    require(ListBoundUtils.allGreaterThan(gaps, BigInt(0)))
    GapCycle(gaps)
  }

  def assertNextGapsNonEmptyV2(seq: SieveSequenceV2): Boolean = {
    nextGapsV2(seq).nonEmpty
  }.holds

}
