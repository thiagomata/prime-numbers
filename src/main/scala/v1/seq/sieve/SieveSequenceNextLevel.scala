package v1.seq.sieve

import stainless.collection.List
import stainless.lang.*
import scala.annotation.tailrec
import v1.Calc
import v1.cycle.CycleUtils
import v1.cycle.memory.MemCycle
import v1.div.properties.AdditionAndMultiplication
import v1.list.ListUtils.{checkAllBiggerThanOne, checkAllPositive}

object SieveSequenceNextLevel {

  def newHead(seq: SieveSequence): BigInt = {
    seq.apply(BigInt(1))
  }

  def candidate(seq: SieveSequence, offset: BigInt): BigInt = {
    require(offset >= 0)
    seq(offset + 1)
  }

  def survives(seq: SieveSequence, offset: BigInt): Boolean = {
    require(offset >= 0)
    val value = candidate(seq, offset)
    Calc.mod(value, seq.head) != BigInt(0)
  }

  def isNotMultipleOfNewPrimes(seq: SieveSequence, value: BigInt): Boolean = {
    require(value > 0)
    SieveUtils.isCoprime(value, seq.primes.tail) && Calc.mod(value, seq.head) != BigInt(0)
  }

  def expansionBlockSize(seq: SieveSequence): BigInt = {
    seq.modulus * seq.head
  }

  def expansionRangeStart(seq: SieveSequence): BigInt = {
    newHead(seq) + 1
  }

  def expansionRangeEnd(seq: SieveSequence): BigInt = {
    newHead(seq) + expansionBlockSize(seq)
  }

  def lastInExpansion(seq: SieveSequence): BigInt = {
    expansionRangeEnd(seq)
  }

//  def assertBlockSizePositive(seq: SieveSequence): Boolean = {
//    expansionBlockSize(seq) > BigInt(0)
//  }.holds
//
//  def assertNewHeadLarger(seq: SieveSequence): Boolean = {
//    newHead(seq) > seq.head
//  }.holds
//
//  def assertNewHeadAtLeastTwo(seq: SieveSequence): Boolean = {
//    assert(assertNewHeadLarger(seq))
//    newHead(seq) >= BigInt(2)
//  }.holds
//
//  def assertNewPrimesPositive(seq: SieveSequence): Boolean = {
//    SieveUtils.checkAllPositive(newHead(seq) :: seq.primes)
//  }.holds
//
//  def assertNewPrimesAllBiggerThanOne(seq: SieveSequence): Boolean = {
//    SieveUtils.checkAllBiggerThanOne(newHead(seq) :: seq.primes)
//  }.holds
//
//  def assertNewProductEqualOrBiggerThanElements(seq: SieveSequence): Boolean = {
//    assert(assertNewPrimesAllBiggerThanOne(seq))
//    SieveUtils.assertProductEqualOrBiggerThanElements(newHead(seq) :: seq.primes)
//  }.holds
//
//  def assertModulusPositive(seq: SieveSequence): Boolean = {
//    seq.modulus > BigInt(0)
//  }.holds

  def nextResidues(seq: SieveSequence): List[BigInt] = {
    SieveUtils.residues(seq.modulus, seq.primes.tail)
  }

  def nextExpanded(seq: SieveSequence): List[BigInt] = {
    SieveUtils.expandResidues(nextResidues(seq), seq.modulus, seq.head)
  }

  def nextFiltered(seq: SieveSequence): List[BigInt] = {
    SieveUtils.filterList(nextExpanded(seq), seq.head)
  }

  def nextSorted(seq: SieveSequence): List[BigInt] = {
    SieveUtils.sortFiltered(nextFiltered(seq))
  }

  def nextGaps(seq: SieveSequence): List[BigInt] = {
    SieveUtils.calculateGaps(nextSorted(seq), seq.modulus * seq.head)
  }

  def nextHeadResidueIndex(seq: SieveSequence): BigInt = {
    val newHeadVal = seq.apply(BigInt(1))
    val newMod = seq.modulus * seq.head
    SieveUtils.nextResidueIndex(nextSorted(seq), BigInt(0), newHeadVal % newMod)
  }

  def nextRotatedGaps(seq: SieveSequence): List[BigInt] = {
    SieveUtils.rotateAt(nextGaps(seq), nextHeadResidueIndex(seq))
  }

  def nextCycle(seq: SieveSequence): MemCycle = {
    val gaps = nextRotatedGaps(seq)
    require(gaps.nonEmpty)
    require(CycleUtils.checkPositiveOrZero(gaps))
    MemCycle(gaps)
  }

//  def assertFirstCandidateSurvives(seq: SieveSequence): Boolean = {
//    survives(seq, BigInt(0))
//  }.holds
//
//  def assertRangeOrdered(seq: SieveSequence): Boolean = {
//    expansionRangeStart(seq) < expansionRangeEnd(seq)
//  }.holds
//
//  def assertNewPrimesValid(seq: SieveSequence): Boolean = {
//    val np = newHead(seq) :: seq.primes
//    assert(assertNewHeadLarger(seq))
//    assert(SieveUtils.checkAllPositive(np))
//    assert(v1.seq.sieve.CycleUtils.allLessThan(seq.primes.tail, seq.head))
//    assert(v1.seq.sieve.CycleUtils.assertAllLessThanTransitive(seq.primes.tail, seq.head, newHead(seq)))
//    SieveUtils.checkAllPositive(np) &&
//      v1.seq.sieve.CycleUtils.allLessThan(np.tail, newHead(seq))
//  }.holds

  @tailrec
  def collectGaps(seq: SieveSequence, lastSurvivor: BigInt, pos: BigInt, remaining: BigInt, gaps: List[BigInt]): List[BigInt] = {
    require(remaining >= 0)
    require(pos >= 0)
    decreases(remaining)

    if (remaining == BigInt(0)) {
      (seq.integral(pos) - lastSurvivor) :: gaps
    } else {
      val current = seq.integral(pos)
      if (current % seq.head == BigInt(0)) {
        collectGaps(seq, lastSurvivor, pos + 1, remaining - 1, gaps)
      } else {
        val gap = current - lastSurvivor
        collectGaps(seq, current, pos + 1, remaining - 1, gap :: gaps)
      }
    }
  }

  def nextGapsV2(seq: SieveSequence): List[BigInt] = {
    val p = seq.head
    val steps = p * seq.cycle.size
    val newHeadVal = seq.apply(BigInt(1))
    collectGaps(seq, newHeadVal, BigInt(1), steps - BigInt(1), List.empty[BigInt])
  }

  def assertNewPrimesNonEmpty(seq: SieveSequence): Boolean = {
    (newHead(seq) :: seq.primes).nonEmpty
  }.holds

  def assertNewPrimesPositive(seq: SieveSequence): Boolean = {
    checkAllPositive(newHead(seq) :: seq.primes)
  }.holds

  def assertNewPrimesAllBiggerThanOne(seq: SieveSequence): Boolean = {
    checkAllBiggerThanOne(newHead(seq) :: seq.primes)
  }.holds

  def assertNewPrimesProductValid(seq: SieveSequence): Boolean = {
    SieveUtils.assertProductEqualOrBiggerThanElements(seq.primes)
  }.holds

  def assertNewCycleSumEqualsProduct(seq: SieveSequence): Boolean = {
    val newMod = seq.modulus * seq.head
    val sorted = nextSorted(seq)
    SieveUtils.assertCalculateGapsSum(sorted, newMod)
    newMod == SieveUtils.product(seq.primes)
  }.holds

  def assertNextGapsNonEmpty(seq: SieveSequence): Boolean = {
    nextGaps(seq).nonEmpty
  }.holds

//  def assertNextGapsPositiveOrZero(seq: SieveSequence): Boolean = {
//    val newMod = seq.modulus * seq.head
//    val residues = SieveUtils.residues(seq.modulus, seq.primes.tail)
//    val expanded = SieveUtils.expandResidues(residues, seq.modulus, seq.head)
//    val filtered = SieveUtils.filterList(expanded, seq.head)
//    val sorted = SieveUtils.sortFiltered(filtered)
//    SieveUtils.assertExpandResiduesRange(residues, seq.modulus, seq.head)
//    SieveUtils.assertFilterListNonNegative(expanded, seq.head)
//    SieveUtils.assertFilterListAllLessThan(expanded, newMod, seq.head)
//    SieveUtils.assertSortFilteredNonNegative(filtered)
//    SieveUtils.assertSortFilteredAllLessThan(filtered, newMod)
//    SieveUtils.assertSortFilteredAscending(filtered)
//    CycleUtils.checkPositiveOrZero(SieveUtils.calculateGaps(sorted, newMod))
//  }.holds

}
