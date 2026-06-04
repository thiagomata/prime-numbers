package v1.seq.sieve

import stainless.collection.List
import stainless.lang.*
import v1.Calc
import v1.cycle.memory.MemCycle
import v1.div.properties.AdditionAndMultiplication
import v1.seq.sieve.SieveUtils.{checkAllBiggerThanOne, checkAllPositive}

object SieveSequenceNextLevel {

  def newHead(seq: SieveSequence): BigInt = {
    seq.apply(BigInt(1))
  }

  def newPrimes(seq: SieveSequence): List[BigInt] = {
    require(checkAllBiggerThanOne(seq.primes))
    assert(seq.head >= 2)
    assert(SieveUtils.isCoprime(seq.head, seq.primes))
    assert(v1.seq.sieve.CycleUtils.allLessThan(seq.primes, seq.head))
    //    val newPrimes = seq.primes :+ seq.head
    val newPrimes = seq.head :: seq.primes
    assert(checkAllBiggerThanOne(newPrimes))
    newPrimes
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
    SieveUtils.isCoprime(value, seq.primes) && Calc.mod(value, seq.head) != BigInt(0)
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

  def assertBlockSizePositive(seq: SieveSequence): Boolean = {
    expansionBlockSize(seq) > BigInt(0)
  }.holds

  def assertNewHeadLarger(seq: SieveSequence): Boolean = {
    newHead(seq) > seq.head
  }.holds

  def assertNewHeadAtLeastTwo(seq: SieveSequence): Boolean = {
    assert(assertNewHeadLarger(seq))
    newHead(seq) >= BigInt(2)
  }.holds

  def assertNewPrimesPositive(seq: SieveSequence): Boolean = {
    SieveUtils.checkAllPositive(seq.head :: seq.primes)
  }.holds

  def assertNewPrimesAllBiggerThanOne(seq: SieveSequence): Boolean = {
    SieveUtils.checkAllBiggerThanOne(seq.head :: seq.primes)
  }.holds

  def assertNewProductEqualOrBiggerThanElements(seq: SieveSequence): Boolean = {
    assert(assertNewPrimesAllBiggerThanOne(seq))
    SieveUtils.assertProductEqualOrBiggerThanElements(seq.head :: seq.primes)
  }.holds

  def assertModulusPositive(seq: SieveSequence): Boolean = {
    seq.modulus > BigInt(0)
  }.holds

  def nextResidues(seq: SieveSequence): List[BigInt] = {
    SieveUtils.residues(seq.modulus, seq.primes)
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
    require(seq.primes.nonEmpty)
    SieveUtils.rotateAt(nextGaps(seq), nextHeadResidueIndex(seq))
  }

  def assertFirstCandidateSurvives(seq: SieveSequence): Boolean = {
    survives(seq, BigInt(0))
  }.holds

  def assertRangeOrdered(seq: SieveSequence): Boolean = {
    expansionRangeStart(seq) < expansionRangeEnd(seq)
  }.holds

  def assertNewPrimesValid(seq: SieveSequence): Boolean = {
    SieveUtils.checkAllPositive(seq.primes)
    val np = newPrimes(seq)
    assert(assertNewHeadLarger(seq))
    assert(SieveUtils.checkAllPositive(np))
    assert(np == seq.head :: seq.primes)
    assert(v1.seq.sieve.CycleUtils.allLessThan(seq.primes, seq.head))
    assert(v1.seq.sieve.CycleUtils.assertAllLessThanTransitive(seq.primes, seq.head, newHead(seq)))
    SieveUtils.checkAllPositive(np) &&
      v1.seq.sieve.CycleUtils.allLessThan(np, newHead(seq))
  }.holds

//  def assertLastSurvives(seq: SieveSequence): Boolean = {
//    val p = seq.head
//    val newH = newHead(seq)
//    val m = seq.modulus
//    val last = newH + m * p
//    assert(AdditionAndMultiplication.ATimesBSameMod(newH, p, m))
//    assert(Calc.mod(newH, p) != BigInt(0))
//    Calc.mod(last, p) != BigInt(0)
//  }.holds
}

