package v1.seq.sieve

import stainless.collection.List
import stainless.lang.*
import v1.seq.sieve.SieveUtils.checkAllPositive

object SieveSequenceNextLevel {

//  def newHead(seq: SieveSequence): BigInt = {
//    seq.apply(BigInt(1))
//  }
//
//  def newPrimes(seq: SieveSequence): List[BigInt] = {
//    assert(seq.head > 0)
//    assert(SieveUtils.isCoprime(seq.head, seq.primes))
//    assert(v1.seq.sieve.CycleUtils.allLessThan(seq.primes, seq.head))
//    seq.primes :+ seq.head
//  }
//
//  def candidate(seq: SieveSequence, offset: BigInt): BigInt = {
//    require(offset >= 0)
//    seq(offset + 1)
//  }
//
//  def survives(seq: SieveSequence, offset: BigInt): Boolean = {
//    require(offset >= 0)
//    val value = candidate(seq, offset)
//    value % seq.head != BigInt(0)
//  }
//
//  def isNotMultipleOfNewPrimes(seq: SieveSequence, value: BigInt): Boolean = {
//    require(value > 0)
//    SieveUtils.isCoprime(value, seq.primes) && value % seq.head != BigInt(0)
//  }
//
//  def expansionBlockSize(seq: SieveSequence): BigInt = {
//    seq.modulus * seq.head
//  }
//
//  def expansionRangeStart(seq: SieveSequence): BigInt = {
//    newHead(seq) + 1
//  }
//
//  def expansionRangeEnd(seq: SieveSequence): BigInt = {
//    newHead(seq) + expansionBlockSize(seq)
//  }
//
//  def lastInExpansion(seq: SieveSequence): BigInt = {
//    expansionRangeEnd(seq)
//  }
//
//  def assertBlockSizePositive(): Boolean = {
//    val s0 = SieveSequence.S_0()
//    expansionBlockSize(s0) > BigInt(0)
//  }.holds
//
//  def assertRangeOrdered(): Boolean = {
//    val s0 = SieveSequence.S_0()
//    expansionRangeStart(s0) < expansionRangeEnd(s0)
//  }.holds
}

