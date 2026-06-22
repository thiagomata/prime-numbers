package v1.chapter6.seq.sieve

import stainless.annotation.extern
import stainless.collection.List
import v1.chapter2.div.Calc
import v1.chapter3.list.ListUtils
import v1.chapter4.cycle.gap.GapCycle
import v1.chapter4.cycle.integral.recursive.CycleIntegral
import v1.chapter4.cycle.memory.MemCycle

case class CycleSieveSequence(
  primes: List[BigInt],
  gapCycle: GapCycle
) {
  require(primes.nonEmpty)
  require(ListUtils.checkAllPositive(primes))
  require(ListUtils.checkAllBiggerThanValue(primes, 1))
  require(SieveUtils.assertProductEqualOrBiggerThanElements(primes.tail))
  require(SieveUtils.isCoprime(primes.head, primes.tail))
  require(SieveUtils.isCoprime(primes.head + gapCycle.memCycle(0), primes.tail))
  require(Calc.mod(primes.head + gapCycle.memCycle(0), primes.head) != BigInt(0))
  require(Calc.mod(SieveUtils.product(primes.tail), primes.head) != BigInt(0))

  val integral: CycleIntegral = CycleIntegral(primes.head, gapCycle.memCycle)

  def head: BigInt = primes.head
  def modulus: BigInt = SieveUtils.product(primes.tail)
  def cycle: MemCycle = gapCycle.memCycle

  def apply(position: BigInt): BigInt = {
    require(position >= 0)
    if (position == 0) head
    else integral(position - 1)
  }

  def first: BigInt = head
  def knownPrimeLimit: BigInt = head * head
  def nextPrime: BigInt = head
  def nextHead: BigInt = apply(BigInt(1))

  @extern
  def next(): CycleSieveSequence = {
    val newHead = apply(BigInt(1))
    val newGapCycle = SieveSequenceNextLevel.nextGapCycle(this)
    CycleSieveSequence(newHead :: primes, newGapCycle)
  }
}

object CycleSieveSequence {
  def S_0(): CycleSieveSequence = {
    CycleSieveSequence(
      primes = List(BigInt(2)),
      gapCycle = GapCycle(List(BigInt(1)))
    )
  }

  def S_1(): CycleSieveSequence = {
    CycleSieveSequence(
      primes = List(BigInt(3), BigInt(2)),
      gapCycle = GapCycle(List(BigInt(2)))
    )
  }
}
