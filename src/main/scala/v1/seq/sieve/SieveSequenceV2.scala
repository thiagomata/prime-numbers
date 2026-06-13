package v1.seq.sieve

import stainless.annotation.extern
import stainless.collection.List
import v1.cycle.gap.GapCycle
import v1.cycle.integral.recursive.CycleIntegral
import v1.cycle.memory.MemCycle
import v1.list.ListUtils

case class SieveSequenceV2(
  primes: List[BigInt],
  gapCycle: GapCycle
) {
  require(primes.nonEmpty)
  require(ListUtils.checkAllPositive(primes))
  require(ListUtils.checkAllBiggerThanValue(primes, 1))
  require(SieveUtils.assertProductEqualOrBiggerThanElements(primes.tail))
  require(SieveUtils.isCoprime(primes.head, primes.tail))

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
  def next(): SieveSequenceV2 = {
    val newHead = apply(BigInt(1))
    val newGapCycle = SieveSequenceNextLevel.nextGapCycleV2(this)
    SieveSequenceV2(newHead :: primes, newGapCycle)
  }
}

object SieveSequenceV2 {
  def S_0V2(): SieveSequenceV2 = {
    SieveSequenceV2(
      primes = List(BigInt(2)),
      gapCycle = GapCycle(List(BigInt(1)))
    )
  }

  def S_1V2(): SieveSequenceV2 = {
    SieveSequenceV2(
      primes = List(BigInt(3), BigInt(2)),
      gapCycle = GapCycle(List(BigInt(2)))
    )
  }
}
