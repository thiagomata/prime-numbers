package v1.seq.sieve

import stainless.collection.List
import stainless.lang.decreases
import stainless.annotation.extern
import v1.cycle.CycleUtils
import v1.cycle.integral.recursive.CycleIntegral
import v1.cycle.memory.MemCycle

case class SieveSequence(
  primes: List[BigInt],
  integral: CycleIntegral
) {
  require(primes.nonEmpty)
  require(primes.head >= BigInt(2))
  require(integral.cycle.size > 0)
  require(integral.initialValue == primes.head)
  require(CycleUtils.checkPositiveOrZero(integral.cycle.values))
  require(SieveUtils.checkAllPositive(primes))
  require(SieveUtils.assertProductEqualOrBiggerThanElements(primes.tail))
  require(v1.seq.sieve.CycleUtils.allLessThan(primes.tail, primes.head))
  require(SieveUtils.isCoprime(primes.head, primes.tail))
  require(integral.cycle.sum() == SieveUtils.product(primes.tail))
  require(integral.cycle(BigInt(0)) < primes.head)
  require(integral.cycle.values.head > BigInt(0))
  require(SieveUtils.isCoprime(primes.head + SieveUtils.product(primes.tail), primes.tail))

  def head: BigInt = primes.head
  def modulus: BigInt = SieveUtils.product(primes.tail)

  def apply(position: BigInt): BigInt = {
    require(position >= 0)
    if (position == 0) head
    else integral(position - 1)
  }

  def first: BigInt = head
  def knownPrimeLimit: BigInt = head * head
  def cycle: MemCycle = integral.cycle
  def nextPrime: BigInt = head
  def nextHead: BigInt = apply(BigInt(1))

  @extern
  def next(): SieveSequence = {
    val gaps = SieveSequenceNextLevel.nextRotatedGaps(this)
    SieveSequence(
      primes = apply(BigInt(1)) :: primes,
      integral = CycleIntegral(apply(BigInt(1)), MemCycle(gaps))
    )
  }
}

object SieveSequence {
  def S_0(): SieveSequence = {
    SieveSequence(
      primes = List(BigInt(2)),
      integral = CycleIntegral(BigInt(2), MemCycle(List(BigInt(1))))
    )
  }

  def S_1(): SieveSequence = {
    SieveSequence(
      primes = List(BigInt(3), BigInt(2)),
      integral = CycleIntegral(BigInt(3), MemCycle(List(BigInt(2))))
    )
  }
}
