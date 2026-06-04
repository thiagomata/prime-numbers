package v1.seq.sieve

import stainless.collection.List
import stainless.lang.decreases
import v1.cycle.CycleUtils
import v1.cycle.integral.recursive.CycleIntegral
import v1.cycle.memory.MemCycle

case class SieveSequence(
  head: BigInt,
  primes: List[BigInt],
  integral: CycleIntegral
) {
  require(head > 0)
  require(head >= BigInt(2))
  require(integral.cycle.size > 0)
  require(integral.initialValue == head)
  require(CycleUtils.checkPositiveOrZero(integral.cycle.values))
  require(SieveUtils.checkAllPositive(primes))
  require(SieveUtils.assertProductEqualOrBiggerThanElements(primes))
  require(v1.seq.sieve.CycleUtils.allLessThan(primes, head))
  require(SieveUtils.isCoprime(head, primes))
  require(integral.cycle.sum() == SieveUtils.product(primes))
  require(integral.cycle(BigInt(0)) < head)
  require(integral.cycle.values.head > BigInt(0))
  require(SieveUtils.isCoprime(head + SieveUtils.product(primes), primes))

  def apply(position: BigInt): BigInt = {
    require(position >= 0)
    if (position == 0) head
    else integral(position - 1)
  }

  def first: BigInt = head
  def knownPrimeLimit: BigInt = head * head
  def cycle: MemCycle = integral.cycle
  def modulus: BigInt = SieveUtils.product(primes)
  def nextPrime: BigInt = head
  def nextHead: BigInt = apply(BigInt(1))

  // def next(): SieveSequence = {
  //   require(primes.nonEmpty)
  //   val gaps = SieveSequenceNextLevel.nextRotatedGaps(this)
  //   SieveSequence(
  //     head = apply(BigInt(1)),
  //     primes = head :: primes,
  //     integral = CycleIntegral(apply(BigInt(1)), MemCycle(gaps))
  //   )
  // }
}

object SieveSequence {
  def S_0(): SieveSequence = {
    SieveSequence(
      head = BigInt(2),
      primes = List.empty,
      integral = CycleIntegral(BigInt(2), MemCycle(List(BigInt(1))))
    )
  }

  def S_1(): SieveSequence = {
    SieveSequence(
      head = BigInt(3),
      primes = List(BigInt(2)),
      integral = CycleIntegral(BigInt(3), MemCycle(List(BigInt(2))))
    )
  }
}
