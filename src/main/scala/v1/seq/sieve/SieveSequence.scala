package v1.seq.sieve

import stainless.collection.List
import stainless.lang.decreases
import v1.Calc
import v1.cycle.integral.recursive.CycleIntegral
import v1.cycle.memory.MemCycle

case class SieveSequence(
  head: BigInt,
  primes: List[BigInt],
  integral: CycleIntegral
) {
  require(head > 0)
  require(integral.cycle.size > 0)
  require(integral.initialValue == BigInt(0))

  def apply(position: BigInt): BigInt = {
    require(position >= 0)
    if (position == 0) head
    else head + integral(position - 1)
  }

  def first: BigInt = head
  def knownPrimeLimit: BigInt = head * head
  def cycle: MemCycle = integral.cycle
  def modulus: BigInt = SieveUtils.product(primes)

  def countMultiples(divisor: BigInt, start: BigInt, length: BigInt): BigInt = {
    require(divisor > 0)
    require(start >= 0)
    require(length >= 0)
    decreases(length)
    if (length == 0) BigInt(0) else {
      val rest = countMultiples(divisor, start, length - 1)
      val current = this.apply(start + length - 1)
      if (Calc.mod(current, divisor) == 0) rest + 1 else rest
    }
  }

  def next(): SieveSequence = {
    SieveSequence.nextLevel(head, primes, cycle)
  }
}

object SieveSequence {
  def S_0(): SieveSequence = {
    SieveSequence(
      head = BigInt(2),
      primes = List.empty,
      integral = CycleIntegral(BigInt(0), MemCycle(List(BigInt(1))))
    )
  }

  def apply(head: BigInt, cycle: MemCycle): SieveSequence = {
    require(head > 0)
    require(cycle.size > 0)
    SieveSequence(
      head = head,
      primes = List.empty,
      integral = CycleIntegral(BigInt(0), cycle)
    )
  }

  def nextLevel(head: BigInt, primes: List[BigInt], cycle: MemCycle): SieveSequence = {
    require(head > 0)
    require(cycle.size > 0)
    SieveSequence(
      head = head + 1,
      primes = head :: primes,
      integral = CycleIntegral(BigInt(0), cycle)
    )
  }
}
