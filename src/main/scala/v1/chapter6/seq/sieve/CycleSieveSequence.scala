package v1.chapter6.seq.sieve

import stainless.collection.List
import stainless.lang.BooleanDecorations
import v1.chapter2.div.Calc
import v1.chapter3.list.{ListBoundUtils, ListUtils}
import v1.chapter3.list.properties.ListRepeatProperties
import v1.chapter4.cycle.gap.GapCycle
import v1.chapter4.cycle.integral.recursive.CycleIntegral
import v1.chapter4.cycle.integral.recursive.properties.CycleIntegralFilterProperties
import v1.chapter4.cycle.memory.MemCycle
import v1.chapter5.prime.{AllPrimesSoFarList, Prime, PrimeUtils, SortedPrimeList}

case class CycleSieveSequence(
  primes: AllPrimesSoFarList,
  gapCycle: GapCycle
) {
  // require(!primes.isEmpty)                                              // [TIMEOUT CANDIDATE]
  // require(primes.head.value + gapCycle.memCycle(0) > primes.head.value) // [TIMEOUT CANDIDATE]
  // require(Calc.mod(primes.head.value + gapCycle.memCycle(0), primes.head.value) != BigInt(0))  // [TIMEOUT CANDIDATE]
  // require(Calc.mod(PrimeUtils.primorial(primes.list.tail.list), primes.head.value) != BigInt(0))  // [TIMEOUT CANDIDATE]

  val primesValues: List[BigInt] = PrimeUtils.primeValues(primes.list.list)
  val primesTailValues: List[BigInt] = PrimeUtils.primeValues(primes.list.tail.list)
  val primorial: BigInt = PrimeUtils.primorial(primes.list.list)
  val integral: CycleIntegral = CycleIntegral(primes.head.value, gapCycle.memCycle)

  def head: BigInt = primes.head.value
  def modulus: BigInt = PrimeUtils.primorial(primes.list.tail.list)
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

  def assertNextHeadGreaterThanHead(): Boolean = {
    apply(BigInt(1)) > head
  }.holds

  // def nextWithGapCycle(newGapCycle: GapCycle): CycleSieveSequence = {   // [TIMEOUT CANDIDATE]
  //   val newHead = apply(BigInt(1))
  //   require(SieveUtils.isCoprime(newHead + newGapCycle.memCycle(0), primesValues))
  //   require(Calc.mod(newHead + newGapCycle.memCycle(0), newHead) != BigInt(0))
  //   require(Calc.mod(primorial, newHead) != BigInt(0))
  //   assert(SieveSequenceNextLevel.assertNextPrimesNonEmpty(this))
  //   assert(SieveSequenceNextLevel.assertNextPrimesPositive(this))
  //   assert(SieveSequenceNextLevel.assertNextPrimesBiggerThanOne(this))
  //   assert(SieveSequenceNextLevel.assertNextTailProductEqualOrBiggerThanElements(this))
  //   assert(SieveSequenceNextLevel.assertNextHeadCoprimeToPrimes(this))
  //   CycleSieveSequence(primes.next, newGapCycle)
  // }
  // 
  // def next(): CycleSieveSequence = {                                    // [TIMEOUT CANDIDATE]
  //   val newHead = apply(BigInt(1))
  //   val newGaps = SieveSequenceNextLevel.nextGapsWalk(this)
  //   require(newGaps.nonEmpty)
  //   require(ListBoundUtils.allGreaterThan(newGaps, BigInt(0)))
  //   val newGapCycle = GapCycle(newGaps)
  //   require(SieveUtils.isCoprime(newHead + newGapCycle.memCycle(0), primesValues))
  //   require(Calc.mod(newHead + newGapCycle.memCycle(0), newHead) != BigInt(0))
  //   require(Calc.mod(primorial, newHead) != BigInt(0))
  //   nextWithGapCycle(newGapCycle)
  // }
  // 
  // def nextFromWindow(): CycleSieveSequence = {                          // [TIMEOUT CANDIDATE]
  //   val steps = head * gapCycle.size
  //   val window = SieveSequenceNextLevel.currentWindow(integral, steps)
  //   val survivors = window.filter(v => Calc.mod(v, head) != BigInt(0))
  //   require(!survivors.isEmpty)
  //   require(survivors.size > BigInt(1))
  //   val gaps = CycleIntegralFilterProperties.gapsFromValues(survivors)
  //   require(ListBoundUtils.allGreaterThan(gaps, BigInt(0)))
  //   val newGapCycle = GapCycle(gaps)
  //   val newHead = apply(BigInt(1))
  //   require(newHead < head * head)
  //   require(SieveUtils.isCoprime(newHead + newGapCycle.memCycle(0), primesValues))
  //   require(Calc.mod(newHead + newGapCycle.memCycle(0), newHead) != BigInt(0))
  //   require(Calc.mod(primorial, newHead) != BigInt(0))
  //   nextWithGapCycle(newGapCycle)
  // }
}

object CycleSieveSequence {
  def S_0(): CycleSieveSequence = {
    CycleSieveSequence(
      primes = AllPrimesSoFarList(SortedPrimeList(List(Prime(BigInt(2))))),
      gapCycle = GapCycle(List(BigInt(1)))
    )
  }

  def S_1(): CycleSieveSequence = {
    CycleSieveSequence(
      primes = AllPrimesSoFarList(SortedPrimeList(List(Prime(BigInt(3)), Prime(BigInt(2))))),
      gapCycle = GapCycle(List(BigInt(2)))
    )
  }
}
