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

case class CycleSieveSequence(
  primes: List[BigInt],
  gapCycle: GapCycle
) {
  require(primes.nonEmpty)
  require(ListUtils.checkAllPositive(primes))
  require(ListUtils.checkAllBiggerThanValue(primes, 1))
  require(SieveUtils.assertProductEqualOrBiggerThanElements(primes.tail))
  require(primes.head + gapCycle.memCycle(0) > primes.head)
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

  def assertNextHeadGreaterThanHead(): Boolean = {
    apply(BigInt(1)) > head
  }.holds

  def nextWithGapCycle(newGapCycle: GapCycle): CycleSieveSequence = {
    val newHead = apply(BigInt(1))
    require(SieveUtils.isCoprime(newHead + newGapCycle.memCycle(0), primes))
    require(Calc.mod(newHead + newGapCycle.memCycle(0), newHead) != BigInt(0))
    require(Calc.mod(SieveUtils.product(primes), newHead) != BigInt(0))

    assert(SieveSequenceNextLevel.assertNextPrimesNonEmpty(this))
    assert(SieveSequenceNextLevel.assertNextPrimesPositive(this))
    assert(SieveSequenceNextLevel.assertNextPrimesBiggerThanOne(this))
    assert(SieveSequenceNextLevel.assertNextTailProductEqualOrBiggerThanElements(this))
    assert(SieveSequenceNextLevel.assertNextHeadCoprimeToPrimes(this))

    CycleSieveSequence(newHead :: primes, newGapCycle)
  }

  def next(): CycleSieveSequence = {
    val newHead = apply(BigInt(1))
    val newGaps = SieveSequenceNextLevel.nextGapsWalk(this)
    require(newGaps.nonEmpty)
    require(ListBoundUtils.allGreaterThan(newGaps, BigInt(0)))
    val newGapCycle = GapCycle(newGaps)
    require(SieveUtils.isCoprime(newHead + newGapCycle.memCycle(0), primes))
    require(Calc.mod(newHead + newGapCycle.memCycle(0), newHead) != BigInt(0))
    require(Calc.mod(SieveUtils.product(primes), newHead) != BigInt(0))

    nextWithGapCycle(newGapCycle)
  }

  /**
   * Verified next-stage construction using the transparent current window.
   *
   * Builds a plain `List[BigInt]` of the first `head * gapCycle.size` integral
   * values (via `currentWindow`), filters out multiples of `head`, derives
   * gaps from survivors, and constructs the next stage.
   *
   * Preconditions mirror `nextWithGapCycle` — the caller must discharge them.
   * Use `SpecDerivedCycleSieve`'s P2 lemmas to prove the survivor gaps
   * satisfy these invariants.
   */
  def nextFromWindow(): CycleSieveSequence = {
    val steps = head * gapCycle.size
    val window = SieveSequenceNextLevel.currentWindow(integral, steps)
    val survivors = window.filter(v => Calc.mod(v, head) != BigInt(0))
    require(!survivors.isEmpty)
    require(survivors.size > BigInt(1))
    val gaps = CycleIntegralFilterProperties.gapsFromValues(survivors)
    require(ListBoundUtils.allGreaterThan(gaps, BigInt(0)))
    val newGapCycle = GapCycle(gaps)
    val newHead = apply(BigInt(1))
    require(newHead < head * head)
    require(SieveUtils.isCoprime(newHead + newGapCycle.memCycle(0), primes))
    require(Calc.mod(newHead + newGapCycle.memCycle(0), newHead) != BigInt(0))
    require(Calc.mod(SieveUtils.product(primes), newHead) != BigInt(0))

    nextWithGapCycle(newGapCycle)
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
