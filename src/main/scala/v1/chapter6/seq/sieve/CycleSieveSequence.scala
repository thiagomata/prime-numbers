package v1.chapter6.seq.sieve

import stainless.collection.List
import v1.chapter2.div.Calc
import v1.chapter3.list.{ListBoundUtils, ListUtils}
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

  /**
   * Builds the next cycle sieve stage when the caller supplies the new gap
   * cycle together with the hard constructor facts for that gap cycle.
   *
   * This method is intentionally conditional. The easy next-stage facts are
   * already known locally: `apply(1)` is positive, bigger than one, coprime to
   * the current prime list, and prepending it preserves the raw prime-list
   * shape required by `CycleSieveSequence`. The difficult part is not the raw
   * list shape; it is proving that the candidate gap cycle is the correct one
   * for the new filter head.
   *
   * The three `require` clauses below are exactly the constructor obligations
   * that depend on the supplied `newGapCycle` rather than on the old sequence
   * alone:
   *
   *  - the first generated value after the new head must still pass the old
   *    prime filters;
   *  - that same value must not be a multiple of the new head;
   *  - the old modulus must not collapse to zero modulo the new head.
   *
   * Keeping these facts as explicit preconditions mirrors `SpecSieveSequence.next`,
   * where the hard "next prime is before head squared" fact is required by the
   * method. This gives us a verified construction point while the larger
   * gap-cycle correctness proof remains isolated in the equivalence ticket.
   */
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
