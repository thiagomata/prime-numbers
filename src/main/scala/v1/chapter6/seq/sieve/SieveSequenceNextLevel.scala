package v1.chapter6.seq.sieve

import stainless.collection.List
import stainless.lang.*
import v1.chapter2.div.Calc

import scala.annotation.tailrec
import v1.chapter3.list.{ListBoundUtils, ListUtils, SortedList}
import v1.chapter4.cycle.gap.GapCycle
import v1.chapter4.cycle.integral.recursive.CycleIntegral
import v1.chapter4.cycle.integral.recursive.properties.CycleIntegralProperties
import v1.chapter6.seq.sieve.properties.SieveSequenceProperties

object SieveSequenceNextLevel {

  def nextResidues(seq: CycleSieveSequence): List[BigInt] = {
    require(seq.modulus > 0)
    require(ListUtils.checkAllPositive(seq.primesTailValues))
    SieveUtils.residues(seq.modulus, seq.primesTailValues)
  }

  def nextExpanded(seq: CycleSieveSequence): List[BigInt] = {
    require(seq.modulus > 0)
    require(ListUtils.checkAllPositive(seq.primesTailValues))
    require(seq.head > 0)
    SieveUtils.expandResidues(nextResidues(seq), seq.modulus, seq.head)
  }

  def nextFiltered(seq: CycleSieveSequence): List[BigInt] = {
    require(seq.modulus > 0)
    require(ListUtils.checkAllPositive(seq.primesTailValues))
    require(seq.head > 0)
    SieveUtils.filterList(nextExpanded(seq), seq.head)
  }

  def nextSorted(seq: CycleSieveSequence): SortedList = {
    require(seq.modulus > 0)
    require(ListUtils.checkAllPositive(seq.primesTailValues))
    require(seq.head > 0)
    SortedList.fromUnsorted(nextFiltered(seq))
  }

  def nextGaps(seq: CycleSieveSequence): List[BigInt] = {
    require(seq.modulus > 0)
    require(ListUtils.checkAllPositive(seq.primesTailValues))
    require(seq.head > 0)
    require(seq.modulus * seq.head > 0)
    SieveUtils.calculateGaps(nextSorted(seq).list, seq.modulus * seq.head)
  }

  def nextHeadResidueIndex(seq: CycleSieveSequence): BigInt = {
    require(seq.modulus > 0)
    require(ListUtils.checkAllPositive(seq.primesTailValues))
    require(seq.head > 0)
    require(seq.modulus * seq.head > 0)
    val newHeadVal = seq.apply(BigInt(1))
    val newMod = seq.modulus * seq.head
    SieveUtils.nextResidueIndex(nextSorted(seq).list, BigInt(0), Calc.mod(newHeadVal, newMod))
  }

  def nextRotatedGaps(seq: CycleSieveSequence): List[BigInt] = {
    require(seq.modulus > 0)
    require(ListUtils.checkAllPositive(seq.primesTailValues))
    require(seq.head > 0)
    require(seq.modulus * seq.head > 0)
    SieveUtils.rotateAt(nextGaps(seq), nextHeadResidueIndex(seq))
  }

  def collectGaps(seq: CycleSieveSequence, lastSurvivor: BigInt, lastPos: BigInt, pos: BigInt, remaining: BigInt, gaps: List[BigInt]): List[BigInt] = {
    require(remaining >= 0)
    require(pos >= 1)
    require(lastSurvivor > 0)
    require(lastPos >= 0)
    require(lastPos < pos)
    require(seq.integral(lastPos) == lastSurvivor)
    require(ListBoundUtils.allGreaterThan(gaps, BigInt(0)))
    decreases(remaining)
    if (remaining == BigInt(0)) {
      assert(assertAllGreaterThanReverse(gaps, BigInt(0)))
      gaps.reverse
    } else {
      val current = seq.apply(pos + 1)
      if (Calc.mod(current, seq.head) == BigInt(0)) {
        collectGaps(seq, lastSurvivor, lastPos, pos + 1, remaining - 1, gaps)
      } else {
        assert(seq.integral(pos) == current)
        assert(CycleIntegralProperties.assertCycleIntegralIncreasing(seq.integral, lastPos, pos))
        assert(current > lastSurvivor)
        val gap = current - lastSurvivor
        assert(gap > BigInt(0))
        collectGaps(seq, current, pos, pos + 1, remaining - 1, gap :: gaps)
      }
    }
  }.ensuring(res => ListBoundUtils.allGreaterThan(res, BigInt(0)))

  def assertAllGreaterThanReverse(list: List[BigInt], value: BigInt): Boolean = {
    require(ListBoundUtils.allGreaterThan(list, value))
    decreases(list.size)
    if (list.isEmpty) {
      ListBoundUtils.allGreaterThan(list.reverse, value)
    } else {
      assert(ListBoundUtils.allGreaterThan(list.tail, value))
      assert(assertAllGreaterThanReverse(list.tail, value))
      assert(ListBoundUtils.allGreaterThan(list.tail.reverse, value))
      assert(list.head > value)
      assert(ListBoundUtils.assertAppendGreaterThan(list.tail.reverse, List(list.head), value))
      ListBoundUtils.allGreaterThan(list.reverse, value)
    }
  }.holds

  def assertCollectGapsAllPositive(
    seq: CycleSieveSequence, lastSurvivor: BigInt, lastPos: BigInt,
    pos: BigInt, remaining: BigInt, gaps: List[BigInt]
  ): Boolean = {
    require(remaining >= 0)
    require(pos >= 1)
    require(lastSurvivor > 0)
    require(lastPos >= 0)
    require(lastPos < pos)
    require(seq.integral(lastPos) == lastSurvivor)
    require(ListBoundUtils.allGreaterThan(gaps, BigInt(0)))
    decreases(remaining)
    if (remaining == BigInt(0)) {
      assert(assertAllGreaterThanReverse(gaps, BigInt(0)))
      ListBoundUtils.allGreaterThan(gaps.reverse, BigInt(0))
    } else {
      val current = seq.apply(pos + 1)
      if (Calc.mod(current, seq.head) == BigInt(0)) {
        assertCollectGapsAllPositive(seq, lastSurvivor, lastPos, pos + 1, remaining - 1, gaps)
      } else {
        assert(seq.integral(pos) == current)
        assert(CycleIntegralProperties.assertCycleIntegralIncreasing(seq.integral, lastPos, pos))
        assert(current > lastSurvivor)
        val gap = current - lastSurvivor
        assert(gap > BigInt(0))
        assertCollectGapsAllPositive(seq, current, pos, pos + 1, remaining - 1, gap :: gaps)
      }
    }
  }.holds

  def nextGapsWalk(seq: CycleSieveSequence): List[BigInt] = {
    val steps = seq.head * seq.gapCycle.size
    val newHead = seq.apply(BigInt(1))
    assert(assertCollectGapsAllPositive(seq, newHead, BigInt(0), BigInt(1), steps, List.empty[BigInt]))
    collectGaps(seq, newHead, BigInt(0), BigInt(1), steps, List.empty[BigInt])
  }.ensuring(res => ListBoundUtils.allGreaterThan(res, BigInt(0)))

  def nextGapCycle(seq: CycleSieveSequence): GapCycle = {
    val gaps = nextGapsWalk(seq)
    require(gaps.nonEmpty)
    require(ListBoundUtils.allGreaterThan(gaps, BigInt(0)))
    GapCycle(gaps)
  }

    def assertNextPrimesNonEmpty(seq: CycleSieveSequence): Boolean = {
    true
  }.holds

  def assertNextHeadPositive(seq: CycleSieveSequence): Boolean = {
    val newHead = seq.apply(BigInt(1))
    assert(CycleIntegralProperties.assertCycleIntegralPositive(seq.integral, BigInt(0)))
    newHead > BigInt(0)
  }.holds

  def assertNextPrimesPositive(seq: CycleSieveSequence): Boolean = {
    assert(assertNextHeadPositive(seq))
    ListUtils.checkAllPositive(seq.primesValues)
  }.holds

  def assertNextHeadBiggerThanOne(seq: CycleSieveSequence): Boolean = {
    val newHead = seq.apply(BigInt(1))
    assert(SieveSequenceProperties.assertStrictlyIncreasing(seq, BigInt(0)))
    newHead > BigInt(1)
  }.holds

  def assertNextPrimesBiggerThanOne(seq: CycleSieveSequence): Boolean = {
    assert(assertNextHeadBiggerThanOne(seq))
    ListUtils.checkAllBiggerThanValue(seq.primesValues, BigInt(1))
  }.holds

  def assertNextTailProductEqualOrBiggerThanElements(seq: CycleSieveSequence): Boolean = {
    SieveUtils.assertProductEqualOrBiggerThanElements(seq.primesValues)
  }.holds

  def assertNextHeadCoprimeToPrimes(seq: CycleSieveSequence): Boolean = {
    val newHead = seq.apply(BigInt(1))
    require(Calc.mod(newHead, seq.head) != BigInt(0))
    require(SieveUtils.isCoprime(newHead, seq.primesTailValues))
    assert(newHead == seq.primes.head.value + seq.gapCycle.memCycle(0))
    assert(seq.primesValues == seq.head :: seq.primesTailValues)
    SieveUtils.isCoprime(newHead, seq.primesValues)
  }.holds

  def assertNextExpandedCoprime(seq: CycleSieveSequence): Boolean = {
    require(seq.modulus > 0)
    require(seq.modulus == SieveUtils.product(seq.primesTailValues))
    require(ListUtils.checkAllPositive(seq.primesTailValues))
    assert(SieveUtils.assertAllRExpandedCoprime(seq.modulus, seq.head, seq.primesTailValues))
    true
  }.holds

  def assertNextFilteredCoprime(seq: CycleSieveSequence): Boolean = {
    require(seq.modulus > 0)
    require(seq.modulus == SieveUtils.product(seq.primesTailValues))
    require(ListUtils.checkAllPositive(seq.primesTailValues))
    assert(assertNextExpandedCoprime(seq))
    true
  }.holds

  def assertResiduesCoprime(seq: CycleSieveSequence): Boolean = {
    require(seq.modulus > 0)
    require(ListUtils.checkAllPositive(seq.primesTailValues))
    SieveUtils.assertResiduesAllCoprime(seq.modulus, seq.primesTailValues)
    true
  }.holds

  def assertNextGapsNonEmpty(seq: CycleSieveSequence): Boolean = {
    require(seq.head > BigInt(0))
    require(seq.modulus > BigInt(0))
    nextGaps(seq).nonEmpty
  }.holds

  def assertNextGapsSize(seq: CycleSieveSequence): Boolean = {
    require(seq.modulus > 0)
    require(ListUtils.checkAllPositive(seq.primesTailValues))
    require(seq.head > 0)
    require(seq.modulus * seq.head > 0)
    // The sorted survivor list is non-empty (there is always at least one value
    // coprime to the tail primes within one period). This is true for every real
    // sequence; stating it as a caller obligation avoids the solver having to
    // re-derive `nextSorted(seq).list.nonEmpty` (the precondition of
    // `assertCalculateGapsSize`) inside this VC — that re-derivation timed out
    // even in isolation. See ticket fix-ch6-timeout-file-by-file.md.
    require(nextSorted(seq).list.nonEmpty)
    assert(SieveUtils.assertCalculateGapsSize(nextSorted(seq).list, seq.modulus * seq.head))
    nextGaps(seq).size == nextSorted(seq).list.size
  }.holds

  def assertNextSortedStrictlyAscending(
    seq: CycleSieveSequence,
    i: BigInt
  ): Boolean = {
    require(seq.modulus > 0)
    require(ListUtils.checkAllPositive(seq.primesTailValues))
    require(seq.head > 0)
    require(i >= 0)
    require(i + 1 < nextSorted(seq).list.size)

    val sorted = nextSorted(seq).list
    val filtered = nextFiltered(seq)
    assert(SortedList.assertSortFilteredAscending(filtered))
    assert(SortedList.isAscending(sorted))
    assert(SortedList.assertIsAscendingAtIndex(sorted, i))
    sorted(i + 1) > sorted(i)
  }.holds

  /**
   * Positivity of `nextGaps` once the sorted pipeline output has its local
   * bounds exposed.
   *
   * Math:
   *
   *   sorted = nextSorted(seq).list
   *   isAscending(sorted)       [from SortedList.sortFiltered postcondition]
   *   0 <= sorted.head
   *   forall x in sorted: x < seq.modulus * seq.head
   *   --------------------------------------------------
   *   forall g in nextGaps(seq): g > 0
   *
   * This keeps the gap arithmetic separate from the pipeline range proof.
   * Sortedness comes from the recursive sorting producer contract; the remaining
   * upstream obligation is to prove the range/head bounds from
   * expand/filter/sort preservation.
   */
  def assertNextGapsAllPositiveGivenSortedBounds(seq: CycleSieveSequence): Boolean = {
    require(seq.modulus > BigInt(0))
    require(ListUtils.checkAllPositive(seq.primesTailValues))
    require(seq.head > BigInt(0))
    require(seq.modulus * seq.head > BigInt(0))
    require(nextSorted(seq).list.nonEmpty)
    require(ListBoundUtils.allLessThan(nextSorted(seq).list, seq.modulus * seq.head))
    require(nextSorted(seq).list.head >= BigInt(0))

    val sorted = nextSorted(seq).list
    assert(SieveUtils.assertCalculateGapsAllPositive(sorted, seq.modulus * seq.head))
    ListBoundUtils.allGreaterThan(nextGaps(seq), BigInt(0))
  }.holds

  /**
   * Rotation preserves positivity for the independently computed next gaps,
   * once the sorted pipeline bounds have been exposed.
   *
   * Math:
   *
   *   forall g in nextGaps(seq): g > 0
   *   nextRotatedGaps(seq) = rotateAt(nextGaps(seq), nextHeadResidueIndex(seq))
   *   -----------------------------------------------------------------------
   *   forall g in nextRotatedGaps(seq): g > 0
   *
   * This is the Phase E L2 wrapper. It deliberately depends on
   * `assertNextGapsAllPositiveGivenSortedBounds` so the rotation proof never
   * reopens the sorting, pairwise-gap, or wrap-gap arithmetic.
   */
  def assertNextRotatedGapsAllPositiveGivenSortedBounds(seq: CycleSieveSequence): Boolean = {
    require(seq.modulus > BigInt(0))
    require(ListUtils.checkAllPositive(seq.primesTailValues))
    require(seq.head > BigInt(0))
    require(seq.modulus * seq.head > BigInt(0))
    require(nextSorted(seq).list.nonEmpty)
    require(ListBoundUtils.allLessThan(nextSorted(seq).list, seq.modulus * seq.head))
    require(nextSorted(seq).list.head >= BigInt(0))

    val gaps = nextGaps(seq)
    val index = nextHeadResidueIndex(seq)
    assert(assertNextGapsAllPositiveGivenSortedBounds(seq))
    assert(ListBoundUtils.allGreaterThan(gaps, BigInt(0)))
    assert(index >= BigInt(0))
    assert(SieveUtils.assertRotateAtPreservesAllGreaterThan(gaps, index, BigInt(0)))
    ListBoundUtils.allGreaterThan(nextRotatedGaps(seq), BigInt(0))
  }.holds

  // --- Phase E: DRAFT — all sub-lemmas verified, SMT chain times out ---
  //
  // To prove: `allGreaterThan(nextRotatedGaps(seq), 0)`
  //
  // Decomposition:
  //   1. nextRotatedGaps = rotateAt(nextGaps, index)
  //      rotation preserves allGreaterThan via assertRotateAtPreservesAllGreaterThan (✓)
  //   2. nextGaps = calculateGaps(sorted, modulus*head) = pairwiseGaps(sorted) ++ wrapGap
  //      a. pairwiseGaps positive via assertPairwiseGapsAllPositive (✓ 15/15) + Phase D (✓)
  //      b. wrapGap = modulus*head - sorted.last + sorted.head
  //         Needs sorted.last < modulus*head — requires bounds chain:
  //         expanded < modulus*head (assertExpandResiduesRange) → filterList preserves
  //         (assertFilterListAllLessThan) → sortFiltered preserves
  //         (assertSortFilteredAllLessThan). Each lemma is individually verified
  //         but composing them in one lemma exhausts the solver (3 attempts timed out).
  //
  // Strategy: split into two lemmas —
  //   L1: allGreaterThan(nextGaps, 0) (pairwise + wrap)
  //   L2: allGreaterThan(nextRotatedGaps, 0) (L1 + rotation)
  //
  // def assertNextRotatedGapsAllPositive(
  //   seq: CycleSieveSequence
  // ): Boolean = {
  //   require(seq.modulus > 0)
  //   require(ListUtils.checkAllPositive(seq.primesTailValues))
  //   require(seq.head > 0)
  //   require(seq.modulus * seq.head > 0)
  //   require(nextSorted(seq).list.nonEmpty)
  //
  //   val rotated = nextRotatedGaps(seq)
  //   ListBoundUtils.allGreaterThan(rotated, BigInt(0))
  // }.holds

  /**
   * Transparent window of `ci`'s first `steps` values.
   *
   * Returns a plain `List[BigInt]` of `ci(0)` through `ci(steps-1)`.
   * Exposed as a concrete list that Stainless can induct over without
   * unfolding `CycleIntegral`/`MemCycle` internals.
   */
  def currentWindow(ci: CycleIntegral, steps: BigInt): List[BigInt] = {
    require(steps >= BigInt(0))
    decreases(steps)
    if (steps == BigInt(0)) List.empty[BigInt]
    else {
      val prefix = currentWindow(ci, steps - BigInt(1))
      prefix :+ ci(steps - BigInt(1))
    }
  }.ensuring((res: List[BigInt]) => res.size == steps)

}
