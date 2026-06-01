package v1.seq.sieve

import stainless.collection.List
import stainless.lang.*
import v1.Calc
import v1.cycle.memory.MemCycle
import v1.seq.Seq

/**
 * SieveSequence represents an infinite sequence of positive integers
 * generated via wheel factorization for the Sieve of Eratosthenes.
 *
 * Each sequence S_k:
 *   - Has a head (the first element, which is prime)
 *   - Has a cycle of gaps that generate the infinite sequence
 *   - S_0: head=2, gaps=[1]     → [2, 3, 4, 5, 6, ...]
 *   - S_1: head=3, gaps=[2]     → [3, 5, 7, 9, 11, ...]
 *   - S_2: head=5, gaps=[4,2]   → [5, 7, 11, 13, 17, ...]
 *
 * The "limit" (head²) is an emergent property - after filtering by all
 * primes up to p, elements up to p² are guaranteed to be prime.
 *
 * @param head The first element in the sequence (2, 3, 5, 7, ...)
 * @param cycle MemCycle containing the gaps that generate the sequence
 */
case class SieveSequence(
  head: BigInt,
  cycle: MemCycle
) {
  require(head > 0)
  require(cycle.size > 0)
  require(cycle.values.forall(_ > 0))

  private val seq: Seq = Seq(
    previous = List(head),
    loop = cycle
  )

  /**
   * Access the element at the given position in the sequence.
   *
   * Uses the existing Seq class which handles cumulative sum over cycles.
   *
   * @param position Non-negative index into the sequence
   * @return The value at the given position
   */
  def apply(position: BigInt): BigInt = {
    require(position >= 0)
    seq(position)
  }

  /**
   * The first element of the sequence (same as head).
   */
  def first: BigInt = head

  /**
   * The number of gaps in the cycle.
   */
  def size: BigInt = cycle.size

  /**
   * The sum of all gaps in one full cycle.
   * This is also the increment after one complete cycle.
   */
  def cycleSum: BigInt = cycle.sum()

  /**
   * The known prime limit - after filtering by head,
   * all elements up to head² are guaranteed to be prime.
   * This is an emergent property, not an input.
   */
  def knownPrimeLimit: BigInt = head * head

  /**
   * Compute the next SieveSequence by filtering out multiples of head.
   *
   * Takes the current sequence and produces S_{k+1}:
   *   - Filters the cycle values (keeps only those NOT divisible by head)
   *   - New head = head + first gap value
   *
   * @return A new SieveSequence with multiples of head removed
   */
  def next(): SieveSequence = {
    val newHead = head + cycle(0)
    val filteredCycle = filterCycle(cycle, head)
    SieveSequence(
      head = newHead,
      cycle = filteredCycle
    )
  }

  /**
   * Filter a MemCycle to keep only values not divisible by the given divisor.
   */
  private def filterCycle(mCycle: MemCycle, divisor: BigInt): MemCycle = {
    require(divisor > 0)
    require(mCycle.values.nonEmpty)
    filterValues(mCycle.values, divisor, List.empty)
  }

  /**
   * Recursively filter values, keeping those not divisible by divisor.
   */
  private def filterValues(
    input: List[BigInt],
    divisor: BigInt,
    acc: List[BigInt]
  ): MemCycle = {
    require(divisor > 0)
    decreases(input)
    if (input.isEmpty) {
      MemCycle(acc.reverse)
    } else {
      val current = input.head
      if (Calc.mod(current, divisor) != 0) {
        filterValues(input.tail, divisor, current :: acc)
      } else {
        filterValues(input.tail, divisor, acc)
      }
    }
  }
}

object SieveSequence {

  /**
   * S_0: All natural numbers starting from 2.
   *
   * After filtering out 1, we have [2, 3, 4, 5, 6, ...]
   * Represented as: head=2, gaps=[1]
   */
  def S_0(): SieveSequence = {
    SieveSequence(
      head = BigInt(2),
      cycle = MemCycle(List(BigInt(1)))
    )
  }

  /**
   * S_1: Odd numbers starting from 3.
   *
   * After filtering multiples of 2, we have [3, 5, 7, 9, 11, ...]
   * Represented as: head=3, gaps=[2]
   */
  def S_1(): SieveSequence = {
    SieveSequence(
      head = BigInt(3),
      cycle = MemCycle(List(BigInt(2)))
    )
  }

  /**
   * Create a SieveSequence from explicit parameters.
   */
  def apply(head: BigInt, cycle: MemCycle): SieveSequence = {
    require(head > 0)
    require(cycle.size > 0)
    require(cycle.values.forall(_ > 0))
    new SieveSequence(head, cycle)
  }
}