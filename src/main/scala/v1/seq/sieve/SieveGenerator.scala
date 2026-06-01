package v1.seq.sieve

import stainless.collection.List
import stainless.lang.*
import v1.Calc
import v1.cycle.memory.MemCycle
import v1.seq.Seq

/**
 * SieveGenerator provides the logic for generating the next level of sieve sequences
 * based on the cycle refinement approach.
 */
object SieveGenerator {
  
  /**
   * Generates the next SieveSequence from the current one.
   * 
   * This implements the cycle refinement process where:
   * 1. The next head is determined as current.head + first_gap
   * 2. The new cycle is derived by filtering out multiples of the current head
   *    from the current cycle values
   * 
   * @param current The current SieveSequence to transform
   * @return The next SieveSequence
   */
  def nextLevel(current: SieveSequence): SieveSequence = {
    // 1. Calculate the new head: head + first_gap
    val newHead = current.head + current.cycle(0)
    
    // 2. Filter the cycle values to remove multiples of current.head
    val filteredCycle = filterCycle(current.cycle, current.head)
    
    SieveSequence(
      head = newHead,
      cycle = filteredCycle
    )
  }
  
  /**
   * Filter a MemCycle to keep only values not divisible by the given divisor.
   * 
   * Uses recursive implementation for Stainless compatibility.
   * 
   * @param mCycle The cycle to filter
   * @param divisor The divisor to check for multiples
   * @return A new MemCycle with filtered values
   */
  private def filterCycle(mCycle: MemCycle, divisor: BigInt): MemCycle = {
    require(divisor > 0)
    require(mCycle.values.nonEmpty)
    filterValues(mCycle.values, divisor, List.empty)
  }
  
  /**
   * Recursively filter values, keeping those not divisible by divisor.
   * 
   * Stainless-compatible recursive implementation.
   * 
   * @param input List of values to filter
   * @param divisor Divisor to check for multiples
   * @param acc Accumulator for filtered values
   * @return A new MemCycle with filtered values
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