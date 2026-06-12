package v1.cycle.integral.recursive.properties

import stainless.collection.List
import stainless.lang.{BigInt, BooleanDecorations, decreases}
import v1.cycle.integral.recursive.CycleIntegral
import v1.cycle.memory.MemCycle
import v1.list.ListBoundUtils
import verification.Helper.assert

/**
 * # CycleIntegral of Constant Cycle [1] = Natural Numbers
 *
 * ## Why This Matters
 *
 * The sieve sequence starts with S_0, which generates all natural numbers >= 2.
 * This is because S_0 uses a gap cycle of [1], meaning each step adds exactly 1.
 *
 * Mathematically: CycleIntegral(init, [1]).apply(n) = init + n + 1
 *
 * For S_0: init = 2, so S_0(n) = n + 2, giving us 2, 3, 4, 5, ...
 *
 * ## The Key Insight
 *
 * A constant cycle of 1s produces an arithmetic progression with step 1.
 * This is the simplest possible cycle, and it generates ALL natural numbers.
 * Later, we filter this list to keep only primes, but we must prove that
 * filtering never removes a prime — only composites.
 *
 * ## Connection to the Sieve
 *
 * This property is the BASE CASE of the sieve's correctness:
 * 1. S_0 = natural numbers (proven here)
 * 2. Filtering preserves all primes (proven in FilterPreservesPrimesProperties)
 * 3. Therefore, every sieve level contains all primes
 *
 * @see `v1.prime.properties.FilterPreservesPrimesProperties` for the filtering proof
 * @see `v1.cycle.integral.recursive.CycleIntegral` for the integral definition
 */
object CycleIntegralOnesProperties {

  /**
   * ## Lemma 1: CycleIntegral of [1] equals init + n + 1
   *
   * **Statement:** For a cycle containing only the value 1:
   * ```
   * CI(init, [1]).apply(n) == init + n + 1
   * ```
   *
   * **Why This Works:**
   * - Base case: CI(0) = cycle(0) + init = 1 + init
   * - Inductive step: CI(n) = CI(n-1) + cycle(n) = CI(n-1) + 1
   * - By induction: CI(n) = init + 1 + n
   *
   * **Intuition:** Each step adds exactly 1, so after n steps we've added n.
   * Starting from init + 1 (the first value), we get init + 1 + n.
   *
   * @param init The initial value (e.g., 2 for S_0)
   * @param pos The position in the sequence (0-indexed)
   * @return true if CI(init, [1]).apply(pos) == init + pos + 1
   */
  def assertCycleIntegralOfOnes(init: BigInt, pos: BigInt): Boolean = {
    require(pos >= 0)
    require(init >= 0)
    val cycle = MemCycle(stainless.collection.List(BigInt(1)))
    val ci = CycleIntegral(init, cycle)
    decreases(pos)
    if (pos == 0) {
      // Base case: CI(0) = cycle(0) + init = 1 + init
      ci(0) == init + BigInt(1)
    } else {
      // Inductive step: CI(pos) = CI(pos-1) + cycle(pos) = CI(pos-1) + 1
      assert(assertCycleIntegralOfOnes(init, pos - 1))
      ci(pos) == init + pos + BigInt(1)
    }
  }.holds

  /**
   * ## Lemma 2: CycleIntegral of [1] is strictly increasing
   *
   * **Statement:** For a cycle of [1] and positions a < b:
   * ```
   * CI(init, [1]).apply(b) > CI(init, [1]).apply(a)
   * ```
   *
   * **Why This Matters:**
   * This proves the sequence never stalls or goes backwards.
   * Every position gives a strictly larger value than the previous.
   *
   * **Proof:** From Lemma 1:
   * - CI(b) = init + b + 1
   * - CI(a) = init + a + 1
   * - Since b > a, we have init + b + 1 > init + a + 1
   *
   * **Intuition:** Each step adds exactly 1, so later positions are always larger.
   * This is the foundation for proving gaps are positive in the sieve.
   *
   * @param init The initial value
   * @param a First position (smaller)
   * @param b Second position (larger)
   * @return true if CI(init, [1]).apply(b) > CI(init, [1]).apply(a)
   */
  def assertCycleIntegralOfOnesStrictlyIncreasing(init: BigInt, a: BigInt, b: BigInt): Boolean = {
    require(a >= 0)
    require(b > a)
    require(init >= 0)
    val cycle = MemCycle(stainless.collection.List(BigInt(1)))
    val ci = CycleIntegral(init, cycle)
    assert(assertCycleIntegralOfOnes(init, a))
    assert(assertCycleIntegralOfOnes(init, b))
    ci(b) > ci(a)
  }.holds
}
