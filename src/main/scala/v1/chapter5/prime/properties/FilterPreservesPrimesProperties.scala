package v1.chapter5.prime.properties

import stainless.collection.List
import stainless.lang.{BigInt, BooleanDecorations, decreases}
import v1.chapter2.div.Calc
import v1.chapter2.div.properties.ModSmallDividend
import v1.chapter5.prime.Prime
import v1.chapter6.seq.sieve.SieveUtils

/**
 * # Filtering Preserves All Primes
 *
 * ## Why This Matters
 *
 * The sieve works by repeatedly filtering out multiples of primes.
 * For example:
 * - Start with natural numbers: 2, 3, 4, 5, 6, 7, 8, 9, 10, ...
 * - Filter out multiples of 2 (keep 2): 2, 3, 5, 7, 9, 11, 13, 15, ...
 * - Filter out multiples of 3 (keep 3): 2, 3, 5, 7, 11, 13, 17, 19, ...
 *
 * **Critical insight:** After filtering, we still have ALL primes!
 * We may also have composites (like 9 after filtering by 2), but we NEVER lose a prime.
 *
 * ## The Core Proof
 *
 * If q is a prime and p is a different prime, then q is NOT a multiple of p.
 * Why? Because if p divided q, then p would be a divisor of q.
 * But q is prime, so its only divisors are 1 and q itself.
 * Since p ≠ q and p > 1, p cannot divide q.
 *
 * ## Connection to the Sieve
 *
 * This property is the INDUCTIVE STEP of the sieve's correctness:
 * 1. S_0 = natural numbers (contains all primes) — proven in CycleIntegralOnesProperties
 * 2. Filtering by prime p preserves all primes — proven here
 * 3. Therefore, every sieve level contains all primes
 *
 * @see `v1.cycle.integral.recursive.properties.CycleIntegralOnesProperties` for the base case
 * @see `v1.prime.Prime` for the definition of primality
 */
object FilterPreservesPrimesProperties {

  /**
   * ## Helper: noDivisorInRange implies mod is non-zero for specific divisor
   *
   * **Statement:** If `noDivisorInRange(n, from, to)` holds and `d` is in `[from, to)`:
   * ```
   * noDivisorInRange(n, from, to) ∧ d >= from ∧ d < to ⟹ mod(n, d) != 0
   * ```
   *
   * **Why This Matters:**
   * This bridges the gap between the recursive `noDivisorInRange` predicate
   * and a specific modulo check. The solver can't automatically connect these,
   * so we prove it explicitly by induction on `to - from`.
   *
   * **Proof:** By induction on `to - from`:
   * - Base case: `from == to` → range is empty, so `d` can't be in it (contradiction)
   * - Inductive step: `from < to`
   *   - If `d == from`: `noDivisorInRange` gives `mod(n, from) != 0`
   *   - If `d > from`: recurse on `noDivisorInRange(n, from+1, to)` with `d >= from+1`
   *
   * @param n The number being checked
   * @param from Lower bound of range (inclusive)
   * @param to Upper bound (exclusive)
   * @param d The specific divisor to check
   * @return true if mod(n, d) != 0 when d is in [from, to)
   */
  private def noDivisorInRangeImpliesModNonZero(
    n: BigInt, from: BigInt, to: BigInt, d: BigInt
  ): Boolean = {
    require(n >= 0)
    require(from >= 1)
    require(to >= from)
    require(Prime.noDivisorInRange(n, from, to))
    require(d >= from)
    require(d < to)
    decreases(to - from)
    if (from == to) {
      // Contradiction: d >= from and d < to, but from == to
      false
    } else if (d == from) {
      // Base case: d == from, so mod(n, d) = mod(n, from) != 0
      Calc.mod(n, d) != BigInt(0)
    } else {
      // Inductive step: d > from, so d >= from+1
      // noDivisorInRange(n, from, to) gives:
      //   mod(n, from) != 0 && noDivisorInRange(n, from+1, to)
      // We need: noDivisorInRange(n, from+1, to) ∧ d >= from+1 ∧ d < to
      noDivisorInRangeImpliesModNonZero(n, from + 1, to, d)
      Calc.mod(n, d) != BigInt(0)
    }
  }.holds

  /**
   * ## Lemma 3: Distinct primes don't divide each other
   *
   * **Statement:** If q and p are distinct primes:
   * ```
   * isPrime(q) ∧ isPrime(p) ∧ q ≠ p ⟹ mod(q, p) ≠ 0
   * ```
   *
   * **Why This Is True:**
   *
   * Case 1: q > p
   * - Since isPrime(q), we have noDivisorInRange(q, 2, q)
   * - p is in [2, q) since p >= 2 and p < q
   * - By helper lemma: mod(q, p) ≠ 0
   *
   * Case 2: q < p
   * - When we compute mod(q, p) with q < p, the result is q itself
   * - Since isPrime(q), we know q > 1
   * - Therefore mod(q, p) = q ≠ 0
   *
   * **Intuition:** Two different primes share no common factors.
   * One cannot be a multiple of the other.
   *
   * @param q First prime
   * @param p Second prime
   * @return true if mod(q, p) ≠ 0 when q ≠ p
   */
  def assertPrimeNotDivisibleByDistinctPrime(q: BigInt, p: BigInt): Boolean = {
    require(q >= 2)
    require(p >= 2)
    require(Prime.isPrime(q))
    require(Prime.isPrime(p))
    require(q != p)
    if (q > p) {
      // Case 1: q > p
      // isPrime(q) means noDivisorInRange(q, 2, q)
      // p is in [2, q) since p >= 2 (from require) and p < q (from q > p)
      // By helper lemma: mod(q, p) ≠ 0
      assert(noDivisorInRangeImpliesModNonZero(q, 2, q, p))
      Calc.mod(q, p) != BigInt(0)
    } else {
      // Case 2: q < p
      // mod(q, p) = q when q < p
      // isPrime(q) means q > 1
      // Therefore mod(q, p) = q ≠ 0
      assert(ModSmallDividend.modSmallDividend(q, p))
      Calc.mod(q, p) != BigInt(0)
    }
  }.holds

  /**
   * ## Lemma 4: Any prime ≠ filterPrime survives filtering
   *
   * **Statement:** For any prime q that is not the filter prime:
   * ```
   * isPrime(q) ∧ q ≠ filterPrime ⟹ mod(q, filterPrime) ≠ 0
   * ```
   *
   * **Why This Matters:**
   * This is a direct restatement of Lemma 3, specialized to the filtering context.
   * It tells us: any prime in our list will NOT be removed by filtering.
   *
   * **Connection to Filtering:**
   * When we filter a list to remove multiples of filterPrime:
   * - We remove elements where mod(element, filterPrime) == 0
   * - By this lemma, no prime q ≠ filterPrime is removed
   * - The filter prime itself is kept explicitly
   *
   * **Intuition:** A prime is never a multiple of a different prime.
   * So filtering by one prime never removes a different prime.
   *
   * @param q A prime number
   * @param filterPrime The prime we're filtering by
   * @return true if mod(q, filterPrime) ≠ 0
   */
  def assertFilterPreservesAllPrimes(q: BigInt, filterPrime: BigInt): Boolean = {
    require(q >= 2)
    require(filterPrime >= 2)
    require(Prime.isPrime(q))
    require(Prime.isPrime(filterPrime))
    require(q != filterPrime)
    // Direct application of Lemma 3
    assert(assertPrimeNotDivisibleByDistinctPrime(q, filterPrime))
    Calc.mod(q, filterPrime) != BigInt(0)
  }.holds

  /**
   * ## Lemma 5: Filtered list contains all primes (by induction)
   *
   * **Statement:** For any prime q in the original list where q ≠ filterPrime:
   * ```
   * q ∈ originalPrimes ∧ isPrime(q) ∧ q ≠ filterPrime ⟹ q ∈ filteredPrimes
   * ```
   * where `filteredPrimes = filterList(originalPrimes, filterPrime)`
   *
   * **Why This Matters:**
   * This is the INDUCTIVE STEP of the sieve's correctness proof:
   * 1. S_0 = natural numbers (contains all primes) — proven in CycleIntegralOnesProperties
   * 2. Filtering by prime p preserves all primes — proven here
   * 3. Therefore, every sieve level contains all primes
   *
   * **Proof:** By induction on `originalPrimes`:
   * - Base case: empty list → q can't be in it (contradiction)
   * - Inductive step:
   *   - If `originalPrimes.head == q`: 
   *     - By Lemma 4: `mod(q, filterPrime) ≠ 0`
   *     - Therefore `filterList` keeps `q` (since `mod(q, filterPrime) ≠ 0`)
   *   - If `originalPrimes.head ≠ q`: recurse on tail
   *
   * **Intuition:** We only remove multiples of primes. Primes are never multiples
   * of other primes (by Lemma 3). So we never remove a prime.
   *
   * @param originalPrimes The list before filtering
   * @param filterPrime The prime we're filtering by
   * @param q A prime to check
   * @return true if q is in the filtered list when q is in the original list
   */
  def assertFilteredContainsAllPrimes(
    originalPrimes: List[BigInt],
    filterPrime: BigInt,
    q: BigInt
  ): Boolean = {
    require(filterPrime >= 2)
    require(Prime.isPrime(filterPrime))
    require(q >= 2)
    require(Prime.isPrime(q))
    require(q != filterPrime)
    require(originalPrimes.contains(q))
    decreases(originalPrimes.size)
    if (originalPrimes.isEmpty) {
      // Contradiction: q is in empty list
      false
    } else {
      val filtered = SieveUtils.filterList(originalPrimes, filterPrime)
      if (originalPrimes.head == q) {
        // q is the head of the list
        // By Lemma 4: mod(q, filterPrime) ≠ 0
        // Therefore filterList keeps q
        assert(assertFilterPreservesAllPrimes(q, filterPrime))
        // filterList keeps head when mod(head, filterPrime) ≠ 0
        filtered.contains(q)
      } else {
        // q is in the tail, recurse
        assert(assertFilteredContainsAllPrimes(originalPrimes.tail, filterPrime, q))
        filtered.contains(q)
      }
    }
  }.holds
}
