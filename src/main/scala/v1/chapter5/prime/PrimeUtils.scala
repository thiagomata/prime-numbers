package v1.chapter5.prime

import stainless.collection.List
import stainless.lang.{BigInt, decreases}
import stainless.lang.BooleanDecorations
import v1.chapter2.div.Calc
import v1.chapter2.div.properties.{AdditionAndMultiplication, ModSmallDividend}
import v1.chapter3.list.{ListBoundUtils, ListUtils}
import v1.chapter3.list.properties.ListProduct
import v1.chapter6.seq.sieve.SieveUtils

import scala.annotation.tailrec

object PrimeUtils {

  /**
   * Returns the largest prime in the list — the one with the highest value.
   *
   * Walk through the list comparing values, keeping the biggest one you've seen so far.
   * If there's a tie, the first one wins (which is fine, they're equal anyway).
   *
   * biggerPrime(p :: ps).value >= p.value for every p in ps
   *
   * @param primes List[Prime] a non-empty list of primes
   * @return Prime the prime with the highest value in the list
   */
  def biggerPrime(primes: List[Prime]): Prime = {
    decreases(primes.size)
    require(primes.nonEmpty)

    if (primes.tail.isEmpty) primes.head
    else {
      val tailMax = biggerPrime(primes.tail)

      if (tailMax.value > primes.head.value)
        tailMax
      else
        primes.head
    }
  }

  /**
   * Checks whether `value` is divisible by any prime in the list.
   *
   * Scans through the primes one by one. As soon as it finds one that divides
   * `value` evenly (remainder is zero), it stops and says "yes." If none do, "no."
   *
   * This is a search, not a computation — it doesn't build any product.
   *
   * isMultiple(v, primes) == ∃ p ∈ primes. mod(v, p.value) == 0
   *
   * @param value  BigInt the number to check (must be > 1)
   * @param primes List[Prime] the list of candidate divisors
   * @return Boolean true if some prime in the list divides value evenly
   */
  @tailrec
  def isMultiple(value: BigInt, primes: List[Prime]): Boolean = {
    require(value > 1)
    decreases(primes.size)

    if (primes.isEmpty) false
    else if (Calc.mod(value, primes.head.value) == BigInt(0)) true
    else isMultiple(value, primes.tail)
  }

  /**
   * The primorial of a list of primes: the product of all their values.
   *
   * So primorial([2, 3, 5]) = 2 * 3 * 5 = 30, and for an empty list it's 1
   * (the multiplicative identity, so that concatenation works out algebraically).
   *
   * This is defined as a plain structural recursion, not via ListProduct,
   * because that keeps proofs simpler — no higher-order functions to unfold.
   *
   * primorial([]) = 1
   * primorial(p :: ps) = p.value * primorial(ps)
   *
   * @param primes List[Prime] any list of primes (empty is fine)
   * @return BigInt the product of all prime values in the list
   */
  def primorial(primes: List[Prime]): BigInt = {
    decreases(primes.size)

    if (primes.isEmpty) BigInt(1)
    else primes.head.value * primorial(primes.tail)
  }

  /**
   * Lemma: the primorial distributes over list concatenation.
   *
   * If you split the primes into two groups and take the product of each,
   * then multiply them, you get the same result as the product of the whole list.
   * This is just multiplication being associative and commutative, but Stainless
   * needs to be walked through it by structural induction.
   *
   * primorial(prefix ++ suffix) == primorial(prefix) * primorial(suffix)
   *
   * @param prefix List[Prime] first part of the list
   * @param suffix List[Prime] second part of the list
   * @return Boolean true if the property holds
   */
  def primorialConcatLemma(prefix: List[Prime], suffix: List[Prime]): Boolean = {
    decreases(prefix.size)
    if (prefix.isEmpty) {
      primorial(prefix ++ suffix) == primorial(prefix) * primorial(suffix)
    } else {
      primorialConcatLemma(prefix.tail, suffix)
      primorial(prefix ++ suffix) == primorial(prefix) * primorial(suffix)
    }
  }.holds
  
  /**
   * Lemma: unfold the primorial into head times tail-primorial.
   *
   * Instead of inlining the definition of primorial inside your proof
   * (which gets messy), call this lemma. It gives Stainless the equality
   * it needs in one step.
   *
   * primorial(p :: ps) == p.value * primorial(ps)
   * primorial([]) == 1
   *
   * @param primes List[Prime] any list of primes
   * @return Boolean true if the property holds
   */
  def primorialUnfold(primes: List[Prime]): Boolean = {
    decreases(primes.size)

    if (primes.isEmpty) {
      primorial(primes) == BigInt(1)
    } else {
      primorialUnfold(primes.tail)

      primorial(primes) ==
        primes.head.value * primorial(primes.tail)
    }
  }.holds

  /**
   * Lemma: the primorial is always strictly positive.
   *
   * Every prime value is > 1, so the product can never be zero or negative.
   * Trivial for a human, but Stainless needs to see the induction.
   *
   * primorial(primes) > 0
   *
   * @param primes List[Prime] any list of primes
   * @return Boolean true if the property holds
   */
  def primorialPositive(primes: List[Prime]): Boolean = {
    decreases(primes.size)

    if (primes.isEmpty) {
      primorial(primes) > 0
    } else {
      primorialPositive(primes.tail)

      assert(primorial(primes.tail) > 0)

      primorial(primes) > 0
    }
  }.holds

  /**
   * Extract the numeric values from a list of Primes.
   *
   * Strips away the Prime wrapper and gives you just the BigInts.
   * The result is the same length, preserves order, and every value is > 1.
   * Also guarantees that the primorial of the Primes equals the ListProduct
   * of the values — the bridge between the Prime and ListProduct worlds.
   *
   * primeValues([]) = []
   * primeValues(p :: ps) = p.value :: primeValues(ps)
   *
   * @param primes List[Prime] any list of primes
   * @return List[BigInt] the values, in the same order
   */
  def primeIsCoprimeWithSmallerList(v: BigInt, primes: List[Prime]): Boolean = {
    require(v > 1)
    require(Prime.isPrime(v))
    require(primes.nonEmpty)
    require(SortedPrimeList.isDescending(primes))
    require(primes.head.value < v)
    decreases(primes.size)

    if (primes.tail.isEmpty) {
      assert(primes.head.value >= 2)
      assert(primes.head.value < v)
      assert(Prime.noDivisorInRangeExcludesValue(v, 2, v, primes.head.value))
      assert(Calc.mod(v, primes.head.value) != BigInt(0))
      assert(ListUtils.checkAllPositive(primeValues(primes)))
      SieveUtils.isCoprime(v, primeValues(primes))
    } else {
      assert(primes.head.value >= 2)
      assert(primes.head.value < v)
      assert(Prime.noDivisorInRangeExcludesValue(v, 2, v, primes.head.value))
      assert(Calc.mod(v, primes.head.value) != BigInt(0))
      assert(SortedPrimeList.isDescending(primes.tail))
      assert(primes.head.value > primes.tail.head.value)
      assert(primes.tail.head.value < v)
      assert(primeIsCoprimeWithSmallerList(v, primes.tail))
      assert(ListUtils.checkAllPositive(primeValues(primes)))
      SieveUtils.isCoprime(v, primeValues(primes))
    }
  }.holds

  def primeValues(primes: List[Prime]): List[BigInt] = {
    decreases(primes.size)
    if (primes.isEmpty) List()
    else primes.head.value :: primeValues(primes.tail)
  }.ensuring(
    result =>

      assert(primes.isEmpty || primes.head.value > 1)

      result.size == primes.size &&
      (primes.isEmpty || result.head == primes.head.value) &&
      (primes.isEmpty || result.tail == primeValues(primes.tail)) &&
      ListBoundUtils.allGreaterThan(result, BigInt(0)) &&
      ListBoundUtils.allGreaterThan(result, BigInt(1)) &&
      primorial(primes) == ListProduct.product(result)
  )
}