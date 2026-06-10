package v1.prime

import stainless.collection.List
import stainless.lang.{BigInt, decreases}
import v1.Calc
import stainless.lang.BooleanDecorations
import v1.list.ListBoundUtils
import v1.list.properties.ListProduct

import scala.annotation.tailrec

object PrimeUtils {

  /**
   * Returns the largest prime (by value) in a non-empty list.
   *
   * Pure structural recursion over the list.
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
   * This is a search predicate, not algebra.
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
   * Primorial defined as a structural recursion over primes.
   *
   * This is intentionally NOT expressed via ListProduct
   * to keep proofs simple and avoid higher-order functions.
   */
  def primorial(primes: List[Prime]): BigInt = {
    decreases(primes.size)

    if (primes.isEmpty) BigInt(1)
    else primes.head.value * primorial(primes.tail)
  }

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
   * Lemma connecting primorial to its recursive structure.
   *
   * This is what you use in proofs instead of unfolding definitions.
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
   * Convenience lemma: primorial is always positive (if primes are positive).
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

  def primeValues(primes: List[Prime]): List[BigInt] = {
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