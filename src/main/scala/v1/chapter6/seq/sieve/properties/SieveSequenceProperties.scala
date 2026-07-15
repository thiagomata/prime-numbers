package v1.chapter6.seq.sieve.properties

import stainless.collection.List
import stainless.lang.{BigInt, BooleanDecorations, decreases}
import v1.chapter3.list.ListBoundUtils
import v1.chapter4.cycle.integral.recursive.properties.CycleIntegralProperties
import v1.chapter5.prime.{Prime, CoprimeUtils}
import v1.chapter5.prime.properties.PrimeProperties
import v1.chapter6.seq.sieve.CycleSieveSequence

object SieveSequenceProperties {

  /**
   * Proves that a cycle sieve sequence strictly increases at position `k`.
   *
   * Under positive gap-cycle storage, the integral step after each generated
   * value adds a positive gap. The result is `seq(k + 1) > seq(k)`.
   */
  def assertStrictlyIncreasing(seq: CycleSieveSequence, k: BigInt): Boolean = {
    require(k >= 0)
    require(ListBoundUtils.allGreaterThan(seq.integral.cycle.values, BigInt(0)))
    require(seq.integral.cycle.values.nonEmpty)
    require(seq.integral.cycle.period > 0)
    require(seq.integral.initialValue >= BigInt(0))
    if (k >= 1) {
      assert(CycleIntegralProperties.assertCycleIntegralIncreasing(seq.integral, k - 1, k))
      seq.apply(k + 1) > seq.apply(k)
    } else {
      assert(CycleIntegralProperties.assertCycleValuePositive(seq.integral, BigInt(0)))
      seq.apply(BigInt(1)) > seq.apply(BigInt(0))
    }
  }.holds

  /**
   * Proves that the head value is a lower bound for every generated value up to
   * index `k`.
   *
   * The proof walks backward through the strictly-increasing property until it
   * reaches index `0`, where `seq(0) == seq.head`.
   */
  def assertHeadIsMinimum(seq: CycleSieveSequence, k: BigInt): Boolean = {
    require(k >= 0)
    require(ListBoundUtils.allGreaterThan(seq.integral.cycle.values, BigInt(0)))
    require(seq.integral.cycle.values.nonEmpty)
    require(seq.integral.cycle.period > 0)
    require(seq.integral.initialValue >= BigInt(0))
    decreases(k)
    if (k == 0) {
      seq.apply(k) >= seq.apply(BigInt(0))
    } else {
      assert(assertStrictlyIncreasing(seq, k - 1))
      assert(assertHeadIsMinimum(seq, k - 1))
      seq.apply(k) >= seq.apply(BigInt(0))
    }
  }.holds

  /**
   * Proves that every generated value at index `k` is positive.
   *
   * The head is positive by precondition, and every later value is produced by a
   * positive cycle-integral step.
   */
  def assertAllValuesPositive(seq: CycleSieveSequence, k: BigInt): Boolean = {
    require(k >= 0)
    require(seq.head > BigInt(0))
    require(ListBoundUtils.allGreaterThan(seq.integral.cycle.values, BigInt(0)))
    require(seq.integral.cycle.values.nonEmpty)
    require(seq.integral.cycle.period > 0)
    require(seq.integral.initialValue >= BigInt(0))
    if (k == 0) {
      seq.apply(k) > BigInt(0)
    } else {
      assert(CycleIntegralProperties.assertCycleIntegralPositive(seq.integral, k - 1))
      seq.apply(k) > BigInt(0)
    }
  }.holds

  /**
   * Proves that the sequence head is prime from the stored prime-tail filter.
   *
   * If the head is coprime with the known tail primes and every smaller
   * non-prime candidate is ruled out by the same range proof, then
   * `Prime.isPrime(seq.head)` holds.
   */
  def assertHeadIsPrime(seq: CycleSieveSequence): Boolean = {
    require(CoprimeUtils.isCoprime(seq.head, seq.primesTailValues))
    require(CoprimeUtils.assertAllNotCoprimeInRange(seq.head, 2, seq.primesTailValues))
    PrimeProperties.assertHeadIsPrime(seq.head, seq.primesTailValues)
    Prime.isPrime(seq.head)
  }.holds
}
