package v1.seq.sieve.properties

import stainless.collection.List
import stainless.lang.{BigInt, BooleanDecorations, decreases}
import v1.cycle.integral.recursive.properties.CycleIntegralProperties
import v1.list.ListBoundUtils
import v1.prime.Prime
import v1.prime.properties.PrimeProperties
import v1.seq.sieve.CycleSieveSequence
import v1.seq.sieve.SieveUtils

object SieveSequenceProperties {

  def assertStrictlyIncreasing(seq: CycleSieveSequence, k: BigInt): Boolean = {
    require(k >= 0)
    require(ListBoundUtils.allGreaterThan(seq.integral.cycle.values, BigInt(0)))
    require(seq.integral.cycle.values.nonEmpty)
    require(seq.integral.cycle.size > 0)
    require(seq.integral.initialValue >= BigInt(0))
    if (k >= 1) {
      assert(CycleIntegralProperties.assertCycleIntegralIncreasing(seq.integral, k - 1, k))
      seq.apply(k + 1) > seq.apply(k)
    } else {
      assert(CycleIntegralProperties.assertCycleValuePositive(seq.integral, BigInt(0)))
      seq.apply(BigInt(1)) > seq.apply(BigInt(0))
    }
  }.holds

  def assertHeadIsMinimum(seq: CycleSieveSequence, k: BigInt): Boolean = {
    require(k >= 0)
    require(ListBoundUtils.allGreaterThan(seq.integral.cycle.values, BigInt(0)))
    require(seq.integral.cycle.values.nonEmpty)
    require(seq.integral.cycle.size > 0)
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

  def assertAllValuesPositive(seq: CycleSieveSequence, k: BigInt): Boolean = {
    require(k >= 0)
    require(seq.head > BigInt(0))
    require(ListBoundUtils.allGreaterThan(seq.integral.cycle.values, BigInt(0)))
    require(seq.integral.cycle.values.nonEmpty)
    require(seq.integral.cycle.size > 0)
    require(seq.integral.initialValue >= BigInt(0))
    if (k == 0) {
      seq.apply(k) > BigInt(0)
    } else {
      assert(CycleIntegralProperties.assertCycleIntegralPositive(seq.integral, k - 1))
      seq.apply(k) > BigInt(0)
    }
  }.holds

  def assertHeadIsPrime(seq: CycleSieveSequence): Boolean = {
    require(SieveUtils.assertAllNotCoprimeInRange(seq.head, 2, seq.primes.tail))
    PrimeProperties.assertHeadIsPrime(seq.head, seq.primes.tail)
    Prime.isPrime(seq.head)
  }.holds
}
