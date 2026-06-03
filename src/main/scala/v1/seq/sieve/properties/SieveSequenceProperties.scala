package v1.seq.sieve.properties

import stainless.lang.*
import v1.Calc
import v1.div.properties.ConsecutiveIntegers
import v1.seq.sieve.SieveSequence
import verification.Helper.{assert}

object SieveSequenceProperties {

  /**
   * Lemma: For S_0 where apply(i) = i + 2,
   * among p consecutive values starting at position start,
   * at least one is divisible by p.
   */
  def atLeastOneMultiplePerBlock(start: BigInt, p: BigInt): Boolean = {
    require(p > 1)
    require(start >= 0)
    ConsecutiveIntegers.existsZero(start + 2, p)
  }.holds

  def assertS0HeadIsTwo(): Boolean = {
    val s0 = SieveSequence.S_0()
    s0.head == BigInt(2)
  }.holds

  def assertS0CycleSumIsOne(): Boolean = {
    val s0 = SieveSequence.S_0()
    s0.cycle.sum() == BigInt(1)
  }.holds

  def assertS0ModulusIsOne(): Boolean = {
    val s0 = SieveSequence.S_0()
    s0.modulus == BigInt(1)
  }.holds

  def assertS0ApplyFormula(n: BigInt): Boolean = {
    require(n >= 0)
    decreases(n)
    val s0 = SieveSequence.S_0()
    if (n == 0) {
      assert(s0.apply(BigInt(0)) == s0.head)
      assert(s0.head == BigInt(2))
      s0.apply(n) == BigInt(2)
    } else {
      assert(assertS0ApplyFormula(n - 1))
      assert(s0.apply(n) == s0.integral(n - 1))
      s0.apply(n) == n + BigInt(2)
    }
  }.holds

  def assertS0StepIsOne(n: BigInt): Boolean = {
    require(n > 0)
    val s0 = SieveSequence.S_0()
    assert(assertS0ApplyFormula(n))
    assert(assertS0ApplyFormula(n - 1))
    s0.apply(n) - s0.apply(n - 1) == BigInt(1)
  }.holds
}
