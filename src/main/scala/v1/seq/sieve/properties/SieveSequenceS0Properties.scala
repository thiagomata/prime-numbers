package v1.seq.sieve.properties

import stainless.lang.*
import v1.div.properties.ModOne
import v1.seq.sieve.SieveSequence
import verification.Helper.{assert}

object SieveSequenceS0Properties {

  def assertS0CycleAlwaysOne(n: BigInt): Boolean = {
    require(n >= 0)
    val s0 = SieveSequence.S_0()
    assert(ModOne.modOneIsZero(n))
    s0.cycle(n) == BigInt(1)
  }.holds

  def assertS0AtZero(): Boolean = {
    val s0 = SieveSequence.S_0()
    assert(s0.apply(BigInt(0)) == s0.head)
    assert(s0.head == BigInt(2))
    s0.apply(BigInt(0)) == BigInt(2)
  }.holds

  def assertS0AtOne(): Boolean = {
    val s0 = SieveSequence.S_0()
    assert(s0.apply(BigInt(1)) == s0.integral(BigInt(0)))
    assert(s0.integral(BigInt(0)) == s0.cycle(BigInt(0)) + s0.integral.initialValue)
    assert(s0.integral.initialValue == s0.head)
    assert(s0.head == BigInt(2))
    assert(s0.cycle(BigInt(0)) == BigInt(1))
    s0.apply(BigInt(1)) == BigInt(3)
  }.holds

  def assertS0Formula(n: BigInt): Boolean = {
    require(n >= 0)
    decreases(n)
    val s0 = SieveSequence.S_0()
    if (n == 0) {
      assert(s0.apply(BigInt(0)) == s0.head)
      assert(s0.head == BigInt(2))
      s0.apply(n) == BigInt(2)
    } else if (n == 1) {
      assert(s0.apply(BigInt(1)) == s0.integral(BigInt(0)))
      assert(s0.integral(BigInt(0)) == s0.cycle(BigInt(0)) + s0.integral.initialValue)
      assert(s0.integral.initialValue == s0.head)
      assert(s0.head == BigInt(2))
      assert(s0.cycle(BigInt(0)) == BigInt(1))
      s0.apply(n) == BigInt(3)
    } else {
      assert(assertS0Formula(n - 1))
      assert(assertS0CycleAlwaysOne(n - 1))
      assert(s0.apply(n) == s0.integral(n - 1))
      assert(s0.integral(n - 1) == s0.cycle(n - 1) + s0.integral(n - 2))
      assert(s0.integral(n - 2) == s0.apply(n - 1))
      assert(s0.cycle(n - 1) == BigInt(1))
      s0.apply(n) == n + BigInt(2)
    }
  }.holds
}
