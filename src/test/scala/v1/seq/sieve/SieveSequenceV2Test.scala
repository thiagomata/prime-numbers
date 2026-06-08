package v1.seq.sieve

import org.scalatest.flatspec.*
import org.scalatest.matchers.should.*
import stainless.collection.List
import v1.cycle.memory.MemCycle

class SieveSequenceV2Test extends FlatSpec with Matchers {

  "SieveSequenceV2.S_0V2()" should "have correct properties" in {
    val s0 = SieveSequenceV2.S_0V2()
    s0.head should be(BigInt(2))
    s0.primes should be(List(BigInt(2)))
    s0.modulus should be(BigInt(1))
    s0.cycle.values should be(List(BigInt(1)))
  }

  "S_0V2().apply" should "produce the sequence 2, 3, 4, 5, ..." in {
    val s0 = SieveSequenceV2.S_0V2()
    s0(BigInt(0)) should be(BigInt(2))
    s0(BigInt(1)) should be(BigInt(3))
    s0(BigInt(2)) should be(BigInt(4))
    s0(BigInt(3)) should be(BigInt(5))
    s0(BigInt(4)) should be(BigInt(6))
  }

  "S_0V2().next()" should "equal SieveSequenceV2 after transition" in {
    val s0 = SieveSequenceV2.S_0V2()
    val s1 = s0.next()
    s1.head should be(BigInt(3))
    s1.primes should be(List(BigInt(3), BigInt(2)))
    s1.cycle.values should be(List(BigInt(2)))
  }

  "SieveSequenceV2.S_1V2()" should "have correct properties" in {
    val s1 = SieveSequenceV2.S_1V2()
    s1.head should be(BigInt(3))
    s1.primes should be(List(BigInt(3), BigInt(2)))
    s1.modulus should be(BigInt(2))
    s1.cycle.values should be(List(BigInt(2)))
  }

  "S_1V2().apply" should "produce the sequence 3, 5, 7, 9, ..." in {
    val s1 = SieveSequenceV2.S_1V2()
    s1(BigInt(0)) should be(BigInt(3))
    s1(BigInt(1)) should be(BigInt(5))
    s1(BigInt(2)) should be(BigInt(7))
    s1(BigInt(3)) should be(BigInt(9))
    s1(BigInt(4)) should be(BigInt(11))
  }

  "S_1V2().next() -> S_2" should "have correct head and primes" in {
    val s2 = SieveSequenceV2.S_1V2().next()
    s2.head should be(BigInt(5))
    s2.primes should be(List(BigInt(5), BigInt(3), BigInt(2)))
    s2.modulus should be(BigInt(6))
    s2.cycle.sum() should be(BigInt(6))
    s2.cycle.size should be(BigInt(2))
  }

  "S_2V2.apply" should "produce 5, 7, 11, 13, 17, ..." in {
    val s2 = SieveSequenceV2.S_1V2().next()
    s2.head should be(BigInt(5))
    s2.cycle.values should be(List(BigInt(2), BigInt(4)))
    s2(BigInt(0)) should be(BigInt(5))
    s2(BigInt(1)) should be(BigInt(7))
    s2(BigInt(2)) should be(BigInt(11))
    s2(BigInt(3)) should be(BigInt(13))
    s2(BigInt(4)) should be(BigInt(17))
  }

  "V2 equivalence with V1" should "match S_0" in {
    SieveSequenceV2.S_0V2().primes should be(SieveSequence.S_0().primes)
    SieveSequenceV2.S_0V2().head should be(SieveSequence.S_0().head)
    SieveSequenceV2.S_0V2().cycle.values should be(SieveSequence.S_0().cycle.values)
  }

  it should "match S_1" in {
    SieveSequenceV2.S_1V2().primes should be(SieveSequence.S_1().primes)
    SieveSequenceV2.S_1V2().head should be(SieveSequence.S_1().head)
    SieveSequenceV2.S_1V2().cycle.values should be(SieveSequence.S_1().cycle.values)
  }

  it should "match S_2 (after next)" in {
    val v1_s2 = SieveSequence.S_1().next()
    val v2_s2 = SieveSequenceV2.S_1V2().next()
    v2_s2.primes should be(v1_s2.primes)
    v2_s2.head should be(v1_s2.head)
    v2_s2.cycle.values should be(v1_s2.cycle.values)
  }

  "nextGapCycle" should "produce GapCycle for S_0" in {
    val gc = SieveSequenceNextLevel.nextGapCycle(SieveSequence.S_0())
    gc.memCycle.values should be(List(BigInt(2)))
    gc.size should be(BigInt(1))
  }

  it should "produce GapCycle for S_1" in {
    val gc = SieveSequenceNextLevel.nextGapCycle(SieveSequence.S_1())
    gc.memCycle.values should be(List(BigInt(2), BigInt(4)))
    gc.size should be(BigInt(2))
  }
}
