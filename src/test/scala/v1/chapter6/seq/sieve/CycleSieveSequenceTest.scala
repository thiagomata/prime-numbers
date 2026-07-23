package v1.chapter6.seq.sieve

import org.scalatest.flatspec.*
import org.scalatest.matchers.should.*
import stainless.collection.List
import v1.chapter4.cycle.memory.MemCycle

class CycleSieveSequenceTest extends FlatSpec with Matchers {

  "CycleSieveSequence.S_0()" should "have correct properties" in {
    val s0 = CycleSieveSequence.S_0()
    s0.head should be(BigInt(2))
    // s0.primes should be(List(BigInt(2)))
    s0.modulus should be(BigInt(1))
    s0.cycle.values should be(List(BigInt(1)))
  }

  "S_0().apply" should "produce the sequence 2, 3, 4, 5, ..." in {
    val s0 = CycleSieveSequence.S_0()
    s0(BigInt(0)) should be(BigInt(2))
    s0(BigInt(1)) should be(BigInt(3))
    s0(BigInt(2)) should be(BigInt(4))
    s0(BigInt(3)) should be(BigInt(5))
    s0(BigInt(4)) should be(BigInt(6))
  }

  // "S_0().next()" should "equal CycleSieveSequence after transition" in {
  //   val s0 = CycleSieveSequence.S_0()
  //   val s1 = s0.next()
  //   s1.head should be(BigInt(3))
  //   s1.primes should be(List(BigInt(3), BigInt(2)))
  //   s1.cycle.values should be(List(BigInt(2)))
  // }

  "CycleSieveSequence.S_1()" should "have correct properties" in {
    val s1 = CycleSieveSequence.S_1()
    s1.head should be(BigInt(3))
    // s1.primes should be(List(BigInt(3), BigInt(2)))
    s1.modulus should be(BigInt(2))
    s1.cycle.values should be(List(BigInt(2)))
  }

  "S_1().apply" should "produce the sequence 3, 5, 7, 9, ..." in {
    val s1 = CycleSieveSequence.S_1()
    s1(BigInt(0)) should be(BigInt(3))
    s1(BigInt(1)) should be(BigInt(5))
    s1(BigInt(2)) should be(BigInt(7))
    s1(BigInt(3)) should be(BigInt(9))
    s1(BigInt(4)) should be(BigInt(11))
  }

  // "S_1().next() -> S_2" should "have correct head and primes" in {
  //   val s2 = CycleSieveSequence.S_1().next()
  //   s2.head should be(BigInt(5))
  //   s2.primes should be(List(BigInt(5), BigInt(3), BigInt(2)))
  //   s2.modulus should be(BigInt(6))
  //   s2.cycle.sum() should be(BigInt(6))
  //   s2.cycle.size should be(BigInt(2))
  // }

  // "S_2V2.apply" should "produce 5, 7, 11, 13, 17, ..." in {
  //   val s2 = CycleSieveSequence.S_1().next()
  //   s2.head should be(BigInt(5))
  //   s2.cycle.values should be(List(BigInt(2), BigInt(4)))
  //   s2(BigInt(0)) should be(BigInt(5))
  //   s2(BigInt(1)) should be(BigInt(7))
  //   s2(BigInt(2)) should be(BigInt(11))
  //   s2(BigInt(3)) should be(BigInt(13))
  //   s2(BigInt(4)) should be(BigInt(17))
  // }

  "nextGapCycle" should "produce GapCycle for S_0" in {
    val gc = SieveSequenceNextLevel.nextGapCycle(CycleSieveSequence.S_0())
    gc.memCycle.values should be(List(BigInt(2)))
    gc.period should be(BigInt(1))
  }

  it should "produce GapCycle for S_1" in {
    val gc = SieveSequenceNextLevel.nextGapCycle(CycleSieveSequence.S_1())
    gc.memCycle.values should be(List(BigInt(2), BigInt(4)))
    gc.period should be(BigInt(2))
  }
}
