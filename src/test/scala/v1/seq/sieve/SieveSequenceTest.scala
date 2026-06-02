package v1.seq.sieve

import org.scalatest.flatspec.*
import org.scalatest.matchers.should.*
import stainless.collection.List
import v1.cycle.memory.MemCycle

class SieveSequenceTest extends FlatSpec with Matchers {

  "SieveSequence.S_0()" should "have correct properties" in {
    val s0 = SieveSequence.S_0()
    s0.head should be(BigInt(2))
    s0.first should be(BigInt(2))
    s0.primes should be(List.empty)
    s0.modulus should be(BigInt(1))
    s0.knownPrimeLimit should be(BigInt(4))
    s0.cycle.values should be(List(BigInt(1)))
  }

  "S_0().apply" should "produce the sequence 2, 3, 4, 5, ..." in {
    val s0 = SieveSequence.S_0()
    s0(BigInt(0)) should be(BigInt(2))
    s0(BigInt(1)) should be(BigInt(3))
    s0(BigInt(2)) should be(BigInt(4))
    s0(BigInt(3)) should be(BigInt(5))
    s0(BigInt(4)) should be(BigInt(6))
  }

  "S_0().next()" should "produce S_1 (odds starting at 3)" in {
    val s0 = SieveSequence.S_0()
    val s1 = s0.next()

    s1.head should be(BigInt(3))
    s1.first should be(BigInt(3))
    s1.primes should be(List(BigInt(2)))
    s1.modulus should be(BigInt(2))
    s1.cycle.values should be(List(BigInt(2)))
  }

  "S_1 sequence" should "be 3, 5, 7, 9, 11, ..." in {
    val s0 = SieveSequence.S_0()
    val s1 = s0.next()

    s1(BigInt(0)) should be(BigInt(3))
    s1(BigInt(1)) should be(BigInt(5))
    s1(BigInt(2)) should be(BigInt(7))
    s1(BigInt(3)) should be(BigInt(9))
    s1(BigInt(4)) should be(BigInt(11))
  }

  "S_1().next()" should "produce S_2 (head=5, cycle=[4,2])" in {
    val s0 = SieveSequence.S_0()
    val s1 = s0.next()
    val s2 = s1.next()

    s2.head should be(BigInt(5))
    s2.first should be(BigInt(5))
    s2.primes should be(List(BigInt(3), BigInt(2)))
    s2.modulus should be(BigInt(6))
    s2.cycle.values should be(List(BigInt(2), BigInt(4)))
  }

  "S_2 sequence" should "start with 5, 7, 11, 13, 17, 19, 23" in {
    val s0 = SieveSequence.S_0()
    val s1 = s0.next()
    val s2 = s1.next()

    s2(BigInt(0)) should be(BigInt(5))
    s2(BigInt(1)) should be(BigInt(7))
    s2(BigInt(2)) should be(BigInt(11))
    s2(BigInt(3)) should be(BigInt(13))
    s2(BigInt(4)) should be(BigInt(17))
    s2(BigInt(5)) should be(BigInt(19))
    s2(BigInt(6)) should be(BigInt(23))
  }

  "S_2().next()" should "produce S_3 (head=7)" in {
    val s0 = SieveSequence.S_0()
    val s1 = s0.next()
    val s2 = s1.next()
    val s3 = s2.next()

    s3.head should be(BigInt(7))
    s3.primes should be(List(BigInt(5), BigInt(3), BigInt(2)))
    s3.modulus should be(BigInt(30))
  }

  "S_3 sequence" should "start with primes: 7, 11, 13, 17, 19, 23, 29, 31" in {
    val s0 = SieveSequence.S_0()
    val s1 = s0.next()
    val s2 = s1.next()
    val s3 = s2.next()

    s3(BigInt(0)) should be(BigInt(7))
    s3(BigInt(1)) should be(BigInt(11))
    s3(BigInt(2)) should be(BigInt(13))
    s3(BigInt(3)) should be(BigInt(17))
    s3(BigInt(4)) should be(BigInt(19))
    s3(BigInt(5)) should be(BigInt(23))
    s3(BigInt(6)) should be(BigInt(29))
    s3(BigInt(7)) should be(BigInt(31))
  }

  "iterated next()" should "produce primes as heads" in {
    val s0 = SieveSequence.S_0()
    val s1 = s0.next()
    val s2 = s1.next()
    val s3 = s2.next()
    val s4 = s3.next()

    s0.head should be(BigInt(2))
    s1.head should be(BigInt(3))
    s2.head should be(BigInt(5))
    s3.head should be(BigInt(7))
    s4.head should be(BigInt(11))
  }

  "knownPrimeLimit" should "be head squared" in {
    val s0 = SieveSequence.S_0()
    val s1 = s0.next()
    val s2 = s1.next()

    s0.knownPrimeLimit should be(BigInt(4))
    s1.knownPrimeLimit should be(BigInt(9))
    s2.knownPrimeLimit should be(BigInt(25))
  }

  "apply(head: BigInt, cycle: MemCycle)" should "create with empty primes" in {
    val seq = SieveSequence(
      head = BigInt(5),
      cycle = MemCycle(List(BigInt(4), BigInt(2)))
    )
    seq.head should be(BigInt(5))
    seq.primes should be(List.empty)
    seq.modulus should be(BigInt(1))
    seq.cycle.values should be(List(BigInt(4), BigInt(2)))
  }
}
