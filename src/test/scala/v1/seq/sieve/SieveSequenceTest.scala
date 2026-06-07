package v1.seq.sieve

import org.scalatest.flatspec.*
import org.scalatest.matchers.should.*
import stainless.collection.List
import v1.cycle.memory.MemCycle

class SieveSequenceTest extends FlatSpec with Matchers {

  "SieveSequence.S_0()" should "have correct properties" in {
    val s0 = SieveSequence.S_0()
    s0.head should be(BigInt(2))
    s0.primes should be(List(BigInt(2)))
    s0.modulus should be(BigInt(1))
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

  "S_0().next()" should "equal S_1()" in {
    val fromS0 = SieveSequence.S_0().next()
    val s1 = SieveSequence.S_1()
    fromS0.head should be(s1.head)
    fromS0.primes should be(s1.primes)
    fromS0.cycle.values should be(s1.cycle.values)
  }

  "S_1().apply" should "produce the sequence 3, 5, 7, 9, ..." in {
    val s1 = SieveSequence.S_1()
    s1(BigInt(0)) should be(BigInt(3))
    s1(BigInt(1)) should be(BigInt(5))
    s1(BigInt(2)) should be(BigInt(7))
    s1(BigInt(3)) should be(BigInt(9))
    s1(BigInt(4)) should be(BigInt(11))
  }

  "S_1().next() -> S_2" should "have correct head and primes" in {
    val s1 = SieveSequence.S_1()
    s1.primes should be(List(BigInt(3), BigInt(2)))
    s1.modulus should be(BigInt(2))
    s1.head should be(BigInt(3))

    val s2 = SieveSequence.S_1().next()
    s2.head should be(BigInt(5))
    s2.primes should be(List(BigInt(5), BigInt(3), BigInt(2)))
    s2.modulus should be(BigInt(6))
    s2.cycle.sum() should be(BigInt(6))
    s2.cycle.size should be(BigInt(2))
  }

  "pipeline debugging S_1" should "show correct intermediate values" in {
    val s1 = SieveSequence.S_1()
    val sorted = SieveSequenceNextLevel.nextSorted(s1)
    val newHeadVal = s1.apply(BigInt(1))
    val newMod = s1.modulus * s1.head
    val target = newHeadVal % newMod
    val idx = SieveUtils.nextResidueIndex(sorted, BigInt(0), target)
    val nrg = SieveSequenceNextLevel.nextRotatedGaps(s1)
    sorted should be(List(BigInt(1), BigInt(5)))
    target should be(BigInt(5))
    idx should be(BigInt(1))
    nrg should be(List(BigInt(2), BigInt(4)))
  }

  "pipeline debugging S_0" should "show correct intermediate values" in {
    val s0 = SieveSequence.S_0()
    val residues = SieveSequenceNextLevel.nextResidues(s0)
    val expanded = SieveSequenceNextLevel.nextExpanded(s0)
    val filtered = SieveSequenceNextLevel.nextFiltered(s0)
    val sorted = SieveSequenceNextLevel.nextSorted(s0)
    val gaps = SieveSequenceNextLevel.nextGaps(s0)
    val headResIdx = SieveSequenceNextLevel.nextHeadResidueIndex(s0)
    val nrg = SieveSequenceNextLevel.nextRotatedGaps(s0)

    residues should be(List(BigInt(0)))
    expanded should be(List(BigInt(0), BigInt(1)))
    filtered should be(List(BigInt(1)))
    sorted should be(List(BigInt(1)))
    gaps should be(List(BigInt(2)))
    headResIdx should be(BigInt(0))
    nrg should be(List(BigInt(2)))
  }

  "nextCycle(S_0)" should "produce MemCycle([2])" in {
    val cycle = SieveSequenceNextLevel.nextCycle(SieveSequence.S_0())
    cycle.values should be(List(BigInt(2)))
  }

  "nextCycle(S_1)" should "produce MemCycle([2,4])" in {
    val cycle = SieveSequenceNextLevel.nextCycle(SieveSequence.S_1())
    cycle.values should be(List(BigInt(2), BigInt(4)))
  }

  "S_2().apply" should "produce 5, 7, 11, 13, 17, ..." in {
    val s2 = SieveSequence.S_1().next()
    s2.head should be(BigInt(5))
    s2.cycle.values should be(List(BigInt(2), BigInt(4)))
    s2(BigInt(0)) should be(BigInt(5))
    s2(BigInt(1)) should be(BigInt(7))
    s2(BigInt(2)) should be(BigInt(11))
    s2(BigInt(3)) should be(BigInt(13))
    s2(BigInt(4)) should be(BigInt(17))
  }

  "S_2().next() -> S_3" should "have correct head and primes" in {
    val s3 = SieveSequence.S_1().next().next()
    s3.head should be(BigInt(7))
    s3.primes should be(List(BigInt(7), BigInt(5), BigInt(3), BigInt(2)))
    s3.modulus should be(BigInt(30))
    s3.cycle.sum() should be(BigInt(30))
    s3.cycle.size should be(BigInt(8))
  }

  "S_3().apply" should "produce 7, 11, 13, 17, 19, 23, 29, ..." in {
    val s3 = SieveSequence.S_1().next().next()
    s3(BigInt(0)) should be(BigInt(7))
    s3(BigInt(1)) should be(BigInt(11))
    s3(BigInt(2)) should be(BigInt(13))
    s3(BigInt(3)) should be(BigInt(17))
    s3(BigInt(4)) should be(BigInt(19))
  }

//  "S_2().next() -> S_3" should "have correct head and primes" in {
//    val s3 = SieveSequence.S_1().next().next()
//    s3.head should be(BigInt(7))
//    s3.primes should be(List(BigInt(7), BigInt(5), BigInt(3), BigInt(2)))
//    s3.modulus should be(BigInt(30))
//    s3.cycle.sum() should be(BigInt(30))
//    s3.cycle.size should be(BigInt(8))
//  }

//  "S_3().apply" should "produce 7, 11, 13, 17, 19, 23, 29, ..." in {
//    val s3 = SieveSequence.S_1().next().next()
//    s3(BigInt(0)) should be(BigInt(7))
//    s3(BigInt(1)) should be(BigInt(11))
//    s3(BigInt(2)) should be(BigInt(13))
//    s3(BigInt(3)) should be(BigInt(17))
//    s3(BigInt(4)) should be(BigInt(19))
//  }
}
