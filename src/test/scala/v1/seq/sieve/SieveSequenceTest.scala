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

  "S_0().countMultiples" should "count multiples correctly" in {
    val s0 = SieveSequence.S_0()
    s0.countMultiples(BigInt(2), BigInt(0), BigInt(2)) should be(BigInt(1))
    s0.countMultiples(BigInt(2), BigInt(0), BigInt(4)) should be(BigInt(2))
    s0.countMultiples(BigInt(3), BigInt(0), BigInt(3)) should be(BigInt(1))
    s0.countMultiples(BigInt(3), BigInt(0), BigInt(6)) should be(BigInt(2))
    s0.countMultiples(BigInt(3), BigInt(5), BigInt(3)) should be(BigInt(1))
  }
}
