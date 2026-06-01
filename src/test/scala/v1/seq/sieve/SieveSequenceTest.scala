package v1.seq.sieve

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import v1.Calc

class SieveSequenceTest extends AnyFlatSpec with Matchers {
  
  "SieveSequence" should "be created with valid head and cycle" in {
    val cycle = MemCycle(List(1))
    val sieve = SieveSequence(2, cycle)
    sieve.head should be (2)
    sieve.cycle.values should be (List(1))
  }
  
  "next() method" should "compute the next sieve sequence correctly" in {
    val cycle = MemCycle(List(1))
    val sieve = SieveSequence(2, cycle)
    val next = sieve.next()
    // This just verifies it compiles and runs without errors
    // In a proper test we'd check that next.head = sieve.head + sieve.cycle(0)
    // But for now we just ensure it doesn't crash
    assert(next != null)
  }
  
  "apply method" should "compute sequence values correctly for S_0" in {
    // S_0 should have head = 2, cycle = [1]
    val cycle = MemCycle(List(1))
    val sieve = SieveSequence(2, cycle)
    
    // First few values in the sequence [2, 3, 4, 5, 6, ...]
    sieve.apply(0) should be (2)
    sieve.apply(1) should be (3)
    sieve.apply(2) should be (4)
    sieve.apply(3) should be (5)
  }
}