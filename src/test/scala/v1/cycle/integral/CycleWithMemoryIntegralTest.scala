package v1.cycle.integral

import org.scalatest.flatspec.*
import org.scalatest.matchers.should.*
import v1.cycle.integral.recursive.CycleIntegral
import v1.cycle.memory.MemCycle
import v1.tests.ArrayUtils.createListFromInt

import scala.BigInt

class CycleWithMemoryIntegralTest extends FlatSpec with Matchers {

  "small values" should "return expected increasing values" in {
    val list = createListFromInt(Array(0, 1, 2))
    val cycle = MemCycle(list)
    val intCycle = CycleIntegral(1000, cycle)
    assert(intCycle.size == 3)
    assert(intCycle.sum == 0 + 1 + 2)
    assert(intCycle(0) == 1000 + 0)
    assert(intCycle(1) == 1000 + 0 + 1)
    assert(intCycle(2) == 1000 + 0 + 1 + 2)
    assert(intCycle(3) == 1000 + 0 + 1 + 2 + 0)
    assert(intCycle(4) == 1000 + 0 + 1 + 2 + 0 + 1)
    assert(intCycle(5) == 1000 + 0 + 1 + 2 + 0 + 1 + 2)
  }

  "big values" should "return expected increasing values" in {
    val list = createListFromInt(Array(1, 10, 100))
    val cycle = MemCycle(list)
    val intCycle = CycleIntegral(1000, cycle)
    assert(intCycle.size == 3)
    assert(intCycle.sum == 1 + 10 + 100)
    assert(intCycle(0) == 1000 + 1)
    assert(intCycle(1) == 1000 + 1 + 10)
    assert(intCycle(2) == 1000 + 1 + 10 + 100)
    assert(intCycle(3) == 1000 + 1 + 10 + 100 + 1)
    assert(intCycle(4) == 1000 + 1 + 10 + 100 + 1 + 10)
    assert(intCycle(5) == 1000 + 1 + 10 + 100 + 1 + 10 + 100)
  }
}
