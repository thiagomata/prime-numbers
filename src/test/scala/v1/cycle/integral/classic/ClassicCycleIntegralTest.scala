package v1.cycle.integral.classic

import org.scalatest.flatspec.FlatSpec
import org.scalatest.matchers.should.Matchers
import v1.chapter4.cycle.integral.classic.ClassicCycleIntegral
import v1.chapter4.cycle.memory.MemCycle
import v1.tests.ArrayUtils.createListFromInt

class ClassicCycleIntegralTest extends FlatSpec with Matchers {

  val primeCycles: List[MemCycle] = List(
    MemCycle(createListFromInt(Array(3))),
    MemCycle(createListFromInt(Array(19))),
    MemCycle(createListFromInt(Array(3, 5, 7))),
    MemCycle(createListFromInt(Array(3, 5, 7, 11, 13, 17))),
  )

  val oddCycles: List[MemCycle] = List(
    MemCycle(createListFromInt(Array(3))),
    MemCycle(createListFromInt(Array(3, 5, 7))),
    MemCycle(createListFromInt(Array(3, 15, 17))),
  )

  val evenCycles: List[MemCycle] = List(
    MemCycle(createListFromInt(Array(2))),
    MemCycle(createListFromInt(Array(2, 4, 8))),
    MemCycle(createListFromInt(Array(10, 20, 30))),
  )

  val allCycles: List[MemCycle] = primeCycles ++ oddCycles ++ evenCycles

  "apply" should "return the correct value for any cycle from 0 to size time 2" in {
    assert(
      allCycles.forall { cycle =>
        val classicCycleIntegral = ClassicCycleIntegral(1000, cycle)
        (BigInt(0) until classicCycleIntegral.cycle.values.size * 2).forall {
          position => {
            val expectedValue = (BigInt(0) to position).map(
              i => cycle(i)
            ).sum + classicCycleIntegral.initialValue
            assert(classicCycleIntegral(position) == expectedValue)
            classicCycleIntegral(position) == expectedValue
          }
        }
      }
    )
  }

  "sum" should "match sum values" in {
    assert(
      allCycles.forall { cycle =>
        cycle.sum() == cycle.values.toScala.sum
      }
    )
  }
}