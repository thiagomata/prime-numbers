package v1.cycle.integral

import org.scalatest.flatspec.*
import org.scalatest.funsuite.AnyFunSuiteLike
import org.scalatest.matchers.should.*
import v1.cycle.integral.mod.ModCycleIntegral
import v1.cycle.integral.recursive.CycleIntegral
import v1.cycle.memory.MemCycle
import v1.tests.ArrayUtils.createListFromInt

import scala.BigInt

class IntegralCycleTest extends FlatSpec with Matchers {

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

  "apply" should "return the correct value for any cycle" in {
    assert(
      allCycles.forall { loopCycle =>
        val cycleIntegral = CycleIntegral(1000, loopCycle)
        (BigInt(1) until cycleIntegral.cycle.values.size).forall {
          position => {
            val expectedValue = (BigInt(0) to position).map(
              i => loopCycle(i)
            ).sum + cycleIntegral.initialValue
            assert(cycleIntegral(position) == expectedValue)
            cycleIntegral(position) == expectedValue
          }
        }
      }
    )
  }
}