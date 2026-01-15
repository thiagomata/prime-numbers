package v1.cycle.integral.mod

import org.scalatest.flatspec.*
import org.scalatest.funsuite.AnyFunSuiteLike
import org.scalatest.matchers.should.*
import v1.cycle.integral.mod.{ModCycleIntegral, ModCycleIntegralProperties}
import v1.cycle.integral.recursive.CycleIntegral
import v1.cycle.memory.MemCycle
import v1.tests.ArrayUtils.createListFromInt

import scala.BigInt

class ModCycleIntegralPropertiesTest extends FlatSpec with Matchers {

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

  "assertFirstValuesMatchIntegral" should "hold for any cycle" in {
    assert(
      allCycles.forall { cycle =>
        val cycleAcc = ModCycleIntegral(1000, cycle)
        (BigInt(0) until cycleAcc.mCycle.values.size).forall {
          position => {
            val verified = ModCycleIntegralProperties.assertFirstValuesMatchIntegral(cycleAcc, position)
            assert(verified)
            verified
          }
        }
      }
    )
  }

  "assertSimplifiedDiffValuesMatchCycle" should "hold for any cycle" in {
    assert(
      allCycles.forall { cycle =>
        val cycleAcc = ModCycleIntegral(1000, cycle)
        (BigInt(0) until cycleAcc.mCycle.values.size).forall {
          position => {
            val verified = ModCycleIntegralProperties.assertSimplifiedDiffValuesMatchCycle(cycleAcc, position)
            assert(verified)
            verified
          }
        }
      }
    )
  }

  "assertCycleAccEqualsCycleIntegral" should "hold for any cycle" in {
    assert(
      allCycles.forall { cycle =>
        val cycleAcc = ModCycleIntegral(1000, cycle)
        val cycleIntegral = CycleIntegral(1000, cycle)
        (BigInt(0) until cycleAcc.mCycle.values.size).forall {
          position => {
            val verified = ModCycleIntegralProperties.assertModCycleEqualsCycleIntegral(cycleAcc, cycleIntegral, position)
            assert(verified)
            verified
          }
        }
      }
    )
  }

  "assertCycleIntegralMatchCycleAccDef" should "hold for any cycle" in {
    assert(
      allCycles.forall { cycle =>
        val cycleAcc = ModCycleIntegral(1000, cycle)
        val cycleIntegral = CycleIntegral(1000, cycle)
        (BigInt(0) until cycleAcc.mCycle.values.size).forall {
          position => {
            val verified = ModCycleIntegralProperties.assertCycleIntegralMatchModCycleDef(cycleAcc, cycleIntegral, position)
            assert(verified)
            verified
          }
        }
      }
    )
  }
}