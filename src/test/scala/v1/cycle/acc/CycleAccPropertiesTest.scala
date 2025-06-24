package v1.cycle.acc

import org.scalatest.flatspec.*
import org.scalatest.funsuite.AnyFunSuiteLike
import org.scalatest.matchers.should.*
import v1.cycle.Cycle
import v1.cycle.integral.CycleIntegral
import v1.tests.ArrayUtils.createListFromInt

import scala.BigInt

class CycleAccPropertiesTest extends FlatSpec with Matchers {

  val primeCycles: List[Cycle] = List(
    Cycle(createListFromInt(Array(3))),
    Cycle(createListFromInt(Array(19))),
    Cycle(createListFromInt(Array(3, 5, 7))),
    Cycle(createListFromInt(Array(3, 5, 7, 11, 13, 17))),
  )

  val oddCycles: List[Cycle] = List(
    Cycle(createListFromInt(Array(3))),
    Cycle(createListFromInt(Array(3, 5, 7))),
    Cycle(createListFromInt(Array(3, 15, 17))),
  )

  val evenCycles: List[Cycle] = List(
    Cycle(createListFromInt(Array(2))),
    Cycle(createListFromInt(Array(2, 4, 8))),
    Cycle(createListFromInt(Array(10, 20, 30))),
  )

  val allCycles: List[Cycle] = primeCycles ++ oddCycles ++ evenCycles

  "assertFirstValuesMatchIntegral" should "hold for any cycle" in {
    assert(
      allCycles.forall { cycle =>
        val cycleAcc = CycleAcc(1000, cycle)
        (BigInt(0) until cycleAcc.cycle.values.size).forall {
          position => {
            val verified = CycleAccProperties.assertFirstValuesMatchIntegral(cycleAcc, position)
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
        val cycleAcc = CycleAcc(1000, cycle)
        (BigInt(0) until cycleAcc.cycle.values.size).forall {
          position => {
            val verified = CycleAccProperties.assertSimplifiedDiffValuesMatchCycle(cycleAcc, position)
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
        val cycleAcc = CycleAcc(1000, cycle)
        val cycleIntegral = CycleIntegral(1000, cycle)
        (BigInt(0) until cycleAcc.cycle.values.size).forall {
          position => {
            val verified = CycleAccProperties.assertCycleAccEqualsCycleIntegral(cycleAcc, cycleIntegral, position)
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
        val cycleAcc = CycleAcc(1000, cycle)
        val cycleIntegral = CycleIntegral(1000, cycle)
        (BigInt(0) until cycleAcc.cycle.values.size).forall {
          position => {
            val verified = CycleAccProperties.assertCycleIntegralMatchCycleAccDef(cycleAcc, cycleIntegral, position)
            assert(verified)
            verified
          }
        }
      }
    )
  }
}