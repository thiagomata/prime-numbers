package v1.cycle.integral.classic.properties

import org.scalatest.flatspec.*
import org.scalatest.matchers.should.*
import v1.cycle.integral.classic.ClassicCycleIntegral
import v1.cycle.memory.MemCycle
import v1.tests.ArrayUtils.createListFromInt

import scala.BigInt

class ClassicCycleIntegralPropertiesTest extends FlatSpec with Matchers {

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

  "assertCycleIntegralEqualsSumFirstPosition" should "hold for any cycle" in {
    assert(
      allCycles.forall { cycle =>
          val cycleAcc =  ClassicCycleIntegral(1000, cycle)
          val verified =  ClassicCycleIntegralProperties.assertCycleIntegralEqualsSumFirstPosition(cycleAcc)
          assert(verified)
          verified
      }
    )
  }

  "assertCycleIntegralEqualsSumSmallPositions" should "hold for any cycle" in {
    assert(
      allCycles.forall { cycle =>
        val cycleAcc =  ClassicCycleIntegral(1000, cycle)
        (BigInt(1) until cycleAcc.cycle.values.size - 1).forall {
          position => {
            val verified =  ClassicCycleIntegralProperties.assertCycleIntegralEqualsSumSmallPositions(cycleAcc, position)
            assert(verified)
            verified
          }
        }
      }
    )
  }

  "assertCycleIntegralEqualsSliceSum" should "hold for any cycle" in {
    assert(
      allCycles.forall { cycle =>
        val cycleAcc =  ClassicCycleIntegral(1000, cycle)
        (BigInt(0) until cycleAcc.cycle.values.size - 1).forall {
          position => {
            val verified =  ClassicCycleIntegralProperties.assertCycleIntegralEqualsSliceSum(cycleAcc, position)
            assert(verified)
            verified
          }
        }
      }
    )
  }

  "assertDiffEqualsCycleValue" should "hold for any cycle" in {
    assert(
      allCycles.forall { cycle =>
        val cycleAcc =  ClassicCycleIntegral(1000, cycle)
        (BigInt(0) until cycleAcc.cycle.values.size * 2).forall {
          position => {
            val verified =  ClassicCycleIntegralProperties.assertDiffEqualsCycleValue(cycleAcc, position)
            assert(verified)
            verified
          }
        }
      }
    )
  }

  "assertSameDiffAfterCycle" should "hold for any cycle" in {
    assert(
      allCycles.forall { cycle =>
        val cycleAcc =  ClassicCycleIntegral(1000, cycle)
        (BigInt(0) until cycleAcc.cycle.values.size * 2).forall {
          position => {
            val verified =  ClassicCycleIntegralProperties.assertSameDiffAfterCycle(cycleAcc, position)
            assert(verified)
            verified
          }
        }
      }
    )
  }

  "assertLastElementBeforeLoop" should "hold for any cycle" in {
    assert(
      allCycles.forall { cycle =>
        val cycleAcc =  ClassicCycleIntegral(1000, cycle)
        val verified =  ClassicCycleIntegralProperties.assertLastElementBeforeLoop(cycleAcc)
        assert(verified)
        verified
      }
    )
  }

  "assertSumModValueAsListEqualsCycleIntegralLoop" should "hold for any cycle" in {
    assert(
      allCycles.forall { cycle =>
        val cycleAcc =  ClassicCycleIntegral(1000, cycle)
        (BigInt(0) until cycleAcc.cycle.values.size * 2).forall {
          position => {
            val verified =  ClassicCycleIntegralProperties.assertSumModValueAsListEqualsCycleIntegralLoop(cycleAcc, position)
            assert(verified)
            verified
          }
        }
      }
    )
  }

  "assertCycleIntegralEqualsSumOfModlValuesAsList" should "hold for any cycle" in {
    assert(
      allCycles.forall { cycle =>
        val cycleAcc =  ClassicCycleIntegral(1000, cycle)
        (BigInt(0) until cycleAcc.cycle.values.size * 2).forall {
          position => {
            val verified =  ClassicCycleIntegralProperties.assertCycleIntegralEqualsSumOfModlValuesAsList(cycleAcc, position)
            assert(verified)
            verified
          }
        }
      }
    )
  }

  "assertFirstValuesAsSliceEqualsModValuesAsList" should "hold for any cycle" in {
    assert(
      allCycles.forall { cycle =>
        val cycleAcc =  ClassicCycleIntegral(1000, cycle)
        (BigInt(1) until cycleAcc.cycle.values.size - 1).forall {
          position => {
            val verified =  ClassicCycleIntegralProperties.assertFirstValuesAsSliceEqualsModValuesAsList(cycleAcc, position)
            assert(verified)
            verified
          }
        }
      }
    )
  }


  //  "assertDiffEqualsCycleValue" should "hold for any cycle" in {
//    assert(
//      allCycles.forall { cycle =>
//        val cycleAcc =  ClassicCycleIntegral(1000, cycle)
//        (BigInt(0) until cycleAcc.cycle.values.size).forall {
//          position => {
//            val verified =  ClassicCycleIntegralProperties.assertDiffEqualsCycleValue(cycleAcc, position)
//            assert(verified)
//            verified
//          }
//        }
//      }
//    )
//  }
//
//  "assertCycleIntegralEqualsSumSmallPositions" should "hold for any cycle" in {
//    assert(
//      allCycles.forall { cycle =>
//        val cycleAcc =  ClassicCycleIntegral(1000, cycle)
//        val cycleIntegral = CycleIntegral(1000, cycle)
//        (BigInt(0) until cycleAcc.mCycle.values.size).forall {
//          position => {
//            val verified =  ClassicCycleIntegralProperties.assertCycleIntegralEqualsSumSmallPositions(cycleAcc, position)
//            assert(verified)
//            verified
//          }
//        }
//      }
//    )
//  }
//
//  "assertCycleIntegralMatchCycleAccDef" should "hold for any cycle" in {
//    assert(
//      allCycles.forall { cycle =>
//        val cycleAcc =  ClassicCycleIntegral(1000, cycle)
//        val cycleIntegral = CycleIntegral(1000, cycle)
//        (BigInt(0) until cycleAcc.mCycle.values.size).forall {
//          position => {
//            val verified =  ClassicCycleIntegralProperties.assertCycleIntegralMatchModCycleDef(cycleAcc, cycleIntegral, position)
//            assert(verified)
//            verified
//          }
//        }
//      }
//    )
//  }
}