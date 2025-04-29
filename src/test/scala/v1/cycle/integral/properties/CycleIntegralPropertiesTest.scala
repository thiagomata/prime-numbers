package v1.cycle.integral.properties

import org.scalatest.flatspec.*
import org.scalatest.matchers.should.*
import v1.cycle.Cycle
import v1.cycle.integral.CycleIntegral
import v1.tests.ArrayUtils.createListFromInt

class CycleIntegralPropertiesTest extends FlatSpec with Matchers {

  "assertCycleIntegralEqualsSumFirstPosition" should "holds for any cycle" in {
    val list = createListFromInt(Array(1, 10, 100))
    val cycle = Cycle(list)
    val intCycle = CycleIntegral(1000, cycle)
    assert(CycleIntegralProperties.assertCycleIntegralEqualsSumFirstPosition(intCycle))
  }

  "assertCycleIntegralEqualsSumSmallPositions" should "holds for small cycle positions bigger than zero" in {
    val list = createListFromInt(Array(1, 10, 100))
    val cycle = Cycle(list)
    val intCycle = CycleIntegral(1000, cycle)
    assert(CycleIntegralProperties.assertCycleIntegralEqualsSumSmallPositions(intCycle, 1))
    assert(CycleIntegralProperties.assertCycleIntegralEqualsSumSmallPositions(intCycle, 2))
  }

  "assertCycleIntegralEqualsSum" should "holds for small cycle positions" in {
    val list = createListFromInt(Array(1, 10, 100))
    val cycle = Cycle(list)
    val intCycle = CycleIntegral(1000, cycle)
    assert(CycleIntegralProperties.assertCycleIntegralEqualsSliceSum(intCycle, 0))
    assert(CycleIntegralProperties.assertCycleIntegralEqualsSliceSum(intCycle, 1))
    assert(CycleIntegralProperties.assertCycleIntegralEqualsSliceSum(intCycle, 2))
  }

  "assertNextPosition" should "holds for any positions bigger than zero" in {
    val list = createListFromInt(Array(1, 10, 100))
    val cycle = Cycle(list)
    val intCycle = CycleIntegral(1000, cycle)
    assert(CycleIntegralProperties.assertNextPosition(intCycle, 1))
    assert(CycleIntegralProperties.assertNextPosition(intCycle, 2))
    assert(CycleIntegralProperties.assertNextPosition(intCycle, 100))
  }

  "assertDiffEqualsCycleValue" should "holds for any positions" in {
    val list = createListFromInt(Array(1, 10, 100))
    val cycle = Cycle(list)
    val intCycle = CycleIntegral(1000, cycle)
    assert(CycleIntegralProperties.assertDiffEqualsCycleValue(intCycle, 0))
    assert(CycleIntegralProperties.assertDiffEqualsCycleValue(intCycle, 1))
    assert(CycleIntegralProperties.assertDiffEqualsCycleValue(intCycle, 2))
    assert(CycleIntegralProperties.assertDiffEqualsCycleValue(intCycle, 100))
  }

  "assertSameDiffAfterCycle" should "holds for any positions" in {
    val list = createListFromInt(Array(1, 10, 100))
    val cycle = Cycle(list)
    val intCycle = CycleIntegral(1000, cycle)
    assert(CycleIntegralProperties.assertSameDiffAfterCycle(intCycle, 0))
    assert(CycleIntegralProperties.assertSameDiffAfterCycle(intCycle, 1))
    assert(CycleIntegralProperties.assertSameDiffAfterCycle(intCycle, 2))
    assert(CycleIntegralProperties.assertSameDiffAfterCycle(intCycle, 100))
  }
}