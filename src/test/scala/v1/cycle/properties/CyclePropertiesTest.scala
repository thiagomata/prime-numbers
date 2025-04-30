package v1.cycle.properties

import org.scalatest.flatspec.*
import org.scalatest.matchers.should.*
import v1.cycle.Cycle
import v1.tests.ArrayUtils.createList

import scala.BigInt

class CyclePropertiesTest extends FlatSpec with Matchers {

  "findValueInCycle" should "hold for any values" in {
    val list = createList(Array(BigInt(0), BigInt(1), BigInt(2)))
    val cycle = Cycle(list)
    assert(CycleProperties.findValueInCycle(cycle, BigInt(0)))
    assert(CycleProperties.findValueInCycle(cycle, BigInt(1)))
    assert(CycleProperties.findValueInCycle(cycle, BigInt(2)))
    assert(CycleProperties.findValueInCycle(cycle, BigInt(4)))
    assert(CycleProperties.findValueInCycle(cycle, BigInt(1000)))
  }

  "smallValueInCycle" should "hold for any small values" in {
    val list = createList(Array(BigInt(0), BigInt(1), BigInt(2)))
    val cycle = Cycle(list)
    assert(CycleProperties.smallValueInCycle(cycle, BigInt(0)))
    assert(CycleProperties.smallValueInCycle(cycle, BigInt(1)))
    assert(CycleProperties.smallValueInCycle(cycle, BigInt(2)))
  }

  "valueMatchAfterManyLoops" should "hold for any multiple" in {
    val list = createList(Array(BigInt(0), BigInt(1), BigInt(2)))
    val cycle = Cycle(list)
    assert(CycleProperties.valueMatchAfterManyLoops(cycle, BigInt(1), BigInt(0)))
    assert(CycleProperties.valueMatchAfterManyLoops(cycle, BigInt(1), BigInt(10)))
    assert(CycleProperties.valueMatchAfterManyLoops(cycle, BigInt(1), BigInt(100)))
  }

  "valueMatchAfterManyLoopsInBoth" should "hold for any multiples" in {
    val list = createList(Array(BigInt(0), BigInt(1), BigInt(2)))
    val cycle = Cycle(list)
    assert(CycleProperties.valueMatchAfterManyLoopsInBoth(cycle, BigInt(1), BigInt(0), BigInt(10)))
    assert(CycleProperties.valueMatchAfterManyLoopsInBoth(cycle, BigInt(1), BigInt(10), BigInt(100)))
    assert(CycleProperties.valueMatchAfterManyLoopsInBoth(cycle, BigInt(1), BigInt(100), BigInt(101)))
  }

  "propagateModFromValueToCycle" should "hold" in {
    val list = createList(Array(BigInt(3), BigInt(15), BigInt(20)))
    val cycle = Cycle(list)
    assert(CycleProperties.propagateModFromValueToCycle(cycle, 5, 1))
    assert(CycleProperties.propagateModFromValueToCycle(cycle, 5, 4))
    assert(CycleProperties.propagateModFromValueToCycle(cycle, 5, 400))
    assert(CycleProperties.propagateModFromValueToCycle(cycle, 17, 0))
    assert(CycleProperties.propagateModFromValueToCycle(cycle, 17, 3))
    assert(CycleProperties.propagateModFromValueToCycle(cycle, 17, 300))
  }
}
