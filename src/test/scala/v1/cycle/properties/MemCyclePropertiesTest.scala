package v1.cycle.properties

import org.scalatest.flatspec.*
import org.scalatest.matchers.should.*
import v1.cycle.memory.MemCycle
import v1.cycle.memory.properties.MemCycleProperties
import v1.tests.ArrayUtils.createList

import scala.BigInt

class MemCyclePropertiesTest extends FlatSpec with Matchers {

  "findValueInCycle" should "hold for any values" in {
    val list = createList(Array(BigInt(0), BigInt(1), BigInt(2)))
    val cycle = MemCycle(list)
    assert(MemCycleProperties.findValueInCycle(cycle, BigInt(0)))
    assert(MemCycleProperties.findValueInCycle(cycle, BigInt(1)))
    assert(MemCycleProperties.findValueInCycle(cycle, BigInt(2)))
    assert(MemCycleProperties.findValueInCycle(cycle, BigInt(4)))
    assert(MemCycleProperties.findValueInCycle(cycle, BigInt(1000)))
  }

  "smallValueInCycle" should "hold for any small values" in {
    val list = createList(Array(BigInt(0), BigInt(1), BigInt(2)))
    val cycle = MemCycle(list)
    assert(MemCycleProperties.smallValueInCycle(cycle, BigInt(0)))
    assert(MemCycleProperties.smallValueInCycle(cycle, BigInt(1)))
    assert(MemCycleProperties.smallValueInCycle(cycle, BigInt(2)))
  }

  "valueMatchAfterManyLoops" should "hold for any multiple" in {
    val list = createList(Array(BigInt(0), BigInt(1), BigInt(2)))
    val cycle = MemCycle(list)
    assert(MemCycleProperties.valueMatchAfterManyLoops(cycle, BigInt(1), BigInt(0)))
    assert(MemCycleProperties.valueMatchAfterManyLoops(cycle, BigInt(1), BigInt(10)))
    assert(MemCycleProperties.valueMatchAfterManyLoops(cycle, BigInt(1), BigInt(100)))
  }

  "valueMatchAfterManyLoopsInBoth" should "hold for any multiples" in {
    val list = createList(Array(BigInt(0), BigInt(1), BigInt(2)))
    val cycle = MemCycle(list)
    assert(MemCycleProperties.valueMatchAfterManyLoopsInBoth(cycle, BigInt(1), BigInt(0), BigInt(10)))
    assert(MemCycleProperties.valueMatchAfterManyLoopsInBoth(cycle, BigInt(1), BigInt(10), BigInt(100)))
    assert(MemCycleProperties.valueMatchAfterManyLoopsInBoth(cycle, BigInt(1), BigInt(100), BigInt(101)))
  }

  "propagateModFromValueToCycle" should "hold" in {
    val list = createList(Array(BigInt(3), BigInt(15), BigInt(20)))
    val cycle = MemCycle(list)
    assert(MemCycleProperties.propagateModFromValueToCycle(cycle, 5, 1))
    assert(MemCycleProperties.propagateModFromValueToCycle(cycle, 5, 4))
    assert(MemCycleProperties.propagateModFromValueToCycle(cycle, 5, 400))
    assert(MemCycleProperties.propagateModFromValueToCycle(cycle, 17, 0))
    assert(MemCycleProperties.propagateModFromValueToCycle(cycle, 17, 3))
    assert(MemCycleProperties.propagateModFromValueToCycle(cycle, 17, 300))
  }

  "assertCycleOfPosEqualsCycleOfModPos" should "hold" in {
    val list = createList(Array(BigInt(3), BigInt(15), BigInt(20)))
    val cycle = MemCycle(list)
    assert(MemCycleProperties.assertCycleOfPosEqualsCycleOfModPos(cycle, 5))
    assert(MemCycleProperties.assertCycleOfPosEqualsCycleOfModPos(cycle, 4))
    assert(MemCycleProperties.assertCycleOfPosEqualsCycleOfModPos(cycle, 400))
    assert(MemCycleProperties.assertCycleOfPosEqualsCycleOfModPos(cycle, 17))
    assert(MemCycleProperties.assertCycleOfPosEqualsCycleOfModPos(cycle, 3))
    assert(MemCycleProperties.assertCycleOfPosEqualsCycleOfModPos(cycle, 300))
  }
}
