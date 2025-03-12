package v1.cycle.properties

import org.scalatest.flatspec.*
import org.scalatest.matchers.should.*
import v1.utils.createList

import scala.BigInt

class CyclePropertiesTest extends FlatSpec with Matchers {

  "findValueInCycle" should "hold for any values" in {
    val list = createList(Array(BigInt(0), BigInt(1), BigInt(2)))
    assert(CycleProperties.findValueInCycle(list, BigInt(0)))
    assert(CycleProperties.findValueInCycle(list, BigInt(1)))
    assert(CycleProperties.findValueInCycle(list, BigInt(2)))
    assert(CycleProperties.findValueInCycle(list, BigInt(4)))
    assert(CycleProperties.findValueInCycle(list, BigInt(1000)))
  }

  "smallValueInCycle" should "hold for any small values" in {
    val list = createList(Array(BigInt(0), BigInt(1), BigInt(2)))
    assert(CycleProperties.smallValueInCycle(list, BigInt(0)))
    assert(CycleProperties.smallValueInCycle(list, BigInt(1)))
    assert(CycleProperties.smallValueInCycle(list, BigInt(2)))
  }

  "findValueTimesSizeInCycle" should "hold for any multiple" in {
    val list = createList(Array(BigInt(0), BigInt(1), BigInt(2)))
    assert(CycleProperties.findValueTimesSizeInCycle(list, BigInt(1), BigInt(0)))
    assert(CycleProperties.findValueTimesSizeInCycle(list, BigInt(1), BigInt(10)))
    assert(CycleProperties.findValueTimesSizeInCycle(list, BigInt(1), BigInt(100)))
  }

  "moveOneCycle" should "hold for any multiples" in {
    val list = createList(Array(BigInt(0), BigInt(1), BigInt(2)))
    assert(CycleProperties.moveOneCycle(list, BigInt(1), BigInt(0), BigInt(10)))
    assert(CycleProperties.moveOneCycle(list, BigInt(1), BigInt(10), BigInt(100)))
    assert(CycleProperties.moveOneCycle(list, BigInt(1), BigInt(100), BigInt(101)))
  }
}
