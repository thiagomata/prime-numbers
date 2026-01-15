package v1.cycle.memory

import org.scalatest.Inspectors.forAll
import org.scalatest.flatspec.*
import org.scalatest.matchers.should.*
import v1.tests.ArrayUtils.createList

case class CycleTestCase(
    name: String,
    input: MemCycle,
    key: BigInt,
    expected: BigInt
)

class MemCycleTest extends FlatSpec with Matchers {

  "Cycle checkMod" should "propagate" in {
    val list = createList(Array(BigInt(3)))
    val c: MemCycle = MemCycle(list)
    val c2 = c.checkMod(BigInt(4))
    val c3 = c2.checkMod(BigInt(5))
    assert(c3.evaluated(4))
    assert(c3.evaluated(5))
  }

  "sum" should "sum values" in {
    val list = createList(Array(BigInt(3),BigInt(4),BigInt(5)))
    val c: MemCycle = MemCycle(list)
    assert(c.sum() == BigInt(12))
  }

  "Cycle" should "return value" in {
    val list = createList(Array(BigInt(0), BigInt(1), BigInt(2)))
    val testCases = List(
      CycleTestCase(
        "get the first key zero",
        MemCycle(list),
        0,
        0
      ),
      CycleTestCase(
        "get the second key one",
        MemCycle(list),
        1,
        1
      ),
      CycleTestCase(
        "get the third key two",
        MemCycle(list),
        2,
        2
      ),
      CycleTestCase(
        "get a key 4# key in a list of size 3",
        MemCycle(list),
        3,
        0
      ),
      CycleTestCase(
        "get a key 10# key in a list of size 3",
        MemCycle(list),
        9,
        0
      ),
    )
    forAll(testCases) { testCase =>
      val result = testCase.input(testCase.key)
      result should be(testCase.expected)
    }
  }
}
