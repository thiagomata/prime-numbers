package v1

import org.scalatest.Inspectors.forAll
import org.scalatest.flatspec.*
import org.scalatest.matchers.should.*
import v1.cycle.Cycle
import v1.tests.ArrayUtils.createList

case class CycleTestCase(
      name: String,
      input: Cycle,
      key: BigInt,
      expected: BigInt
)

class CycleTest extends FlatSpec with Matchers {

  "Cycle checkMod" should "propagate" in {
    val list = createList(Array(BigInt(3)))
    val c: Cycle = Cycle(list)
    val c2 = c.checkMod(BigInt(4))
    val c3 = c2.checkMod(BigInt(5))
    assert(c3.evaluated(4))
    assert(c3.evaluated(5))
  }

  "sum" should "sum values" in {
    val list = createList(Array(BigInt(3),BigInt(4),BigInt(5)))
    val c: Cycle = Cycle(list)
    assert(c.sum() == BigInt(12))
  }

  "Cycle" should "return value" in {
    val list = createList(Array(BigInt(0), BigInt(1), BigInt(2)))
    val testCases = List(
      CycleTestCase(
        "get the first key zero",
        Cycle(list),
        0,
        0
      ),
      CycleTestCase(
        "get the second key one",
        Cycle(list),
        1,
        1
      ),
      CycleTestCase(
        "get the third key two",
        Cycle(list),
        2,
        2
      ),
      CycleTestCase(
        "get a key 4# key in a list of size 3",
        Cycle(list),
        3,
        0
      ),
      CycleTestCase(
        "get a key 10# key in a list of size 3",
        Cycle(list),
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
