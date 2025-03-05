package v1

import v1.div.DivMod

import org.scalatest.Inspectors.forAll
import org.scalatest.flatspec.*
import org.scalatest.matchers.should.*

case class SolveTestCase(
                          name: String,
                          input: DivMod,
                          expected: DivMod
)

class DivTest extends FlatSpec with Matchers {

  "Div" should "solve" in {
    val testCases = List(
      SolveTestCase(
        "simple",
        DivMod(10,2,0,10),
        DivMod(10,2,5,0),
      ),
      SolveTestCase(
        "with remainder",
        DivMod(10,3,0,10),
        DivMod(10,3,3,1),
      ),
      SolveTestCase(
        "tirival negative",
        DivMod(-10,-10,0,-10),
        DivMod(-10,-10,1,0),
      ),
    )
    forAll(testCases) { testCase =>
      val result = testCase.input.solve
      result should be (testCase.expected)
    }
  }
}
