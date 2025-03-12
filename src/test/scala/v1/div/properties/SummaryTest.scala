package v1.div.properties

import org.scalatest.flatspec.FlatSpec
import org.scalatest.matchers.should.Matchers

class SummaryTest extends FlatSpec with Matchers {

  // b cannot be zero since that would be a division by zero
  case class SummaryTestCase(a: BigInt, b: BigInt, c: BigInt, m: BigInt)

  val testCases: List[SummaryTestCase] = List.apply(
    SummaryTestCase(a=BigInt(0),   b=BigInt(1),   c=BigInt(0),    m=BigInt(0)),
    SummaryTestCase(a=BigInt(10),  b=BigInt(2),   c=BigInt(3),    m=BigInt(0)),
    SummaryTestCase(a=BigInt(13),  b=BigInt(2),   c=BigInt(3),    m=BigInt(0)),
    SummaryTestCase(a=BigInt(2),   b=BigInt(13),  c=BigInt(3),    m=BigInt(0)),
    SummaryTestCase(a=BigInt(2),   b=BigInt(13),  c=BigInt(13),   m=BigInt(0)),
    SummaryTestCase(a=BigInt(10),  b=BigInt(2),   c=BigInt(2),    m=BigInt(0)),
    SummaryTestCase(a=BigInt(10),  b=BigInt(2),   c=BigInt(-3),   m=BigInt(0)),
    SummaryTestCase(a=BigInt(10),  b=BigInt(2),   c=BigInt(3),    m=BigInt(7)),
    SummaryTestCase(a=BigInt(10),  b=BigInt(2),   c=BigInt(-13),  m=BigInt(7)),
    SummaryTestCase(a=BigInt(10),  b=BigInt(-2),  c=BigInt(3),    m=BigInt(7)),
    SummaryTestCase(a=BigInt(10),  b=BigInt(-12), c=BigInt(3),    m=BigInt(7)),
    SummaryTestCase(a=BigInt(-10), b=BigInt(-12), c=BigInt(3),    m=BigInt(7)),
    SummaryTestCase(a=BigInt(-10), b=BigInt(-12), c=BigInt(-3),   m=BigInt(7)),
  )

  "Summary" should "hold for any non b zero pair" in {
    assert(testCases.forall(
      testCase => {
        Summary.PropertySummary(
          testCase.a, testCase.b, testCase.c, testCase.m
        )
      })
    )
  }
}
