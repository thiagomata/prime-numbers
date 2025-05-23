package v1

import org.scalatest.Inspectors.forAll
import org.scalatest.flatspec.*
import org.scalatest.matchers.should.*
import v1.cycle.Cycle
import v1.seq.Seq
import v1.tests.ArrayUtils.createList

case class SeqTestCase(
                        name: String,
                        input: Seq,
                        key: BigInt,
                        expected: BigInt
                      )

class SeqTest extends FlatSpec with Matchers {

  "Seq" should "return previous value" in {
    val previous = createList(Array(BigInt(0), BigInt(1), BigInt(2)))
    val loop = Cycle(createList(Array(BigInt(1))))
    val testCases = List(
      SeqTestCase(
        "get the first key zero",
        Seq(previous, loop),
        0,
        0
      ),
      SeqTestCase(
        "get the second key one",
        Seq(previous, loop),
        1,
        1
      ),
      SeqTestCase(
        "get the third key two",
        Seq(previous, loop),
        2,
        2
      ),
    )
    forAll(testCases) { testCase =>
      val result = testCase.input(testCase.key)
      result should be(testCase.expected)
    }
  }

  "Seq" should "return loop value with loop = (1)" in {
    val previous = createList(Array(BigInt(0), BigInt(1), BigInt(2)))
    val loop = Cycle(createList(Array(BigInt(1))))
    val testCases = List(
      SeqTestCase(
        "get a key 4# key = last prev + loop * 1 = 2 + 1 = 3",
        Seq(previous, loop),
        3,
        3
      ),
      SeqTestCase(
        "get a key 10# key in a list of size 3 = 2 + 7 * 1",
        Seq(previous, loop),
        9,
        9
      ),
    )
    forAll(testCases) { testCase =>
      val result = testCase.input(testCase.key)
      result should be(testCase.expected)
    }
  }

  "Seq" should "return the loop value with loop (10,100)" in {
    val previous = createList(Array(BigInt(0), BigInt(1), BigInt(2)))
    val loop = Cycle(createList(Array(BigInt(10),BigInt(100))))
    val testCases = List(
      SeqTestCase(
        "get a key 4# key in a list of size 3: 0 1 2 +10",
        Seq(previous, loop),
        3,
        12
      ),
      SeqTestCase(
        "get a key 10# key in a list of size 3:  0 1 2 +10 +100 +10 +100 +10 +100 +10",
        // 2 +10 +100 +10 +100 +10 +100 +10
        // 2 + (110 * 3) + 10
        Seq(previous, loop),
        9,
        342
      ),
    )
    forAll(testCases) { testCase =>
      val result = testCase.input(testCase.key)
      result should be(testCase.expected)
    }
  }}
