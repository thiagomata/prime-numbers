package v1.list.integral.properties

import org.scalatest.flatspec.*
import org.scalatest.matchers.should.*
import stainless.collection
import stainless.collection.List
import v1.list.integral
import v1.tests.ArrayUtils.{createList, createListFromInt}

import scala.BigInt

class IntegralPropertiesTest extends FlatSpec with Matchers {

  val manyLists: List[collection.List[BigInt]] = List(
    List[BigInt](),
    createListFromInt(Array(1)),
    createListFromInt(Array(1, 2)),
    createListFromInt(Array(1, 2, 3)),
    createListFromInt(Array(1, 10, 1000)),
    createListFromInt(Array(1, 100, 1000)),
    createListFromInt(Array(10, 100, 1000)),
    createListFromInt(Array(1, 10, 100, 1000))
  )

  "assertAccDifferenceEqualsTailHead" should "hold for all lists" in {
    assert(
      manyLists.forall(
        list => {
          val acc = integral.Integral(list)
          if (list.size > 1) IntegralProperties.assertAccDifferenceEqualsTailHead(acc) else true
        }
      )
    )
  }

  "assertAccDiffMatchesList" should "hold for all lists" in {
    assert(
      manyLists.forall(
        list => {
          val acc = integral.Integral(list)
          (BigInt(0) until list.size - BigInt(1)).forall { position =>
            IntegralProperties.assertAccDiffMatchesList(acc, position)
          }
        }
      )
    )
  }

  "assertAccMatchesApply" should "hold for all lists" in {
    assert(
      manyLists.forall(
        list => {
          val acc = integral.Integral(list)
          (BigInt(0) until list.size).forall { position =>
            IntegralProperties.assertAccMatchesApply(acc, position)
          }
        }
      )
    )
  }

  "assertLastEqualsSum" should "hold for all lists" in {
    assert(
      manyLists.forall(
        list => {
          val acc = integral.Integral(list)
          if (list.isEmpty) true else IntegralProperties.assertLastEqualsSum(acc)
        }
      )
    )
  }

  "assertSizeAccEqualsSizeList" should "hold for all lists" in {
    assert(
      manyLists.forall(
        list => {
          val acc = integral.Integral(list)
          IntegralProperties.assertSizeAccEqualsSizeList(acc.list, acc.init)
        }
      )
    )
  }

  "assertLast" should "hold for all lists" in {
    assert(
      manyLists.forall(
        list => {
          val acc = integral.Integral(list)
          if (list.isEmpty) true else IntegralProperties.assertLast(acc)
        }
      )
    )
  }
}