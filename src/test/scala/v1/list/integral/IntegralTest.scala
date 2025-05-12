package v1.list.integral

import org.scalatest.flatspec.*
import org.scalatest.matchers.should.*
import stainless.collection
import stainless.collection.List
import v1.list.integral
import v1.tests.ArrayUtils.{createList, createListFromInt}

import scala.BigInt

class IntegralTest extends FlatSpec with Matchers {

  "Acc" should "holds for any list" in {
    val list = createListFromInt(Array(1, 10, 100))
    val acc = integral.Integral(list)
    assert(acc.acc == createListFromInt(Array(1, 11, 111)))
    assert(acc(0) == 1)
    assert(acc(1) == 11)
    assert(acc(2) == 111)

    val list2 = createListFromInt(Array(1, 20, 300))
    val acc2 = integral.Integral(list2)
    assert(integral.Integral(list2).acc == createListFromInt(Array(1, 21, 321)))
    assert(acc2(0) == 1)
    assert(acc2(1) == 21)
    assert(acc2(2) == 321)
  }

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
          if (list.size > 1) acc.assertAccDifferenceEqualsTailHead else true
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
            acc.assertAccDiffMatchesList(position)
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
            acc.assertAccMatchesApply(position)
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
          if (list.isEmpty) true else acc.assertLastEqualsSum
        }
      )
    )
  }

  "assertSizeAccEqualsSizeList" should "hold for all lists" in {
    assert(
      manyLists.forall(
        list => {
          val acc = integral.Integral(list)
          acc.assertSizeAccEqualsSizeList(acc.list, acc.init)
        }
      )
    )
  }

  "isEmpty" should "be false for all lists" in {
    assert(
      manyLists.forall(
        list => {
          val acc = integral.Integral(list)
          acc.isEmpty == list.isEmpty
        }
      )
    )
  }

  "nonEmpty" should "be true for all lists" in {
    assert(
      manyLists.forall(
        list => {
          val acc = integral.Integral(list)
          acc.nonEmpty == list.nonEmpty
        }
      )
    )
  }

  "assertLast" should "hold for all lists" in {
    assert(
      manyLists.forall(
        list => {
          val acc = integral.Integral(list)
          if (list.isEmpty) true else acc.assertLast
        }
      )
    )
  }
}