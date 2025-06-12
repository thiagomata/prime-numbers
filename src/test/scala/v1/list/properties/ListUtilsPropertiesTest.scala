package v1.list.properties

import org.scalatest.flatspec.*
import org.scalatest.matchers.should.*
import stainless.collection.List
import v1.list.ListUtils

import scala.BigInt

class ListUtilsPropertiesTest extends FlatSpec with Matchers {

  val manyLists = List(
    List(BigInt(1)),
    List(BigInt(1), BigInt(2)),
    List(BigInt(1), BigInt(2), BigInt(3)),
    List(BigInt(1), BigInt(10), BigInt(1000)),
    List(BigInt(1), BigInt(100), BigInt(1000)),
    List(BigInt(10), BigInt(100), BigInt(1000)),
    List(BigInt(1), BigInt(10), BigInt(100), BigInt(1000))
  )


  "listSumAddValue" should "hold" in {
    val list = List(BigInt(1), BigInt(10), BigInt(100), BigInt(1000))
    assert(ListUtilsProperties.listSumAddValue(list,list.head))
  }

  "listCombine" should "hold" in {
    assert(
      manyLists.forall(
        listA => manyLists.forall(
          listB => ListUtilsProperties.listCombine(listA, listB)
        )
      )
    )
  }

  "listSwap" should "hold" in {
    assert(
      manyLists.forall(
        listA => manyLists.forall(
          listB => ListUtilsProperties.listSwap(listA, listB)
        )
      )
    )
  }

  "listAddValueTail" should "hold" in {
    assert(
      manyLists.forall(
        list => manyLists.forall(
          value => ListUtilsProperties.listAddValueTail(list, value.head)
        )
      )
    )
  }

  "assertAppendToSlice" should "hold" in {
    assert(
      manyLists.forall(
        list => {
          if (list.size < 2) {
            true
          } else {
            (BigInt(0) until (list.size - BigInt(1))).forall(
              from => {
                (from + 1 until list.size).forall(
                  to => {
                    ListUtilsProperties.assertAppendToSlice(list, from, to)
                  }
                )
              }
            )
          }
        }
      )
    )
  }

  "listSlice remove head" should "hold" in {
    assert(
      manyLists.forall(
        list => {
          if (list.size < 2) {
            true
          } else {
            val from = BigInt(1)
            val to = list.size - 1
            val slice = ListUtils.slice(list, from, to)
            assert(List(list.head) ++ slice == list)
            List(list.head) ++ slice == list
          }
        }
      )
    )
  }

  "listSlice remove last" should "hold" in {
    assert(
      manyLists.forall(
        list => {
          if (list.size < 2) {
            true
          } else {
            val from = BigInt(0)
            val to = list.size - 2
            val slice = ListUtils.slice(list, from, to)
            assert(slice ++ List(list.last) == list)
            slice ++ List(list.last) == list
          }
        }
      )
    )
  }

  "assertTailShiftLeft" should "hold" in {
    assert(
      manyLists.forall(
        list => {
          (BigInt(0) until list.size).forall(
            position => {
              ListUtilsProperties.assertTailShiftLeft(list, position)
            }
          )
        }
      )
    )
  }
}
