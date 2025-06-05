package v1.list.properties

import org.scalatest.flatspec.*
import org.scalatest.matchers.should.*
import stainless.collection.List
import v1.list.ListUtils

import scala.BigInt

class SliceEquivalenceLemmasTest extends FlatSpec with Matchers {

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
    assert(SliceEquivalenceLemmas.tailHeadAndIndexRangeSlicesAreEqual(list, 0, list.size - 1))
  }
}