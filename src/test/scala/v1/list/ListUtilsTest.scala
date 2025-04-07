package v1.list

import org.scalatest.flatspec.*
import org.scalatest.matchers.should.*
import stainless.collection.List
import stainless.proof.check
import v1.list.properties.ListUtilsProperties
import v1.tests.ArrayUtils.{createList, createListFromInt}

import scala.{+:, BigInt}

class ListUtilsTest extends FlatSpec with Matchers {

  "create list from int" should "create list" in {
    val list = createListFromInt(Array(1,2,3))
    val expected = List(BigInt(1),BigInt(2),BigInt(3))
    assert(list == expected)
  }

  "create list" should "create list" in {
    val list = createList(Array(BigInt(1),BigInt(2),BigInt(3)))
    val expected = List(BigInt(1),BigInt(2),BigInt(3))
    assert(list == expected)
  }

  "sum" should "sum values" in {
    val received = ListUtils.sum(
      createListFromInt(Array(1,2,3))
    )
    assert(received == BigInt(6))
  }

  "sum" should "sum values with init value" in {
    val list = createListFromInt(Array(1,2,3))

    val received = ListUtils.sum(
      list :+ 100,
    )
    check(ListUtilsProperties.listSumAddValue(list,BigInt(100)))
    assert(received == BigInt(106))
  }
}
