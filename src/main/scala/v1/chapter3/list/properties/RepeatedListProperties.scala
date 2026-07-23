package v1.chapter3.list.properties

import stainless.collection.List
import stainless.lang.*
import v1.chapter1.verification.Helper.assert
import v1.chapter2.div.Calc
import v1.chapter3.list.RepeatedList
import v1.chapter3.list.ListUtils
import v1.chapter3.list.properties.ListUtilsProperties

object RepeatedListProperties {

  def assertSumBase(
    list: List[BigInt]
  ): Boolean = {
    require(list.nonEmpty)
    RepeatedList(list, 1).sum == ListUtils.sum(list)
  }.holds

  def assertSumStep(
    list: List[BigInt],
    times: BigInt
  ): Boolean = {
    require(list.nonEmpty)
    require(times > 1)
    val current = RepeatedList(list, times)
    val prev = RepeatedList(list, times - 1)
    ListUtils.listCombine(list, prev.toValues)
    current.sum == ListUtils.sum(list) + prev.sum
  }.holds

  def assertSumMultiplier(
    list: List[BigInt],
    times: BigInt
  ): Boolean = {
    require(list.nonEmpty)
    require(times > 0)
    decreases(times)
    val totalSum = ListUtils.sum(list)
    if (times == 1) {
      assertSumBase(list)
    } else {
      assertSumMultiplier(list, times - 1)
      assertSumStep(list, times)
    }
    RepeatedList(list, times).sum == times * totalSum
  }.holds

  def assertElementNotMultiple(
    list: List[BigInt],
    times: BigInt,
    filterValue: BigInt,
    index: BigInt
  ): Boolean = {
    require(list.nonEmpty)
    require(times > 0)
    require(filterValue > 0)
    require(index >= 0)
    require(index < list.size * times)
    require(Calc.mod(list(Calc.mod(index, list.size)), filterValue) != BigInt(0))
    Calc.mod(RepeatedList(list, times).apply(index), filterValue) != BigInt(0)
  }.holds

}
