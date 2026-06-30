package v1.chapter3.list.properties

import stainless.collection.List
import stainless.lang.*
import v1.chapter1.verification.Helper.assert
import v1.chapter2.div.Calc
import v1.chapter2.div.properties.AdditionAndMultiplication
import v1.chapter3.list.ListBoundUtils
import v1.chapter3.list.ListUtils
import v1.chapter3.list.properties.ListUtilsProperties

object ListRepeatProperties {

  def repeat(list: List[BigInt], times: BigInt): List[BigInt] = {
    require(times >= 0)
    decreases(times)
    if (times == 0) List.empty[BigInt]
    else list ++ repeat(list, times - 1)
  }

  def repeatedApplyAt(
    list: List[BigInt],
    times: BigInt,
    index: BigInt
  ): BigInt = {
    require(list.nonEmpty)
    require(times > 0)
    require(index >= 0)
    require(index < list.size * times)
    list(Calc.mod(index, list.size))
  }

  def assertModStableUnderSize(
    index: BigInt,
    size: BigInt
  ): Boolean = {
    require(size > 0)
    require(index >= size)
    AdditionAndMultiplication.APlusBSameModPlusDiv(
      index - size, size)
    Calc.mod(index - size, size) == Calc.mod(index, size)
  }.holds

  def assertRepeatSumMultiplier(
    list: List[BigInt],
    times: BigInt
  ): Boolean = {
    require(times >= 0)
    decreases(times)
    val totalSum = ListUtils.sum(list)
    if (times == 0) {
      assert(ListUtils.sum(repeat(list, 0)) == BigInt(0))
    } else {
      assertRepeatSumMultiplier(list, times - 1)
      ListUtils.listCombine(list, repeat(list, times - 1))
      assert(ListUtils.sum(repeat(list, times)) ==
        totalSum + ListUtils.sum(repeat(list, times - 1)))
      assert(ListUtils.sum(repeat(list, times - 1)) ==
        (times - 1) * totalSum)
    }
    ListUtils.sum(repeat(list, times)) == times * totalSum
  }.holds

  def assertConcatAccessLeft[T](
    listA: List[T],
    listB: List[T],
    index: BigInt
  ): Boolean = {
    require(listA.nonEmpty)
    require(index >= 0)
    require(index < listA.size)
    decreases(index)
    if (index == 0) true
    else {
      assertConcatAccessLeft(listA.tail, listB, index - 1)
    }
    (listA ++ listB)(index) == listA(index)
  }.holds

  def assertConcatAccessRight[T](
    listA: List[T],
    listB: List[T],
    index: BigInt
  ): Boolean = {
    require(index >= listA.size)
    require(index < listA.size + listB.size)
    if (listA.isEmpty) true
    else if (index == 0 && listA.size == 1) {
      assert((listA ++ listB)(0) == listA(0))
    } else if (index < listA.size) true
    else if (listA.tail.isEmpty) {
      assert(listA.size == 1)
      assert((listA ++ listB)(index) == listB(index - 1))
    } else {
      assertConcatAccessRight(listA.tail, listB, index - 1)
    }
    (listA ++ listB)(index) == listB(index - listA.size)
  }.holds

  def assertRepeatSize(
    list: List[BigInt],
    times: BigInt
  ): Boolean = {
    require(times >= 0)
    decreases(times)
    if (times == 0) {
      assert(repeat(list, 0).size == 0)
    } else {
      assertRepeatSize(list, times - 1)
      assert(repeat(list, times).size ==
        list.size + repeat(list, times - 1).size)
    }
    repeat(list, times).size == list.size * times
  }.holds

  /**
   * Repeating a list preserves a strict lower bound on every element.
   *
   * This is the constructor bridge for repeated gap cycles: if one period of
   * gaps is positive, then any positive number of repeated periods is still
   * positive element-by-element.
   */
  def assertRepeatAllGreaterThan(
    list: List[BigInt],
    times: BigInt,
    value: BigInt
  ): Boolean = {
    require(times >= 0)
    require(ListBoundUtils.allGreaterThan(list, value))
    decreases(times)
    if (times == 0) {
      ListBoundUtils.allGreaterThan(repeat(list, times), value)
    } else {
      assertRepeatAllGreaterThan(list, times - 1, value)
      assert(ListBoundUtils.allGreaterThan(repeat(list, times - 1), value))
      assert(ListBoundUtils.assertAppendGreaterThan(
        list,
        repeat(list, times - 1),
        value
      ))
      ListBoundUtils.allGreaterThan(repeat(list, times), value)
    }
  }.holds

  def assertRepeatConcat(
    list: List[BigInt],
    times: BigInt
  ): Boolean = {
    require(times > 0)
    decreases(times)
    if (times == 1) {
      assert(repeat(list, 1) == list)
    } else {
      assertRepeatConcat(list, times - 1)
    }
    repeat(list, times) == list ++ repeat(list, times - 1)
  }.holds

  def assertRepeatSumDecomposition(
    list: List[BigInt],
    times: BigInt
  ): Boolean = {
    require(list.nonEmpty)
    require(times > 0)
    decreases(times)
    val listSum = ListUtils.sum(list)
    if (times == 1) {
      assert(repeat(list, 1) == list)
      assert(ListUtils.sum(repeat(list, 1)) == listSum)
    } else {
      assertRepeatSumDecomposition(list, times - 1)
      ListUtils.listCombine(list, repeat(list, times - 1))
      assert(ListUtils.sum(repeat(list, times)) ==
        listSum + ListUtils.sum(repeat(list, times - 1)))
    }
    ListUtils.sum(repeat(list, times)) == listSum + ListUtils.sum(repeat(list, times - 1))
  }.holds

  def assertRepeatSumTimes(
    list: List[BigInt],
    times: BigInt
  ): Boolean = {
    require(times >= 0)
    assertRepeatSumMultiplier(list, times)
    ListUtils.sum(repeat(list, times)) == ListUtils.sum(list) * times
  }.holds

  def assertRepeatedIndex(
    list: List[BigInt],
    times: BigInt,
    index: BigInt
  ): Boolean = {
    require(list.nonEmpty)
    require(times > 0)
    require(index >= 0)
    require(index < list.size * times)
    decreases(times)
    val size = list.size
    if (times == 1) {
      assert(repeat(list, 1) == list)
      assert(index < size)
      assert(Calc.mod(index, size) == index)
    } else if (index < size) {
      assertConcatAccessLeft(list, repeat(list, times - 1), index)
      assert((list ++ repeat(list, times - 1))(index) == list(index))
      assert(repeat(list, times)(index) == list(index))
      assert(list(index) == list(Calc.mod(index, size)))
    } else {
      assert(index >= size)
      assertRepeatSize(list, times - 1)
      assert(repeat(list, times - 1).size == size * (times - 1))
      assertConcatAccessRight(list, repeat(list, times - 1), index)
      assert((list ++ repeat(list, times - 1))(index) ==
        repeat(list, times - 1)(index - size))
      assert(repeat(list, times)(index) ==
        repeat(list, times - 1)(index - size))
      assertRepeatedIndex(list, times - 1, index - size)
      assertModStableUnderSize(index, size)
    }
    repeat(list, times)(index) == list(Calc.mod(index, size))
  }.holds

  def sumAfterMerge(
    values: List[BigInt],
    mergeIndex: BigInt
  ): BigInt = {
    require(values.nonEmpty)
    require(mergeIndex >= 0)
    require(mergeIndex + 1 < values.size)
    decreases(mergeIndex)
    if (mergeIndex == 0) {
      (values.head + values.tail.head) +
        ListUtils.sum(values.tail.tail)
    } else {
      values.head +
        sumAfterMerge(values.tail, mergeIndex - 1)
    }
  }

  def assertMergePreservesListSum(
    values: List[BigInt],
    mergeIndex: BigInt
  ): Boolean = {
    require(values.nonEmpty)
    require(mergeIndex >= 0)
    require(mergeIndex + 1 < values.size)
    decreases(mergeIndex)
    if (mergeIndex == 0) {
      assert(ListUtils.sum(values) ==
        values.head + values.tail.head +
          ListUtils.sum(values.tail.tail))
    } else {
      assertMergePreservesListSum(values.tail, mergeIndex - 1)
      assert(ListUtils.sum(values.tail) ==
        sumAfterMerge(values.tail, mergeIndex - 1))
    }
    ListUtils.sum(values) == sumAfterMerge(values, mergeIndex)
  }.holds

  def assertMergeSumBase(
    oldValues: List[BigInt],
    newValues: List[BigInt]
  ): Boolean = {
    require(oldValues.size >= 2)
    require(newValues.size == oldValues.size - 1)
    require(newValues.head == oldValues.head + oldValues.tail.head)
    require(ListUtils.sum(newValues.tail) ==
      ListUtils.sum(oldValues.tail.tail))
    ListUtils.sum(newValues) == ListUtils.sum(oldValues)
  }.holds

  def assertMergeSumStep(
    oldValues: List[BigInt],
    newValues: List[BigInt]
  ): Boolean = {
    require(oldValues.nonEmpty)
    require(newValues.nonEmpty)
    require(oldValues.head == newValues.head)
    require(ListUtils.sum(newValues.tail) ==
      ListUtils.sum(oldValues.tail))
    ListUtils.sum(newValues) == ListUtils.sum(oldValues)
  }.holds

  /**
   * Bridge lemma (Approach 1 decomposition): if `newValues` is pointwise-equal
   * to `sumAfterMerge`'s recursive shape (the predicate mirrors `sumAfterMerge`
   * element-for-element), then `sum(newValues) == sumAfterMerge(oldValues, mergeIndex)`.
   *
   * This avoids the failed `assertMergeSumPreserved` induction by replacing
   * "prove sum(newValues) == sum(oldValues) recursively" with "prove newValues
   * matches the constructed sumAfterMerge shape," which is structural rather
   * than arithmetic and should compose cleanly.
   *
   * @param oldValues  the original values list
   * @param newValues  the merged values list
   * @param mergeIndex the merge point
   * @return `sum(newValues) == sumAfterMerge(oldValues, mergeIndex)`
   */
  def newValuesAfterMerge(
    oldValues: List[BigInt],
    newValues: List[BigInt],
    mergeIndex: BigInt
  ): Boolean = {
    require(oldValues.nonEmpty)
    require(mergeIndex >= 0)
    require(mergeIndex + 1 < oldValues.size)
    require(newValues.size == oldValues.size - 1)
    decreases(mergeIndex)
    if (mergeIndex == 0) {
      newValues.head == oldValues.head + oldValues.tail.head &&
        newValues.tail == oldValues.tail.tail
    } else {
      newValues.head == oldValues.head &&
        newValuesAfterMerge(
          oldValues.tail, newValues.tail, mergeIndex - 1)
    }
  }

  def assertSumNewValuesAfterMerge(
    oldValues: List[BigInt],
    newValues: List[BigInt],
    mergeIndex: BigInt
  ): Boolean = {
    require(oldValues.nonEmpty)
    require(mergeIndex >= 0)
    require(mergeIndex + 1 < oldValues.size)
    require(newValues.size == oldValues.size - 1)
    require(newValuesAfterMerge(oldValues, newValues, mergeIndex))
    decreases(mergeIndex)
    if (mergeIndex == 0) {
      assert(newValues.head == oldValues.head + oldValues.tail.head)
      assert(newValues.tail == oldValues.tail.tail)
      ListUtils.listCombine(newValues.head :: newValues.tail, List.empty[BigInt])
    } else {
      assertSumNewValuesAfterMerge(
        oldValues.tail, newValues.tail, mergeIndex - 1)
      assert(newValues.head == oldValues.head)
    }
    ListUtils.sum(newValues) == sumAfterMerge(oldValues, mergeIndex)
  }.holds

  /**
   * GAP 2 closure (Approach 1): merging two consecutive values preserves
   * the total list sum.
   *
   * Composes two verified lemmas:
   *  1. `assertSumNewValuesAfterMerge`: `sum(newValues) == sumAfterMerge(oldValues, mergeIndex)`
   *  2. `assertMergePreservesListSum`:  `sumAfterMerge(oldValues, mergeIndex) == sum(oldValues)`
   *
   * Replaces the failed direct induction `assertMergeSumPreserved`. The
   * decomposition works because `sumAfterMerge` is defined recursively with
   * the same structure as the merged list, so relating `newValues` to it is
   * structural (predicate match) rather than arithmetic.
   *
   * @param oldValues  the original values list
   * @param newValues  the merged values list (matches newValuesAfterMerge)
   * @param mergeIndex the merge point
   * @return `sum(newValues) == sum(oldValues)`
   */
  def assertMergeSumPreserved(
    oldValues: List[BigInt],
    newValues: List[BigInt],
    mergeIndex: BigInt
  ): Boolean = {
    require(oldValues.nonEmpty)
    require(mergeIndex >= 0)
    require(mergeIndex + 1 < oldValues.size)
    require(newValues.size == oldValues.size - 1)
    require(newValuesAfterMerge(oldValues, newValues, mergeIndex))

    assert(assertSumNewValuesAfterMerge(oldValues, newValues, mergeIndex))
    assert(assertMergePreservesListSum(oldValues, mergeIndex))

    ListUtils.sum(newValues) == ListUtils.sum(oldValues)
  }.holds

}
