package v1.chapter3.list

import stainless.collection.List
import stainless.lang.*
import v1.chapter2.div.Calc
import v1.chapter3.list.ListUtils

case class RepeatedList(original: List[BigInt], nTimes: BigInt) {
  require(original.nonEmpty)
  require(nTimes > 0)

  def size: BigInt = original.size * nTimes

  def apply(index: BigInt): BigInt = {
    require(index >= 0)
    require(index < size)
    original(Calc.mod(index, original.size))
  }.ensuring(result =>
    result == original(Calc.mod(index, original.size)) &&
    (index >= original.size || result == original(index)))

  def toValues: List[BigInt] = {
    decreases(nTimes)
    if (nTimes == 1) original
    else original ++ RepeatedList(original, nTimes - 1).toValues
  }.ensuring(result =>
    result.size == original.size * nTimes &&
    result.nonEmpty)

  def sum: BigInt = {
    ListUtils.sum(toValues)
  }
}
