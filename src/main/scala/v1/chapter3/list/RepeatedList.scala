package v1.chapter3.list

import stainless.collection.List
import stainless.lang.*
import v1.chapter2.div.Calc

case class RepeatedList(original: List[BigInt], nTimes: BigInt) {
  require(original.nonEmpty)
  require(nTimes > 0)

  def size: BigInt = original.size * nTimes

  def toValues: List[BigInt] = {
    decreases(nTimes)
    if (nTimes == 1) original
    else original ++ RepeatedList(original, nTimes - 1).toValues
  }

  def apply(index: BigInt): BigInt = {
    require(index >= 0)
    require(index < size)
    original(Calc.mod(index, original.size))
  }
}
