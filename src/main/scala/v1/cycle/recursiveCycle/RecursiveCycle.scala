package v1.cycle.recursiveCycle

import stainless.collection.List
import stainless.lang.decreases
import v1.cycle.CycleUtils

case class RecursiveCycle(values: List[BigInt]) {
  require(values.nonEmpty, "Values list cannot be empty")
  require(CycleUtils.checkPositiveOrZero(values))

  def size: BigInt = values.size

  def apply(key: BigInt): BigInt = {
    decreases(key)
    require(key >= 0)

    if (key < size) {
      values(key)
    } else {
      apply(key - values.size)
    }
  }
}
