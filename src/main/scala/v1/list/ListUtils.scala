package v1.list

import stainless.collection.List
import stainless.lang.decreases
import v1.list.properties.ListUtilsProperties

object ListUtils {

  def sum(loopList: List[BigInt]): BigInt = {
    if (loopList.isEmpty) {
      BigInt(0)
    } else {
      loopList.head + sum(loopList.tail)
    }
  }

  def slice(list: List[BigInt], from: BigInt, to: BigInt): List[BigInt] = {
    require(from >= 0)
    require(to >= from)
    require(to < list.size)
    decreases(to)

    val current: BigInt = list(to)
    if (from == to) {
      List(current)
    } else {
      val prev = slice(list, from, to - 1)
      ListUtilsProperties.listAddValueTail(prev, current)
      prev ++ List(current)
    }
  }
}
