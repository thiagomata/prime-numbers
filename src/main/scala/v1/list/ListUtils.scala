package v1.list

import stainless.collection.List
import stainless.lang.decreases
import v1.list.properties.ListUtilsProperties

import scala.annotation.tailrec

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

//  def sum(list: List[BigInt]): BigInt = {
//
//    @tailrec
//    def loop(acc: BigInt, currentPos: BigInt): BigInt = {
//      require(currentPos >= 0)
//      require(currentPos <= list.size)
//      decreases(currentPos)
//
//      if (currentPos) == BigInt(0) then acc else loop(acc + list(currentPos - 1), currentPos - 1)
//    }
//
//    loop(BigInt(0), list.size)
//  }
}
