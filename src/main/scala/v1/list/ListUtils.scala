package v1.list

import stainless.collection.List
import stainless.lang.decreases

import scala.annotation.tailrec

object ListUtils {

  def sum(list: List[BigInt]): BigInt = {

    @tailrec
    def loop(acc: BigInt, currentPos: BigInt): BigInt = {
      require(currentPos >= 0)
      require(currentPos <= list.size)
      decreases(currentPos)

      if (currentPos) == BigInt(0) then acc else loop(acc + list(currentPos - 1), currentPos - 1)
    }

    loop(BigInt(0), list.size)
  }
}
