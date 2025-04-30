package v1.list

import stainless.collection.List
import stainless.lang.decreases

import scala.annotation.tailrec

object ListBuilder {

  def createList(values: Array[BigInt]): List[BigInt] = {

    @tailrec
    def convert(index: Int, acc: List[BigInt]): List[BigInt] = {
      require(index >= 0)
      require(index <= values.length)
      decreases(index)

      if (index == 0 ) {
        acc
      } else {
        convert(
          index - 1,
          List[BigInt](values(index - 1)) ++ acc
        )
      }
    }

    convert(values.length, List[BigInt]())
  }
}

