package v1.tests

import stainless.annotation.extern

object ArrayUtils {

  @extern
  def createListFromInt(values: Array[Int]): stainless.collection.List[BigInt] = {
    val bigIntList: Array[BigInt] = values.map(v => BigInt(v))
    stainless.collection.List.fromScala(bigIntList.toList)
  }

  @extern
  def createList(values: Array[BigInt]): stainless.collection.List[BigInt] = {
    require(values.length > 0)
    stainless.collection.List.fromScala(values.toList)
  }
}
