package v1.cycle.properties

import stainless.collection.*
import stainless.lang.*
import stainless.proof.check
import v1.Calc
import v1.cycle.Cycle
import v1.div.properties.AdditionAndMultiplication

object CycleProperties {
  def findValueInCycle(list: List[BigInt], key: BigInt): Boolean = {
    require(key >= 0)
    require(list.size > 0)
    val cycle = Cycle(list)
    cycle(key) == list(Calc.mod(key, list.size))
  }.holds

  def smallValueInCycle(list: List[BigInt], key: BigInt): Boolean = {
    require(key >= 0)
    require(key < list.size)
    require(list.size > 0)
    val cycle = Cycle(list)
    cycle(key) == list(key)
  }.holds

  def findValueTimesSizeInCycle(list: List[BigInt], key: BigInt, m: BigInt): Boolean = {
    require(key >= 0)
    require(list.size > 0)
    require(m >= 0)
    val cycle = Cycle(list)
    AdditionAndMultiplication.ATimesBSameMod(key, list.size, m)
    cycle(key) == cycle(key + list.size * m)
  }.holds

  def moveOneCycle(list: List[BigInt], key: BigInt, m1: BigInt, m2: BigInt): Boolean = {
    require(key >= 0)
    require(list.size > 0)
    require(m1 >= 0)
    require(m2 >= 0)
    val cycle = Cycle(list)
    AdditionAndMultiplication.ATimesBSameMod(key, list.size, m1)
    AdditionAndMultiplication.ATimesBSameMod(key, list.size, m2)
    check(cycle(key) == cycle(key + list.size * m1))
    check(cycle(key) == cycle(key + list.size * m2))
    cycle(key + list.size * m1) == cycle(key + list.size * m2)
  }.holds
}
