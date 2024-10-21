package v1.cycle.properties

import v1.cycle.Cycle
import v1.Calc
import stainless.lang.*
import stainless.proof.check
import stainless.collection.*
import v1.properties.DivModAdditionAndMultiplication

object CycleProperties {
  def findValueInCycle(list: List[BigInt], key: BigInt): Boolean = {
    require(key >= 0)
    require(list.size > 0)
    val cycle = Cycle(list)
    cycle(key) == list(Calc.mod(key, list.size))
  }.holds

  def findValueTimesSizeInCycle(list: List[BigInt], key: BigInt, m: BigInt): Boolean = {
    require(key >= 0)
    require(list.size > 0)
    require(m >= 0)
    val cycle = Cycle(list)
    DivModAdditionAndMultiplication.APlusMultipleTimesBSameMod(key, list.size, m)
    cycle(key) == cycle(key + list.size * m)
  }.holds

  def moveOneCycle(list: List[BigInt], key: BigInt, m1: BigInt, m2: BigInt): Boolean = {
    require(key >= 0)
    require(list.size > 0)
    require(m1 >= 0)
    require(m2 >= 0)
    val cycle = Cycle(list)
    DivModAdditionAndMultiplication.APlusMultipleTimesBSameMod(key, list.size, m1)
    DivModAdditionAndMultiplication.APlusMultipleTimesBSameMod(key, list.size, m2)
    check(cycle(key) == cycle(key + list.size * m1))
    check(cycle(key) == cycle(key + list.size * m2))
    cycle(key + list.size * m1) == cycle(key + list.size * m2)
  }.holds
}
