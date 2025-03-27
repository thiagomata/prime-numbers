package v1.cycle.properties

import stainless.collection.*
import stainless.lang.*
import stainless.proof.check
import v1.Calc
import v1.cycle.Cycle
import v1.div.properties.{AdditionAndMultiplication, ModSmallDividend}

import scala.annotation.tailrec

object CycleProperties {

  def findValueInCycle(cycle: Cycle, key: BigInt): Boolean = {
    require(key >= 0)
    require(cycle.size > 0)
    cycle(key) == cycle.values(Calc.mod(key, cycle.size))
  }.holds

  def smallValueInCycle(cycle: Cycle, key: BigInt): Boolean = {
    require(key >= 0)
    require(key < cycle.size)
    require(cycle.size > 0)
    cycle(key) == cycle.values(key)
  }.holds

  def findValueTimesSizeInCycle(cycle: Cycle, key: BigInt, m: BigInt): Boolean = {
    require(key >= 0)
    require(cycle.size > 0)
    require(m >= 0)
    AdditionAndMultiplication.ATimesBSameMod(key, cycle.size, m)
    cycle(key) == cycle(key + cycle.size * m)
  }.holds

  def moveOneCycle(cycle: Cycle, key: BigInt, m1: BigInt, m2: BigInt): Boolean = {
    require(key >= 0)
    require(cycle.size > 0)
    require(m1 >= 0)
    require(m2 >= 0)
    AdditionAndMultiplication.ATimesBSameMod(key, cycle.size, m1)
    AdditionAndMultiplication.ATimesBSameMod(key, cycle.size, m2)
    check(cycle(key) == cycle(key + cycle.size * m1))
    check(cycle(key) == cycle(key + cycle.size * m2))
    cycle(key + cycle.size * m1) == cycle(key + cycle.size * m2)
  }.holds

  def keyMatchesWithModKey(cycle: Cycle, value: BigInt, key: BigInt): Boolean = {
    require(cycle.size > 0)
    require(key >= 0)
    require(value > 0)
    decreases(key)

    val divKeySize = Calc.div(key, cycle.size)
    val modKeySize = Calc.mod(key, cycle.size)
    check(modKeySize < cycle.size)
    moveOneCycle(cycle, key, divKeySize, 0)
    check(cycle(key) == cycle(modKeySize))
    smallValueInCycle(cycle, modKeySize)
    check(cycle(modKeySize) == cycle.values(modKeySize))
    cycle(key) == cycle.values(modKeySize)
  }.holds

  def propMatchOnValues(cycle: Cycle, value: BigInt): Boolean = {
    require(value > 0)

    @tailrec
    def loop(cycle: Cycle, value: BigInt, key: BigInt): Boolean = {
      require(key >= 0)
      require(key < cycle.values.size)
      require(value > 0)
      decreases(key)

      val matchKey = modIsNotZero(cycle.values(key), value)
      if (key == 0) {
        matchKey
      } else {
        matchKey && loop(cycle = cycle, value = value, key = (key - 1))
      }
    }

    loop(cycle = cycle, value = value, key = ( cycle.values.size - 1 ))
  }

  def modIsNotZero(cycleValue: BigInt, value: BigInt): Boolean = {
    require(value > 0)
    Calc.mod(cycleValue, value) != 0
  }

  def modIsZero(cycleValue: BigInt, value: BigInt): Boolean = {
    require(value != 0)
    Calc.mod(cycleValue, value) == 0
  }

  def propAllCycle(cycle: Cycle, value: BigInt, key: BigInt): Boolean = {
    require(key >= 0)
    require(value > 0)
    require(cycle.size > 0)
    val modKeySize = Calc.mod(key, cycle.size)

    keyMatchesWithModKey(cycle, value, key)
    check(cycle(key) == cycle.values(modKeySize))
    if(modIsNotZero(cycle.values(modKeySize), value)) {
      modIsNotZero(cycle(key), value)
    } else {
      true
    }
  }.holds
}