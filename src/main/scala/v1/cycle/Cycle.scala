package v1.cycle

import stainless.collection.List
import stainless.lang.decreases
import stainless.proof.check
import v1.Calc
import v1.cycle.Cycle.{appendForAll, appendForNone, appendForSome}
import v1.list.ListUtils

import scala.annotation.tailrec

case class Cycle private(
  values: List[BigInt],
  modIsZeroForAllValues: List[BigInt] = stainless.collection.List.empty,
  modIsZeroForNoneValues: List[BigInt] = stainless.collection.List.empty,
  modIsZeroForSomeValues: List[BigInt] = stainless.collection.List.empty,
) {
  require(Cycle.isValid(
    values,
    modIsZeroForAllValues,
    modIsZeroForSomeValues,
    modIsZeroForNoneValues
  ))

  private def isValid: Boolean = {
    Cycle.isValid(
      values,
      modIsZeroForAllValues,
      modIsZeroForSomeValues,
      modIsZeroForNoneValues
    )
  }

  def countModZero(dividend: BigInt): BigInt = {
    require(dividend > 0)
    require(this.values.nonEmpty)
    require(Cycle.checkPositiveOrZero(values))
    Cycle.countModZero(this.values, dividend)
  }

  def apply(value: BigInt): BigInt = {
    require(value >= 0)
    val index = Calc.mod(value, values.size)
    check(index >= 0)
    check(index < values.size)
    values(index)
  }

  def size: BigInt = values.size

  def sum(): BigInt = ListUtils.sum(values)

  def checkMod(dividend: BigInt): Cycle = {
    require(dividend > 0)
    check(this.isValid)

    if (this.evaluated(dividend)) {
      this
    } else {
      val totalModZero = Cycle.countModZero(this.values, dividend)

      if (totalModZero == this.values.size) {
        check(this.countModZero(dividend) == this.values.size)
        appendForAll(this, dividend)
      }
      else if (totalModZero == 0) {
        check(this.countModZero(dividend) == 0)
        appendForNone(this, dividend)
      }
      else {
        check(this.countModZero(dividend) != 0)
        check(this.countModZero(dividend) != values.size)
        appendForSome(this, dividend)
      }
    }
  }

  def allModValuesAreZero(dividend: BigInt): Boolean = {
    require(dividend > 0)
    this.countModZero(dividend) == this.values.size
  }

  def noModValuesAreZero(dividend: BigInt): Boolean = {
    require(dividend > 0)
    this.countModZero(dividend) == 0
  }

  def someModValuesAreZero(dividend: BigInt): Boolean = {
    require(dividend > 0)
    this.countModZero(dividend) != 0 &&
      this.countModZero(dividend) != this.values.size
  }

  def evaluated(dividend: BigInt): Boolean = {
    this.modIsZeroForSomeValues.contains(dividend) ||
      this.modIsZeroForAllValues.contains(dividend) ||
      this.modIsZeroForNoneValues.contains(dividend)
  }
}

object Cycle {
  def apply(values: List[BigInt]): Cycle = {
    require(values.nonEmpty)
    require(checkPositiveOrZero(values))
    new Cycle(values)
  }

  def isValid(
               values: List[BigInt],
               modIsZeroForAllValues: List[BigInt],
               modIsZeroForSomeValues: List[BigInt],
               modIsZeroForNoneValues: List[BigInt],
             ): Boolean = {
    values.nonEmpty &&
      Cycle.checkPositiveOrZero(values) &&
      Cycle.checkPositive(modIsZeroForAllValues) &&
      Cycle.checkPositive(modIsZeroForSomeValues) &&
      Cycle.checkPositive(modIsZeroForNoneValues) &&
      Cycle.checkZeroForAll(modIsZeroForAllValues, values) &&
      Cycle.checkZeroForSome(modIsZeroForSomeValues, values) &&
      Cycle.checkZeroForNone(modIsZeroForNoneValues, values)
  }

  def countModZero(values: List[BigInt], dividend: BigInt): BigInt = {
    require(dividend > 0)
    require(values.nonEmpty)
    require(checkPositiveOrZero(values))

    @tailrec
    def loopModCheck(loopList: List[BigInt], totalAcc: BigInt = BigInt(0)): BigInt = {
      decreases(loopList.size)

      if (loopList.isEmpty) {
        return totalAcc
      }
      val current = loopList.head
      val thisValueModsZero = if (Calc.mod(current, dividend) == 0) then BigInt(1) else BigInt(0)
      loopModCheck(loopList.tail, totalAcc + thisValueModsZero)
    }

    loopModCheck(values)
  }

  private def checkZeroForSome(modIsZeroForSomeValues: List[BigInt], values: List[BigInt]): Boolean = {
    require(values.nonEmpty)
    require(checkPositive(modIsZeroForSomeValues))
    require(checkPositiveOrZero(values))

    @tailrec
    def loop(list: List[BigInt]): Boolean = {
      require(checkPositive(list))
      decreases(list.size)
      if (list.isEmpty) return true

      val dividend = list.head
      check(dividend > 0)
      val result = countModZero(values, dividend)
      val valid = (result != values.size && result != 0)
      if (!valid) then false else loop(list.tail)
    }

    loop(modIsZeroForSomeValues)
  }

  private def checkZeroForAll(modIsZeroForAllValues: List[BigInt], values: List[BigInt]): Boolean = {
    require(values.nonEmpty)
    require(checkPositive(modIsZeroForAllValues))
    require(checkPositiveOrZero(values))

    @tailrec
    def loop(list: List[BigInt]): Boolean = {
      decreases(list.size)
      require(checkPositive(list))

      if (list.isEmpty) return true

      val dividend = list.head
      check(dividend > 0)
      val result = countModZero(values, dividend)
      val valid = result == values.size
      if (!valid) then false else loop(list.tail)
    }

    loop(modIsZeroForAllValues)
  }

  private def appendForAll(cycle: Cycle, dividend: BigInt): Cycle = {
    require(dividend > 0)
    require(cycle.isValid)
    require(countModZero(cycle.values, dividend) == cycle.values.size)

    val newList = dividend :: cycle.modIsZeroForAllValues
    check(newList.tail == cycle.modIsZeroForAllValues)
    check(newList.head == dividend)
    check(checkZeroForAll(newList, cycle.values))

    Cycle(
      values = cycle.values,
      modIsZeroForAllValues = newList,
      modIsZeroForNoneValues = cycle.modIsZeroForNoneValues,
      modIsZeroForSomeValues = cycle.modIsZeroForSomeValues,
    )
  }

  private def appendForNone(cycle: Cycle, dividend: BigInt): Cycle = {
    require(dividend > 0)
    require(cycle.isValid)
    require(countModZero(cycle.values, dividend) == 0)

    val newList = dividend :: cycle.modIsZeroForNoneValues
    check(newList.tail == cycle.modIsZeroForNoneValues)
    check(newList.head == dividend)
    check(checkZeroForNone(newList, cycle.values))

    Cycle(
      values = cycle.values,
      modIsZeroForAllValues = cycle.modIsZeroForAllValues,
      modIsZeroForNoneValues = newList,
      modIsZeroForSomeValues = cycle.modIsZeroForSomeValues,
    )
  }

  private def appendForSome(cycle: Cycle, dividend: BigInt): Cycle = {
    require(dividend > 0)
    require(cycle.isValid)
    require(countModZero(cycle.values, dividend) != 0)
    require(countModZero(cycle.values, dividend) != cycle.values.size)

    val newList = dividend :: cycle.modIsZeroForSomeValues
    check(newList.tail == cycle.modIsZeroForSomeValues)
    check(newList.head == dividend)
    check(checkZeroForSome(newList, cycle.values))

    Cycle(
      values = cycle.values,
      modIsZeroForAllValues = cycle.modIsZeroForAllValues,
      modIsZeroForNoneValues = cycle.modIsZeroForNoneValues,
      modIsZeroForSomeValues = newList,
    )
  }

  private def checkZeroForNone(modIsZeroForNoneValues: List[BigInt], values: List[BigInt]): Boolean = {
    require(values.nonEmpty)
    require(checkPositiveOrZero(values))
    require(checkPositive(modIsZeroForNoneValues))

    @tailrec
    def loop(list: List[BigInt]): Boolean = {
      decreases(list.size)
      require(checkPositive(list))
      if (list.isEmpty) return true

      val dividend = list.head
      val result = countModZero(values, dividend)
      val valid = result == 0
      if (!valid) then false else loop(list.tail)
    }

    loop(modIsZeroForNoneValues)
  }

  private def checkPositive(list: List[BigInt]): Boolean = {

    @tailrec
    def loop(listLoop: List[BigInt]): Boolean = {
      decreases(listLoop.size)
      if (listLoop.isEmpty) return true
      val valid = listLoop.head > 0
      if (!valid) false else loop(listLoop.tail)
    }

    loop(list)
  }

  private def checkPositiveOrZero(list: List[BigInt]): Boolean = {

    @tailrec
    def loop(listLoop: List[BigInt]): Boolean = {
      decreases(listLoop.size)
      if (listLoop.isEmpty) return true
      val valid = listLoop.head >= 0
      if (!valid) false else loop(listLoop.tail)
    }

    loop(list)
  }
}