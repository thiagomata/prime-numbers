package v1.cycle

import stainless.proof.check
import stainless.collection.List
import stainless.lang.decreases
import v1.Calc
import v1.cycle.Cycle.{appendForAll, appendForNone, appendForSome, checkZeroForAll, checkZeroForNone, checkZeroForSome, countModZero}

import scala.annotation.tailrec

case class Cycle private(
  values: List[BigInt],
  modIsZeroForAllValues: List[BigInt] = stainless.collection.List.empty,
  modIsZeroForNoneValues: List[BigInt] = stainless.collection.List.empty,
  modIsZeroForSomeValues: List[BigInt] = stainless.collection.List.empty,
) {
  require(values.nonEmpty)
  require(Cycle.checkPositive(values))
  require(Cycle.checkPositive(modIsZeroForAllValues))
  require(Cycle.checkZeroForAll(modIsZeroForAllValues, values))
  require(Cycle.checkPositive(modIsZeroForSomeValues))
  require(Cycle.checkZeroForSome(modIsZeroForSomeValues, values))
  require(Cycle.checkPositive(modIsZeroForNoneValues))
  require(Cycle.checkZeroForNone(modIsZeroForNoneValues, values))

  def apply(value: BigInt): BigInt = {
    require(value >= 0)
    val index = Calc.mod(value, values.size)
    check(index >= 0)
    check(index < values.size)
    values(index)
  }
  
  def size: BigInt = values.size

  def checkMod(dividend: BigInt): Cycle = {
    require(dividend > 0)
    check(Cycle.checkZeroForAll(modIsZeroForAllValues, values))
    check(Cycle.checkZeroForSome(modIsZeroForSomeValues, values))
    check(Cycle.checkZeroForNone(modIsZeroForNoneValues, values))

    if (this.evaluated(dividend)) {
      this
    } else {
      val totalModZero = Cycle.countModZero(this.values, dividend)

      if (totalModZero == this.values.size) {
        check(countModZero(values,dividend) == this.values.size)
        check(checkZeroForAll(this.modIsZeroForAllValues, values))
        check(values.nonEmpty)
        check(dividend > 0)
        check(Cycle.checkPositive(this.modIsZeroForAllValues))
        check(Cycle.checkZeroForAll(this.modIsZeroForAllValues, values))
        check(Cycle.countModZero(values, dividend) == values.size)

        val newModIsZeroForAll = appendForAll(this.modIsZeroForAllValues,dividend, values)
        Cycle(
          values = this.values,
          modIsZeroForAllValues = newModIsZeroForAll,
          modIsZeroForNoneValues = this.modIsZeroForNoneValues,
          modIsZeroForSomeValues = this.modIsZeroForSomeValues,
        )
      }
      else if (totalModZero == 0) {

        check(countModZero(values,dividend) == 0)
        check(checkZeroForNone(this.modIsZeroForNoneValues, values))
        check(values.nonEmpty)
        check(dividend > 0)
        check(Cycle.checkPositive(this.modIsZeroForNoneValues))
        check(Cycle.checkZeroForNone(this.modIsZeroForNoneValues, values))
        check(Cycle.countModZero(values, dividend) == 0)

        val newModIsZeroForNone = appendForNone(this.modIsZeroForNoneValues,dividend, values)
        Cycle(
          values = this.values,
          modIsZeroForAllValues = this.modIsZeroForAllValues,
          modIsZeroForNoneValues = newModIsZeroForNone,
          modIsZeroForSomeValues = this.modIsZeroForSomeValues,
        )
      }
      else {
        check(countModZero(values,dividend) != 0)
        check(countModZero(values,dividend) != values.size)
        check(checkZeroForSome(this.modIsZeroForSomeValues, values))
        val newModIsZeroForSome = appendForSome(this.modIsZeroForSomeValues,dividend, values)
        Cycle(
          values = this.values,
          modIsZeroForAllValues = this.modIsZeroForAllValues,
          modIsZeroForNoneValues = this.modIsZeroForNoneValues,
          modIsZeroForSomeValues = newModIsZeroForSome,
        )
      }
    }
  }

  def evaluated(dividend: BigInt): Boolean = {
    this.modIsZeroForSomeValues.contains(dividend)  ||
      this.modIsZeroForAllValues.contains(dividend) ||
      this.modIsZeroForNoneValues.contains(dividend)
  }
}

object Cycle {
  def apply(values: List[BigInt] ): Cycle = {
    require(values.nonEmpty)
    require(checkPositive(values))
    new Cycle(values)
  }

  def countModZero(values: List[BigInt], dividend: BigInt): BigInt = {
    require(dividend > 0)
    require(values.nonEmpty)
    require(checkPositive(values))

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

//  private def checkZeroForSome(modIsZeroForSomeValues: List[BigInt], values: List[BigInt]): Boolean = {
//    require(values.nonEmpty)
//    modIsZeroForSomeValues.forall(
//      dividend => {
//        val totalModZero = countModZero(values, dividend)
//        totalModZero > 0 &&
//          totalModZero < values.size
//      }
//    )
//  }

  private def checkZeroForSome(modIsZeroForSomeValues: List[BigInt], values: List[BigInt]): Boolean = {
    require(values.nonEmpty)
    require(checkPositive(modIsZeroForSomeValues))
    require(checkPositive(values))

    @tailrec
    def loop(list: List[BigInt]): Boolean = {
      require(checkPositive(list))
      decreases(list.size)
      if (list.isEmpty) return true

      val dividend = list.head
      check(dividend > 0)
      val result = countModZero(values, dividend)
      val valid = (result != values.size && result != 0)
      if( !valid ) then false else loop(list.tail)
    }
    loop(modIsZeroForSomeValues)
  }

  private def checkZeroForAll(modIsZeroForAllValues: List[BigInt], values: List[BigInt]): Boolean = {
    require(values.nonEmpty)
    require(checkPositive(modIsZeroForAllValues))
    require(checkPositive(values))


    @tailrec
    def loop(list: List[BigInt]): Boolean = {
      decreases(list.size)
      require(checkPositive(list))

      if (list.isEmpty) return true

      val dividend = list.head
      check(dividend > 0)
      val result = countModZero(values, dividend)
      val valid = result == values.size
      if( !valid ) then false else loop(list.tail)
    }
    loop(modIsZeroForAllValues)
  }

  private def appendForAll(previousMods: List[BigInt], dividend: BigInt, values: List[BigInt] ): List[BigInt] = {
    require(dividend > 0)
    require(values.nonEmpty)
    require(checkPositive(values))
    require(checkPositive(previousMods))
    require(checkZeroForAll(previousMods, values))
    require(countModZero(values,dividend) == values.size)
    val newList = dividend :: previousMods
    check(newList.tail == previousMods)
    check(newList.head == dividend)
    check(checkZeroForAll(newList, values))
    newList
  }

  private def appendForNone(previousMods: List[BigInt], dividend: BigInt, values: List[BigInt] ): List[BigInt] = {
    require(dividend > 0)
    require(values.nonEmpty)
    require(checkPositive(values))
    require(checkPositive(previousMods))
    require(checkZeroForNone(previousMods, values))
    require(countModZero(values,dividend) == 0)
    val newList = dividend :: previousMods
    check(newList.tail == previousMods)
    check(newList.head == dividend)
    check(checkZeroForNone(newList, values))
    newList
  }

  private def appendForSome(previousMods: List[BigInt], dividend: BigInt, values: List[BigInt] ): List[BigInt] = {
    require(dividend > 0)
    require(values.nonEmpty)
    require(checkPositive(values))
    require(checkPositive(previousMods))
    require(checkZeroForSome(previousMods, values))
    require(countModZero(values,dividend) != values.size)
    require(countModZero(values,dividend) != 0)
    val newList = dividend :: previousMods
    check(newList.tail == previousMods)
    check(newList.head == dividend)
    check(checkZeroForSome(newList, values))
    newList
  }

  private def checkZeroForNone(modIsZeroForNoneValues: List[BigInt], values: List[BigInt]): Boolean = {
    require(values.nonEmpty)
    require(checkPositive(values))
    require(checkPositive(modIsZeroForNoneValues))

    @tailrec
    def loop(list: List[BigInt]): Boolean = {
      decreases(list.size)
      require(checkPositive(list))
      if (list.isEmpty) return true

      val dividend = list.head
      val result = countModZero(values, dividend)
      val valid = result == 0
      if( !valid ) then false else loop(list.tail)
    }
    loop(modIsZeroForNoneValues)
  }

  private def checkPositive(list: List[BigInt]): Boolean = {
    @tailrec
    def loop(listLoop: List[BigInt]): Boolean = {
      decreases(listLoop.size)
      if (listLoop.isEmpty) {
        return true
      }
      if (listLoop.head <= 0) false else loop(listLoop.tail)
    }
    loop(list)
  }
}