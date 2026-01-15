package v1.cycle


import stainless.collection.List
import stainless.lang.decreases
import v1.Calc
import v1.cycle.memory.MemCycle
import verification.Helper.assert

import scala.annotation.tailrec

object CycleUtils {
  def apply(values: List[BigInt]): MemCycle = {
    require(values.nonEmpty)
    require(checkPositiveOrZero(values))
    MemCycle(values)
  }

  def isValid(
               values: List[BigInt],
               modIsZeroForAllValues: List[BigInt],
               modIsZeroForSomeValues: List[BigInt],
               modIsZeroForNoneValues: List[BigInt],
             ): Boolean = {
    values.nonEmpty &&
      CycleUtils.checkPositiveOrZero(values) &&
      CycleUtils.checkPositive(modIsZeroForAllValues) &&
      CycleUtils.checkPositive(modIsZeroForSomeValues) &&
      CycleUtils.checkPositive(modIsZeroForNoneValues) &&
      CycleUtils.checkZeroForAll(modIsZeroForAllValues, values) &&
      CycleUtils.checkZeroForSome(modIsZeroForSomeValues, values) &&
      CycleUtils.checkZeroForNone(modIsZeroForNoneValues, values)
  }

  def countModZero(values: List[BigInt], dividend: BigInt): BigInt = {
    require(dividend > 0)
    require(values.nonEmpty)
    require(checkPositiveOrZero(values))

    @tailrec
    def loop(loopList: List[BigInt], totalAcc: BigInt = BigInt(0)): BigInt = {
      decreases(loopList.size)

      if (loopList.isEmpty) {
        return totalAcc
      }
      val current = loopList.head
      val thisValueModsZero = if (Calc.mod(current, dividend) == 0) then BigInt(1) else BigInt(0)
      loop(loopList.tail, totalAcc + thisValueModsZero)
    }

    loop(values)
  }

  def checkZeroForSome(modIsZeroForSomeValues: List[BigInt], values: List[BigInt]): Boolean = {
    require(values.nonEmpty)
    require(checkPositive(modIsZeroForSomeValues))
    require(checkPositiveOrZero(values))

    @tailrec
    def loop(list: List[BigInt]): Boolean = {
      require(checkPositive(list))
      decreases(list.size)
      if (list.isEmpty) return true

      val dividend = list.head
      assert(dividend > 0)
      val result = countModZero(values, dividend)
      val valid = (result != values.size && result != 0)
      if (!valid) then false else loop(list.tail)
    }

    loop(modIsZeroForSomeValues)
  }

  def checkZeroForAll(modIsZeroForAllValues: List[BigInt], values: List[BigInt]): Boolean = {
    require(values.nonEmpty)
    require(checkPositive(modIsZeroForAllValues))
    require(checkPositiveOrZero(values))

    @tailrec
    def loop(list: List[BigInt]): Boolean = {
      decreases(list.size)
      require(checkPositive(list))

      if (list.isEmpty) return true

      val dividend = list.head
      assert(dividend > 0)
      val result = countModZero(values, dividend)
      val valid = result == values.size
      if (!valid) then false else loop(list.tail)
    }

    loop(modIsZeroForAllValues)
  }


//  def appendForNone(mCycle: MemCycle, dividend: BigInt): MemCycle = {
//    require(dividend > 0)
//    require(mCycle.isValid)
//    require(countModZero(mCycle.values, dividend) == 0)
//
//    val newList = dividend :: mCycle.modIsZeroForNoneValues
//    assert(newList.tail == mCycle.modIsZeroForNoneValues)
//    assert(newList.head == dividend)
//    assert(checkZeroForNone(newList, mCycle.values))
//
//    MemCycle(
//      cycle = mCycle.cycle,
//      modIsZeroForAllValues = mCycle.modIsZeroForAllValues,
//      modIsZeroForNoneValues = newList,
//      modIsZeroForSomeValues = mCycle.modIsZeroForSomeValues,
//    )
//  }

//  def appendForSome(mCycle: MemCycle, dividend: BigInt): MemCycle = {
//    require(dividend > 0)
//    require(mCycle.isValid)
//    require(countModZero(mCycle.values, dividend) != 0)
//    require(countModZero(mCycle.values, dividend) != mCycle.values.size)
//
//    val newList = dividend :: mCycle.modIsZeroForSomeValues
//    assert(newList.tail == mCycle.modIsZeroForSomeValues)
//    assert(newList.head == dividend)
//    assert(checkZeroForSome(newList, mCycle.values))
//
//    MemCycle(
//      cycle = mCycle.cycle,
//      modIsZeroForAllValues = mCycle.modIsZeroForAllValues,
//      modIsZeroForNoneValues = mCycle.modIsZeroForNoneValues,
//      modIsZeroForSomeValues = newList,
//    )
//  }

  def checkZeroForNone(modIsZeroForNoneValues: List[BigInt], values: List[BigInt]): Boolean = {
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

  def checkPositive(list: List[BigInt]): Boolean = {

    @tailrec
    def loop(listLoop: List[BigInt]): Boolean = {
      decreases(listLoop.size)
      if (listLoop.isEmpty) return true
      val valid = listLoop.head > 0
      if (!valid) false else loop(listLoop.tail)
    }

    loop(list)
  }

  def checkPositiveOrZero(list: List[BigInt]): Boolean = {

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
