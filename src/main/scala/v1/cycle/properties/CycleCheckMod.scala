package v1.cycle.properties

import v1.cycle.Cycle
import stainless.collection.*
import stainless.lang.*
import stainless.proof.check
import v1.Calc

import scala.annotation.tailrec

object CycleCheckMod {

  def forAnyCheckModValuesRemains(cycle: Cycle, dividend: BigInt): Boolean = {
    require(dividend > 0)
    val newCycle = cycle.checkMod(dividend)
    newCycle.values == cycle.values
  }.holds
//
//  def checkModIsZero(cycle: Cycle, dividend: BigInt): Boolean = {
//    require(dividend > 0)
//    require(!cycle.evaluated(dividend))
//
////    @tailrec
////    def loopCheckModIsZero(loopValueKey: BigInt =  cycle.values.size - 1): Boolean = {
////      require(loopValueKey >= 0)
////      require(loopValueKey < cycle.values.size)
////
////      val currentValue = cycle.values(loopValueKey)
////      val currentModIsZero = Calc.mod(currentValue, dividend) == 0
////      if (loopValueKey == 0) {
////        currentModIsZero
////      } else {
////        currentModIsZero && loopCheckModIsZero(loopValueKey - 1)
////      }
////    }
//
//    def loopCheckModIsZero(): Boolean = {
//      cycle.values.forall(
//        value => {
//          Calc.mod(value, dividend) == 0
//        }
//      )
//    }
//
//    val newCycle = cycle.checkMod(dividend)
//    if (loopCheckModIsZero()) {
//      check(Cycle.countModZero(cycle.values, dividend) == cycle.values.size)
//      true
////      (newCycle.modIsZeroForSomeValues == cycle.modIsZeroForSomeValues) &&
////        (newCycle.modIsNotZeroForAllValues == cycle.modIsNotZeroForAllValues) &&
////        (newCycle.modIsZeroForAllValues == cycle.modIsZeroForAllValues :+ dividend )
//    } else {
//      true
//    }
//  }.holds
}
