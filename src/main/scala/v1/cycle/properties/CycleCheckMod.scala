package v1.cycle.properties

import stainless.lang.*
//import verification.Helper.check
import stainless.proof.check
import v1.cycle.Cycle

object CycleCheckMod {

  def forAnyCheckModValuesRemains(cycle: Cycle, dividend: BigInt): Boolean = {
    require(dividend > 0)
    val newCycle = cycle.checkMod(dividend)
    newCycle.values == cycle.values
  }.holds

  def notEvaluatedNotInTheList(cycle: Cycle, dividend: BigInt): Boolean = {
    require(dividend > 0)
    require(!cycle.evaluated(dividend))

    !cycle.modIsZeroForSomeValues.contains(dividend) &&
      !cycle.modIsZeroForAllValues.contains(dividend) &&
      !cycle.modIsZeroForNoneValues.contains(dividend)
  }.holds

  def evaluatedInSomeList(cycle: Cycle, dividend: BigInt): Boolean = {
    require(dividend > 0)
    require(!cycle.evaluated(dividend))

    val evalCycle = cycle.checkMod(dividend)

    evalCycle.modIsZeroForSomeValues.contains(dividend) ||
      evalCycle.modIsZeroForAllValues.contains(dividend) ||
      evalCycle.modIsZeroForNoneValues.contains(dividend)
  }.holds

  def oneListNotInOther(cycle: Cycle, dividend: BigInt): Boolean = {
    require(dividend > 0)
    require(!cycle.evaluated(dividend))

    val evalCycle = cycle.checkMod(dividend)

    if (evalCycle.modIsZeroForSomeValues.contains(dividend)) {
      !evalCycle.modIsZeroForAllValues.contains(dividend) && !evalCycle.modIsZeroForNoneValues.contains(dividend)
    }
    else if (evalCycle.modIsZeroForAllValues.contains(dividend)) {
      !evalCycle.modIsZeroForSomeValues.contains(dividend) && !evalCycle.modIsZeroForNoneValues.contains(dividend)
    }
    else if (evalCycle.modIsZeroForNoneValues.contains(dividend)) {
      !evalCycle.modIsZeroForAllValues.contains(dividend) && !evalCycle.modIsZeroForSomeValues.contains(dividend)
    } else {
      false
    }
  }.holds

  def ifInAllModAll(cycle: Cycle, dividend: BigInt): Boolean = {
    require(dividend > 0)
    require(!cycle.evaluated(dividend))

    val evalCycle = cycle.checkMod(dividend)
    if (evalCycle.modIsZeroForAllValues.contains(dividend)) {
      evalCycle.countModZero(dividend) == evalCycle.values.size
    } else {
      evalCycle.countModZero(dividend) != evalCycle.values.size
    }
  }.holds

  def ifInSomeModSome(cycle: Cycle, dividend: BigInt): Boolean = {
    require(dividend > 0)
    require(!cycle.evaluated(dividend))

    val evalCycle = cycle.checkMod(dividend)
    if (evalCycle.modIsZeroForSomeValues.contains(dividend)) {
      evalCycle.countModZero(dividend) != evalCycle.values.size &&
        evalCycle.countModZero(dividend) != 0
    } else {
      evalCycle.countModZero(dividend) == evalCycle.values.size ||
        evalCycle.countModZero(dividend) == 0
    }
  }.holds

  def ifInNoneModNone(cycle: Cycle, dividend: BigInt): Boolean = {
    require(dividend > 0)
    require(!cycle.evaluated(dividend))

    val evalCycle = cycle.checkMod(dividend)
    if (evalCycle.modIsZeroForNoneValues.contains(dividend)) {
      evalCycle.countModZero(dividend) == 0
    } else {
      evalCycle.countModZero(dividend) != 0
    }
  }.holds

  def allModZeroPropagate(cycle: Cycle, dividendA: BigInt, dividendB: BigInt): Boolean = {
    require(dividendA > 0)
    require(dividendB > 0)
    require(dividendA != dividendB)
    require(Cycle.countModZero(cycle.values, dividendA) == cycle.values.size)
    require(Cycle.countModZero(cycle.values, dividendB) == cycle.values.size)
    require(!cycle.evaluated(dividendA))
    require(!cycle.evaluated(dividendB))

    check(!cycle.modIsZeroForAllValues.contains(dividendA))
    check(!cycle.modIsZeroForSomeValues.contains(dividendA))
    check(!cycle.modIsZeroForNoneValues.contains(dividendA))

    check(!cycle.modIsZeroForAllValues.contains(dividendB))
    check(!cycle.modIsZeroForSomeValues.contains(dividendB))
    check(!cycle.modIsZeroForNoneValues.contains(dividendB))

    val cycleA = cycle.checkMod(dividendA)
    check(cycleA.values == cycle.values)
    check(cycleA.allModValuesAreZero(dividendA))
    check(cycleA.allModValuesAreZero(dividendB))
    check(cycleA.evaluated(dividendA))
    check(!cycleA.evaluated(dividendB))
    check(cycleA.modIsZeroForAllValues == dividendA :: cycle.modIsZeroForAllValues)
    check(cycleA.modIsZeroForAllValues.contains(dividendA))
    check(cycle.countModZero(dividendB) == cycleA.values.size)

    val cycleB = cycleA.checkMod(dividendB)
    check(cycleB.values == cycleA.values)
    check(cycleB.allModValuesAreZero(dividendA))
    check(cycleB.allModValuesAreZero(dividendB))
    check(cycleB.modIsZeroForAllValues == dividendB :: cycleA.modIsZeroForAllValues)
    check(cycleB.modIsZeroForNoneValues == cycleA.modIsZeroForNoneValues)
    check(cycleB.modIsZeroForSomeValues == cycleA.modIsZeroForSomeValues)
    check(cycleB.evaluated(dividendA))
    check(cycleB.evaluated(dividendB))
    check(cycleB.modIsZeroForAllValues.contains(dividendA))
    check(cycleB.modIsZeroForAllValues.contains(dividendA))

    cycleB.allModValuesAreZero(dividendA) &&
      cycleB.allModValuesAreZero(dividendB)
  }.holds

  def noModZeroPropagate(cycle: Cycle, dividendA: BigInt, dividendB: BigInt): Boolean = {
    require(dividendA > 0)
    require(dividendB > 0)
    require(dividendA != dividendB)
    require(Cycle.countModZero(cycle.values, dividendA) == 0)
    require(Cycle.countModZero(cycle.values, dividendB) == 0)
    require(!cycle.evaluated(dividendA))
    require(!cycle.evaluated(dividendB))

    check(!cycle.modIsZeroForAllValues.contains(dividendA))
    check(!cycle.modIsZeroForSomeValues.contains(dividendA))
    check(!cycle.modIsZeroForNoneValues.contains(dividendA))

    check(!cycle.modIsZeroForAllValues.contains(dividendB))
    check(!cycle.modIsZeroForSomeValues.contains(dividendB))
    check(!cycle.modIsZeroForNoneValues.contains(dividendB))

    check(cycle.countModZero(dividendA) == 0)
    check(cycle.countModZero(dividendB) == 0)

    val cycleA = cycle.checkMod(dividendA)
    check(cycleA.values == cycle.values)
    check(cycleA.noModValuesAreZero(dividendA))
    check(cycleA.noModValuesAreZero(dividendB))
    check(cycleA.evaluated(dividendA))
    check(!cycleA.evaluated(dividendB))
    check(cycleA.modIsZeroForNoneValues == dividendA :: cycle.modIsZeroForNoneValues)
    check(cycleA.modIsZeroForNoneValues.contains(dividendA))

    val cycleB = cycleA.checkMod(dividendB)
    check(cycleB.values == cycleA.values)
    check(cycleB.noModValuesAreZero(dividendA))
    check(cycleB.noModValuesAreZero(dividendB))
    check(cycleB.modIsZeroForNoneValues == dividendB :: cycleA.modIsZeroForNoneValues)
    check(cycleB.modIsZeroForAllValues == cycleA.modIsZeroForAllValues)
    check(cycleB.modIsZeroForSomeValues == cycleA.modIsZeroForSomeValues)
    check(cycleB.evaluated(dividendA))
    check(cycleB.evaluated(dividendB))
    check(cycleB.modIsZeroForNoneValues.contains(dividendA))
    check(cycleB.modIsZeroForNoneValues.contains(dividendA))

    cycleB.noModValuesAreZero(dividendA) &&
      cycleB.noModValuesAreZero(dividendB)
  }.holds

  def someModZeroPropagate(cycle: Cycle, dividendA: BigInt, dividendB: BigInt): Boolean = {
    require(dividendA > 0)
    require(dividendB > 0)
    require(dividendA != dividendB)
    require(Cycle.countModZero(cycle.values, dividendA) != 0)
    require(Cycle.countModZero(cycle.values, dividendB) != 0)
    require(Cycle.countModZero(cycle.values, dividendA) != cycle.values.size)
    require(Cycle.countModZero(cycle.values, dividendB) != cycle.values.size)
    require(!cycle.evaluated(dividendA))
    require(!cycle.evaluated(dividendB))

    check(!cycle.modIsZeroForAllValues.contains(dividendA))
    check(!cycle.modIsZeroForSomeValues.contains(dividendA))
    check(!cycle.modIsZeroForNoneValues.contains(dividendA))

    check(!cycle.modIsZeroForAllValues.contains(dividendB))
    check(!cycle.modIsZeroForSomeValues.contains(dividendB))
    check(!cycle.modIsZeroForNoneValues.contains(dividendB))

    check(cycle.countModZero(dividendB) != 0)
    check(cycle.countModZero(dividendA) != 0)
    check(cycle.countModZero(dividendB) != cycle.values.size)
    check(cycle.countModZero(dividendA) != cycle.values.size)

    val cycleA = cycle.checkMod(dividendA)
    check(cycleA.values == cycle.values)
    check(cycleA.someModValuesAreZero(dividendA))
    check(cycleA.someModValuesAreZero(dividendB))
    check(cycleA.evaluated(dividendA))
    check(!cycleA.evaluated(dividendB))
    check(cycleA.modIsZeroForSomeValues == dividendA :: cycle.modIsZeroForSomeValues)
    check(cycleA.modIsZeroForSomeValues.contains(dividendA))

    val cycleB = cycleA.checkMod(dividendB)
    check(cycleB.values == cycleA.values)
    check(cycleB.someModValuesAreZero(dividendA))
    check(cycleB.someModValuesAreZero(dividendB))
    check(cycleB.modIsZeroForSomeValues == dividendB :: cycleA.modIsZeroForSomeValues)
    check(cycleB.modIsZeroForAllValues == cycleA.modIsZeroForAllValues)
    check(cycleB.modIsZeroForNoneValues == cycleA.modIsZeroForNoneValues)
    check(cycleB.evaluated(dividendA))
    check(cycleB.evaluated(dividendB))
    check(cycleB.modIsZeroForSomeValues.contains(dividendA))
    check(cycleB.modIsZeroForSomeValues.contains(dividendA))

    cycleB.someModValuesAreZero(dividendA) &&
      cycleB.someModValuesAreZero(dividendB)
  }.holds

  def afterMethodListAndZeroModCountAreOnSync(cycle: Cycle, dividend: BigInt): Boolean = {
    require(dividend > 0)
    val cycleAfterCheck = cycle.checkMod(dividend)

    val modValueMatchList = if (cycleAfterCheck.allModValuesAreZero(dividend) ) {
      cycleAfterCheck.modIsZeroForAllValues.contains(dividend) &&
      !cycleAfterCheck.modIsZeroForSomeValues.contains(dividend) &&
      !cycleAfterCheck.modIsZeroForNoneValues.contains(dividend)
    } else if (cycleAfterCheck.noModValuesAreZero(dividend) ) {
      cycleAfterCheck.modIsZeroForNoneValues.contains(dividend) &&
        !cycleAfterCheck.modIsZeroForSomeValues.contains(dividend) &&
        !cycleAfterCheck.modIsZeroForAllValues.contains(dividend)
    } else if (cycleAfterCheck.someModValuesAreZero(dividend)) {
      cycleAfterCheck.modIsZeroForSomeValues.contains(dividend) &&
        !cycleAfterCheck.modIsZeroForNoneValues.contains(dividend) &&
        !cycleAfterCheck.modIsZeroForAllValues.contains(dividend)
    } else {
      false
    }

    val listMatchModValue = if ( cycleAfterCheck.modIsZeroForAllValues.contains(dividend) ) {
      cycleAfterCheck.allModValuesAreZero(dividend) &&
        !cycleAfterCheck.noModValuesAreZero(dividend) &&
        !cycleAfterCheck.someModValuesAreZero(dividend)
    } else if (cycleAfterCheck.modIsZeroForNoneValues.contains(dividend) ) {
       cycleAfterCheck.noModValuesAreZero(dividend) &&
        !cycleAfterCheck.allModValuesAreZero(dividend) &&
        !cycleAfterCheck.someModValuesAreZero(dividend)
    } else if (cycleAfterCheck.modIsZeroForSomeValues.contains(dividend)) {
      cycleAfterCheck.someModValuesAreZero(dividend) &&
        !cycleAfterCheck.allModValuesAreZero(dividend) &&
        !cycleAfterCheck.noModValuesAreZero(dividend)
    } else {
      false
    }

    modValueMatchList && listMatchModValue
  }
}
