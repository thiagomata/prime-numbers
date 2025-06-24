package v1.cycle.properties

import stainless.lang.*
import v1.cycle.{Cycle, CycleUtils}
import verification.Helper.assert

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
    require(CycleUtils.countModZero(cycle.values, dividendA) == cycle.values.size)
    require(CycleUtils.countModZero(cycle.values, dividendB) == cycle.values.size)
    require(!cycle.evaluated(dividendA))
    require(!cycle.evaluated(dividendB))

    assert(!cycle.modIsZeroForAllValues.contains(dividendA))
    assert(!cycle.modIsZeroForSomeValues.contains(dividendA))
    assert(!cycle.modIsZeroForNoneValues.contains(dividendA))

    assert(!cycle.modIsZeroForAllValues.contains(dividendB))
    assert(!cycle.modIsZeroForSomeValues.contains(dividendB))
    assert(!cycle.modIsZeroForNoneValues.contains(dividendB))

    val cycleA = cycle.checkMod(dividendA)
    assert(cycleA.values == cycle.values)
    assert(cycleA.allModValuesAreZero(dividendA))
    assert(cycleA.allModValuesAreZero(dividendB))
    assert(cycleA.evaluated(dividendA))
    assert(!cycleA.evaluated(dividendB))
    assert(cycleA.modIsZeroForAllValues == dividendA :: cycle.modIsZeroForAllValues)
    assert(cycleA.modIsZeroForAllValues.contains(dividendA))
    assert(cycle.countModZero(dividendB) == cycleA.values.size)

    val cycleB = cycleA.checkMod(dividendB)
    assert(cycleB.values == cycleA.values)
    assert(cycleB.allModValuesAreZero(dividendA))
    assert(cycleB.allModValuesAreZero(dividendB))
    assert(cycleB.modIsZeroForAllValues == dividendB :: cycleA.modIsZeroForAllValues)
    assert(cycleB.modIsZeroForNoneValues == cycleA.modIsZeroForNoneValues)
    assert(cycleB.modIsZeroForSomeValues == cycleA.modIsZeroForSomeValues)
    assert(cycleB.evaluated(dividendA))
    assert(cycleB.evaluated(dividendB))
    assert(cycleB.modIsZeroForAllValues.contains(dividendA))
    assert(cycleB.modIsZeroForAllValues.contains(dividendA))

    cycleB.allModValuesAreZero(dividendA) &&
      cycleB.allModValuesAreZero(dividendB)
  }.holds

  def noModZeroPropagate(cycle: Cycle, dividendA: BigInt, dividendB: BigInt): Boolean = {
    require(dividendA > 0)
    require(dividendB > 0)
    require(dividendA != dividendB)
    require(CycleUtils.countModZero(cycle.values, dividendA) == 0)
    require(CycleUtils.countModZero(cycle.values, dividendB) == 0)
    require(!cycle.evaluated(dividendA))
    require(!cycle.evaluated(dividendB))

    assert(!cycle.modIsZeroForAllValues.contains(dividendA))
    assert(!cycle.modIsZeroForSomeValues.contains(dividendA))
    assert(!cycle.modIsZeroForNoneValues.contains(dividendA))

    assert(!cycle.modIsZeroForAllValues.contains(dividendB))
    assert(!cycle.modIsZeroForSomeValues.contains(dividendB))
    assert(!cycle.modIsZeroForNoneValues.contains(dividendB))

    assert(cycle.countModZero(dividendA) == 0)
    assert(cycle.countModZero(dividendB) == 0)

    val cycleA = cycle.checkMod(dividendA)
    assert(cycleA.values == cycle.values)
    assert(cycleA.noModValuesAreZero(dividendA))
    assert(cycleA.noModValuesAreZero(dividendB))
    assert(cycleA.evaluated(dividendA))
    assert(!cycleA.evaluated(dividendB))
    assert(cycleA.modIsZeroForNoneValues == dividendA :: cycle.modIsZeroForNoneValues)
    assert(cycleA.modIsZeroForNoneValues.contains(dividendA))

    val cycleB = cycleA.checkMod(dividendB)
    assert(cycleB.values == cycleA.values)
    assert(cycleB.noModValuesAreZero(dividendA))
    assert(cycleB.noModValuesAreZero(dividendB))
    assert(cycleB.modIsZeroForNoneValues == dividendB :: cycleA.modIsZeroForNoneValues)
    assert(cycleB.modIsZeroForAllValues == cycleA.modIsZeroForAllValues)
    assert(cycleB.modIsZeroForSomeValues == cycleA.modIsZeroForSomeValues)
    assert(cycleB.evaluated(dividendA))
    assert(cycleB.evaluated(dividendB))
    assert(cycleB.modIsZeroForNoneValues.contains(dividendA))
    assert(cycleB.modIsZeroForNoneValues.contains(dividendA))

    cycleB.noModValuesAreZero(dividendA) &&
      cycleB.noModValuesAreZero(dividendB)
  }.holds

  def someModZeroPropagate(cycle: Cycle, dividendA: BigInt, dividendB: BigInt): Boolean = {
    require(dividendA > 0)
    require(dividendB > 0)
    require(dividendA != dividendB)
    require(CycleUtils.countModZero(cycle.values, dividendA) != 0)
    require(CycleUtils.countModZero(cycle.values, dividendB) != 0)
    require(CycleUtils.countModZero(cycle.values, dividendA) != cycle.values.size)
    require(CycleUtils.countModZero(cycle.values, dividendB) != cycle.values.size)
    require(!cycle.evaluated(dividendA))
    require(!cycle.evaluated(dividendB))

    assert(!cycle.modIsZeroForAllValues.contains(dividendA))
    assert(!cycle.modIsZeroForSomeValues.contains(dividendA))
    assert(!cycle.modIsZeroForNoneValues.contains(dividendA))

    assert(!cycle.modIsZeroForAllValues.contains(dividendB))
    assert(!cycle.modIsZeroForSomeValues.contains(dividendB))
    assert(!cycle.modIsZeroForNoneValues.contains(dividendB))

    assert(cycle.countModZero(dividendB) != 0)
    assert(cycle.countModZero(dividendA) != 0)
    assert(cycle.countModZero(dividendB) != cycle.values.size)
    assert(cycle.countModZero(dividendA) != cycle.values.size)

    val cycleA = cycle.checkMod(dividendA)
    assert(cycleA.values == cycle.values)
    assert(cycleA.someModValuesAreZero(dividendA))
    assert(cycleA.someModValuesAreZero(dividendB))
    assert(cycleA.evaluated(dividendA))
    assert(!cycleA.evaluated(dividendB))
    assert(cycleA.modIsZeroForSomeValues == dividendA :: cycle.modIsZeroForSomeValues)
    assert(cycleA.modIsZeroForSomeValues.contains(dividendA))

    val cycleB = cycleA.checkMod(dividendB)
    assert(cycleB.values == cycleA.values)
    assert(cycleB.someModValuesAreZero(dividendA))
    assert(cycleB.someModValuesAreZero(dividendB))
    assert(cycleB.modIsZeroForSomeValues == dividendB :: cycleA.modIsZeroForSomeValues)
    assert(cycleB.modIsZeroForAllValues == cycleA.modIsZeroForAllValues)
    assert(cycleB.modIsZeroForNoneValues == cycleA.modIsZeroForNoneValues)
    assert(cycleB.evaluated(dividendA))
    assert(cycleB.evaluated(dividendB))
    assert(cycleB.modIsZeroForSomeValues.contains(dividendA))
    assert(cycleB.modIsZeroForSomeValues.contains(dividendA))

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
