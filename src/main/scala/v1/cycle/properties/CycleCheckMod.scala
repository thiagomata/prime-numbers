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
}
