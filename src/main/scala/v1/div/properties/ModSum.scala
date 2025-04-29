  package v1.div.properties

import stainless.lang.*
import verification.Helper.assert
//import verification.Helper.check
import stainless.proof.check
import v1.Calc
import v1.Calc.mod
import verification.Helper.equality

import scala.annotation.tailrec

object ModSum {
  def sumSymmetricalMods(b: BigInt, step: BigInt): Boolean = {
    require(b > 0)
    require(step > 0)
    require(step < b)
    assert(Calc.mod(step, b) == step)
    assert(Calc.mod(b - step, b) == b - step)
    assert(Calc.mod(step, b) + Calc.mod(b - step, b) == step + b - step)
    Calc.mod(step, b) + Calc.mod(b - step, b) == b
  }.holds

  def checkAllPreviousValues(a: BigInt, b: BigInt): Boolean = {
    require(b > 0)
    decreases(a)
    require(a < b)
    require(a >= 0)
    if ( a == 0 ) {
      ModSmallDividend.modSmallDividend(a, b)
    } else {
      ModSmallDividend.modSmallDividend(a, b) &&
        ModSmallDividend.modSmallDividend(a - 1, b)
    }
    Calc.mod(a,b) == a
  }.holds

  def sumAllValues(from: BigInt, to: BigInt): BigInt = {
    require(from >= 0)
    require(to >= 0)
    require(to >= from)
    decreases(to)
    if (from == to) {
      to
    } else {
       to + sumAllValues(from, to - 1)
    }
  }

  def sumAllMods(from: BigInt, to: BigInt, b: BigInt): BigInt = {
    require(b > 0)
    require(from >= 0)
    require(to >= 0)
    require(to >= from)
    decreases(to)
    if (from == to) {
      Calc.mod(to, b)
    } else {
      Calc.mod(to,b) + sumAllMods(from, to - 1, b)
    }
  }

  def sumAllModsEqualSumOfAllSmallValues(b: BigInt): Boolean = {
    require(b > 0)
    checkAllPreviousValues(b - 1, b)
    sumAllMods(0, b - 1, b) == sumAllValues(0, b - 1)
  }

  def checkValueShift(a: BigInt, b: BigInt): Boolean = {
    require(b > 0)
    require(a >= 0)
    decreases(a)

    if (a < b) {
      ModSmallDividend.modSmallDividend(a,b)
      mod(a,b) == a
    } else {
      ModOperations.modLess(a,b,b)
      assert(
        equality(
          mod(a - b, b),
          mod(mod(a, b) - mod(b, b), b),
          mod(mod(a, b) - 0, b),
          mod(mod(a, b), b),
          mod(a, b),
        )
      )
      assert(mod(a,b) == mod(a - b, b))
      checkValueShift(a - b, b)
    }
  }.holds
}
