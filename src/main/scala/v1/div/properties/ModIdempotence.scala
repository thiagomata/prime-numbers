package v1.div.properties

import v1.div.DivMod
import stainless.lang.*
import stainless.proof.check
import v1.Calc.mod
import v1.Calc.div

object ModIdempotence {
  def modIdempotence(a: BigInt, b: BigInt): Boolean = {
    require(b != 0)
    val div = DivMod(a, b, 0, a)
    if (a >= 0) {
      check(modIdempotencePositiveA(a, b))
      check(mod(a, b) == mod(mod(a, b), b))
    } else {
      check(modIdempotencePositiveA(-a, b))
      val divModNegative = DivMod(a, b, 0, a)
      val solvedNegative = divModNegative.solve
      check(a == solvedNegative.div * b + solvedNegative.mod)
      check(solvedNegative.mod >= 0)
      check(solvedNegative.mod <= solvedNegative.absB)
      check(mod(a, b) == mod(mod(a, b), b))
    }
    mod(a, b) == mod(mod(a, b), b)
  }

  def modIdempotencePositiveA(a: BigInt, b: BigInt): Boolean = {
    require(b != 0)
    require(a >= 0)

    val divMod = DivMod(a, b, 0, a)

    val solved = divMod.solve
    check(solved.isFinal)
    check(solved.b == divMod.b)
    check(solved.a == divMod.a)
    check(divMod.absB > 0)
    check(solved.mod < divMod.absB)
    check(solved.mod >= 0)

    val result = solved.mod
    check(result <= a)
    check(result < divMod.absB)
    check(result == mod(a, b))

    check(mod(result, b) == result)
    check(mod(a, b) == mod(result, b))
    mod(a, b) == mod(mod(a, b), b)
  }.holds

  def modUniqueDiv(x: DivMod, y: DivMod): Boolean = {
    require(x.isValid)
    require(y.isValid)
    require(x.a == y.a)
    require(x.b == y.b)
    require(x.b != 0)
    check(modUnique(x.a, x.b, x.div, x.mod, y.div, y.mod))
    x.solve == y.solve
  }.holds

  def modUnique(a: BigInt, b: BigInt, divx: BigInt, modx: BigInt, divy: BigInt, mody: BigInt): Boolean = {
    require(b != 0)
    val divDiff = divx - divy
    val absDivDiff = if (divDiff < 0) -divDiff else divDiff
    decreases(absDivDiff)
    require(divx * b + modx == a)
    require(divy * b + mody == a)

    val x = DivMod(a, b, divx, modx)
    val y = DivMod(a, b, divy, mody)

    if (divx == divy) {
      check(modx == mody)
      check(x == y)
    }
    if (divx < divy) {
      AdditionAndMultiplication.MoreDivLessMod(a, b, divx, modx)
      val next =  DivMod(a, b, divx + 1, modx - b)
      check(x.solve == next.solve)
      modUnique(a, b, divx + 1, modx - b, divy, mody)
      check(x.solve == y.solve)
    }
    if (divx > divy) {
      AdditionAndMultiplication.LessDivMoreMod(a, b, divx, modx)
      val next =  DivMod(a, b, divx - 1, modx + b)
      check(x.solve == next.solve)
      modUnique(a, b, divx - 1, modx + b, divy, mody)
      check(x.solve == y.solve)
    }
    check(x.solve == y.solve)

    DivMod(a, b, divx, modx).solve == DivMod(a, b, divy, mody).solve
  }.holds

  def modModPlus(a: BigInt, b: BigInt, c: BigInt): Boolean = {
    require(b != 0)

    val divModA = DivMod(a, b, 0, a)
    val solvedA = divModA.solve
    val divModC = DivMod(c, b, 0, c)
    val solvedC = divModC.solve
    val addModAC = solvedA.mod + solvedC.mod
    val divModAC = DivMod(addModAC, b, 0, addModAC)
    val solvedAC = divModAC.solve
    val absB = if (b < 0) -b else b

    check(solvedA.isFinal && solvedA.isValid)
    check(solvedC.isFinal && solvedC.isValid)
    check(solvedAC.isFinal && solvedAC.isValid)

    check(solvedA.mod >= 0)
    check(solvedC.mod < absB)

    check(solvedC.mod >= 0)
    check(solvedC.mod < absB)

    check(addModAC == solvedA.mod + solvedC.mod)
    check(addModAC < 2 * absB)
    check(addModAC >= 0)

    check(solvedAC.a == addModAC)
    check(solvedAC.a >= 0)
    check(solvedAC.b == b)

    check(solvedA.mod < absB)
    check(solvedC.mod < absB)
    check(solvedAC.mod < 2 * absB)

    check(solvedAC.div < 2)
    check(solvedAC.div > -2)
    check(solvedAC.div == 0 || solvedAC.div == 1 || solvedAC.div == -1)

    if (solvedAC.div == 0) {
      check(solvedAC.mod == addModAC)
      check(solvedAC.mod == solvedA.mod + solvedC.mod)
      check(mod(mod(a, b) + mod(c, b), b) == mod(a, b) + mod(c, b))
      check(solvedAC.a == solvedAC.b * solvedAC.div + solvedAC.mod)
      check(div(mod(a, b) + mod(c, b), b) == 0)
    }

    if (solvedAC.div == 1) {
      check(solvedAC.mod == addModAC - b)
      check(solvedAC.a == solvedAC.b * solvedAC.div + solvedAC.mod)
      check(solvedAC.b > 0)
      check(addModAC == b + solvedAC.mod)
      check(solvedA.mod + solvedC.mod == solvedAC.mod + b)
      check(solvedAC.mod == solvedA.mod + solvedC.mod - b)
      check(mod(mod(a, b) + mod(c, b), b) == mod(a, b) + mod(c, b) - b)
      check(div(mod(a, b) + mod(c, b), b) == 1)
    }

    if (solvedAC.div == -1) {
      check(solvedAC.mod == addModAC + b)
      check(solvedAC.a == solvedAC.b * solvedAC.div + solvedAC.mod)
      check(solvedAC.b < 0)
      check(addModAC == b * -1 + solvedAC.mod)
      check(addModAC == -b + solvedAC.mod)
      check(addModAC == solvedAC.mod - b)
      check(solvedA.mod + solvedC.mod == solvedAC.mod - b)
      check(solvedAC.mod == solvedA.mod + solvedC.mod + b)
      check(mod(mod(a, b) + mod(c, b), b) == mod(a, b) + mod(c, b) + b)
      check(div(mod(a, b) + mod(c, b), b) == -1)
    }

    mod(mod(a, b) + mod(c, b), b) == mod(a, b) + mod(c, b) - b * div(mod(a, b) + mod(c, b), b)
  }.holds

  def modModMinus(a: BigInt, b: BigInt, c: BigInt): Boolean = {
    require(b != 0)

    val divModA = DivMod(a, b, 0, a)
    val solvedA = divModA.solve
    val divModC = DivMod(c, b, 0, c)
    val solvedC = divModC.solve
    val subModAC = solvedA.mod - solvedC.mod
    val divModAC = DivMod(subModAC, b, 0, subModAC)
    val solvedAC = divModAC.solve
    val absB = if (b < 0) -b else b

    check(solvedA.isFinal && solvedA.isValid )
    check(solvedC.isFinal && solvedC.isValid)
    check(solvedAC.isFinal && solvedAC.isValid)

    check(solvedA.mod >= 0)
    check(solvedA.mod < absB)

    check(solvedC.mod >= 0)
    check(solvedC.mod < absB)

    check(subModAC == solvedA.mod - solvedC.mod)
    check(subModAC <= solvedA.mod)
    check(subModAC > -absB)

    check(solvedAC.a == subModAC)
    check(solvedAC.a > -absB)
    check(solvedAC.a <= solvedA.mod)
    check(solvedAC.b == b)
    check(solvedAC.mod >= 0)
    check(solvedAC.mod < absB)

    check(solvedAC.a == solvedAC.b * solvedAC.div + solvedAC.mod)
    check(solvedAC.div < 2)
    check(solvedAC.div > -2)
    check(solvedAC.div == 0 || solvedAC.div == 1 || solvedAC.div == -1)
    if (solvedAC.div == 0) {
      check(solvedAC.mod == subModAC)
      check(solvedAC.mod == solvedA.mod - solvedC.mod)
      check(mod(mod(a, b) - mod(c, b), b) == mod(a, b) - mod(c, b))
      check(solvedAC.a == solvedAC.b * solvedAC.div + solvedAC.mod)
      check(solvedAC.a == solvedAC.mod)
      check(div(mod(a, b) - mod(c, b), b) == 0)
    }
    if (solvedAC.div == 1) {
      check(solvedAC.mod == subModAC - b)
      check(solvedAC.a == solvedAC.b * solvedAC.div + solvedAC.mod)
      check(subModAC == b + solvedAC.mod)
      check(solvedA.mod - solvedC.mod == solvedAC.mod + b)
      check(solvedAC.mod == solvedA.mod - solvedC.mod - b)
      check(mod(mod(a, b) - mod(c, b), b) == mod(a, b) - mod(c, b) - b)
      check(div(mod(a, b) - mod(c, b), b) == 1)
    }
    if (solvedAC.div == -1) {
      check(solvedAC.mod == subModAC + b)
      check(solvedAC.a == solvedAC.b * solvedAC.div + solvedAC.mod)
      check(subModAC == b * -1 + solvedAC.mod)
      check(subModAC == -b + solvedAC.mod)
      check(subModAC == solvedAC.mod - b)
      check(solvedA.mod - solvedC.mod == solvedAC.mod - b)
      check(solvedAC.mod == solvedA.mod - solvedC.mod + b)
      check(mod(mod(a, b) - mod(c, b), b) == mod(a, b) - mod(c, b) + b)
      check(div(mod(a, b) - mod(c, b), b) == -1)
    }

    mod(mod(a, b) - mod(c, b), b) == mod(a, b) - mod(c, b) - b * div(mod(a, b) - mod(c, b), b)
  }.holds
}
