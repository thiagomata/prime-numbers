package v1.chapter2.div.properties

import stainless.lang.*
import v1.chapter2.div.Calc.{div, mod}
import v1.chapter1.verification.Helper.{assert, equality}
import v1.chapter2.div.DivMod

object ModIdempotence {
  def modIdempotence(a: BigInt, b: BigInt): Boolean = {
    require(b != 0)
    val div = DivMod(a, b, 0, a)
    if (a >= 0) {
      assert(modIdempotencePositiveA(a, b))
      assert(mod(a, b) == mod(mod(a, b), b))
    } else {
      assert(modIdempotencePositiveA(-a, b))
      val divModNegative = DivMod(a, b, 0, a)
      val solvedNegative = divModNegative.solve
      assert(a == solvedNegative.div * b + solvedNegative.mod)
      assert(solvedNegative.mod >= 0)
      assert(solvedNegative.mod <= solvedNegative.absB)
      assert(mod(a, b) == mod(mod(a, b), b))
    }
    mod(a, b) == mod(mod(a, b), b)
  }

  def modIdempotencePositiveA(a: BigInt, b: BigInt): Boolean = {
    require(b != 0)
    require(a >= 0)

    val divMod = DivMod(a, b, 0, a)

    val solved = divMod.solve
    assert(solved.isFinal)
    assert(solved.b == divMod.b)
    assert(solved.a == divMod.a)
    assert(divMod.absB > 0)
    assert(solved.mod < divMod.absB)
    assert(solved.mod >= 0)

    val result = solved.mod
    assert(result <= a)
    assert(result < divMod.absB)
    assert(result == mod(a, b))

    assert(mod(result, b) == result)
    assert(mod(a, b) == mod(result, b))
    mod(a, b) == mod(mod(a, b), b)
  }.holds

  def modUniqueDiv(x: DivMod, y: DivMod): Boolean = {
    require(x.isValid)
    require(y.isValid)
    require(x.a == y.a)
    require(x.b == y.b)
    require(x.b != 0)
    assert(modUnique(x.a, x.b, x.div, x.mod, y.div, y.mod))
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
      assert(modx == mody)
      assert(x == y)
    }
    if (divx < divy) {
      assertDivModWithMoreDivAndLessModSameSolution(a, b, divx, modx)
      val next =  DivMod(a, b, divx + 1, modx - b)
      assert(x.solve == next.solve)
      modUnique(a, b, divx + 1, modx - b, divy, mody)
      assert(x.solve == y.solve)
    }
    if (divx > divy) {
      assertDivModWithLessDivAndMoreModSameSolution(a, b, divx, modx)
      val next =  DivMod(a, b, divx - 1, modx + b)
      assert(x.solve == next.solve)
      modUnique(a, b, divx - 1, modx + b, divy, mody)
      assert(x.solve == y.solve)
    }
    assert(x.solve == y.solve)

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

    assert(solvedA.isFinal && solvedA.isValid)
    assert(solvedC.isFinal && solvedC.isValid)
    assert(solvedAC.isFinal && solvedAC.isValid)

    assert(solvedA.mod >= 0)
    assert(solvedC.mod < absB)

    assert(solvedC.mod >= 0)
    assert(solvedC.mod < absB)

    assert(addModAC == solvedA.mod + solvedC.mod)
    assert(addModAC < 2 * absB)
    assert(addModAC >= 0)

    assert(solvedAC.a == addModAC)
    assert(solvedAC.a >= 0)
    assert(solvedAC.b == b)

    assert(solvedA.mod < absB)
    assert(solvedC.mod < absB)
    assert(solvedAC.mod < 2 * absB)

    assert(solvedAC.div < 2)
    assert(solvedAC.div > -2)
    assert(solvedAC.div == 0 || solvedAC.div == 1 || solvedAC.div == -1)

    if (solvedAC.div == 0) {
      assert(solvedAC.mod == addModAC)
      assert(solvedAC.mod == solvedA.mod + solvedC.mod)
      assert(mod(mod(a, b) + mod(c, b), b) == mod(a, b) + mod(c, b))
      assert(solvedAC.a == solvedAC.b * solvedAC.div + solvedAC.mod)
      assert(div(mod(a, b) + mod(c, b), b) == 0)
    }

    if (solvedAC.div == 1) {
      assert(solvedAC.mod == addModAC - b)
      assert(solvedAC.a == solvedAC.b * solvedAC.div + solvedAC.mod)
      assert(solvedAC.b > 0)
      assert(addModAC == b + solvedAC.mod)
      assert(solvedA.mod + solvedC.mod == solvedAC.mod + b)
      assert(solvedAC.mod == solvedA.mod + solvedC.mod - b)
      assert(mod(mod(a, b) + mod(c, b), b) == mod(a, b) + mod(c, b) - b)
      assert(div(mod(a, b) + mod(c, b), b) == 1)
    }

    if (solvedAC.div == -1) {
      assert(solvedAC.mod == addModAC + b)
      assert(solvedAC.a == solvedAC.b * solvedAC.div + solvedAC.mod)
      assert(solvedAC.b < 0)
      assert(addModAC == b * -1 + solvedAC.mod)
      assert(addModAC == -b + solvedAC.mod)
      assert(addModAC == solvedAC.mod - b)
      assert(solvedA.mod + solvedC.mod == solvedAC.mod - b)
      assert(solvedAC.mod == solvedA.mod + solvedC.mod + b)
      assert(mod(mod(a, b) + mod(c, b), b) == mod(a, b) + mod(c, b) + b)
      assert(div(mod(a, b) + mod(c, b), b) == -1)
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

    assert(solvedA.isFinal && solvedA.isValid )
    assert(solvedC.isFinal && solvedC.isValid)
    assert(solvedAC.isFinal && solvedAC.isValid)

    assert(solvedA.mod >= 0)
    assert(solvedA.mod < absB)

    assert(solvedC.mod >= 0)
    assert(solvedC.mod < absB)

    assert(subModAC == solvedA.mod - solvedC.mod)
    assert(subModAC <= solvedA.mod)
    assert(subModAC > -absB)

    assert(solvedAC.a == subModAC)
    assert(solvedAC.a > -absB)
    assert(solvedAC.a <= solvedA.mod)
    assert(solvedAC.b == b)
    assert(solvedAC.mod >= 0)
    assert(solvedAC.mod < absB)

    assert(solvedAC.a == solvedAC.b * solvedAC.div + solvedAC.mod)
    assert(solvedAC.div < 2)
    assert(solvedAC.div > -2)
    assert(solvedAC.div == 0 || solvedAC.div == 1 || solvedAC.div == -1)
    if (solvedAC.div == 0) {
      assert(solvedAC.mod == subModAC)
      assert(solvedAC.mod == solvedA.mod - solvedC.mod)
      assert(mod(mod(a, b) - mod(c, b), b) == mod(a, b) - mod(c, b))
      assert(solvedAC.a == solvedAC.b * solvedAC.div + solvedAC.mod)
      assert(solvedAC.a == solvedAC.mod)
      assert(div(mod(a, b) - mod(c, b), b) == 0)
    }
    if (solvedAC.div == 1) {
      assert(solvedAC.mod == subModAC - b)
      assert(solvedAC.a == solvedAC.b * solvedAC.div + solvedAC.mod)
      assert(subModAC == b + solvedAC.mod)
      assert(solvedA.mod - solvedC.mod == solvedAC.mod + b)
      assert(solvedAC.mod == solvedA.mod - solvedC.mod - b)
      assert(mod(mod(a, b) - mod(c, b), b) == mod(a, b) - mod(c, b) - b)
      assert(div(mod(a, b) - mod(c, b), b) == 1)
    }
    if (solvedAC.div == -1) {
      assert(solvedAC.mod == subModAC + b)
      assert(solvedAC.a == solvedAC.b * solvedAC.div + solvedAC.mod)
      assert(subModAC == b * -1 + solvedAC.mod)
      assert(subModAC == -b + solvedAC.mod)
      assert(subModAC == solvedAC.mod - b)
      assert(solvedA.mod - solvedC.mod == solvedAC.mod - b)
      assert(solvedAC.mod == solvedA.mod - solvedC.mod + b)
      assert(mod(mod(a, b) - mod(c, b), b) == mod(a, b) - mod(c, b) + b)
      assert(div(mod(a, b) - mod(c, b), b) == -1)
    }

    mod(mod(a, b) - mod(c, b), b) == mod(a, b) - mod(c, b) - b * div(mod(a, b) - mod(c, b), b)
  }.holds

  def assertDivModWithMoreDivAndLessModSameSolution(a: BigInt, b: BigInt, div: BigInt, mod: BigInt): Boolean = {
    require(b != 0)
    require(div * b + mod == a)
    val div1 = DivMod(a, b, div, mod)
    val div2 = DivMod(a, b, div + 1, mod - b)

    if (div1.isFinal) assert(!div2.isFinal && div2.solve == div1.solve)
    if (div2.isFinal) assert(!div1.isFinal && div1.solve == div2.solve)

    if (div1.mod < 0) {
      assert(div1.solve == div1.increaseMod)
      if (b > 0) {
        equality(
          div2.solve,
          div2.increaseMod,
          div1.increaseMod,
          div1.solve
        )
      } else {
        equality(
          div1.increaseMod,
          div2.solve,
          div1.solve
        )
      }
      assert(div1.solve == div2.solve)
    }
    if (div1.mod > 0 && ! div1.isFinal && ! div2.isFinal) {
      if (b > 0) {
        assert(div2.mod < div1.mod)
        equality(
          div1.solve,
          div1.reduceMod,
          div2.solve
        )
      } else {
        assert(div2.mod > div1.mod)
        equality(
          div2.solve,
          div2.reduceMod,
          div2.solve
        )
      }
    }
    assert(div1.solve == div2.solve)
    DivMod(a,b, div + 1, mod - b).solve == DivMod(a,b, div, mod).solve &&
      DivMod(a,b, div + 1, mod - b).solve.div == DivMod(a,b, div, mod).solve.div &&
      DivMod(a,b, div + 1, mod - b).solve.mod == DivMod(a,b, div, mod).solve.mod
  }.holds

  def assertDivModWithLessDivAndMoreModSameSolution(a: BigInt, b: BigInt, div: BigInt, mod: BigInt): Boolean = {
    require(b != 0)
    require(div * b + mod == a)

    equality(
      a,
      div * b + mod,
      (div - 1) * b + (mod + b)
    )
    assertDivModWithMoreDivAndLessModSameSolution(a, b, div - 1, mod + b)

    DivMod(a, b, div, mod).solve == DivMod(a, b, div - 1, mod + b).solve
  }.holds
}
