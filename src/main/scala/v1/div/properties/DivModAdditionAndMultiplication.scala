package v1.properties

import v1.Calc
import v1.Div
import stainless.lang.*
import stainless.proof.check

object DivModAdditionAndMultiplication {

  def APlusBSameModPlusDiv(a: BigInt, b: BigInt): Boolean = {
    require(b != 0)
    require(a >= 0)

    val input = Div(a, b, 0, a)
    val solved = input.solve

    check(solved.isFinal)
    check(solved.isValid)
    check(solved.a == a)
    check(solved.b == b)
    check(solved.div * solved.b + solved.mod == solved.a)
    check(solved.div * solved.b + solved.mod + solved.b - solved.b == solved.a)
    check(solved.div * solved.b + solved.mod + solved.b == solved.a + solved.b)
    check((solved.div + 1 ) * solved.b + solved.mod == (solved.a + solved.b))

    val next = Div(solved.a + solved.b, solved.b, solved.div + 1, solved.mod)
    check(next.b == b)
    check(next.mod == solved.mod)
    check(next.div == solved.div + 1)
    check(next.isFinal)
    check(next.solve == next)

    check(Calc.mod(a, b) == input.solve.mod)
    check(Calc.div(a, b) == input.solve.div)
    check(Calc.mod(a, b) == solved.mod)
    check(Calc.div(a, b) == solved.div)

    val nextZero = Div(solved.a + solved.b, solved.b, 0, solved.a + solved.b)
    ModIdempotence.modUniqueDiv(next, nextZero)    
    check(Calc.mod(solved.a + solved.b, solved.b) == next.mod)

    check(input.solve.mod == next.mod)
    check(Calc.mod(a, b) == next.mod)
    check(input.solve.div + 1 == next.div)

    Calc.mod(a,b) == Calc.mod(a+b,b) &&
    Calc.div(a,b) + 1 == Calc.div(a+b,b)
  }.holds

  def APlusMultipleTimesBSameMod(a: BigInt, b: BigInt, m: BigInt): Boolean = {
    require(b != 0)
    require(m >= 0)
    require(a >= 0)
    decreases(m)

    APlusBSameModPlusDiv(a, b)
    if (m > 1) {
      check(Calc.mod(a, b) == Calc.mod(a + b, b))
      check(APlusMultipleTimesBSameMod(a + b, b, m - 1))
      check(Calc.mod(a, b) == Calc.mod(a + b * m, b))
      check(Calc.div(a, b) + m == Calc.div(a + b * m, b))
    }

    Calc.mod(a,b) == Calc.mod(a+b*m,b) &&
    Calc.div(a,b) + m == Calc.div(a+b*m,b)
  }.holds


  def MoreDivLessMod(a: BigInt, b: BigInt, div: BigInt, mod: BigInt): Boolean = {
    require(b != 0)
    require(div * b + mod == a)
    val div1 = Div(a, b, div, mod)
    val div2 = Div(a, b, div + 1, mod - b)

    if (div2.isFinal) then check(!div1.isFinal)

    if (div1.isFinal) {
      check(!div2.isFinal)
      check(div2.solve == div1.solve)
    }
    if (div2.isFinal) {
      check(!div1.isFinal)
      check(div1.solve == div2.solve)
    }

    if (div1.mod < 0) {
      check(div1.solve == div1.increaseMod)
      if (b > 0) {
        check(div2.solve == div2.increaseMod)
        check(div2.increaseMod == div1.increaseMod)
        check(div1.solve == div2.solve)
      } else {
        check(div1.increaseMod == div2.solve)
        check(div1.solve == div2.solve)
      }
      check(div1.solve == div2.solve)
    }
    if (div1.mod > 0 && ! div1.isFinal && ! div2.isFinal) {
      if (b > 0 ) {
        check(div2.mod < div1.mod)
        check(div1.solve == div1.reduceMod)
        check(div1.reduceMod == div2.solve)
      } else {
        check(div2.mod > div1.mod)
        check(div2.solve == div2.reduceMod)
        check(div2.reduceMod == div1.solve)
      }
    }
    Div(a,b, div + 1, mod - b).solve.mod == Div(a,b, div, mod).solve.mod
  }.holds

  def LessDivMoreMod(a: BigInt, b: BigInt, div: BigInt, mod: BigInt): Boolean = {
    require(b != 0)
    require(div * b + mod == a)

    check(a == div * b + mod)
    check(a == (div - 1) * b + (mod + b))
    MoreDivLessMod(a, b, div - 1, mod + b)

    Div(a, b, div, mod).solve == Div(a, b, div - 1, mod + b).solve
  }.holds

  def MoreDivLessModManyTimess(a: BigInt, b: BigInt, div: BigInt, mod: BigInt, m: BigInt): Boolean = {
    require(b > 0)
    require(div * b + mod == a)
    require(m >= 1)
    require(a >= 0)
    decreases(m)

    MoreDivLessMod(a, b, div, mod)

    val finalDiv = div + m
    val finalMod = mod - m * b

    if (m > 1) {
      val prevDiv = div + m - 1
      val prevMod = mod - m * b + b

      MoreDivLessMod(a, b, prevDiv, prevMod)

      check(Div(a, b, prevDiv, prevMod).solve == Div(a, b, finalDiv, finalMod).solve)
      check(MoreDivLessModManyTimess(a, b, div, mod, m - 1))

      check(Div(a, b, finalDiv, finalMod).solve == Div(a, b, div, mod).solve)
    }

    Div(a, b, finalDiv, finalMod).solve == Div(a, b, div, mod).solve
  }.holds

  def LessDivMoreModManyTimes(a: BigInt, b: BigInt, div: BigInt, mod: BigInt, m: BigInt): Boolean = {
    require(b != 0)
    require(div * b + mod == a)
    require(m > 0)
    decreases(m)

    LessDivMoreMod(a, b, div, mod)
    if (m > 1) {
      LessDivMoreModManyTimes(a, b, div - 1, mod + b, m - 1)
      check(Div(a, b, div - 1, mod + b).solve == Div(a, b, div, mod).solve)
    }
    Div(a, b, div - m, mod + m*b).solve == Div(a, b, div, mod).solve
  }.holds
}

