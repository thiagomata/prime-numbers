package v1.div.properties

import stainless.lang.*
import stainless.proof.check
import v1.Calc
import v1.div.DivMod
import verification.Helper.equality

object AdditionAndMultiplication {

  def APlusBSameModPlusDiv(a: BigInt, b: BigInt): Boolean = {
    require(b != 0)

    val input = DivMod(a, b, 0, a)
    val solved = input.solve

    check(solved.isFinal)
    check(solved.isValid)
    check(solved.a == a)
    check(solved.b == b)
    check(solved.div * solved.b + solved.mod == solved.a)
    check(solved.div * solved.b + solved.mod + solved.b - solved.b == solved.a)
    check(solved.div * solved.b + solved.mod + solved.b == solved.a + solved.b)
    check((solved.div + 1 ) * solved.b + solved.mod == (solved.a + solved.b))

    val next = DivMod(solved.a + solved.b, solved.b, solved.div + 1, solved.mod)
    check(next.b == b)
    check(next.mod == solved.mod)
    check(next.div == solved.div + 1)
    check(next.isFinal)
    check(next.solve == next)

    check(
      equality(
        Calc.mod(a, b), //  is equals to
        input.solve.mod, // is equals to
        solved.mod
      )
    )

    check(
      equality(
        Calc.div(a, b), //  is equals to
        input.solve.div, // is equals to
        solved.div
      )
    )

    val nextZero = DivMod(solved.a + solved.b, solved.b, 0, solved.a + solved.b)
    ModIdempotence.modUniqueDiv(next, nextZero)    
    check(Calc.mod(solved.a + solved.b, solved.b) == next.mod)
    check(solved.a == a)
    check(solved.b == b)
    check(Calc.mod(a + b, b) == next.mod)

    check(
      equality(
        input.solve.mod, //                      is equals to
        next.mod, //                             is equals to
        next.solve.mod, //                       is equals to
        nextZero.solve.mod, //                   is equals to
        DivMod(a + b, b, 0, a + b).solve.mod, // is equals to
        Calc.mod(a + b, b), //                   is equals to
        Calc.mod(a, b)
      )
    )

    val sameMod = Calc.mod(a, b) == Calc.mod(a + b, b)
    check(Calc.mod(a, b) == Calc.mod(a + b, b))

    check(input.solve.div + 1 == next.div)
    check(Calc.div(a, b) + 1 == Calc.div(a + b, b))
    val nextDiv = Calc.div(a, b) + 1 == Calc.div(a + b, b)


    sameMod && nextDiv
  }.holds

  def ALessBSameModDecreaseDiv(a: BigInt, b: BigInt): Boolean = {
    require(b != 0)

    val input = DivMod(a, b, 0, a)
    val solved = input.solve

    check(solved.isFinal)
    check(solved.isValid)
    check(solved.a == a)
    check(solved.b == b)
    check(solved.div * solved.b + solved.mod == solved.a)
    check(solved.div * solved.b + solved.mod + solved.b - solved.b == solved.a)
    check(solved.div * solved.b + solved.mod - solved.b == solved.a - solved.b)
    check((solved.div - 1 ) * solved.b + solved.mod == (solved.a - solved.b))

    val next = DivMod(solved.a - solved.b, solved.b, solved.div - 1, solved.mod)
    check(next.b == b)
    check(next.mod == solved.mod)
    check(next.div == solved.div - 1)
    check(next.isFinal)
    check(next.solve == next)

    check(
      equality(
        Calc.mod(a, b), //  is equals to
        input.solve.mod, // is equals to
        solved.mod
      )
    )
    check(
      equality(
        Calc.div(a, b), //  is equals to
        input.solve.div, // is equals to
        solved.div
      )
    )

    val nextZero = DivMod(solved.a - solved.b, solved.b, 0, solved.a - solved.b)
    ModIdempotence.modUniqueDiv(next, nextZero)

    check(
      equality(
        input.solve.mod, //                      is equals to
        next.solve.mod, //                       is equals to
        DivMod(a - b, b, 0, a - b).solve.mod, // is equals to
        nextZero.solve.mod, //                   is equals to
        Calc.mod(a,b), //                        is equals to
        Calc.mod(a - b, b)
      )
    )

    check(Calc.mod(a, b) == Calc.mod(a - b, b))
    val sameMod = Calc.mod(a, b) == Calc.mod(a - b, b)

    check(input.solve.div - 1 == next.div)
    val nextDiv = Calc.div(a, b) - 1 == Calc.div(a - b, b)

    sameMod && nextDiv

  }.holds

  def ATimesBSameMod(a: BigInt, b: BigInt, m: BigInt): Boolean = {
    require(b != 0)
    if (m >= 0) {
      check(m >= 0)
      check(APlusMultipleTimesBSameMod(a, b, m))
    } else {
      check(-m >= 0)
      check(ALessMultipleTimesBSameMod(a, b, -m))
    }
    Calc.mod(a, b) == Calc.mod(a + b * m, b) &&
      Calc.div(a, b) + m == Calc.div(a + b * m, b)
  }.holds

  def APlusMultipleTimesBSameMod(a: BigInt, b: BigInt, m: BigInt): Boolean = {
    require(b != 0)
    require(m >= 0)
    decreases(m)

    if (m >= 1) {
      APlusBSameModPlusDiv(a, b)
      check(Calc.mod(a, b) == Calc.mod(a + b, b))
      check(APlusMultipleTimesBSameMod(a + b, b, m - 1))
      check(Calc.mod(a, b) == Calc.mod(a + b * m, b))
      check(Calc.div(a, b) + m == Calc.div(a + b * m, b))
    }

    Calc.mod(a,b) == Calc.mod(a+b*m,b) &&
    Calc.div(a,b) + m == Calc.div(a+b*m,b)
  }.holds

  def ALessMultipleTimesBSameMod(a: BigInt, b: BigInt, m: BigInt): Boolean = {
    require(b != 0)
    require(m >= 0)

    decreases(m)

    if (m >= 1) {
      ALessBSameModDecreaseDiv(a, b)
      check(Calc.mod(a, b) == Calc.mod(a - b, b))
      check(ALessMultipleTimesBSameMod(a - b, b, m - 1))
      check(Calc.mod(a, b) == Calc.mod(a - b * m, b))
      check(Calc.div(a, b) - m == Calc.div(a - b * m, b))
    }

    Calc.mod(a,b) == Calc.mod(a-b*m,b) &&
      Calc.div(a,b) - m == Calc.div(a-b*m,b)
  }.holds

  def MoreDivLessMod(a: BigInt, b: BigInt, div: BigInt, mod: BigInt): Boolean = {
    require(b != 0)
    require(div * b + mod == a)
    val div1 = DivMod(a, b, div, mod)
    val div2 = DivMod(a, b, div + 1, mod - b)

    if (div1.isFinal) check(!div2.isFinal && div2.solve == div1.solve)
    if (div2.isFinal) check(!div1.isFinal && div1.solve == div2.solve)

    if (div1.mod < 0) {
      check(div1.solve == div1.increaseMod)
      if (b > 0) {
        check(
          equality(
            div2.solve, //       is equals to
            div2.increaseMod, // is equals to
            div1.increaseMod, // is equals to
            div1.solve
          )
        )
      } else {
        check(
          equality(
            div1.increaseMod, // is equals to
            div2.solve, //       is equals to
            div1.solve
          )
        )
      }
      check(div1.solve == div2.solve)
    }
    if (div1.mod > 0 && ! div1.isFinal && ! div2.isFinal) {
      if (b > 0 ) {
        check(div2.mod < div1.mod)
        check(
          equality(
            div1.solve, //       is equals to
            div1.reduceMod, //   is equals to
            div2.solve
          )
        )
      } else {
        check(div2.mod > div1.mod)
        check(
          equality(
            div2.solve, //     is equals to
            div2.reduceMod, // is equals to
            div2.solve
          )
        )
      }
    }
    check(div1.solve == div2.solve)
    DivMod(a,b, div + 1, mod - b).solve.mod == DivMod(a,b, div, mod).solve.mod
  }.holds

  def LessDivMoreMod(a: BigInt, b: BigInt, div: BigInt, mod: BigInt): Boolean = {
    require(b != 0)
    require(div * b + mod == a)

    check(
      equality(
        a,                         // is equals to
        div * b + mod,             // is equals to
        (div - 1) * b + (mod + b)
      )
    )
    MoreDivLessMod(a, b, div - 1, mod + b)

    DivMod(a, b, div, mod).solve == DivMod(a, b, div - 1, mod + b).solve
  }.holds

  def MoreDivLessModManyTimes(a: BigInt, b: BigInt, div: BigInt, mod: BigInt, m: BigInt): Boolean = {
    require(b > 0)
    require(div * b + mod == a)
    require(m >= 1)
    decreases(m)

    MoreDivLessMod(a, b, div, mod)

    val finalDiv = div + m
    val finalMod = mod - m * b

    if (m > 1) {
      val prevDiv = div + m - 1
      val prevMod = mod - m * b + b

      MoreDivLessMod(a, b, prevDiv, prevMod)

      check(DivMod(a, b, prevDiv, prevMod).solve == DivMod(a, b, finalDiv, finalMod).solve)
      check(MoreDivLessModManyTimes(a, b, div, mod, m - 1))

      check(DivMod(a, b, finalDiv, finalMod).solve == DivMod(a, b, div, mod).solve)
    }

    DivMod(a, b, finalDiv, finalMod).solve == DivMod(a, b, div, mod).solve
  }.holds

  def LessDivMoreModManyTimes(a: BigInt, b: BigInt, div: BigInt, mod: BigInt, m: BigInt): Boolean = {
    require(b != 0)
    require(div * b + mod == a)
    require(m > 0)
    decreases(m)

    LessDivMoreMod(a, b, div, mod)
    if (m > 1) {
      LessDivMoreModManyTimes(a, b, div - 1, mod + b, m - 1)
      check(DivMod(a, b, div - 1, mod + b).solve == DivMod(a, b, div, mod).solve)
    }
    DivMod(a, b, div - m, mod + m*b).solve == DivMod(a, b, div, mod).solve
  }.holds
}

