package v1.div.properties

import stainless.lang.*
import v1.Calc
import v1.div.DivMod
import verification.Helper.{assert, equality}

object AdditionAndMultiplication {

  /**
   * Increasing the dividend by the divisor should increase the quotient by 1
   * and the remainder should be the same.
   * 
   * In other words:
   * if a == div * b + mod then a + b == (div + 1) * b + mod
   * 
   * Therefore:
   * div(a, b) + 1 == div(a + b, b)
   * mod(a, b) == mod(a + b, b) 
   * 
   * @param a BigInt Dividend
   * @param b BigInt Divisor
   * @return Boolean True if the property holds
   */ 
  def APlusBSameModPlusDiv(a: BigInt, b: BigInt): Boolean = {
    require(b != 0)

    val input = DivMod(a, b, 0, a)
    val solved = input.solve

    assert(solved.isFinal)
    assert(solved.isValid)
    assert(solved.a == a)
    assert(solved.b == b)
    assert(solved.div * solved.b + solved.mod == solved.a)
    assert(solved.div * solved.b + solved.mod + solved.b - solved.b == solved.a)
    assert(solved.div * solved.b + solved.mod + solved.b == solved.a + solved.b)
    assert((solved.div + 1 ) * solved.b + solved.mod == (solved.a + solved.b))

    val next = DivMod(solved.a + solved.b, solved.b, solved.div + 1, solved.mod)
    assert(next.b == b)
    assert(next.mod == solved.mod)
    assert(next.div == solved.div + 1)
    assert(next.isFinal)
    assert(next.solve == next)

    equality(
      Calc.mod(a, b), //  is equals to
      input.solve.mod, // is equals to
      solved.mod
    )

    equality(
      Calc.div(a, b), //  is equals to
      input.solve.div, // is equals to
      solved.div
    )

    val nextZero = DivMod(solved.a + solved.b, solved.b, 0, solved.a + solved.b)
    ModIdempotence.modUniqueDiv(next, nextZero)    
    assert(Calc.mod(solved.a + solved.b, solved.b) == next.mod)
    assert(solved.a == a)
    assert(solved.b == b)
    assert(Calc.mod(a + b, b) == next.mod)

    equality(
      input.solve.mod, //                      is equals to
      next.mod, //                             is equals to
      next.solve.mod, //                       is equals to
      nextZero.solve.mod, //                   is equals to
      DivMod(a + b, b, 0, a + b).solve.mod, // is equals to
      Calc.mod(a + b, b), //                   is equals to
      Calc.mod(a, b)
    )

    val sameMod = Calc.mod(a, b) == Calc.mod(a + b, b)
    assert(Calc.mod(a, b) == Calc.mod(a + b, b))

    assert(input.solve.div + 1 == next.div)
    assert(Calc.div(a, b) + 1 == Calc.div(a + b, b))
    val nextDiv = Calc.div(a, b) + 1 == Calc.div(a + b, b)


    sameMod && nextDiv
  }.holds

  /**
    * Decreasing the dividend by the divisor should decrease the quotient by 1
    * and the remainder should be the same.
    * 
    * In other words:
    * if a == div * b + mod then a - b == (div - 1) * b + mod
    *
    * Therefore:
    * div(a, b) - 1 == div(a - b, b)
    * mod(a, b) == mod(a - b, b)
    *
   * @param a BigInt Dividend
   * @param b BigInt Divisor
   * @return Boolean True if the property holds
    */
  def ALessBSameModDecreaseDiv(a: BigInt, b: BigInt): Boolean = {
    require(b != 0)

    val input = DivMod(a, b, 0, a)
    val solved = input.solve

    assert(solved.isFinal)
    assert(solved.isValid)
    assert(solved.a == a)
    assert(solved.b == b)
    assert(solved.div * solved.b + solved.mod == solved.a)
    assert(solved.div * solved.b + solved.mod + solved.b - solved.b == solved.a)
    assert(solved.div * solved.b + solved.mod - solved.b == solved.a - solved.b)
    assert((solved.div - 1 ) * solved.b + solved.mod == (solved.a - solved.b))

    val next = DivMod(solved.a - solved.b, solved.b, solved.div - 1, solved.mod)
    assert(next.b == b)
    assert(next.mod == solved.mod)
    assert(next.div == solved.div - 1)
    assert(next.isFinal)
    assert(next.solve == next)

    equality(
      Calc.mod(a, b), //  is equals to
      input.solve.mod, // is equals to
      solved.mod
    )
    equality(
      Calc.div(a, b), //  is equals to
      input.solve.div, // is equals to
      solved.div
    )

    val nextZero = DivMod(solved.a - solved.b, solved.b, 0, solved.a - solved.b)
    ModIdempotence.modUniqueDiv(next, nextZero)

    equality(
      input.solve.mod, //                      is equals to
      next.solve.mod, //                       is equals to
      DivMod(a - b, b, 0, a - b).solve.mod, // is equals to
      nextZero.solve.mod, //                   is equals to
      Calc.mod(a,b), //                        is equals to
      Calc.mod(a - b, b)
    )

    assert(Calc.mod(a, b) == Calc.mod(a - b, b))
    val sameMod = Calc.mod(a, b) == Calc.mod(a - b, b)

    assert(input.solve.div - 1 == next.div)
    val nextDiv = Calc.div(a, b) - 1 == Calc.div(a - b, b)

    sameMod && nextDiv

  }.holds

  /**
   * Multiplying the dividend by any integer m should not change the
   * remainder and the quotient should be increased by m.
   * 
   * In other words:
   * if a == div * b + mod then a * m == (div + m) * b + mod
   *
   * Therefore:
   * div(a + b * m, b) == div(a, b) + m
   * mod(a + b * m, b) == mod(a, b)
   * div(a - b * m, b) == div(a, b) - m
   * mod(a - b * m, b) == mod(a, b)
   *
   * @param a BigInt Dividend
   * @param b BigInt Divisor
   * @return Boolean True if the property holds
   */
  def ATimesBSameMod(a: BigInt, b: BigInt, m: BigInt): Boolean = {
    require(b != 0)
    if (m >= 0) {
      assert(m >= 0)
      assert(APlusMultipleTimesBSameMod(a, b, m))
    } else {
      assert(-m >= 0)
      assert(ALessMultipleTimesBSameMod(a, b, -m))
    }
    Calc.mod(a, b) == Calc.mod(a + b * m, b) &&
      Calc.div(a, b) + m == Calc.div(a + b * m, b)
  }.holds

  /**
   * Multiplying the dividend by any positive m should not change the
   * remainder and the quotient should be increased by m.
   * 
   * In other words:
   * if a == div * b + mod then a + b * m == (div + m) * b + mod
   * 
   * Therefore:
   *
   * div(a + b * m, b) == div(a, b) + m
   * mod(a + b * m, b) == mod(a, b)
   *
   * @param a BigInt Dividend
   * @param b BigInt Divisor
   * @return Boolean True if the property holds
   */
  def APlusMultipleTimesBSameMod(a: BigInt, b: BigInt, m: BigInt): Boolean = {
    require(b != 0)
    require(m >= 0)
    decreases(m)

    if (m >= 1) {
      APlusBSameModPlusDiv(a, b)
      assert(Calc.mod(a, b) == Calc.mod(a + b, b))
      assert(APlusMultipleTimesBSameMod(a + b, b, m - 1))
      assert(Calc.mod(a, b) == Calc.mod(a + b * m, b))
      assert(Calc.div(a, b) + m == Calc.div(a + b * m, b))
    }

    Calc.mod(a, b) == Calc.mod(a + b * m, b) &&
    Calc.div(a, b) + m == Calc.div( a + b * m, b)
  }.holds

  /**
   * Subtracting the dividend by any positive integer m should not change the
   * remainder and the quotient should be decreased by m.
   *
   * In other words:
   * if a == div * b + mod then a - b * m == (div - m) * b + mod
   *
   * Therefore:
   * div(a, b) - m == div(a - m * b, b)
   * mod(a, b) == mod(a - m * b, b)
   *
   * @param a BigInt Dividend
   * @param b BigInt Divisor
   * @return Boolean True if the property holds
   */
  def ALessMultipleTimesBSameMod(a: BigInt, b: BigInt, m: BigInt): Boolean = {
    require(b != 0)
    require(m >= 0)

    decreases(m)

    if (m >= 1) {
      ALessBSameModDecreaseDiv(a, b)
      assert(Calc.mod(a, b) == Calc.mod(a - b, b))
      assert(ALessMultipleTimesBSameMod(a - b, b, m - 1))
      assert(Calc.mod(a, b) == Calc.mod(a - b * m, b))
      assert(Calc.div(a, b) - m == Calc.div(a - b * m, b))
    }

    Calc.mod(a,b) == Calc.mod(a-b*m,b) &&
      Calc.div(a,b) - m == Calc.div(a-b*m,b)
  }.holds

  /**
   * Increasing the quotient (div) by 1 and decreasing the remainder (mod) by
   * b yields the same solution.
   *
   * In other words:
   *
   * a == div * b + mod == (div + 1) * b + ( mod − b )
   * DivMod(a, b, div + 1, mod - b).solve == DivMod(a, b, div, mod).solve
   *
   * @param a BigInt Dividend
   * @param b BigInt Divisor
   * @param div BigInt Quotient
   * @param mod BigInt Remainder
   * @return Boolean True if the property holds
   */
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
          div2.solve, //       is equals to
          div2.increaseMod, // is equals to
          div1.increaseMod, // is equals to
          div1.solve
        )
      } else {
        equality(
          div1.increaseMod, // is equals to
          div2.solve, //       is equals to
          div1.solve
        )
      }
      assert(div1.solve == div2.solve)
    }
    if (div1.mod > 0 && ! div1.isFinal && ! div2.isFinal) {
      if (b > 0 ) {
        assert(div2.mod < div1.mod)
        equality(
          div1.solve, //       is equals to
          div1.reduceMod, //   is equals to
          div2.solve
        )
      } else {
        assert(div2.mod > div1.mod)
        equality(
          div2.solve, //     is equals to
          div2.reduceMod, // is equals to
          div2.solve
        )
      }
    }
    assert(div1.solve == div2.solve)
    DivMod(a,b, div + 1, mod - b).solve == DivMod(a,b, div, mod).solve &&
      DivMod(a,b, div + 1, mod - b).solve.div == DivMod(a,b, div, mod).solve.div &&
      DivMod(a,b, div + 1, mod - b).solve.mod == DivMod(a,b, div, mod).solve.mod
  }.holds

  /**
   * Decreasing the quotient (div) by 1 and increasing the remainder (mod) by
   * b yields the same solution
   *
   * In other words:
   *
   * a == div * b + mod == (div - 1) * b + ( mod + b )
   * DivMod(a,b, div - 1, mod + b).solve == DivMod(a, b, div, mod).solve
   *
   * @param a BigInt Dividend
   * @param b BigInt Divisor
   * @param div BigInt Quotient
   * @param mod BigInt Remainder
   * @return Boolean True if the property holds
   */
  def assertDivModWithLessDivAndMoreModSameSolution(a: BigInt, b: BigInt, div: BigInt, mod: BigInt): Boolean = {
    require(b != 0)
    require(div * b + mod == a)

    equality(
      a,                         // is equals to
      div * b + mod,             // is equals to
      (div - 1) * b + (mod + b)
    )
    assertDivModWithMoreDivAndLessModSameSolution(a, b, div - 1, mod + b)

    DivMod(a, b, div, mod).solve == DivMod(a, b, div - 1, mod + b).solve
  }.holds

  /**
   * Any valid DivMod with the same Dividend and Divisor will generate the same solution.
   *
   * if DivMod(a, b, div1, mod1) is valid and DivMod(a, b, div2, mod2) is also valid
   * where div1 is equals to div2 + m and and mod1 = mod2 - m * b
   * then DivMod(a, b, div1.mod1).solve is equals to DivMod(a, b, div2.mod2).solve
   *
   * @param a Dividend
   * @param b Divisor
   * @param div Quotient
   * @param mod Remainder
   * @param m Multipler
   * @return Boolean true if the property holds
   */
  def MoreDivLessModManyTimes(a: BigInt, b: BigInt, div: BigInt, mod: BigInt, m: BigInt): Boolean = {
    require(b > 0)
    require(div * b + mod == a)
    require(m >= 1)
    decreases(m)

    assertDivModWithMoreDivAndLessModSameSolution(a, b, div, mod)

    val finalDiv = div + m
    val finalMod = mod - m * b

    if (m > 1) {
      val prevDiv = div + m - 1
      val prevMod = mod - m * b + b

      assertDivModWithMoreDivAndLessModSameSolution(a, b, prevDiv, prevMod)

      assert(DivMod(a, b, prevDiv, prevMod).solve == DivMod(a, b, finalDiv, finalMod).solve)
      assert(MoreDivLessModManyTimes(a, b, div, mod, m - 1))

      assert(DivMod(a, b, finalDiv, finalMod).solve == DivMod(a, b, div, mod).solve)
    }

    DivMod(a, b, finalDiv, finalMod).solve == DivMod(a, b, div, mod).solve
  }.holds


  /**
   * Any valid DivMod with the same Dividend and Divisor will generate the same solution.
   *
   * if DivMod(a, b, div1, mod1) is valid and DivMod(a, b, div2, mod2) is also valid
   * where div1 is equals to div2 - m and and mod1 = mod2 + m * b
   * then DivMod(a, b, div1.mod1).solve is equals to DivMod(a, b, div2.mod2).solve
   *
   * @param a Dividend
   * @param b Divisor
   * @param div Quotient
   * @param mod Remainder
   * @param m Multipler
   * @return Boolean true if the property holds
   */
  def LessDivMoreModManyTimes(a: BigInt, b: BigInt, div: BigInt, mod: BigInt, m: BigInt): Boolean = {
    require(b != 0)
    require(div * b + mod == a)
    require(m > 0)
    decreases(m)

    assertDivModWithLessDivAndMoreModSameSolution(a, b, div, mod)
    if (m > 1) {
      LessDivMoreModManyTimes(a, b, div - 1, mod + b, m - 1)
      assert(DivMod(a, b, div - 1, mod + b).solve == DivMod(a, b, div, mod).solve)
    }
    DivMod(a, b, div - m, mod + m * b).solve == DivMod(a, b, div, mod).solve
  }.holds
}

