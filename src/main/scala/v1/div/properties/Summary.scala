package v1.properties

import stainless.lang.*
import stainless.proof.check
import v1.{Calc, DivMod}

object Summary {
  def PropertySummary(a: BigInt, b: BigInt, m: BigInt): Boolean = {
    require(a >= 0)
    require(b != 0)
    require(m >= 1)

    if (b > a ) {
      check(ModSmallDividend.modSmallDividend(a, b))
      Calc.mod(b, b) == 0
    }

    if (a > 0) {
      check(ModIdentity.modIdentity(a))
      Calc.mod(a, a) == 0
    }

    check(AdditionAndMultiplication.APlusBSameModPlusDiv(a, b))
    check(Calc.div(a,b) + 1 == Calc.div(a+b,b))

    check(AdditionAndMultiplication.ATimesBSameMod(a, b, m))
    check(Calc.mod(a,b) == Calc.mod(a+b*m,b))
    check(Calc.div(a,b) + m == Calc.div(a+b*m,b))

    true
  }.holds

  def DivSummary(a: BigInt, b: BigInt, div: BigInt, mod: BigInt) = {
    require(b != 0)
    require(div * b + mod == a)

    AdditionAndMultiplication.MoreDivLessMod(a, b, div, mod)
    AdditionAndMultiplication.LessDivMoreMod(a, b, div, mod)

    check(DivMod(a, b, div, mod).solve == DivMod(a, b, div + 1, mod - b).solve)
    check(DivMod(a, b, div, mod).solve == DivMod(a, b, div - 1, mod + b).solve)

    true
  }
}
