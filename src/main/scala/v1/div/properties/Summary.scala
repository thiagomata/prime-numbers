package v1.properties

import stainless.lang.*
import stainless.proof.check
import v1.Calc.{div, mod}
import v1.div.properties.ModOperations
import v1.{Calc, DivMod}

object Summary {
  def PropertySummary(a: BigInt, b: BigInt, c: BigInt, m: BigInt): Boolean = {
    require(b != 0)
    require(m >= 0)

    if (a >= 0 && b > a) {
      check(ModSmallDividend.modSmallDividend(a, b))
      check(ModIdempotence.modIdempotence(a, b))
    }

    check(ModIdentity.modIdentity(b))
    check(AdditionAndMultiplication.APlusBSameModPlusDiv(a, b))
    check(AdditionAndMultiplication.ALessBSameModDecreaseDiv(a, b))
    check(AdditionAndMultiplication.ATimesBSameMod(a, b, m))

    check(AdditionAndMultiplication.ALessMultipleTimesBSameMod(a, b, m))
    check(AdditionAndMultiplication.APlusMultipleTimesBSameMod(a, b, m))

    check(ModOperations.modAdd(a, b, c))
    check(ModOperations.modLess(a, b, c))

//    (if a >= 0 && b > a then div(a,b) == 0 else true)  &&
//    (if a >= 0 && b > a then mod(a,b) == a else true)  &&
//    mod(b, b)         == 0                             &&
//    div(b, b)         == 1                             &&
//    mod(a + b * m, b) == mod(a, b)                     &&
//    mod(a - b * m, b) == mod(a, b)                     &&
//    mod(mod(a, b), b) == mod(a, b)                     &&
//    div(a + b, b)     == div(a, b) + 1                 &&
//    div(a - b, b)     == div(a, b) - 1                 &&
//    div(a + b * m, b) == div(a, b) + m                 &&
//    div(a - b * m, b) == div(a, b) - m                 &&
//    mod(a + c, b)     == mod(mod(a, b) + mod(c, b), b) &&
//    mod(a - c, b)     == mod(mod(a, b) - mod(c, b), b) &&
//    div(a + c, b)     == div(a, b) + div(c, b) + div(mod(a, b) + mod(c, b), b) &&
//    div(a - c, b)     == div(a, b) - div(c, b) + div(mod(a, b) - mod(c, b), b)
    true
  }.holds
}
