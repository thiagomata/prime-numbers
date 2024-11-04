package v1.properties

import stainless.lang.*
import stainless.proof.check
import v1.div.properties.ModOperations
import v1.{Calc, DivMod}

object Summary {
  def PropertySummary(a: BigInt, b: BigInt, c: BigInt, m: BigInt): Boolean = {
    require(b != 0)
    require(m >= 0)

    if (a >= 0 && b > a ) {
      check(b != 0)
      check(b > a)
      check(a >= 0)
      check(ModSmallDividend.modSmallDividend(a, b))
      check(ModIdempotence.modIdempotence(a, b))
      check(Calc.mod(a, b) == a)
      check(Calc.div(a, b) == 0)
    }

    check(ModIdentity.modIdentity(b))
    check(Calc.mod(b, b) == 0)
    check(Calc.div(b, b) == 1)

    check(AdditionAndMultiplication.APlusBSameModPlusDiv(a, b))
    check(AdditionAndMultiplication.ALessBSameModDecreaseDiv(a, b))
    check(AdditionAndMultiplication.ATimesBSameMod(a, b, m))

    check(b != 0)
    check(m >= 0)
    check(AdditionAndMultiplication.ALessMultipleTimesBSameMod(a, b, m))
    check(AdditionAndMultiplication.APlusMultipleTimesBSameMod(a, b, m))
    check(Calc.mod( a + b * m, b ) == Calc.mod( a, b ))

    check(b != 0)
    check(ModOperations.modAdd(a, b, c))
    check(Calc.div(a + c, b) == Calc.div(a, b) + Calc.div(c, b) + Calc.div(Calc.mod(a, b) + Calc.mod(c, b), b))
    check(Calc.mod(a + c, b) == Calc.mod(Calc.mod(a, b) + Calc.mod(c, b), b))

    check(ModOperations.modLess(a, b, c))
    check(Calc.mod(a - c, b) == Calc.mod(Calc.mod(a, b) - Calc.mod(c, b), b))
    check(Calc.div(a - c, b) == Calc.div(a, b) - Calc.div(c, b) + Calc.div(Calc.mod(a, b) - Calc.mod(c, b), b))


    ( if a >= 0 && b > a then Calc.div(a,b) == 0 else true )           &&
    ( if a >= 0 && b > a then Calc.mod(a,b) == a else true )           &&
    Calc.mod( b, b )     == 0                                          &&
    Calc.div( b, b )     == 1                                          &&
    Calc.mod( a + b * m, b ) == Calc.mod( a, b )                       &&
    Calc.mod( a - b * m, b ) == Calc.mod( a, b )                       &&
    Calc.mod(Calc.mod(a, b), b) == Calc.mod( a, b )                    &&
    Calc.div( a + b, b ) == Calc.div( a, b ) + 1                       &&
    Calc.div( a - b, b ) == Calc.div( a, b ) - 1                       &&
    Calc.div( a + b * m, b ) == Calc.div( a, b ) + m                   &&
    Calc.div( a - b * m, b ) == Calc.div( a, b ) - m                   &&
    Calc.mod(a + c, b) == Calc.mod(Calc.mod(a, b) + Calc.mod(c, b), b) &&
    Calc.mod(a - c, b) == Calc.mod(Calc.mod(a, b) - Calc.mod(c, b), b) &&
    Calc.div(a + c, b) == Calc.div(a, b) + Calc.div(c, b) + Calc.div(Calc.mod(a, b) + Calc.mod(c, b), b) &&
    Calc.div(a - c, b) == Calc.div(a, b) - Calc.div(c, b) + Calc.div(Calc.mod(a, b) - Calc.mod(c, b), b)
  }.holds
}
