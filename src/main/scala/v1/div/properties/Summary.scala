package v1.div.properties

import stainless.lang.*
import v1.Calc
import v1.Calc.{div, mod}
import verification.Helper.assert

object Summary {
  def PropertySummary(a: BigInt, b: BigInt, c: BigInt, m: BigInt): Boolean = {
    require(b != 0)
    require(m >= 0)

    if (a >= 0 && b > a) {
      assert(ModSmallDividend.modSmallDividend(a, b))
    }

    assert(ModIdempotence.modIdempotence(a, b))
    assert(ModIdentity.modIdentity(b))
    assert(AdditionAndMultiplication.APlusBSameModPlusDiv(a, b))
    assert(AdditionAndMultiplication.ALessBSameModDecreaseDiv(a, b))
    assert(AdditionAndMultiplication.ATimesBSameMod(a, b, m))

    assert(AdditionAndMultiplication.ALessMultipleTimesBSameMod(a, b, m))
    assert(AdditionAndMultiplication.APlusMultipleTimesBSameMod(a, b, m))

    assert(ModOperations.modAdd(a, b, c))
    assert(ModOperations.modLess(a, b, c))

    assert(ModIdempotence.modModPlus(a, b, c))
    assert(ModIdempotence.modModMinus(a, b, c))

    assert(if  a >= 0 && b > 0 then ModOperations.addOne(a, b) else true)

    assert(mod(a + c, b) == mod(mod(a, b) + mod(c, b), b))
    assert(mod(a - c, b) == mod(mod(a, b) - mod(c, b), b))
    assert(if a >= 0 && b > a then div(a,b) == 0 else true)
    assert(if a >= 0 && b > a then mod(a,b) == a else true)
    assert(if b > 0 then mod(mod(a, b), b) == mod(a, b) else true)
    assert(mod(b, b)         == 0)
    assert(div(b, b)         == 1)
    assert(mod(a + b * m, b) == mod(a, b))
    assert(mod(a - b * m, b) == mod(a, b))
    assert(div(a + b, b)     == div(a, b) + 1)
    assert(div(a - b, b)     == div(a, b) - 1)
    assert(div(a + b * m, b) == div(a, b) + m)
    assert(div(a - b * m, b) == div(a, b) - m)
    assert(div(a + c, b)     == div(a, b) + div(c, b) + div(mod(a, b) + mod(c, b), b))
    assert(div(a - c, b)     == div(a, b) - div(c, b) + div(mod(a, b) - mod(c, b), b))
    assert(mod(a + c, b)     == mod(mod(a, b) + mod(c, b), b))
    assert(mod(a - c, b)     == mod(mod(a, b) - mod(c, b), b))
    assert(mod(a + c, b)     == mod(a, b) + mod(c, b) - b * div(mod(a, b) + mod(c, b), b))
    assert(mod(a - c, b)     == mod(a, b) - mod(c, b) - b * div(mod(a, b) - mod(c, b), b))
    assert(if a >= 0 && b > 0 && mod(a, b) != b - 1 then mod(a + 1, b) == mod(a, b) + 1 else true)
    assert(if a >= 0 && b > 0 && mod(a, b) == b - 1 then mod(a + 1, b) == 0 else true)
    assert(if a >= 0 && b > 0 && mod(a, b) != b - 1 then div(a + 1, b) == div(a, b) else true)
    assert(if a >= 0 && b > 0 && mod(a, b) == b - 1 then div(a + 1, b) == div(a, b) + 1 else true)

    (if a >= 0 && b > a then div(a,b) == 0 else true)  &&
    (if a >= 0 && b > a then mod(a,b) == a else true)  &&
    mod(b, b)         == 0                             &&
    div(b, b)         == 1                             &&
    mod(a + b * m, b) == mod(a, b)                     &&
    mod(a - b * m, b) == mod(a, b)                     &&
    mod(mod(a, b), b) == mod(a, b)                     &&
    div(a + b, b)     == div(a, b) + 1                 &&
    div(a - b, b)     == div(a, b) - 1                 &&
    div(a + b * m, b) == div(a, b) + m                 &&
    div(a - b * m, b) == div(a, b) - m                 &&
    div(a + c, b)     == div(a, b) + div(c, b) + div(mod(a, b) + mod(c, b), b)     &&
    div(a - c, b)     == div(a, b) - div(c, b) + div(mod(a, b) - mod(c, b), b)     &&
    mod(a + c, b)     == mod(mod(a, b) + mod(c, b), b)                             &&
    mod(a - c, b)     == mod(mod(a, b) - mod(c, b), b)                             &&
    mod(a + c, b)     == mod(a, b) + mod(c, b) - b * div(mod(a, b) + mod(c, b), b) &&
    mod(a - c, b)     == mod(a, b) - mod(c, b) - b * div(mod(a, b) - mod(c, b), b) &&
    (if a >= 0 && b > 0 && mod(a, b) != b - 1 then mod(a + 1, b) == mod(a, b) + 1 else true) &&
    (if a >= 0 && b > 0 && mod(a, b) == b - 1 then mod(a + 1, b) == 0 else true) &&
    (if a >= 0 && b > 0 && mod(a, b) != b - 1 then div(a + 1, b) == div(a, b) else true) &&
    (if a >= 0 && b > 0 && mod(a, b) == b - 1 then div(a + 1, b) == div(a, b) + 1 else true)
  }.holds
}
