package v1.div.properties

import stainless.lang.*
import v1.Calc
import v1.Calc.{div, mod}
import v1.div.DivMod
import v1.div.properties.ModIdempotence.modUniqueDiv
import verification.Helper
import verification.Helper.{assert, equality}

object ModOperations {

  def modAdd(a: BigInt, b: BigInt, c: BigInt): Boolean = {
    require(b != 0)

    val x = DivMod(a, b, 0, a)
    val solvedX = x.solve
    assert(solvedX.isFinal && solvedX.isValid)
    assert(solvedX.mod < x.absB)
    assert(solvedX.a == a)
    assert(solvedX.b == b)
    assert(solvedX.a == solvedX.b * solvedX.div + solvedX.mod)
    assert(solvedX.a - solvedX.b * solvedX.div == solvedX.mod)

    val y = DivMod(c, b, 0, c)
    val solvedY = y.solve
    assert(solvedY.isFinal && solvedY.isValid)
    assert(solvedY.mod < x.absB)
    assert(solvedY.a == c)
    assert(solvedY.b == b)
    assert(solvedY.a == solvedY.b * solvedY.div + solvedY.mod)
    assert(solvedY.a - solvedY.b * solvedY.div == solvedY.mod)

    val xy = DivMod(a + c, b, 0, a + c)
    val solvedXY = xy.solve
    assert(solvedXY.isFinal && solvedXY.isValid)
    assert(solvedXY.mod < x.absB)
    assert(solvedXY.a == a + c)
    assert(solvedXY.b == b)
    assert(solvedXY.a == solvedXY.b * solvedXY.div + solvedXY.mod)
    assert(a + c == b * solvedXY.div + solvedXY.mod)

    val z = DivMod(solvedX.mod + solvedY.mod, b, 0, solvedX.mod + solvedY.mod)
    assert(z.a == z.b * z.div + z.mod)
    assert(z.a == solvedX.mod + solvedY.mod)
    assert(z.b == b)
    assert(z.mod == solvedX.mod + solvedY.mod)
    assert(z.div == 0)
    assert(z.a == z.b * z.div + z.mod)

    val solvedZ = z.solve
    assert(solvedZ.isValid && solvedZ.isFinal)
    assert(solvedZ.mod < x.absB)
    assert(modUniqueDiv(z, solvedZ))
    assert(z.solve.mod == solvedZ.mod)

    assert(solvedX.mod + solvedY.mod == b * solvedZ.div + solvedZ.mod)
    assert(solvedX.a - solvedX.b * solvedX.div + solvedY.a - solvedY.b * solvedY.div == b * solvedZ.div + solvedZ.mod)
    assert(a - b * solvedX.div + c - b * solvedY.div == b * solvedZ.div + solvedZ.mod)
    assert(a + c == b * solvedZ.div + b * solvedX.div + b * solvedY.div + solvedZ.mod)

    val bigDiv = solvedZ.div + solvedX.div + solvedY.div
    assert(a + c == b * bigDiv + solvedZ.mod)

    val w = DivMod(a + c, b, bigDiv, solvedZ.mod)
    assert(solvedZ.mod < x.absB)
    assert(w.mod == solvedZ.mod)
    assert(w.isFinal)
    assert(w.solve == w)

    assert(b != 0)
    assert(AdditionAndMultiplication.ATimesBSameMod(a + c, b, bigDiv))
    assert(mod(a + c, b) == mod(a + c + b * bigDiv, b))
    assert(w.isValid)
    assert(xy.isValid)
    assert(w.a == xy.a)
    assert(w.b == xy.b)
    assert(modUniqueDiv(w, xy))
    assert(w.solve == xy.solve)

    equality(
      w.solve.mod,        // is equals to
      xy.solve.mod,       // is equals to
      mod(a + c, b),      // is equals to
      solvedZ.mod,        // is equals to
      mod(mod(a, b) + mod(c, b), b)
    )

    assert(mod(a + c, b) == mod(mod(a, b) + mod(c, b), b))
    assert(div(a + c, b) == div(a, b) + div(c, b) + div(mod(a, b) + mod(c, b), b))

    mod(a + c, b) == mod(mod(a, b) + mod(c, b), b) &&
      div(a + c, b) == div(a, b) + div(c, b) + div(mod(a, b) + mod(c, b), b)
  }.holds

  def modZeroPlusC(a: BigInt, b: BigInt, c: BigInt): Boolean = {
    require(b != 0)
    require(c >= 0)
    require(mod(a, b) == 0)

    modAdd(a, b, c)
    assert(mod(a + c, b) == mod(mod(a, b) + mod(c, b), b))
    assert(mod(a + c, b) == mod(0 + mod(c, b), b))
    assert(mod(a + c, b) == mod(mod(c, b), b))

    assert(ModIdempotence.modIdempotence(c, b))
    assert(mod(mod(c, b), b) == mod(c, b))
    assert(mod(a + c, b) == mod(c, b))

    mod(a + c, b) == mod(c, b) &&
    mod(a + c, b) == mod(mod(c, b), b)
  }.holds

  def modLess(a: BigInt, b: BigInt, c: BigInt): Boolean = {
    require(b != 0)

    val x = a - c
    assert(modAdd(x, b, c))

    assert(x == b * div(x, b) + mod(x, b))
    assert(a == b * div(a, b) + mod(a, b))
    assert(c == b * div(c, b) + mod(c, b))

    equality(
      x,                                                            // is equal to
      a - c,                                                        // is equal to
      (a) - (c),                                                    // is equal to
      (b * div(a, b) + mod(a, b)) - (b * div(c, b) + mod(c, b)),    // is equal to
      b * div(a, b) + mod(a, b) - b * div(c, b) - mod(c, b),        // is equal to
      b * div(a, b) - b * div(c, b) + mod(a, b) - mod(c, b),        // is equal to
      b * (div(a, b) - div(c, b)) + mod(a, b) - mod(c, b),          // is equal to
      b * div(x, b) + mod(x, b),                                    // is equal to
      b * div(a - c, b) + mod(a - c, b)
    )


    assert(a == b * div(a, b) + mod(a, b))
    assert(c == b * div(c, b) + mod(c, b))
    equality(
      a - c,                                                        // is equal to
      b * div(a, b) + mod(a, b) - (b * div(c, b) + mod(c, b)),      // is equal to
      b * div(a, b) + mod(a, b) - b * div(c, b) - mod(c, b),        // is equal to
      b * div(a, b) - b * div(c, b) + mod(a, b) - mod(c, b),        // is equal to
    )
    assert(mod(a - c, b) == mod(b * (div(a, b) - div(c, b)) + mod(a, b) - mod(c, b), b))
    val m = div(a, b) - div(c, b)
    val others = mod(a, b) - mod(c, b)
    assert(mod(a - c, b) == mod(b * m + others, b))
    AdditionAndMultiplication.ATimesBSameMod(others, b, m)
    assert(mod(b * m + others, b) == mod(others, b))
    assert(mod(a - c, b) == mod(mod(a, b) - mod(c, b), b))

    assert(div(x + c, b) == div(x, b) + div(c, b) + div(mod(x, b) + mod(c, b), b))
    assert(div(a - c + c, b) == div(a - c, b) + div(c, b) + div(mod(a - c, b) + mod(c, b), b))
    assert(div(a, b) == div(a - c, b) + div(c, b) + div(mod(a - c, b) + mod(c, b), b))
    assert(div(a - c, b) + div(c, b) + div(mod(a - c, b) + mod(c, b), b) == div(a, b))
    assert(div(a - c, b) + div(mod(a - c, b) + mod(c, b), b) == div(a, b) - div(c, b))
    assert(div(a - c, b) == div(a, b) - div(c, b) - div(mod(a - c, b) + mod(c, b), b))
    assert(div(a - c, b) == div(a, b) - div(c, b) - div(mod(mod(a, b) - mod(c, b), b) + mod(c, b), b))

    val absB = if (b < 0) -b else b
    val sign = if (b < 0) BigInt(-1) else BigInt(1)

    assert(ModIdempotence.modModMinus(a, b, c))
    assert(
      mod(mod(a, b) - mod(c, b), b) == mod(a, b) - mod(c, b) ||
      mod(mod(a, b) - mod(c, b), b) == mod(a, b) - mod(c, b) + b ||
      mod(mod(a, b) - mod(c, b), b) == mod(a, b) - mod(c, b) - b
    )
    assert(
      mod(mod(a, b) - mod(c, b), b) + mod(c, b) == mod(a, b) - mod(c, b) + mod(c, b) ||
      mod(mod(a, b) - mod(c, b), b) + mod(c, b) == mod(a, b) - mod(c, b) + b + mod(c, b) ||
      mod(mod(a, b) - mod(c, b), b) + mod(c, b) == mod(a, b) - mod(c, b) - b + mod(c, b)
    )
    assert(
      mod(mod(a, b) - mod(c, b), b) + mod(c, b) == mod(a, b) ||
      mod(mod(a, b) - mod(c, b), b) + mod(c, b) == mod(a, b) + b ||
      mod(mod(a, b) - mod(c, b), b) + mod(c, b) == mod(a, b) - b
    )

    mod(a - c, b) == mod(mod(a, b) - mod(c, b), b) &&
    div(a - c, b) == div(a, b) - div(c, b) + div(mod(a, b) - mod(c, b), b)
  }.holds
}
