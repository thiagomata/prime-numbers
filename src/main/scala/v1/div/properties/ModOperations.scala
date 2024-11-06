package v1.div.properties

import v1.Calc
import v1.DivMod
import stainless.lang.*
import stainless.proof.check
import v1.Calc.{div, mod}
import v1.properties.{AdditionAndMultiplication, ModIdempotence}
import v1.properties.ModIdempotence.modUniqueDiv
import verification.Helper
import verification.Helper.equality

object ModOperations {

  def modAdd(a: BigInt, b: BigInt, c: BigInt): Boolean = {
    require(b != 0)

    val x = DivMod(a, b, 0, a)
    val solvedX = x.solve
    check(solvedX.isFinal && solvedX.isValid)
    check(solvedX.mod < x.absB)
    check(solvedX.a == a)
    check(solvedX.b == b)
    check(solvedX.a == solvedX.b * solvedX.div + solvedX.mod)
    check(solvedX.a - solvedX.b * solvedX.div == solvedX.mod)

    val y = DivMod(c, b, 0, c)
    val solvedY = y.solve
    check(solvedY.isFinal && solvedY.isValid)
    check(solvedY.mod < x.absB)
    check(solvedY.a == c)
    check(solvedY.b == b)
    check(solvedY.a == solvedY.b * solvedY.div + solvedY.mod)
    check(solvedY.a - solvedY.b * solvedY.div == solvedY.mod)

    val xy = DivMod(a + c, b, 0, a + c)
    val solvedXY = xy.solve
    check(solvedXY.isFinal && solvedXY.isValid)
    check(solvedXY.mod < x.absB)
    check(solvedXY.a == a + c)
    check(solvedXY.b == b)
    check(solvedXY.a == solvedXY.b * solvedXY.div + solvedXY.mod)
    check(a + c == b * solvedXY.div + solvedXY.mod)

    val z = DivMod( solvedX.mod + solvedY.mod, b, 0, solvedX.mod + solvedY.mod)
    check(z.a == z.b * z.div + z.mod)
    check(z.a == solvedX.mod + solvedY.mod)
    check(z.b == b)
    check(z.mod == solvedX.mod + solvedY.mod)
    check(z.div == 0)
    check(z.a == z.b * z.div + z.mod)

    val solvedZ = z.solve
    check(solvedZ.isValid && solvedZ.isFinal)
    check(solvedZ.mod < x.absB)
    check(modUniqueDiv(z, solvedZ))
    check(z.solve.mod == solvedZ.mod)

    check(solvedX.mod + solvedY.mod == b * solvedZ.div + solvedZ.mod)
    check(solvedX.a - solvedX.b * solvedX.div + solvedY.a - solvedY.b * solvedY.div == b * solvedZ.div + solvedZ.mod)
    check(a - b * solvedX.div + c - b * solvedY.div == b * solvedZ.div + solvedZ.mod)
    check(a + c == b * solvedZ.div + b * solvedX.div + b * solvedY.div + solvedZ.mod)

    val bigDiv = solvedZ.div + solvedX.div + solvedY.div
    check(a + c == b * bigDiv + solvedZ.mod)

    val w = DivMod(a + c, b, bigDiv, solvedZ.mod)
    check(solvedZ.mod < x.absB)
    check(w.mod == solvedZ.mod)
    check(w.isFinal)
    check(w.solve == w)

    check(b != 0)
    AdditionAndMultiplication.ATimesBSameMod(a + c, b, bigDiv)
    check( mod(a + c,b) == mod( a + c + b * bigDiv, b ))
    check(w.isValid)
    check(xy.isValid)
    check(w.a == xy.a)
    check(w.b == xy.b)
    check(modUniqueDiv(w, xy))
    check( w.solve == xy.solve)

    check( Helper.equality(
      w.solve.mod,               // is equals to
      xy.solve.mod,              // is equals to
      mod(a+c,b),           // is equals to
      solvedZ.mod,               // is equals to
      mod(mod(a, b) + mod(c, b), b)
    ))

    check(mod(a + c, b) == mod(mod(a, b) + mod(c, b), b))
    check(div(a + c, b) == div(a, b) + div(c, b) + div(mod(a, b) + mod(c, b), b))

    mod(a + c, b) == mod(mod(a, b) + mod(c, b), b) &&
    div(a + c, b) == div(a, b) + div(c, b) + div(mod(a, b) + mod(c, b), b)
  }.holds

  def modZeroPlusC(a: BigInt, b: BigInt, c: BigInt): Boolean = {
    require(b != 0)
    require(mod(a, b) == 0)
    modAdd(a,b,c)
    check(mod(a + c, b) == mod(mod(a, b) + mod(c, b), b))
    check(mod(a + c, b) == mod(0 + mod(c, b), b))
    check(mod(a + c, b) == mod(mod(c, b), b))
    if (c >= 0) {
      check(c >= 0)
      check(b != 0)
      check(ModIdempotence.modIdempotence(c, b))
      check(mod(mod(c, b), b) == mod(c, b))
      check(mod(a + c, b) == mod(c, b))
    }

    ( if c >= 0 then mod(a + c, b) == mod(c, b) else true ) &&
    mod(a + c, b) == mod(mod(c, b), b)
  }.holds

  def modLess(a: BigInt, b: BigInt, c: BigInt): Boolean = {
    require(b != 0)

    val x = a - c
    modAdd(x, b, c)

    check( x == b * div(x,b) + mod(x,b) )
    check( a == b * div(a,b) + mod(a,b) )
    check( c == b * div(c,b) + mod(c,b) )

    check(
      equality(
        x,
        a - c,
        (a) - (c),
        (b * div(a, b) + mod(a, b)) - (b * div(c, b) + mod(c, b)),
        b * div(a, b) + mod(a, b) - b * div(c, b) - mod(c, b),
        b * div(a, b) - b * div(c, b) + mod(a, b) - mod(c, b),
        b * ( div(a, b) - div(c, b) ) + mod(a, b) - mod(c, b),
        b * div(x, b) + mod(x, b),
        b * div(a - c, b) + mod(a - c, b)
      )
    )


    check( a == b * div(a,b) + mod(a,b) )
    check( c == b * div(c,b) + mod(c,b) )
    check( a - c == b * div(a,b) + mod(a,b) - ( b * div(c,b) + mod(c,b) ) )
    check( a - c == b * div(a,b) + mod(a,b) - b * div(c,b) - mod(c,b) )
    check( a - c == b * div(a,b) - b * div(c,b) + mod(a,b) - mod(c,b) )
    check( a - c == b * ( div(a,b) - div(c,b) ) + mod(a,b) - mod(c,b) )
    check( mod( a - c, b) == mod( b * ( div(a,b) - div(c,b) ) + mod(a,b) - mod(c,b), b ) )
    val m = div(a, b) - div(c, b)
    val others = mod(a,b) - mod(c,b)
    check( mod( a - c, b) == mod( b * m + others, b ) )
    AdditionAndMultiplication.ATimesBSameMod(others, b, m)
    check( mod( b * m + others, b ) == mod( others, b ) )
    check( mod( a - c, b) == mod( mod(a,b) - mod(c,b), b ) )

    check(div(x + c, b)     == div(x, b) + div(c, b) + div(mod(x, b) + mod(c, b), b))
    check(div(a - c + c, b) == div(a - c, b) + div(c, b) + div(mod(a - c, b) + mod(c, b), b))
    check(div(a, b)         == div(a - c, b) + div(c, b) + div(mod(a - c, b) + mod(c, b), b))
    check(div(a - c, b) + div(c, b) + div(mod(a - c, b) + mod(c, b), b) == div(a, b))
    check(div(a - c, b) + div(mod(a - c, b) + mod(c, b), b) == div(a, b) - div(c, b))
    check(div(a - c, b)     == div(a, b) - div(c, b) - div(mod(a - c, b)  + mod(c, b), b))
    check(div(a - c, b)     == div(a, b) - div(c, b) - div(mod(mod(a,b) - mod(c,b), b) + mod(c, b), b))

    val absB = if (b < 0) -b else b
    val sign = if (b < 0) BigInt(-1) else BigInt(1)

    ModIdempotence.modModLess(a, b, c)
    check(
      mod(mod(a,b) - mod(c,b), b) == mod(a,b) - mod(c,b) ||
      mod(mod(a,b) - mod(c,b), b) == mod(a,b) - mod(c,b) + b ||
      mod(mod(a,b) - mod(c,b), b) == mod(a,b) - mod(c,b) - b
    )



//    check(mod(a,b) < absB)
//    check(mod(a,b) >= 0)
//    check(mod(c,b) < absB)
//    check(mod(c,b) >= 0)
//    check(mod(a,b) - mod(c,b) < absB)
//    check(mod(a,b) - mod(c,b) > -absB)
//    if (mod(a,b) - mod(c,b) < 0) {
//      check(mod(mod(a,b) - mod(c,b), b) == -(mod(a,b) - mod(c,b)))
//    }
    // 0 <= mod(a,b) < b
    // 0 <= mod(c,b) < b
    // b < mod(a,b) - mod(c,b) < b


    mod(a - c, b) == mod(mod(a, b) - mod(c, b), b) // &&
//    div(a - c, b) == div(a, b) - div(c, b) + div(mod(a, b) - mod(c, b), b)
  }.holds
}
