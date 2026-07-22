package v1.chapter2.div.properties

import stainless.lang.*
import v1.chapter1.verification.Helper.{assert, equality}
import v1.chapter2.div.{Calc, DivMod}

object ModIdentity {
  def modIdentity(a: BigInt): Boolean = {
    require(a != 0)
    Calc.mod(a, a) == 0 && Calc.div(a, a) == 1
  }.holds

  def longProof(n: BigInt): Boolean = {
    require(n != 0)
    assert(!DivMod(a = n, b = n, div = 0, mod = n).isFinal)
    assert(DivMod(a=n, b=n, div=1, mod=0).isFinal) // by definition

    if (n > 0) {
      equality(
        DivMod(a=n, b=n, div=0, mod=n).solve,               // is equals to
        DivMod(a=n, b=n, div=0, mod=n).reduceMod.solve,     // is equals to
        DivMod(a=n, b=n, div=0, mod=n).ModLessB.reduceMod,  // is equals to
        DivMod(a=n, b=n, div=1, mod=0).reduceMod,           // is equals to itself, since it is already final (asserted above)
        DivMod(a=n, b=n, div=1, mod=0)
      )
    } else {
      equality(
        DivMod(a=n, b=n, div=0, mod=n).solve,                 // is equals to
        DivMod(a=n, b=n, div=0, mod=n).increaseMod.solve,     // is equals to
        DivMod(a=n, b=n, div=0, mod=n).ModPlusB.increaseMod,  // is equals to itself, since it is already final (asserted above)
        DivMod(a=n, b=n, div=1, mod=0)
      )
    }
    DivMod(a=n, b=n, div=0, mod=n).solve == DivMod(a=n, b=n, div=1, mod=0)
  }.holds
}
