package v1.div.properties

import stainless.lang.*
import stainless.proof.check
import v1.Calc
import v1.div.DivMod
import verification.Helper.equality

object ModIdentity {
  def modIdentity(a: BigInt): Boolean = {
    require(a != 0)
    Calc.mod(a, a) == 0 && Calc.div(a, a) == 1
  }.holds

  def longProof(n: BigInt): Boolean = {
    require(n != 0)
    check(!DivMod(a = n, b = n, div = 0, mod = n).isFinal)

    if (n > 0) {
      check(
        equality(
          DivMod(a=n, b=n, div=0, mod=n).solve,               // is equals to
          DivMod(a=n, b=n, div=0, mod=n).reduceMod.solve,     // is equals to
          DivMod(a=n, b=n, div=0, mod=n).ModLessB.reduceMod,  // is equals to
          DivMod(a=n, b=n, div=1, mod=0).reduceMod,           // is equals to
          DivMod(a=n, b=n, div=1, mod=0)
        )
      )
      // since
      check(DivMod(a=n, b=n, div=1, mod=0).isFinal)
    } else {
      check(equality(
        DivMod(a=n, b=n, div=0, mod=n).solve,                 // is equals to
        DivMod(a=n, b=n, div=0, mod=n).increaseMod.solve,     // is equals to
        DivMod(a=n, b=n, div=0, mod=n).ModPlusB.increaseMod,  // is equals to
        DivMod(a=n, b=n, div=1, mod=0)
      ))
      // since
      check(DivMod(a=n, b=n, div=1, mod=0).isFinal)
    }
    DivMod(a=n, b=n, div=0, mod=n).solve == DivMod(a=n, b=n, div=1, mod=0)
  }.holds
}
