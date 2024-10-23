package v1.properties

import v1.Calc
import v1.Div
import stainless.lang._
import stainless.proof.check

object ModIdentity {
  def modIdentity(a: BigInt): Boolean = {
    require(a != 0)
    Calc.mod(a, a) == 0
  }.holds

  def longProof(n: BigInt): Boolean = {
    require(n != 0)
    check(!Div(a = n, b = n, div = 0, mod = n).isFinal)

    if (n > 0) {
      check(
        Div(a=n, b=n, div=0, mod=n).solve ==
        Div(a=n, b=n, div=0, mod=n).reduceMod.solve
      )
      check(
        Div(a=n, b=n, div=0, mod=n).reduceMod.solve ==
        Div(a=n, b=n, div=0, mod=n).ModLessB.reduceMod
      )
      check(
        Div(a=n, b=n, div=0, mod=n).ModLessB.reduceMod ==
        Div(a=n, b=n, div=1, mod=0).reduceMod
      )
      check(
        Div(a=n, b=n, div=1, mod=0).reduceMod ==
        Div(a=n, b=n, div=1, mod=0)
      )
      // since
      check(Div(a=n, b=n, div=1, mod=0).isFinal)
    } else {
      check(
        Div(a=n, b=n, div=0, mod=n).solve ==
          Div(a=n, b=n, div=0, mod=n).increaseMod.solve
      )
      check(
        Div(a=n, b=n, div=0, mod=n).increaseMod.solve ==
          Div(a=n, b=n, div=0, mod=n).ModPlusB.increaseMod
      )
      check(
        Div(a=n, b=n, div=0, mod=n).ModPlusB.increaseMod ==
          Div(a=n, b=n, div=1, mod=0)
      )
      // since
      check(Div(a=n, b=n, div=1, mod=0).isFinal)
    }
    Div(a=n, b=n, div=0, mod=n).solve == Div(a=n, b=n, div=1, mod=0)
  }.holds
}
