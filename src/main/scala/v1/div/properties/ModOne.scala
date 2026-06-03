package v1.div.properties

import stainless.lang.*
import v1.Calc
import verification.Helper.assert

object ModOne {

  def modOneIsZero(n: BigInt): Boolean = {
    require(n >= 0)
    assert(ModSmallDividend.modSmallDividend(BigInt(0), BigInt(1)))
    assert(AdditionAndMultiplication.ATimesBSameMod(BigInt(0), BigInt(1), n))
    Calc.mod(n, BigInt(1)) == BigInt(0)
  }.holds

  def divOneIsN(n: BigInt): Boolean = {
    require(n >= 0)
    decreases(n)
    if (n == 0) {
      assert(ModSmallDividend.modSmallDividend(BigInt(0), BigInt(1)))
      Calc.div(n, BigInt(1)) == BigInt(0)
    } else {
      assert(divOneIsN(n - 1))
      assert(ModOperations.addOne(n - 1, BigInt(1)))
      Calc.div(n, BigInt(1)) == n
    }
  }.holds
}
