package v1.div

import stainless.lang.*
import verification.Helper.assert

import scala.language.postfixOps

case class DivMod(a: BigInt, b: BigInt, div: BigInt, mod: BigInt) {
  require(div * b + mod == a)
  require(b != 0)

  def absB: BigInt = if (b > 0) b else -b
  def isValid: Boolean = div * b + mod == a
  def isFinal: Boolean = if (b > 0) mod < b && mod >= 0 else mod < -b && mod >= 0

  def solve: DivMod = {
    if (this.isFinal) return this

    val result = if (mod > 0) then reduceMod else increaseMod
    (assert(result.isFinal && result.isValid))
    (assert(result.a == a && result.b == b))
    result
  }.ensuring(res => res.isFinal && res.isValid && res.a == a && res.b == b)

  def reduceMod: DivMod = {
    require(mod >= 0)
    decreases(mod)

    if (isFinal) return this

    val next = if (b > 0) then ModLessB else ModPlusB

    val result = next.reduceMod
    (assert(result.isFinal && result.isValid))
    (assert(result.mod < mod))
    (assert(result.a == a && result.b == b))
    result
  }.ensuring(res => res.isFinal && res.isValid)

  def increaseMod: DivMod = {
    require(mod < 0) //                                               since mod is negative, it is not final
    decreases(-mod) //                                                mod should increase every iteration

    val next = if (b < 0) then ModLessB else ModPlusB //              increase the mod by abs(b)
    val result = if (next.isFinal) then next else next.increaseMod // repeat until mod is final
    (assert(result.isFinal && result.isValid)) //                     result is final and valid
    (assert(result.a == a && result.b == b)) //                       result has the same a and b as the original DivMod
    (assert(result.mod >= 0)) //                                      result has a non-negative mod
    result
  }.ensuring(res => res.isFinal && res.isValid)

  def ModPlusB: DivMod = {
    (assert(div * b + mod == a))
    (assert(div * b - b + mod + b == a))  //         adding +b and -b does not change the value
    (assert((div - 1) * b + (mod + b) == a)) //      isolating div - 1 and mod + b
    val next = DivMod(a, b, div - 1, mod + b) //     is valid because next.div * next.b + next.mod == next.a as proved above
    (assert(next.a == a && next.b == b)) //          next.a and next.b are the same as the original DivMod
    (assert(next.mod == mod + b)) //                 next.mod is the same as the original DivMod plus b
    (assert(next.div == div - 1)) //                 next.div is the same as the original DivMod minus 1
    (assert(next.isValid)) //                        next is valid
    next
  }

  def ModLessB: DivMod = {
    assert(div * b + mod == a)
    assert(div * b + b + mod - b == a) //          adding -b and +b does not change the value
    assert((div + 1) * b + (mod - b) == a) //      isolating div + 1 and mod - b
    val next = DivMod(a, b, div + 1, mod - b) //   is valid because next.div * next.b + next.mod == next.a as proved above
    assert(next.a == a && next.b == b) //          next.a and next.b are the same as the original DivMod
    assert(next.mod == mod - b) //                 next.mod is the same as the original DivMod minus b
    assert(next.div == div + 1) //                 next.div is the same as the original DivMod plus 1
    assert(next.isValid) //                        next is valid
    next
  }

  override def equals(obj: Any): Boolean = {
    obj match {
      case that: DivMod =>
        ( that.a == this.a &&
          that.b == this.b &&
          that.div == this.div &&
          that.mod == this.mod ) ||
          ( that.solve == this.solve ) // we also consider two DivMod equal if they are the same after solving
      case _ => false
    }
  }
}