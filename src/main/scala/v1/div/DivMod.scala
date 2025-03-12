package v1.div

import stainless.lang.*
import stainless.proof.check

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
    check(result.isFinal && result.isValid)
    check(result.a == a && result.b == b)
    result
  }.ensuring(res => res.isFinal && res.isValid && res.a == a && res.b == b)

  def reduceMod: DivMod = {
    require(mod >= 0)
    decreases(mod)

    if (isFinal) return this

    val next = if (b > 0) then ModLessB else ModPlusB

    val result = next.reduceMod
    check(result.isFinal && result.isValid)
    check(result.mod < mod)
    check(result.a == a && result.b == b)
    result
  }.ensuring(res => res.isFinal && res.isValid)

  def increaseMod: DivMod = {
    require(mod < 0) //                                               since mod is negative, it is not final
    decreases(-mod) //                                                mod should increase every iteration

    val next = if (b < 0) then ModLessB else ModPlusB //              increase the mod by abs(b)
    val result = if (next.isFinal) then next else next.increaseMod // repeat until mod is final
    check(result.isFinal && result.isValid) //                        result is final and valid
    check(result.a == a && result.b == b) //                          result has the same a and b as the original DivMod
    check(result.mod >= 0) //                                         result has a non-negative mod
    result
  }.ensuring(res => res.isFinal && res.isValid)

  def ModPlusB: DivMod = {
    check(div * b + mod == a)
    check(div * b - b + mod + b == a)  //         adding +b and -b does not change the value
    check((div - 1) * b + (mod + b) == a) //      isolating div - 1 and mod + b
    val next = DivMod(a, b, div - 1, mod + b) //  is valid because next.div * next.b + next.mod == next.a as proved above
    check(next.a == a && next.b == b) //          next.a and next.b are the same as the original DivMod
    check(next.mod == mod + b) //                 next.mod is the same as the original DivMod plus b
    check(next.div == div - 1) //                 next.div is the same as the original DivMod minus 1
    check(next.isValid) //                        next is valid
    next
  }

  def ModLessB: DivMod = {
    check(div * b + mod == a)
    check(div * b + b + mod - b == a) //          adding -b and +b does not change the value
    check((div + 1) * b + (mod - b) == a) //      isolating div + 1 and mod - b
    val next = DivMod(a, b, div + 1, mod - b) //  is valid because next.div * next.b + next.mod == next.a as proved above
    check(next.a == a && next.b == b) //          next.a and next.b are the same as the original DivMod
    check(next.mod == mod - b) //                 next.mod is the same as the original DivMod minus b
    check(next.div == div + 1) //                 next.div is the same as the original DivMod plus 1
    check(next.isValid) //                        next is valid
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