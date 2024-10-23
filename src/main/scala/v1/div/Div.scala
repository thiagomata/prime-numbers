package v1

import stainless.lang.*
import stainless.proof.check
import scala.language.postfixOps

case class Div(
                a: BigInt,
                b: BigInt,
                div: BigInt,
                mod: BigInt
              ) {
  require(div * b + mod == a)
  require(b != 0)

  def isValid: Boolean = {
    div * b + mod == a
  }
  def isFinal: Boolean = {
    if (b > 0) mod < b && mod >= 0
    else mod < -b && mod >= 0
  }

  def solve: Div = {
    if (this.isFinal) {
      return this
    }
    val result = if (mod > 0) {
      reduceMod
    } else {
      increaseMod
    }
    check(result.isFinal)
    check(result.isValid)
    check(result.a == a)
    check(result.b == b)
    result
  }.ensuring(res => res.isFinal && res.isValid && res.a == a && res.b == b)

  def reduceMod: Div = {
    require(mod >= 0)
    decreases(mod)

    if isFinal then
      return this

    val next = if (b > 0) {
      check(b > 0)
      ModLessB
    } else {
      assert(b < 0)
      ModPlusB
    }
    val absB = if (b > 0) b else -b
    check(next.a == a)
    check(next.b == b)
    check(next.mod < mod)
    check(next.mod == mod - absB)
    check(next.isValid)

    val result = next.reduceMod
    check(result.isFinal)
    check(result.mod < mod)
    check(result.a == a)
    check(result.b == b)
    check(result.isValid)
    result
  }.ensuring(res => res.isFinal)

  def increaseMod: Div = {
    val absB = if (b >= 0) b else -b
    require(mod < 0)
    decreases(-mod)

    if isFinal then
      return this

    val next = if (b < 0) {
      check(b < 0)
      ModLessB
    } else {
      check(b > 0)
      ModPlusB
    }
    check(next.a == a)
    check(next.b == b)
    check(next.mod > mod)
    check(next.isValid)

    val result = if (next.isFinal) then next else next.increaseMod
    check(result.isFinal)
    check(result.a == a)
    check(result.b == b)
    check(result.mod > mod)
    check(result.isValid)
    result
  }.ensuring(res => res.isFinal && res.isValid)

  def ModPlusB: Div = {
    check(div * b + mod == a)
    check(div * b - b + mod + b == a)
    check((div - 1) * b + (mod + b) == a)
    val next = Div(a, b, div - 1, mod + b)
    check(next.a == a)
    check(next.b == b)
    check(next.mod == mod + b)
    check(next.div == div - 1)
    check(next.isValid)
    next
  }

  def ModLessB: Div = {
    check(div * b + mod == a)
    check(div * b + b + mod - b == a)
    check((div + 1) * b + (mod - b) == a)
    val next = Div(a, b, div + 1, mod - b)
    check(next.a == a)
    check(next.b == b)
    check(next.mod == mod - b)
    check(next.div == div + 1)
    check(next.isValid)
    next
  }

  override def equals(obj: Any): Boolean = {
    obj match {
      case that: Div =>
        ( that.a == this.a &&
          that.b == this.b &&
          that.div == this.div &&
          that.mod == this.mod ) ||
          ( that.solve == this.solve )
      case _ => false
    }
  }
}