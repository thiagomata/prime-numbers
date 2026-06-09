package v1.prime

import stainless.lang.*
import stainless.collection.List
import stainless.annotation.extern
import v1.Calc

import scala.annotation.tailrec

object Prime {

  @tailrec
  def noDivisorInRange(n: BigInt, from: BigInt, to: BigInt): Boolean = {
    require(n >= 0)
    require(from >= 1)
    require(to >= from)
    decreases(to - from)
    if (from == to) {
      true
    } else {
      Calc.mod(n, from) != BigInt(0) && noDivisorInRange(n, from + 1, to)
    }
  }

  def isPrime(p: BigInt): Boolean = {
    require(p >= 0)
    if (p <= 1) {
      false
    } else {
      noDivisorInRange(p, 2, p)
    }
  }
}