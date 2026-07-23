package v1.chapter5.prime

import stainless.lang.*
import v1.chapter2.div.Calc

import scala.annotation.tailrec

class Prime(inputValue: BigInt) {
  require(Prime.isPrime(inputValue))

  val value: BigInt = inputValue;

  def apply(): BigInt = value
}

object Prime {
  @tailrec
  final def noDivisorInRange(n: BigInt, from: BigInt, to: BigInt): Boolean = {
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

  def noDivisorInRangeExcludesValue(n: BigInt, from: BigInt, to: BigInt, value: BigInt): Boolean = {
    require(n >= 0)
    require(from >= 1)
    require(to >= from)
    require(noDivisorInRange(n, from, to))
    require(value >= from)
    require(value < to)
    decreases(value - from)

    if (value == from) {
      Calc.mod(n, from) != BigInt(0)
    } else {
      assert(noDivisorInRange(n, from + 1, to))
      noDivisorInRangeExcludesValue(n, from + 1, to, value)
      Calc.mod(n, value) != BigInt(0)
    }
  }.holds

  final def findSmallestDivisor(n: BigInt, from: BigInt): BigInt = {
    require(n > 1 && from >= 2 && from <= n)
    decreases(n - from)
    if (from >= n) n
    else if (Calc.mod(n, from) == BigInt(0)) from
    else findSmallestDivisor(n, from + 1)
  }.ensuring(res => res >= from && res <= n && Calc.mod(n, res) == BigInt(0))

  def assertFindSmallestDivisorMinimality(n: BigInt, from: BigInt): Boolean = {
    require(n > 1 && from >= 2 && from <= n)
    decreases(n - from)
    if (from >= n) true
    else if (Calc.mod(n, from) == BigInt(0)) {
      val res = findSmallestDivisor(n, from)
      if (res > from) noDivisorInRange(n, from, res - 1)
      else true
    } else {
      assertFindSmallestDivisorMinimality(n, from + 1)
      val res = findSmallestDivisor(n, from)
      if (res > from) noDivisorInRange(n, from, res - 1)
      else true
    }
  }.holds

  def assertFindSmallestDivisorEquivNoDivisorInRange(n: BigInt, from: BigInt): Boolean = {
    require(n > 1 && from >= 2 && from <= n)
    decreases(n - from)
    if (from >= n)
      (findSmallestDivisor(n, from) == n) == noDivisorInRange(n, from, n)
    else if (Calc.mod(n, from) == BigInt(0))
      (findSmallestDivisor(n, from) == n) == noDivisorInRange(n, from, n)
    else
      assertFindSmallestDivisorEquivNoDivisorInRange(n, from + 1)
  }.holds

  def isPrime(value: BigInt): Boolean = {
    require(value >= 0)
    if (value <= 1) {
      false
    } else {
      noDivisorInRange(value, 2, value)
    }
  }
}