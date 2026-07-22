package v1.chapter5.prime

import stainless.collection.List
import stainless.lang.*
import v1.chapter2.div.Calc
import v1.chapter2.div.properties.AdditionAndMultiplication
import v1.chapter3.list.ListUtils

import scala.annotation.tailrec

object CoprimeUtils {

  @tailrec
  def isCoprime(value: BigInt, primes: List[BigInt]): Boolean = {
    require(ListUtils.checkAllPositive(primes))
    decreases(primes.size)
    if (primes.isEmpty) true
    else if (Calc.mod(value, primes.head) == BigInt(0)) false
    else isCoprime(value, primes.tail)
  }

  def assertModZero(n: BigInt): Boolean = {
    require(n != BigInt(0))
    Calc.mod(BigInt(0), n) == BigInt(0)
  }.holds

  def assertModZeroImpliesDivTimesBEqualsA(a: BigInt, b: BigInt): Boolean = {
    require(b != 0)
    require(Calc.mod(a, b) == BigInt(0))
    Calc.div(a, b) * b == a
  }.holds

  def assertMultipleModZero(k: BigInt, n: BigInt): Boolean = {
    require(n != BigInt(0))
    require(k >= BigInt(0))
    AdditionAndMultiplication.APlusMultipleTimesBSameMod(BigInt(0), n, k)
    assert(assertModZero(n))
    Calc.mod(k * n, n) == BigInt(0)
  }.holds

  def filterList(list: List[BigInt], divisor: BigInt): List[BigInt] = {
    require(divisor > 0)
    decreases(list.size)
    if (list.isEmpty) List.empty
    else {
      val rest = filterList(list.tail, divisor)
      if (Calc.mod(list.head, divisor) != BigInt(0)) list.head :: rest
      else rest
    }
  }

  def hasPrimeFactorInList(d: BigInt, primes: List[BigInt]): Boolean = {
    require(ListUtils.checkAllPositive(primes))
    decreases(primes.size)
    if (primes.isEmpty) false
    else if (Calc.mod(d, primes.head) == BigInt(0)) true
    else hasPrimeFactorInList(d, primes.tail)
  }

  def assertIsCoprimeForAll(n: BigInt, primes: List[BigInt]): Boolean = {
    require(ListUtils.checkAllPositive(primes))
    require(isCoprime(n, primes))
    decreases(primes.size)
    if (primes.isEmpty) true
    else {
      assert(assertIsCoprimeForAll(n, primes.tail))
      Calc.mod(n, primes.head) != BigInt(0)
    }
  }.holds

  def assertHasPrimeFactorImpliesNotCoprime(d: BigInt, primes: List[BigInt]): Boolean = {
    require(ListUtils.checkAllPositive(primes))
    require(hasPrimeFactorInList(d, primes))
    decreases(primes.size)
    if (primes.isEmpty) {
      false
    } else if (Calc.mod(d, primes.head) == BigInt(0)) {
      Calc.mod(d, primes.head) == BigInt(0) && !isCoprime(d, primes)
    } else {
      assert(assertHasPrimeFactorImpliesNotCoprime(d, primes.tail))
      !isCoprime(d, primes)
    }
  }.holds

  def assertNoDivisorByFactorList(n: BigInt, d: BigInt, primes: List[BigInt]): Boolean = {
    require(n > 1)
    require(d >= 2)
    require(ListUtils.checkAllPositive(primes))
    require(isCoprime(n, primes))
    require(!isCoprime(d, primes))
    decreases(primes.size)

    if (primes.isEmpty) true
    else {
      val p = primes.head
      if (Calc.mod(d, p) == BigInt(0)) {
        assert(assertIsCoprimeForAll(n, primes))
        if (Calc.mod(n, d) == BigInt(0)) {
          assert(assertModZeroImpliesDivTimesBEqualsA(n, d))
          assert(assertModZeroImpliesDivTimesBEqualsA(d, p))
          val nd = Calc.div(n, d)
          val dp = Calc.div(d, p)
          assert(nd * d == n)
          assert(dp * p == d)
          assert(nd * dp * p == n)
          assert(nd * dp >= 0)
          assert(assertMultipleModZero(nd * dp, p))
          false
        } else {
          true
        }
      } else {
        assert(assertNoDivisorByFactorList(n, d, primes.tail))
        Calc.mod(n, d) != BigInt(0)
      }
    }
  }.holds

  def assertAllNotCoprimeInRange(limit: BigInt, d: BigInt, primes: List[BigInt]): Boolean = {
    require(limit >= 2)
    require(d >= 2)
    require(d <= limit)
    require(ListUtils.checkAllPositive(primes))
    decreases(limit - d)
    if (d >= limit) true
    else {
      hasPrimeFactorInList(d, primes) && assertAllNotCoprimeInRange(limit, d + 1, primes)
    }
  }
}
