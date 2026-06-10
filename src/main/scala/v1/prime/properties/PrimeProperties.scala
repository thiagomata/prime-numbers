package v1.prime.properties

import stainless.collection.List
import stainless.lang.{BigInt, decreases}
import v1.Calc
import v1.prime.{Prime, PrimeUtils}
import stainless.lang.BooleanDecorations
import v1.div.properties.AdditionAndMultiplication.ATimesBSameMod
import v1.div.properties.{AdditionAndMultiplication, ModIdentity, ModSmallDividend}
import v1.list.ListBoundUtils
import v1.list.properties.ListProduct
import v1.prime.PrimeUtils.{primorial, primorialConcatLemma}

object PrimeProperties {

  def allPrimesDividePrimorial(primes: List[Prime]): Boolean = {
    decreases(primes.size)
    if (primes.isEmpty) true
    else {
      val primorial: BigInt = PrimeUtils.primorial(primes)
      val tailPrimorial: BigInt = PrimeUtils.primorial(primes.tail)
      assert(primorial == primes.head.value * tailPrimorial)
      assert(ModIdentity.modIdentity(primes.head.value))

      // mod(a + b * m, b) == mod(a, b)
      assert(AdditionAndMultiplication.ATimesBSameMod
        (
          0, // a
          primes.head.value, // b
          tailPrimorial // m
        )
      )
      assert(Calc.mod(primorial, primes.head.value) == 0)

      Calc.mod(primorial, primes.head.value) == 0 &&
        allPrimesDividePrimorial(primes.tail)
    }
  }.holds

  private def productAppendLemma(list1: List[BigInt], list2: List[BigInt]): Boolean = {
    decreases(list1.size)
    require(ListBoundUtils.allGreaterThan(list1, 0))
    require(ListBoundUtils.allGreaterThan(list2, 0))
    if (list1.isEmpty) {
      ListProduct.product(list1 ++ list2) ==
        ListProduct.product(list1) * ListProduct.product(list2)
    } else {
      productAppendLemma(list1.tail, list2)
      ListProduct.product(list1 ++ list2) ==
        ListProduct.product(list1) * ListProduct.product(list2)
    }
  }.holds

  private def loop(remaining: List[BigInt], prefix: BigInt): Boolean = {
    decreases(remaining.size)
    require(ListBoundUtils.allGreaterThan(remaining, 0))
    if (remaining.isEmpty) true
    else {
      val p = remaining.head
      val suffix = ListProduct.product(remaining.tail)
      val full = prefix * p * suffix
      assert(ModSmallDividend.modSmallDividend(BigInt(0), p))
      assert(ATimesBSameMod(BigInt(0), p, prefix * suffix))
      assert(Calc.mod(full, p) == BigInt(0))
      Calc.mod(full, p) == BigInt(0) && loop(remaining.tail, prefix * p)
    }
  }.holds

  def checkProductModZero(elements: List[BigInt]): Boolean = {
    require(ListBoundUtils.allGreaterThan(elements, 0))
    loop(elements, BigInt(1))
  }.holds

  def checkPrimorialModZero(primes: List[Prime]): Boolean = {
    checkProductModZero(PrimeUtils.primeValues(primes))
  }.holds

  def checkPrimorialModZeroHead(primes: List[Prime]): Boolean = {
    require(primes.nonEmpty)
    assert(allPrimesDividePrimorial(primes))
    assert(checkPrimorialModZero(primes))
    Calc.mod(PrimeUtils.primorial(primes), primes.head.value) == BigInt(0)
  }.holds

  def checkPrimorialModZeroTailLoop(previous: List[Prime], current: List[Prime]): Boolean = {
    decreases(current.size)
    if (current.isEmpty) true
    else {
      val p = current.head.value
      val tailPrimorial = PrimeUtils.primorial(current.tail)
      val previousPrimorial = PrimeUtils.primorial(previous)
      val combinedPrimorial = previousPrimorial * p * tailPrimorial

      primorialConcatLemma(previous, current)
      assert(primorial(current) == p * primorial(current.tail))
      assert(primorial(previous ++ current) == previousPrimorial * p * primorial(current.tail))
      assert(primorial(previous ++ current) == combinedPrimorial)

      assert(ModSmallDividend.modSmallDividend(BigInt(0), p))
      AdditionAndMultiplication.ATimesBSameMod(
        BigInt(0), p, previousPrimorial * tailPrimorial
      )
      Calc.mod(combinedPrimorial, p) == BigInt(0) &&
        checkPrimorialModZeroTailLoop(previous :+ current.head, current.tail)
    }
  }.holds

  def checkPrimorialModZeroAll(primes: List[Prime]): Boolean = {
    decreases(primes.size)
    checkPrimorialModZeroTailLoop(List.empty, primes)
  }.holds
}
