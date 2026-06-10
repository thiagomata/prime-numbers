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

//  def checkPrimorialModZero(primes: List[Prime]): Boolean = {
//    def loop(primes: List[Prime]): Boolean = {
//      decreases(primes.size)
//      if (primes.isEmpty) true
//      else {
//        assert(allPrimesDividePrimorial(primes))
//        val p = PrimeUtils.primorial(primes)
//        Calc.mod(p, primes.head.value) == 0 && loop(primes.tail)
//      }
//    }
//    loop(primes)
//  }.holds

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
}
