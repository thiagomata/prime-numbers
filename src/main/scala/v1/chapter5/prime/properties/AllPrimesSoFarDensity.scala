package v1.chapter5.prime.properties

import stainless.lang.*
import v1.chapter2.div.Calc
import v1.chapter2.div.properties.{AdditionAndMultiplication, ConsecutiveIntegers}
import v1.chapter2.div.properties.ModNativeCompatibility
import v1.chapter5.prime.CoprimeUtils
import v1.chapter3.list.ListBoundUtils
import v1.chapter3.list.properties.{ListProduct, ListProductDiv}
import v1.chapter5.prime.{AllPrimesSoFarList, PrimeUtils}

object AllPrimesSoFarDensity {

  private def assertModZeroPreservedByNonNegativeMultiplier(
    value: BigInt,
    divisor: BigInt,
    multiplier: BigInt
  ): Boolean = {
    require(value >= BigInt(0))
    require(divisor > BigInt(0))
    require(multiplier >= BigInt(0))
    require(Calc.mod(value, divisor) == BigInt(0))

    val quotient = Calc.div(value, divisor)

    CoprimeUtils.assertModZeroImpliesDivTimesBEqualsA(value, divisor)
    assert(quotient * divisor == value)
    assert(quotient >= BigInt(0))
    assert(multiplier * quotient >= BigInt(0))

    AdditionAndMultiplication.ATimesBSameMod(
      BigInt(0),
      divisor,
      multiplier * quotient
    )
    CoprimeUtils.assertModZero(divisor)
    assert(Calc.mod((multiplier * quotient) * divisor, divisor) == BigInt(0))
    assert(multiplier * value == (multiplier * quotient) * divisor)
    Calc.mod(multiplier * value, divisor) == BigInt(0)
  }.ensuring(res =>
    res && Calc.mod(multiplier * value, divisor) == BigInt(0)
  )

  private def assertAllElementsDivideScaledProduct(
    elements: stainless.collection.List[BigInt],
    multiplier: BigInt
  ): Boolean = {
    require(multiplier > BigInt(0))
    require(ListBoundUtils.allGreaterThan(elements, BigInt(0)))
    require(ListBoundUtils.allGreaterThan(elements, BigInt(1)))
    decreases(elements.size)

    val product = ListProduct.product(elements)
    val modulus = multiplier * product

    ListProduct.positiveProduct(elements)
    assert(product > BigInt(0))
    assert(modulus > BigInt(0))

    if (elements.isEmpty) {
      ConsecutiveIntegers.allPrimesDivideM(elements, modulus)
    } else {
      val p = elements.head
      val tailProduct = ListProduct.product(elements.tail)
      val tailMultiplier = multiplier * p
      val tailModulus = tailMultiplier * tailProduct

      assert(p > BigInt(0))
      assert(ListProductDiv.ListProductDiv(elements))
      assert(Calc.mod(product, p) == BigInt(0))
      assertModZeroPreservedByNonNegativeMultiplier(product, p, multiplier)
      assert(Calc.mod(modulus, p) == BigInt(0))
      ModNativeCompatibility.percentEqualsCalcMod(modulus, p)
      assert(modulus % p == BigInt(0))

      assertAllElementsDivideScaledProduct(elements.tail, tailMultiplier)
      assert(ConsecutiveIntegers.allPrimesDivideM(elements.tail, tailModulus))
      assert(product == p * tailProduct)
      assert(modulus == tailModulus)
      assert(ConsecutiveIntegers.allPrimesDivideM(elements.tail, modulus))
      ConsecutiveIntegers.allPrimesDivideM(elements, modulus)
    }
  }.ensuring(res =>
    res && ConsecutiveIntegers.allPrimesDivideM(
      elements,
      multiplier * ListProduct.product(elements)
    )
  )

  /**
   * Conditional bridge from the concrete AllPrimesSoFarList stage object to the
   * Chapter 2 prime-list density theorem.
   *
   * This lemma deliberately does not discharge the prime-list structure yet.
   * Callers must still provide the raw density preconditions for the extracted
   * prime values and their primorial.
   */
  def assertDensityForAllPrimesSoFarConditional(
    primes: AllPrimesSoFarList,
    start: BigInt,
    blocks: BigInt
  ): Boolean = {
    require(start >= BigInt(0))
    require(blocks >= BigInt(1))

    val primeList = primes.list.list
    val values = PrimeUtils.primeValues(primeList)
    val modulus = PrimeUtils.primorial(primeList)

    require(modulus > BigInt(0))
    require(ConsecutiveIntegers.noMultiplesInList(values))
    require(ConsecutiveIntegers.allPrimesDivideM(values, modulus))

    ConsecutiveIntegers.densityForPrimeList(start, values, modulus, blocks)
  }.holds

  /**
   * The primorial of the prime list is divisible by every extracted prime value.
   */
  def assertPrimeValuesDividePrimorial(
    primes: AllPrimesSoFarList
  ): Boolean = {
    val primeList = primes.list.list
    val values = PrimeUtils.primeValues(primeList)
    val modulus = PrimeUtils.primorial(primeList)

    assert(modulus == ListProduct.product(values))
    assert(ListProductDiv.allElementsDivideProduct(values))

    if (values.isEmpty) {
      ConsecutiveIntegers.allPrimesDivideM(values, modulus)
    } else {
      assert(values.head > BigInt(1))
      assert(ListProduct.positiveProduct(values))
      assert(modulus > BigInt(0))
      assert(ListProductDiv.ListProductDiv(values))
      assert(Calc.mod(modulus, values.head) == BigInt(0))
      ModNativeCompatibility.percentEqualsCalcMod(modulus, values.head)
      assert(modulus % values.head == BigInt(0))
      assert(ListProductDiv.allElementsDivideProduct(values.tail))
      assertAllElementsDivideScaledProduct(values.tail, values.head)
      assert(ConsecutiveIntegers.allPrimesDivideM(
        values.tail,
        values.head * ListProduct.product(values.tail)
      ))
      assert(modulus == values.head * ListProduct.product(values.tail))
      assert(ConsecutiveIntegers.allPrimesDivideM(values.tail, modulus))
      ConsecutiveIntegers.allPrimesDivideM(values, modulus)
    }
  }.holds
}
