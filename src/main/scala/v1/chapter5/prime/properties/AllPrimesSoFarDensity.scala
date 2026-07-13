package v1.chapter5.prime.properties

import stainless.collection.List
import stainless.lang.*
import v1.chapter2.div.Calc
import v1.chapter2.div.properties.{AdditionAndMultiplication, ConsecutiveIntegers, ModSmallDividend}
import v1.chapter2.div.properties.ModNativeCompatibility
import v1.chapter5.prime.CoprimeUtils
import v1.chapter3.list.ListBoundUtils
import v1.chapter3.list.properties.{ListProduct, ListProductDiv}
import v1.chapter5.prime.{AllPrimesSoFarList, Prime, PrimeUtils, SortedPrimeList}

object AllPrimesSoFarDensity {

  private def previousFilterScale(filters: List[BigInt]): BigInt = {
    decreases(filters.size)
    if (filters.isEmpty) BigInt(1)
    else (filters.head - BigInt(1)) * previousFilterScale(filters.tail)
  }

  private def assertPreviousFilterScalePositive(
    filters: List[BigInt]
  ): Boolean = {
    require(ListBoundUtils.allGreaterThan(filters, BigInt(1)))
    decreases(filters.size)

    if (filters.isEmpty) {
      previousFilterScale(filters) >= BigInt(1)
    } else {
      assert(filters.head > BigInt(1))
      assert(filters.head - BigInt(1) >= BigInt(1))
      assert(ListBoundUtils.allGreaterThan(filters.tail, BigInt(1)))
      assertPreviousFilterScalePositive(filters.tail)
      assert(previousFilterScale(filters.tail) >= BigInt(1))
      previousFilterScale(filters) >= BigInt(1)
    }
  }.ensuring(res => res && previousFilterScale(filters) >= BigInt(1))

  def assertHeadDensityPreservedAfterPreviousFiltersConditional(
    start: BigInt,
    head: BigInt,
    previous: List[BigInt],
    blocks: BigInt
  ): Boolean = {
    require(start >= BigInt(0))
    require(head > BigInt(1))
    require(blocks >= BigInt(1))
    require(ListBoundUtils.allGreaterThan(previous, BigInt(1)))
    require(ListBoundUtils.allLessThan(previous, head))
    decreases(previous.size)

    val scale = previousFilterScale(previous)

    if (previous.isEmpty) {
      assert(scale == BigInt(1))
    } else {
      val p = previous.head
      val tail = previous.tail
      val tailScale = previousFilterScale(tail)
      val localBlocks = blocks * tailScale

      assert(p > BigInt(1))
      assert(p < head)
      assert(p != head)
      assert(ListBoundUtils.allGreaterThan(tail, BigInt(1)))
      assert(ListBoundUtils.allLessThan(tail, head))
      assertPreviousFilterScalePositive(tail)
      assert(tailScale >= BigInt(1))
      assert(localBlocks >= BigInt(1))
      ConsecutiveIntegers.densityPreservedAfterFiltering(start, p, head, localBlocks)
      assertHeadDensityPreservedAfterPreviousFiltersConditional(start, head, tail, blocks)
      assert(scale == (p - BigInt(1)) * tailScale)
    }

    (blocks * scale) * head == blocks * head * scale
  }.ensuring(res =>
    res && (blocks * previousFilterScale(previous)) * head ==
      blocks * head * previousFilterScale(previous)
  )

  def assertHeadDensityPreservedAfterAllPreviousFilters(
    primes: AllPrimesSoFarList,
    start: BigInt,
    blocks: BigInt
  ): Boolean = {
    require(!primes.isEmpty)
    require(start >= BigInt(0))
    require(blocks >= BigInt(1))

    val primeList = primes.list.list
    val head = primes.head.value
    val previousPrimes = primeList.tail
    val previous = PrimeUtils.primeValues(previousPrimes)

    assert(SortedPrimeList.isDescending(primeList))
    SortedPrimeList.assertTailDescending(primeList)
    assert(SortedPrimeList.isDescending(previousPrimes))

    if (previousPrimes.nonEmpty) {
      assert(primeList.head.value > previousPrimes.head.value)
      assert(previousPrimes.head.value < head)
    }

    assertPrimeValuesLessThan(previousPrimes, head)
    assert(ListBoundUtils.allLessThan(previous, head))
    assert(ListBoundUtils.allGreaterThan(previous, BigInt(1)))
    assertHeadDensityPreservedAfterPreviousFiltersConditional(start, head, previous, blocks)
  }.holds

  private def assertPrimeValuesLessThan(
    primes: List[Prime],
    bound: BigInt
  ): Boolean = {
    require(SortedPrimeList.isDescending(primes))
    require(primes.isEmpty || primes.head.value < bound)
    decreases(primes.size)

    val values = PrimeUtils.primeValues(primes)

    if (primes.isEmpty) {
      ListBoundUtils.allLessThan(values, bound)
    } else {
      assert(values.head == primes.head.value)
      assert(values.head < bound)
      SortedPrimeList.assertTailDescending(primes)

      if (primes.tail.nonEmpty) {
        assert(primes.head.value > primes.tail.head.value)
        assert(primes.tail.head.value < bound)
      }

      assertPrimeValuesLessThan(primes.tail, bound)
      assert(values.tail == PrimeUtils.primeValues(primes.tail))
      assert(ListBoundUtils.allLessThan(values.tail, bound))
      ListBoundUtils.allLessThan(values, bound)
    }
  }.ensuring(res =>
    res && ListBoundUtils.allLessThan(PrimeUtils.primeValues(primes), bound)
  )

  private def assertNoMultipleOfHeadForPrimeValues(
    head: BigInt,
    primes: List[Prime]
  ): Boolean = {
    require(head > BigInt(1))
    require(ListBoundUtils.allGreaterThan(PrimeUtils.primeValues(primes), BigInt(0)))
    require(ListBoundUtils.allLessThan(PrimeUtils.primeValues(primes), head))
    decreases(primes.size)

    val values = PrimeUtils.primeValues(primes)

    if (values.isEmpty) {
      ConsecutiveIntegers.noMultipleOfHead(head, values)
    } else {
      val q = values.head

      assert(q > BigInt(0))
      assert(q < head)
      ModSmallDividend.modSmallDividend(q, head)
      ModNativeCompatibility.percentEqualsCalcMod(q, head)
      assert(q % head == q)
      assert(q % head != BigInt(0))

      assert(values.tail == PrimeUtils.primeValues(primes.tail))
      assert(ListBoundUtils.allGreaterThan(values.tail, BigInt(0)))
      assert(ListBoundUtils.allLessThan(values.tail, head))
      assertNoMultipleOfHeadForPrimeValues(head, primes.tail)
      assert(ConsecutiveIntegers.noMultipleOfHead(head, values.tail))
      ConsecutiveIntegers.noMultipleOfHead(head, values)
    }
  }.ensuring(res =>
    res && ConsecutiveIntegers.noMultipleOfHead(head, PrimeUtils.primeValues(primes))
  )

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
   * Prime values extracted from all-primes-so-far are non-redundant filters.
   */
  def assertPrimeValuesNoMultiplesInAllPrimesSoFar(
    primes: AllPrimesSoFarList
  ): Boolean = {
    decreases(primes.size)

    val primeList = primes.list.list
    val values = PrimeUtils.primeValues(primeList)

    if (values.isEmpty || values.tail.isEmpty) {
      ConsecutiveIntegers.noMultiplesInList(values)
    } else {
      assert(SortedPrimeList.isDescending(primeList))
      assert(values.head == primeList.head.value)
      assert(values.head > BigInt(1))
      assert(values.tail == PrimeUtils.primeValues(primeList.tail))

      SortedPrimeList.assertTailDescending(primeList)
      assert(primeList.head.value > primeList.tail.head.value)
      assertPrimeValuesLessThan(primeList.tail, values.head)
      assert(ListBoundUtils.allLessThan(values.tail, values.head))
      assertNoMultipleOfHeadForPrimeValues(values.head, primeList.tail)
      assert(ConsecutiveIntegers.noMultipleOfHead(values.head, values.tail))

      assertPrimeValuesNoMultiplesInAllPrimesSoFar(primes.tail)
      assert(ConsecutiveIntegers.noMultiplesInList(values.tail))
      ConsecutiveIntegers.noMultiplesInList(values)
    }
  }.holds

  /**
   * The Chapter 2 density theorem applies to the exact prime values carried by
   * all-primes-so-far.
   */
  def assertDensityForAllPrimesSoFar(
    primes: AllPrimesSoFarList,
    start: BigInt,
    blocks: BigInt
  ): Boolean = {
    require(start >= BigInt(0))
    require(blocks >= BigInt(1))

    val primeList = primes.list.list
    val values = PrimeUtils.primeValues(primeList)
    val modulus = PrimeUtils.primorial(primeList)

    assertPrimeValuesNoMultiplesInAllPrimesSoFar(primes)
    assert(ConsecutiveIntegers.noMultiplesInList(values))
    assertPrimeValuesDividePrimorial(primes)
    assert(ConsecutiveIntegers.allPrimesDivideM(values, modulus))
    assertDensityForAllPrimesSoFarConditional(primes, start, blocks)
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
