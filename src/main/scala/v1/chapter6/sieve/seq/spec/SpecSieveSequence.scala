package v1.chapter6.sieve.seq.spec

import stainless.collection.List
import stainless.lang.*
import v1.chapter2.div.Calc
import v1.chapter2.div.properties.{AdditionAndMultiplication, ModIdempotence, ModOperations}
import v1.chapter3.list.ListUtils
import v1.chapter5.prime.*
import v1.chapter6.sieve.seq.spec.SieveUtils

import scala.annotation.tailrec

/**
 * Linear-scan specification for one sieve-sequence stage.
 *
 * This is the mathematical source of truth for the package. It models one stage
 * as an infinite stream of natural numbers starting at the current head. The
 * tail primes are the active filters, and a value is accepted exactly when it is
 * not a multiple of any tail prime.
 *
 * This class is intentionally not the operational gap-cycle representation.
 * There is no stored `GapCycle`, no residue sorting, and no rotated finite
 * history. The point is to make the semantics plain enough to prove stream
 * facts such as soundness, completeness, strict monotonicity, period, gap
 * positivity, and spec-level counting theorems.
 *
 * `CycleSieveSequence` is the concrete replay representation. It should match
 * this spec, but it does not define the meaning of acceptance. The bridge from
 * this spec to a trusted cycle lives in `SpecDerivedSieveSequence`.
 *
 * For example, with `[3, 2]`, the head is `3` and the only filter is `2`, so
 * the generator should produce `3, 5, 7, 9, 11, ...`. The value `9` is accepted
 * even though it is not prime, because the only question at this stage is
 * whether it is a multiple of `2`.
 *
 * With `[5, 3, 2]`, the head is `5` and the filters are `3` and `2`, so the
 * generator should produce `5, 7, 11, 13, 17, 19, 23, 25, ...`. Again, `25` is
 * accepted because it is not divisible by `3` or `2`; the head `5` is not part
 * of the active filter.
 *
 * The class is also not claiming that every emitted value is prime. A single
 * stage filters only by previous primes. Prime generation comes from the chain
 * of stage heads, not from treating every value emitted by one stage as prime.
 */
case class SpecSieveSequence(primes: AllPrimesSoFarList) {
  require(!primes.isEmpty)
  require(primes.size > 1)
  require(CoprimeUtils.isCoprime(primes.head.value, PrimeUtils.primeValues(primes.list.tail.list)))

  // ── Data Model ──────────────────────────────────────────────────────────

  def head: Prime = primes.head

  def filterPrimes: List[Prime] = primes.list.tail.list

  def filterValues: List[BigInt] =
    PrimeUtils.primeValues(filterPrimes)

  def tailPrimorial: BigInt = {
    PrimeUtils.primorialPositive(filterPrimes)
    PrimeUtils.primorial(filterPrimes)
  }.ensuring(_ > BigInt(0))

  def searchBound(k: BigInt): BigInt = {
    require(k >= BigInt(0))
    head.value + k * tailPrimorial
  }.ensuring(_ >= head.value)

  /** True when `value` is coprime with every active filter prime. */
  def passesFilter(value: BigInt): Boolean =
    CoprimeUtils.isCoprime(value, PrimeUtils.primeValues(filterPrimes))

  def accepts(value: BigInt): Boolean =
    value >= head.value && passesFilter(value)

  def apply(k: BigInt): BigInt = {
    require(k >= BigInt(0))
    decreases(k)

    if (k == BigInt(0)) {
      assert(accepts(head.value))
      head.value
    } else {
      val previous = apply(k - BigInt(1))
      val upper = searchBound(k)

      assert(previous <= searchBound(k - BigInt(1)))
      assert(tailPrimorial > BigInt(0))
      assert(searchBound(k - BigInt(1)) < upper)
      assert(previous + BigInt(1) <= upper)
      assert(searchBoundPassesFilter(k))
      assert(accepts(upper))
      searchNext(previous + BigInt(1), upper)
    }
  }.ensuring(res => res >= head.value && res <= searchBound(k) && accepts(res))

  def next: SpecSieveSequence = {
    require(primes.nextPrime.value < head.value * head.value)

    val newPrimes = primes.next

    SortedPrimeList.assertTailDescending(newPrimes.list.list)
    assert(PrimeUtils.primeIsCoprimeWithSmallerList(
      newPrimes.head.value, newPrimes.list.tail.list
    ))

    SpecSieveSequence(newPrimes)
  }

  @tailrec
  final def noAcceptedBetween(from: BigInt, until: BigInt): Boolean = {
    require(from >= head.value)
    require(from <= until)
    decreases(until - from)

    if (from == until) {
      true
    } else {
      !accepts(from) && noAcceptedBetween(from + BigInt(1), until)
    }
  }

  private def searchBoundPassesFilter(k: BigInt): Boolean = {
    require(k >= BigInt(0))

    primorialMatchesSieveProduct(filterPrimes)
    assert(tailPrimorial == SieveUtils.product(filterValues))
    assert(expandedCoprimePreservesFilter(
      head.value,
      k,
      tailPrimorial,
      filterValues,
      BigInt(1)
    ))
    passesFilter(searchBound(k))
  }.holds

  private def searchNext(current: BigInt, upper: BigInt): BigInt = {
    require(current >= head.value)
    require(current <= upper)
    require(accepts(upper))
    decreases(upper - current)

    if (accepts(current)) {
      current
    } else {
      assert(current < upper)
      val next = searchNext(current + BigInt(1), upper)
      assert(!accepts(current))
      assert(noAcceptedBetween(current + BigInt(1), next))
      next
    }
  }.ensuring(res =>
    res >= current &&
      res <= upper &&
      accepts(res) &&
      noAcceptedBetween(current, res)
  )

  // ── Core Proofs ─────────────────────────────────────────────────────────

  /** Proves the generator makes progress: apply(k+1) > apply(k). */
  def applyStrictlyIncreases(k: BigInt): Boolean = {
    require(k >= BigInt(0))

    val previous = apply(k)
    val upper = searchBound(k + BigInt(1))
    val next = apply(k + BigInt(1))

    assert(previous <= searchBound(k))
    assert(tailPrimorial > BigInt(0))
    assert(searchBound(k) < upper)
    assert(previous + BigInt(1) <= upper)
    assert(searchBoundPassesFilter(k + BigInt(1)))
    assert(accepts(upper))
    assert(next == searchNext(previous + BigInt(1), upper))
    assert(next >= previous + BigInt(1))
    next > previous
  }.holds

  private def assertApplyIncreases(fromIndex: BigInt, toIndex: BigInt): Boolean = {
    require(fromIndex >= BigInt(0))
    require(toIndex >= BigInt(0))
    require(fromIndex < toIndex)
    decreases(toIndex - fromIndex)
    if (fromIndex + BigInt(1) == toIndex) {
      assert(applyStrictlyIncreases(fromIndex))
      apply(fromIndex) < apply(toIndex)
    } else {
      assert(applyStrictlyIncreases(fromIndex))
      assert(assertApplyIncreases(fromIndex + BigInt(1), toIndex))
      apply(fromIndex) < apply(toIndex)
    }
  }.holds

  def applyIndexOrderPreservesValues(from: BigInt, until: BigInt): Boolean = {
    require(from >= BigInt(0))
    require(until >= from)
    decreases(until - from)

    if (from == until) {
      apply(from) <= apply(until)
    } else {
      assert(from < until)
      assert(until - BigInt(1) >= from)
      assert(applyIndexOrderPreservesValues(from, until - BigInt(1)))
      assert(applyStrictlyIncreases(until - BigInt(1)))
      assert(apply(until - BigInt(1)) < apply(until))
      apply(from) <= apply(until)
    }
  }.holds

  def assertApplyMonotonic(from: BigInt, until: BigInt): Boolean = {
    require(from >= BigInt(0))
    require(until >= from)
    assert(applyIndexOrderPreservesValues(from, until))
    apply(from) <= apply(until)
  }.holds

  def applyIndexStrictlyPreservesValues(from: BigInt, until: BigInt): Boolean = {
    require(from >= BigInt(0))
    require(until > from)
    decreases(until - from)

    if (until == from + BigInt(1)) {
      assert(applyStrictlyIncreases(from))
      apply(from) < apply(until)
    } else {
      assert(until - BigInt(1) > from)
      assert(applyIndexStrictlyPreservesValues(from, until - BigInt(1)))
      assert(applyStrictlyIncreases(until - BigInt(1)))
      assert(apply(until - BigInt(1)) < apply(until))
      apply(from) < apply(until)
    }
  }.holds


  def assertApplyInjective(firstIndex: BigInt, secondIndex: BigInt): Boolean = {
    require(firstIndex >= BigInt(0))
    require(secondIndex >= BigInt(0))
    require(apply(firstIndex) == apply(secondIndex))
    if (firstIndex == secondIndex) {
      true
    } else if (firstIndex < secondIndex) {
      assert(assertApplyIncreases(firstIndex, secondIndex))
      assert(apply(firstIndex) < apply(secondIndex))
      firstIndex == secondIndex
    } else {
      assert(assertApplyIncreases(secondIndex, firstIndex))
      assert(apply(secondIndex) < apply(firstIndex))
      firstIndex == secondIndex
    }
  }.holds

  def indexOfAccepted(value: BigInt): BigInt = {
    require(accepts(value))

    assert(value >= head.value)
    assert(apply(BigInt(0)) == head.value)
    assert(apply(BigInt(0)) <= value)
    findIndexForAcceptedFrom(value, BigInt(0))
  }.ensuring(res => res >= BigInt(0) && apply(res) == value && (res > BigInt(0) ==> apply(res - BigInt(1)) < value))

  private def findIndexForAcceptedFrom(value: BigInt, k: BigInt): BigInt = {
    require(accepts(value))
    require(value >= head.value)
    require(k >= BigInt(0))
    require(apply(k) <= value)
    decreases(value - apply(k))

    val current = apply(k)

    if (current == value) {
      k
    } else {
      assert(current < value)
      assert(nextDoesNotPassAcceptedValue(k, value))
      val next = apply(k + BigInt(1))
      assert(next <= value)
      assert(applyStrictlyIncreases(k))
      assert(next > current)
      assert(value - next < value - current)
      val result = findIndexForAcceptedFrom(value, k + BigInt(1))
      assert(result >= k + BigInt(1))
      assert(apply(result) == value)
      result
    }
  }.ensuring(res => res >= k && apply(res) == value && (res > k ==> apply(res - BigInt(1)) < value))

  def assertGapPositive(k: BigInt): Boolean = {
    require(k >= BigInt(0))
    assert(applyStrictlyIncreases(k))
    apply(k + BigInt(1)) - apply(k) > BigInt(0)
  }.holds

  def noAcceptedBetweenRejects(from: BigInt, until: BigInt, value: BigInt): Boolean = {
    require(from >= head.value)
    require(from <= until)
    require(noAcceptedBetween(from, until))
    require(value >= from)
    require(value < until)
    decreases(value - from)

    assert(from < until)
    assert(!accepts(from))

    if (value == from) {
      !accepts(value)
    } else {
      assert(noAcceptedBetween(from + BigInt(1), until))
      assert(value >= from + BigInt(1))
      noAcceptedBetweenRejects(from + BigInt(1), until, value)
      !accepts(value)
    }
  }.holds

  def applySkipsNoAcceptedBetween(k: BigInt): Boolean = {
    require(k > BigInt(0))

    val previous = apply(k - BigInt(1))
    val upper = searchBound(k)
    val result = apply(k)

    assert(previous <= searchBound(k - BigInt(1)))
    assert(tailPrimorial > BigInt(0))
    assert(searchBound(k - BigInt(1)) < upper)
    assert(previous + BigInt(1) <= upper)
    assert(searchBoundPassesFilter(k))
    assert(accepts(upper))
    assert(result == searchNext(previous + BigInt(1), upper))
    noAcceptedBetween(previous + BigInt(1), result)
  }.holds

  def nextDoesNotPassAcceptedValue(k: BigInt, value: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(value >= head.value)
    require(accepts(value))
    require(apply(k) < value)

    val previous = apply(k)
    val next = apply(k + BigInt(1))

    if (next <= value) {
      true
    } else {
      assert(value >= previous + BigInt(1))
      assert(value < next)
      assert(previous + BigInt(1) <= next)
      assert(applySkipsNoAcceptedBetween(k + BigInt(1)))
      assert(noAcceptedBetween(previous + BigInt(1), next))
      assert(noAcceptedBetweenRejects(previous + BigInt(1), next, value))
      assert(!accepts(value))
      next <= value
    }
  }.holds

  def assertNoAcceptedValueBetweenGeneratedValues(k: BigInt, value: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(value >= head.value)
    require(apply(k) < value)
    require(value < apply(k + BigInt(1)))

    val previous = apply(k)
    val nextValue = apply(k + BigInt(1))

    assert(value >= previous + BigInt(1))
    assert(previous + BigInt(1) <= nextValue)
    assert(applySkipsNoAcceptedBetween(k + BigInt(1)))
    assert(noAcceptedBetween(previous + BigInt(1), nextValue))
    assert(noAcceptedBetweenRejects(previous + BigInt(1), nextValue, value))

    !accepts(value)
  }.holds

  def valueBoundImpliesIndexBound(index: BigInt, bound: BigInt): Boolean = {
    require(index >= BigInt(0))
    require(bound >= BigInt(0))
    require(apply(index) <= apply(bound))

    if (index <= bound) {
      true
    } else {
      assert(bound < index)
      assert(bound + BigInt(1) <= index)
      assert(applyStrictlyIncreases(bound))
      assert(apply(bound) < apply(bound + BigInt(1)))
      assert(applyIndexOrderPreservesValues(bound + BigInt(1), index))
      assert(apply(bound + BigInt(1)) <= apply(index))
      assert(apply(bound) < apply(index))
      index <= bound
    }
  }.holds

  def assertIndexOfAcceptedAtMost(value: BigInt, bound: BigInt): Boolean = {
    require(value >= head.value)
    require(accepts(value))
    require(bound >= BigInt(0))
    require(value <= apply(bound))

    val index = indexOfAccepted(value)

    assert(index >= BigInt(0))
    assert(apply(index) == value)
    assert(apply(index) <= apply(bound))
    assert(valueBoundImpliesIndexBound(index, bound))

    index <= bound
  }.holds


  // ── Bridge Proofs ───────────────────────────────────────────────────────
  //
  // These are domain-bridge lemmas that connect the prime-domain product
  // representation to the sieve-domain BigInt product, and prove the filter
  // periodicity that makes the bounded search work. They are kept here because
  // searchBoundPassesFilter depends on them, and because their .ensuring
  // blocks on assertBlockShift and assertGapPeriodic use them.

  def primorialMatchesSieveProduct(primeList: List[Prime]): Boolean = {
    decreases(primeList.size)

    if (primeList.isEmpty) {
      PrimeUtils.primorial(primeList) == SieveUtils.product(PrimeUtils.primeValues(primeList))
    } else {
      primorialMatchesSieveProduct(primeList.tail)
      PrimeUtils.primorial(primeList) == SieveUtils.product(PrimeUtils.primeValues(primeList))
    }
  }.holds

  def expandedCoprimePreservesFilter(
    r: BigInt,
    i: BigInt,
    modulus: BigInt,
    values: List[BigInt],
    prefixProd: BigInt
  ): Boolean = {
    require(i >= BigInt(0))
    require(modulus > BigInt(0))
    require(prefixProd > BigInt(0))
    require(ListUtils.checkAllPositive(values))
    require(modulus == prefixProd * SieveUtils.product(values))
    require(SieveUtils.isCoprime(r, values))
    decreases(values.size)

    if (values.isEmpty) {
      SieveUtils.isCoprime(r + i * modulus, values)
    } else {
      val p = values.head
      val factor = prefixProd * SieveUtils.product(values.tail)

      assert(SieveUtils.assertProductNonNegative(values.tail))
      assert(SieveUtils.product(values.tail) >= BigInt(0))
      assert(factor >= BigInt(0))
      assert(SieveUtils.assertMultipleModZero(factor, p))
      assert(Calc.mod(modulus, p) == BigInt(0))
      assert(SieveUtils.assertIsCoprimeForAll(r, values))
      assert(Calc.mod(r, p) != BigInt(0))
      assert(SieveUtils.assertMultiplePreservesDivisible(i, modulus, p))
      assert(Calc.mod(i * modulus, p) == BigInt(0))
      assert(SieveUtils.assertAddPreservesNotZeroMod(r, p, i * modulus))
      assert(Calc.mod(r + i * modulus, p) != BigInt(0))
      assert(expandedCoprimePreservesFilter(r, i, modulus, values.tail, prefixProd * p))
      assert(SieveUtils.isCoprime(r + i * modulus, values.tail))
      SieveUtils.isCoprime(r + i * modulus, values)
    }
  }.holds

  def assertModIsCoprimeForAll(
    value: BigInt,
    r: BigInt,
    q: BigInt,
    modulus: BigInt,
    values: List[BigInt],
    prefixProd: BigInt
  ): Boolean = {
    require(ListUtils.checkAllPositive(values))
    require(SieveUtils.isCoprime(value, values))
    require(q >= BigInt(0))
    require(modulus > BigInt(0))
    require(prefixProd > BigInt(0))
    require(modulus == prefixProd * SieveUtils.product(values))
    require(Calc.mod(value, modulus) == r)
    require(Calc.div(value, modulus) == q)
    decreases(values.size)

    if (values.isEmpty) {
      SieveUtils.isCoprime(r, values)
    } else {
      val p = values.head
      val tailProd = SieveUtils.product(values.tail)

      assert(SieveUtils.assertProductNonNegative(values.tail))
      assert(tailProd >= BigInt(0))
      assert(prefixProd * tailProd >= BigInt(0))
      assert(SieveUtils.assertMultipleModZero(prefixProd * tailProd, p))
      assert(Calc.mod(modulus, p) == BigInt(0))

      assert(SieveUtils.assertIsCoprimeSound(value, values))
      assert(Calc.mod(value, p) != BigInt(0))

      assert(SieveUtils.assertMultiplePreservesDivisible(q, modulus, p))
      assert(Calc.mod(q * modulus, p) == BigInt(0))

      assert(value == q * modulus + r)
      ModOperations.modZeroPlusC(q * modulus, p, r)
      assert(Calc.mod(value, p) == Calc.mod(r, p))

      assert(Calc.mod(r, p) != BigInt(0))

      val newPrefix = prefixProd * p
      assert(SieveUtils.product(values) == p * tailProd)
      assert(modulus == newPrefix * tailProd)
      assert(assertModIsCoprimeForAll(value, r, q, modulus, values.tail, newPrefix))
      SieveUtils.isCoprime(r, values)
    }
  }.holds

  def assertReverseCoprimePreservation(
    v: BigInt,
    modulus: BigInt,
    values: List[BigInt],
    prefixProd: BigInt
  ): Boolean = {
    require(v >= BigInt(0))
    require(ListUtils.checkAllPositive(values))
    require(SieveUtils.isCoprime(v + modulus, values))
    require(modulus > BigInt(0))
    require(prefixProd > BigInt(0))
    require(modulus == prefixProd * SieveUtils.product(values))
    decreases(values.size)

    if (values.isEmpty) {
      SieveUtils.isCoprime(v, values)
    } else {
      val p = values.head
      val tailProd = SieveUtils.product(values.tail)

      assert(SieveUtils.assertProductNonNegative(values.tail))
      assert(tailProd >= BigInt(0))
      assert(prefixProd * tailProd >= BigInt(0))
      assert(SieveUtils.assertMultipleModZero(prefixProd * tailProd, p))
      assert(Calc.mod(modulus, p) == BigInt(0))

      assert(SieveUtils.assertIsCoprimeSound(v + modulus, values))
      assert(Calc.mod(v + modulus, p) != BigInt(0))

      ModOperations.modAdd(v, p, modulus)
      ModIdempotence.modIdempotence(v, p)
      assert(Calc.mod(v + modulus, p) == Calc.mod(v, p))

      assert(Calc.mod(v, p) != BigInt(0))

      val newPrefix = prefixProd * p
      assert(SieveUtils.product(values) == p * tailProd)
      assert(modulus == newPrefix * tailProd)
      assert(assertReverseCoprimePreservation(v, modulus, values.tail, newPrefix))
      SieveUtils.isCoprime(v, values)
    }
  }.holds

  def assertBlockShift(k: BigInt, p: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(p >= BigInt(0))
    require(apply(p) == head.value + tailPrimorial)
    decreases(k)

    if (k == BigInt(0)) {
      true
    } else {
      primorialMatchesSieveProduct(filterPrimes)
      assert(tailPrimorial == SieveUtils.product(filterValues))
      assert(assertBlockShift(k - 1, p))
      true
    }
  }.ensuring(res => {
    if (k == BigInt(0)) {
      res && apply(p) == apply(k) + tailPrimorial
    } else {
      primorialMatchesSieveProduct(filterPrimes)
      assert(tailPrimorial == SieveUtils.product(filterValues))

      val target = apply(k) + tailPrimorial
      assert(target >= head.value)
      primorialMatchesSieveProduct(filterPrimes)
      assert(tailPrimorial == SieveUtils.product(filterValues))
      assert(SieveUtils.isCoprime(apply(k), filterValues))
      assert(expandedCoprimePreservesFilter(
        apply(k), BigInt(1), tailPrimorial, filterValues, BigInt(1)
      ))
      assert(accepts(target))
      assert(apply(k - 1 + p) < target)
      assert(nextDoesNotPassAcceptedValue(k - 1 + p, target))
      assert(apply(k + p) <= target)

      val shifted = apply(k + p) - tailPrimorial
      assert(shifted >= BigInt(0))
      assert(assertReverseCoprimePreservation(shifted, tailPrimorial, filterValues, BigInt(1)))
      assert(accepts(shifted))
      assert(apply(k - 1) < shifted)
      assert(nextDoesNotPassAcceptedValue(k - 1, shifted))
      assert(apply(k) <= shifted)
      assert(apply(k) + tailPrimorial <= apply(k + p))

      res && apply(k + p) == apply(k) + tailPrimorial
    }
  })

}
