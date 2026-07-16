package v1.chapter60.sieve.seq.spec.properties

import stainless.collection.List
import stainless.lang.*
import v1.chapter2.div.Calc
import v1.chapter2.div.properties.{AdditionAndMultiplication, ModOperations}
import v1.chapter3.list.ListBoundUtils
import v1.chapter4.cycle.gap.GapCycle
import v1.chapter4.cycle.integral.recursive.CycleIntegral
import v1.chapter4.cycle.integral.recursive.properties.CycleIntegralProperties
import v1.chapter4.cycle.memory.properties.MemCycleProperties
import v1.chapter5.prime.*
import v1.chapter60.sieve.seq.spec.SieveUtils
import v1.chapter60.sieve.seq.spec.SpecSieveSequence

object SpecSieveSeqPeriodProperties {

  def period(seq: SpecSieveSequence): BigInt = {
    assert(assertHeadPlusTailPrimorialAccepted(seq))
    seq.indexOfAccepted(seq.head.value + seq.tailPrimorial)
  }.ensuring(s => s > BigInt(0) && seq.apply(s) == seq.head.value + seq.tailPrimorial)

  def assertBlockShift(seq: SpecSieveSequence, k: BigInt, p: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(p >= BigInt(0))
    require(seq.apply(p) == seq.head.value + seq.tailPrimorial)
    decreases(k)

    if (k == BigInt(0)) {
      true
    } else {
      seq.primorialMatchesSieveProduct(seq.filterPrimes)
      assert(seq.tailPrimorial == SieveUtils.product(seq.filterValues))
      assert(assertBlockShift(seq, k - 1, p))
      true
    }
  }.ensuring(res => {
    if (k == BigInt(0)) {
      res && seq.apply(p) == seq.apply(k) + seq.tailPrimorial
    } else {
      seq.primorialMatchesSieveProduct(seq.filterPrimes)
      assert(seq.tailPrimorial == SieveUtils.product(seq.filterValues))

      val target = seq.apply(k) + seq.tailPrimorial
      assert(target >= seq.head.value)
      seq.primorialMatchesSieveProduct(seq.filterPrimes)
      assert(seq.tailPrimorial == SieveUtils.product(seq.filterValues))
      assert(SieveUtils.isCoprime(seq.apply(k), seq.filterValues))
      assert(seq.expandedCoprimePreservesFilter(
        seq.apply(k), BigInt(1), seq.tailPrimorial, seq.filterValues, BigInt(1)
      ))
      assert(seq.accepts(target))
      assert(seq.apply(k - 1 + p) < target)
      assert(seq.nextDoesNotPassAcceptedValue(k - 1 + p, target))
      assert(seq.apply(k + p) <= target)

      val shifted = seq.apply(k + p) - seq.tailPrimorial
      assert(shifted >= BigInt(0))
      assert(seq.assertReverseCoprimePreservation(shifted, seq.tailPrimorial, seq.filterValues, BigInt(1)))
      assert(seq.accepts(shifted))
      assert(seq.apply(k - 1) < shifted)
      assert(seq.nextDoesNotPassAcceptedValue(k - 1, shifted))
      assert(seq.apply(k) <= shifted)
      assert(seq.apply(k) + seq.tailPrimorial <= seq.apply(k + p))

      res && seq.apply(k + p) == seq.apply(k) + seq.tailPrimorial
    }
  })

  def assertBlockShiftMultiple(seq: SpecSieveSequence, k: BigInt, n: BigInt, period: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(n >= BigInt(0))
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    decreases(n)
    if (n == BigInt(0)) {
      seq.apply(k + n * period) == seq.apply(k) + n * seq.tailPrimorial
    } else {
      val prev = n - BigInt(1)
      assert(assertBlockShiftMultiple(seq, k, prev, period))
      assert(assertBlockShift(seq, k + prev * period, period))
      seq.apply(k + n * period) == seq.apply(k) + n * seq.tailPrimorial
    }
  }.holds

  def sumGap(seq: SpecSieveSequence, from: BigInt, until: BigInt): BigInt = {
    require(from >= BigInt(0))
    require(until >= from)
    decreases(until - from)
    if (from == until) BigInt(0)
    else (seq.apply(from + BigInt(1)) - seq.apply(from)) + sumGap(seq, from + BigInt(1), until)
  }

  def assertSumGapTelescopes(seq: SpecSieveSequence, from: BigInt, until: BigInt): Boolean = {
    require(from >= BigInt(0))
    require(until >= from)
    decreases(until - from)
    if (from == until) {
      sumGap(seq, from, until) == seq.apply(until) - seq.apply(from)
    } else {
      assert(assertSumGapTelescopes(seq, from + BigInt(1), until))
      sumGap(seq, from, until) == seq.apply(until) - seq.apply(from)
    }
  }.holds

  def assertSumGapPositive(seq: SpecSieveSequence, from: BigInt, until: BigInt): Boolean = {
    require(from >= BigInt(0))
    require(until > from)
    decreases(until - from)
    if (from + BigInt(1) == until) {
      assert(seq.applyStrictlyIncreases(from))
      sumGap(seq, from, until) > BigInt(0)
    } else {
      assert(assertSumGapPositive(seq, from + BigInt(1), until))
      assert(seq.applyStrictlyIncreases(from))
      sumGap(seq, from, until) > BigInt(0)
    }
  }.holds

  def gapList(seq: SpecSieveSequence, from: BigInt, count: BigInt): List[BigInt] = {
    require(from >= BigInt(0))
    require(count >= BigInt(0))
    decreases(count)
    if (count == BigInt(0)) List.empty[BigInt]
    else (seq.apply(from + BigInt(1)) - seq.apply(from)) :: gapList(seq, from + BigInt(1), count - BigInt(1))
  }

  def assertGapListPositive(seq: SpecSieveSequence, from: BigInt, count: BigInt): Boolean = {
    require(from >= BigInt(0))
    require(count >= BigInt(0))
    decreases(count)
    if (count == BigInt(0)) {
      ListBoundUtils.allGreaterThan(List.empty[BigInt], BigInt(0))
    } else {
      assert(seq.assertGapPositive(from))
      assert(assertGapListPositive(seq, from + BigInt(1), count - BigInt(1)))
      ListBoundUtils.allGreaterThan(gapList(seq, from, count), BigInt(0))
    }
  }.holds

  def assertGapListSize(seq: SpecSieveSequence, from: BigInt, count: BigInt): Boolean = {
    require(from >= BigInt(0))
    require(count >= BigInt(0))
    decreases(count)
    if (count == BigInt(0)) {
      gapList(seq, from, count).size == BigInt(0)
    } else {
      assert(assertGapListSize(seq, from + BigInt(1), count - BigInt(1)))
      gapList(seq, from, count).size == count
    }
  }.holds

  def assertGapListFirstEqualsGap(seq: SpecSieveSequence, from: BigInt, count: BigInt): Boolean = {
    require(from >= BigInt(0))
    require(count > BigInt(0))
    gapList(seq, from, count).head == seq.apply(from + BigInt(1)) - seq.apply(from)
  }.holds

  def assertGapListApplyEqualsGapAtPosition(seq: SpecSieveSequence, from: BigInt, count: BigInt, r: BigInt): Boolean = {
    require(from >= BigInt(0))
    require(count > BigInt(0))
    require(r >= BigInt(0))
    require(r < count)
    decreases(r)
    if (r == BigInt(0)) {
      gapList(seq, from, count).apply(r) == seq.apply(from + BigInt(1)) - seq.apply(from)
    } else {
      assert(assertGapListApplyEqualsGapAtPosition(seq, from + BigInt(1), count - BigInt(1), r - BigInt(1)))
      gapList(seq, from, count).apply(r) == seq.apply(from + r + BigInt(1)) - seq.apply(from + r)
    }
  }.holds

  def specGapCycle(seq: SpecSieveSequence, period: BigInt): GapCycle = {
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)

    val gaps = gapList(seq, BigInt(0), period)

    assert(assertGapListPositive(seq, BigInt(0), period))
    assert(assertGapListSize(seq, BigInt(0), period))
    assert(gaps.size == period)
    assert(gaps.nonEmpty)

    GapCycle(gaps)
  }.ensuring(result => result.memCycle.values == gapList(seq, BigInt(0), period))

  def assertSpecGapPeriodPositive(seq: SpecSieveSequence, period: BigInt): Boolean = {
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)

    assert(assertGapListPositive(seq, BigInt(0), period))
    ListBoundUtils.allGreaterThan(gapList(seq, BigInt(0), period), BigInt(0))
  }.holds

  def assertSpecGapCycleIntegralBase(seq: SpecSieveSequence, period: BigInt): Boolean = {
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)

    val gaps = gapList(seq, BigInt(0), period)
    val gapCycle = specGapCycle(seq, period)
    val integral = CycleIntegral(seq.head.value, gapCycle.memCycle)

    assert(gapCycle.memCycle.values == gaps)
    assert(gaps.nonEmpty)
    assert(gaps.head == seq.apply(BigInt(1)) - seq.apply(BigInt(0)))
    assert(integral(BigInt(0)) == seq.head.value + gaps.head)

    integral(BigInt(0)) == seq.apply(BigInt(1))
  }.holds

  def assertMemCycleGapMatch(seq: SpecSieveSequence, i: BigInt, period: BigInt): Boolean = {
    require(i >= BigInt(0))
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    decreases(i)

    val gapCycle = specGapCycle(seq, period)
    val mem = gapCycle.memCycle

    assert(assertGapListSize(seq, BigInt(0), period))
    assert(mem.period == period)
    assert(mem.period > BigInt(0))
    assert(mem.values == gapList(seq, BigInt(0), period))

    if (i < period) {
      assert(MemCycleProperties.smallValueInCycle(mem, i))
      assert(assertGapListApplyEqualsGapAtPosition(seq, BigInt(0), period, i))
      mem(i) == seq.apply(i + BigInt(1)) - seq.apply(i)
    } else {
      assert(MemCycleProperties.valueMatchAfterManyLoops(mem, i - period, BigInt(1)))
      assert(assertMemCycleGapMatch(seq, i - period, period))
      assert(assertGapPeriodic(seq, i - period, period))
      mem(i) == seq.apply(i + BigInt(1)) - seq.apply(i)
    }
  }.holds

  def assertSpecGapCycleIntegralMatchesApply(seq: SpecSieveSequence, period: BigInt, k: BigInt): Boolean = {
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(k > BigInt(0))
    decreases(k)

    val gapCycle = specGapCycle(seq, period)
    val mem = gapCycle.memCycle
    val integral = CycleIntegral(seq.head.value, mem)

    if (k == BigInt(1)) {
      assert(assertSpecGapCycleIntegralBase(seq, period))
      integral(BigInt(0)) == seq.apply(BigInt(1))
    } else {
      assert(CycleIntegralProperties.assertNextPosition(integral, k - BigInt(1)))
      assert(assertSpecGapCycleIntegralMatchesApply(seq, period, k - BigInt(1)))
      assert(assertMemCycleGapMatch(seq, k - BigInt(1), period))
      integral(k - BigInt(1)) == seq.apply(k)
    }
  }.holds

  def assertApplyResidueCycles(seq: SpecSieveSequence, k: BigInt, p: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(p >= BigInt(0))
    require(seq.apply(p) == seq.head.value + seq.tailPrimorial)
    true
  }.ensuring(res => {
    seq.primorialMatchesSieveProduct(seq.filterPrimes)
    assert(seq.tailPrimorial == SieveUtils.product(seq.filterValues))
    assert(seq.assertBlockShift(k, p))
    assert(seq.apply(k + p) == seq.apply(k) + seq.tailPrimorial)
    assert(AdditionAndMultiplication.APlusMultipleTimesBSameMod(seq.apply(k), seq.tailPrimorial, BigInt(1)))
    res && Calc.mod(seq.apply(k + p), seq.tailPrimorial) == Calc.mod(seq.apply(k), seq.tailPrimorial)
  })

  def assertGapPeriodic(seq: SpecSieveSequence, k: BigInt, p: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(p >= BigInt(0))
    require(seq.apply(p) == seq.head.value + seq.tailPrimorial)
    true
  }.ensuring(res => {
    seq.primorialMatchesSieveProduct(seq.filterPrimes)
    assert(seq.tailPrimorial == SieveUtils.product(seq.filterValues))
    assert(seq.assertBlockShift(k, p))
    assert(seq.apply(k + p) == seq.apply(k) + seq.tailPrimorial)
    assert(seq.assertBlockShift(k + BigInt(1), p))
    assert(seq.apply(k + BigInt(1) + p) == seq.apply(k + BigInt(1)) + seq.tailPrimorial)
    val g1 = seq.apply(k + BigInt(1)) - seq.apply(k)
    val g2 = seq.apply(k + BigInt(1) + p) - seq.apply(k + p)
    res && g1 == g2
  })

  def assertGapSum(seq: SpecSieveSequence, p: BigInt): Boolean = {
    require(p >= BigInt(0))
    require(seq.apply(p) == seq.head.value + seq.tailPrimorial)
    seq.primorialMatchesSieveProduct(seq.filterPrimes)
    assert(seq.tailPrimorial == SieveUtils.product(seq.filterValues))
    assert(assertSumGapTelescopes(seq, BigInt(0), p))
    sumGap(seq, BigInt(0), p) == seq.tailPrimorial
  }.holds

  def assertApplyEqualsHeadPlusGapSum(seq: SpecSieveSequence, position: BigInt): Boolean = {
    require(position >= BigInt(0))
    assert(assertSumGapTelescopes(seq, BigInt(0), position))
    seq.apply(position) == seq.head.value + sumGap(seq, BigInt(0), position)
  }.holds

  def assertApplyModIsCoprime(seq: SpecSieveSequence, k: BigInt): Boolean = {
    require(k >= BigInt(0))

    val value = seq.apply(k)
    val r = Calc.mod(value, seq.tailPrimorial)
    val q = Calc.div(value, seq.tailPrimorial)

    seq.primorialMatchesSieveProduct(seq.filterPrimes)
    assert(seq.tailPrimorial == SieveUtils.product(seq.filterValues))

    seq.assertModIsCoprimeForAll(value, r, q, seq.tailPrimorial, seq.filterValues, BigInt(1))
  }.holds

  def assertHeadPlusTailPrimorialAccepted(seq: SpecSieveSequence): Boolean = {
    seq.primorialMatchesSieveProduct(seq.filterPrimes)
    assert(seq.tailPrimorial == SieveUtils.product(seq.filterValues))
    assert(assertHeadPlusTailCoprimeWalk(seq, seq.filterPrimes, BigInt(1)))
    seq.accepts(seq.head.value + seq.tailPrimorial)
  }.holds

  // ── Private helpers ───────────────────────────────────────────────────

  private def assertHeadPlusTailCoprimeWalk(
    seq: SpecSieveSequence,
    primes: List[Prime],
    prefixProd: BigInt
  ): Boolean = {
    require(!primes.isEmpty)
    require(prefixProd >= BigInt(0))
    require(seq.tailPrimorial == prefixProd * SieveUtils.product(PrimeUtils.primeValues(primes)))
    require(CoprimeUtils.isCoprime(seq.head.value, PrimeUtils.primeValues(primes)))
    decreases(primes.size)

    val p = primes.head.value
    val suffixValues = PrimeUtils.primeValues(primes.tail)
    if (primes.tail.isEmpty) {
      CoprimeUtils.assertMultipleModZero(prefixProd, p)
      ModOperations.modZeroPlusC(seq.tailPrimorial, p, seq.head.value)
      CoprimeUtils.isCoprime(seq.head.value + seq.tailPrimorial, PrimeUtils.primeValues(primes))
    } else {
      val suffixProduct = SieveUtils.product(suffixValues)
      val factor = prefixProd * suffixProduct
      SieveUtils.assertProductNonNegative(List(factor))
      CoprimeUtils.assertMultipleModZero(factor, p)
      ModOperations.modZeroPlusC(seq.tailPrimorial, p, seq.head.value)
      assert(SieveUtils.product(PrimeUtils.primeValues(primes)) == p * suffixProduct)
      assert(assertHeadPlusTailCoprimeWalk(seq, primes.tail, prefixProd * p))
      CoprimeUtils.isCoprime(seq.head.value + seq.tailPrimorial, PrimeUtils.primeValues(primes))
    }
  }.holds

  private def assertGapPeriodicMultiple(seq: SpecSieveSequence, k: BigInt, n: BigInt, period: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(n >= BigInt(0))
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    decreases(n)
    if (n == BigInt(0)) {
      seq.apply(k + BigInt(1)) - seq.apply(k) == seq.apply(k + BigInt(1)) - seq.apply(k)
    } else {
      assert(assertGapPeriodicMultiple(seq, k, n - BigInt(1), period))
      assert(assertGapPeriodic(seq, k + (n - BigInt(1)) * period, period))
      seq.apply(k + BigInt(1) + n * period) - seq.apply(k + n * period) == seq.apply(k + BigInt(1)) - seq.apply(k)
    }
  }.holds
}
