package v1.chapter60.sieve.seq.spec.properties

import stainless.annotation.extern
import stainless.collection.List
import stainless.lang.*
import v1.chapter2.div.Calc
import v1.chapter2.div.properties.{AdditionAndMultiplication, ModIdempotence, ModOperations}
import v1.chapter3.list.{ListBoundUtils, ListUtils}
import v1.chapter4.cycle.gap.GapCycle
import v1.chapter4.cycle.integral.recursive.CycleIntegral
import v1.chapter4.cycle.integral.recursive.properties.CycleIntegralProperties
import v1.chapter4.cycle.memory.properties.MemCycleProperties
import v1.chapter5.prime.*
import v1.chapter5.prime.properties.PrimeProperties
import v1.chapter6.seq.sieve.SieveUtils
import v1.chapter60.sieve.seq.spec.SpecSieveSequence

import scala.annotation.tailrec

final case class SpecSieveSeqPeriodProperties(seq: SpecSieveSequence) {
  import seq.*

  def assertHeadPlusTailPrimorialAccepted(): Boolean = {
    primorialMatchesSieveProduct(filterPrimes)
    assert(tailPrimorial == SieveUtils.product(filterValues))
    assert(assertHeadPlusTailCoprimeWalk(filterPrimes, BigInt(1)))
    accepts(head.value + tailPrimorial)
  }.holds

  private def assertHeadPlusTailCoprimeWalk(
    primes: List[Prime],
    prefixProd: BigInt
  ): Boolean = {
    require(!primes.isEmpty)
    require(prefixProd >= BigInt(0))
    require(tailPrimorial == prefixProd * SieveUtils.product(PrimeUtils.primeValues(primes)))
    require(CoprimeUtils.isCoprime(head.value, PrimeUtils.primeValues(primes)))
    decreases(primes.size)

    val p = primes.head.value
    val suffixValues = PrimeUtils.primeValues(primes.tail)
    if (primes.tail.isEmpty) {
      CoprimeUtils.assertMultipleModZero(prefixProd, p)
      ModOperations.modZeroPlusC(tailPrimorial, p, head.value)
      CoprimeUtils.isCoprime(head.value + tailPrimorial, PrimeUtils.primeValues(primes))
    } else {
      val suffixProduct = SieveUtils.product(suffixValues)
      val factor = prefixProd * suffixProduct
      SieveUtils.assertProductNonNegative(List(factor))
      CoprimeUtils.assertMultipleModZero(factor, p)
      ModOperations.modZeroPlusC(tailPrimorial, p, head.value)
      assert(SieveUtils.product(PrimeUtils.primeValues(primes)) == p * suffixProduct)
      assert(assertHeadPlusTailCoprimeWalk(primes.tail, prefixProd * p))
      CoprimeUtils.isCoprime(head.value + tailPrimorial, PrimeUtils.primeValues(primes))
    }
  }.holds

  /**
   * Returns the number of accepted values in one filter period.
   *
   * The period boundary is `head.value + tailPrimorial` — the first accepted
   * value after stepping through a full residue cycle. This is the canonical
   * gap-cycle size for the current stage.
   *
   * Requires `accepts(head.value + tailPrimorial)` as a precondition.
   * The `SpecDerivedSieveSequence` constructor discharges this via
   * `apply(period) == head + tailPrimorial` together with `apply`'s
   * postcondition `accepts(result)`.
   */
  def period(): BigInt = {
    assert(assertHeadPlusTailPrimorialAccepted())
    indexOfAccepted(head.value + tailPrimorial)
  }.ensuring(s => s > BigInt(0) && apply(s) == head.value + tailPrimorial)

  /**
   * Proves that the residue of apply(k) modulo tail primorial is coprime
   * with all filter primes. This establishes the fundamental connection
   * between V0's linear-scan generator and the residue cycle: every
   * generated value, when reduced modulo the filter modulus, lands on
   * a residue that survives all filter primes.
   *
   * For each filter prime p:
   *   1. accepts(apply(k)) gives Calc.mod(apply(k), p) != 0
   *      2. Since tailPrimorial = product(filterValues), each p divides it.
   *      Uses the prefix-product decomposition from expandedCoprimePreservesFilter
   *      to prove Calc.mod(tailPrimorial, p) == 0 at each step.
   *      3. assertMultiplePreservesDivisible gives Calc.mod(q * tailPrimorial, p) == 0
   *      4. modZeroPlusC gives Calc.mod(q*tailPrimorial + r, p) == Calc.mod(r, p)
   *      (when mod(q*tailPrimorial, p) == 0, which follows from step 2)
   *      5. From (1) and (4): Calc.mod(r, p) != 0
   *      Therefore isCoprime(r, filterValues).
   */
  def assertApplyModIsCoprime(k: BigInt): Boolean = {
    require(k >= BigInt(0))

    val value = apply(k)
    val r = Calc.mod(value, tailPrimorial)
    val q = Calc.div(value, tailPrimorial)

    primorialMatchesSieveProduct(filterPrimes)
    assert(tailPrimorial == SieveUtils.product(filterValues))

    assertModIsCoprimeForAll(value, r, q, tailPrimorial, filterValues, BigInt(1))
  }.holds

  /**
   * Proves that the residues of apply(k) modulo tailPrimorial cycle
   * with period p = indexOfAccepted(head + tailPrimorial).
   *
   * From assertBlockShift: apply(k + p) == apply(k) + tailPrimorial.
   * Then mod(apply(k+p), M) == mod(apply(k) + M, M) == mod(apply(k), M).
   */
  def assertApplyResidueCycles(k: BigInt, p: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(p >= BigInt(0))
    require(apply(p) == head.value + tailPrimorial)
    true
  }.ensuring(res => {
    primorialMatchesSieveProduct(filterPrimes)
    assert(tailPrimorial == SieveUtils.product(filterValues))
    assert(assertBlockShift(k, p))
    assert(apply(k + p) == apply(k) + tailPrimorial)
    assert(AdditionAndMultiplication.APlusMultipleTimesBSameMod(apply(k), tailPrimorial, BigInt(1)))
    res && Calc.mod(apply(k + p), tailPrimorial) == Calc.mod(apply(k), tailPrimorial)
  })

  def assertGapPeriodic(k: BigInt, p: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(p >= BigInt(0))
    require(apply(p) == head.value + tailPrimorial)
    true
  }.ensuring(res => {
    primorialMatchesSieveProduct(filterPrimes)
    assert(tailPrimorial == SieveUtils.product(filterValues))
    assert(assertBlockShift(k, p))
    assert(apply(k + p) == apply(k) + tailPrimorial)
    assert(assertBlockShift(k + BigInt(1), p))
    assert(apply(k + BigInt(1) + p) == apply(k + BigInt(1)) + tailPrimorial)
    val g1 = apply(k + BigInt(1)) - apply(k)
    val g2 = apply(k + BigInt(1) + p) - apply(k + p)
    res && g1 == g2
  })

  /**
   * Asserts that the sum of gaps from `0` to `p` equals `tailPrimorial`, where
   * p = indexOfAccepted(head + tailPrimorial).
   *
   * @param p any position
   * @return true if the assertion holds
   */
  def assertGapSum(p: BigInt): Boolean = {
    require(p >= BigInt(0))
    require(apply(p) == head.value + tailPrimorial)
    primorialMatchesSieveProduct(filterPrimes)
    assert(tailPrimorial == SieveUtils.product(filterValues))
    assert(assertSumGapTelescopes(BigInt(0), p))
    sumGap(BigInt(0), p) == tailPrimorial
  }.holds

  /**
   * Proves that `apply(k)` equals `head.value + sumGap(0, k)`.
   *
   * This is the entry point for expressing V0's linear-scan generator as a
   * cumulative-gap-sum (CycleIntegral) representation. By telescoping:
   * {{{
   *   sumGap(0, k) == apply(k) - apply(0) == apply(k) - head.value
   * }}}
   * so rearranging gives `apply(k) == head.value + sumGap(0, k)`.
   *
   * The proof delegates to the private `assertSumGapTelescopes(0, k)` which
   * already proves the telescoping equality. This lemma makes that fact
   * publicly available for the V0-V2 bridge ticket.
   */
  def assertApplyEqualsHeadPlusGapSum(position: BigInt): Boolean = {
    require(position >= BigInt(0))
    assert(assertSumGapTelescopes(BigInt(0), position))
    apply(position) == head.value + sumGap(BigInt(0), position)
  }.holds

  /**
   * Extracts a concrete list of consecutive gaps from the sequence.
   *
   * Returns `[apply(from + 1) - apply(from), ..., apply(from + count - 1) - apply(from + count - 2)]`
   * as a `List[BigInt]`. The list has exactly `count` elements (proved by
   * `assertGapListSize`), and every element is strictly positive (proved by
   * `assertGapListPositive`).
   *
   * This makes the gap cycle explicitly constructable: calling
   * `gapList(0, period)` produces the finite gap list that, when wrapped in a
   * `GapCycle`, generates the same gaps as V0.
   */
  def gapList(from: BigInt, count: BigInt): List[BigInt] = {
    require(from >= BigInt(0))
    require(count >= BigInt(0))
    decreases(count)
    if (count == BigInt(0)) List.empty[BigInt]
    else (apply(from + BigInt(1)) - apply(from)) :: gapList(from + BigInt(1), count - BigInt(1))
  }

  /**
   * Returns true when `value` survives the active tail filters.
   *
   * This method deliberately says nothing about where the generator starts.
   * It answers only the divisibility question: does any prime in `filterPrimes`
   * divide `value`? Keeping this separate from `accepts` is useful for the
   * bounded search proof, because the Euclid-style witness first proves that a
   * number passes the tail filters, and only afterward proves that it is high
   * enough to be inside the current search window.
   */

  /**
   * Proves that every gap in `gapList(from, count)` is strictly positive.
   *
   * The proof uses induction on `count`: each element is `apply(i + 1) - apply(i)`
   * which is strictly positive by `assertGapPositive(i)`. The list-level
   * positivity is expressed via `ListBoundUtils.allGreaterThan(result, 0)`.
   */
  def assertGapListPositive(from: BigInt, count: BigInt): Boolean = {
    require(from >= BigInt(0))
    require(count >= BigInt(0))
    decreases(count)
    if (count == BigInt(0)) {
      ListBoundUtils.allGreaterThan(List.empty[BigInt], BigInt(0))
    } else {
      assert(assertGapPositive(from))
      assert(assertGapListPositive(from + BigInt(1), count - BigInt(1)))
      ListBoundUtils.allGreaterThan(gapList(from, count), BigInt(0))
    }
  }.holds

  /**
   * Proves that `gapList(from, count)` has exactly `count` elements.
   *
   * The proof uses induction on `count`: the base case (empty list) has size 0,
   * and the cons case adds exactly one element.
   */
  def assertGapListSize(from: BigInt, count: BigInt): Boolean = {
    require(from >= BigInt(0))
    require(count >= BigInt(0))
    decreases(count)
    if (count == BigInt(0)) {
      gapList(from, count).size == BigInt(0)
    } else {
      assert(assertGapListSize(from + BigInt(1), count - BigInt(1)))
      gapList(from, count).size == count
    }
  }.holds

  /**
   * Proves that the first element of any non-empty gapList is the adjacent gap.
   *
   * By definition, `gapList(from, count)` for count > 0 unfolds to
   * `(apply(from + 1) - apply(from)) :: gapList(from + 1, count - 1)`,
   * so its head equals `apply(from + 1) - apply(from)`.
   */
  def assertGapListFirstEqualsGap(from: BigInt, count: BigInt): Boolean = {
    require(from >= BigInt(0))
    require(count > BigInt(0))
    gapList(from, count).head == apply(from + BigInt(1)) - apply(from)
  }.holds

  /**
   * Proves that any position in gapList stores the corresponding adjacent gap.
   *
   * `gapList(from, count)(r)` for `r < count` accesses the r-th element
   * of the gap list. By structural induction on `r`, each element is
   * `apply(from + r + 1) - apply(from + r)` — the gap at position `from + r`.
   */
  def assertGapListApplyEqualsGapAtPosition(from: BigInt, count: BigInt, r: BigInt): Boolean = {
    require(from >= BigInt(0))
    require(count > BigInt(0))
    require(r >= BigInt(0))
    require(r < count)
    decreases(r)
    if (r == BigInt(0)) {
      gapList(from, count).apply(r) == apply(from + BigInt(1)) - apply(from)
    } else {
      assert(assertGapListApplyEqualsGapAtPosition(from + BigInt(1), count - BigInt(1), r - BigInt(1)))
      gapList(from, count).apply(r) == apply(from + r + BigInt(1)) - apply(from + r)
    }
  }.holds

  /**
   * Builds the finite gap cycle described by this specification sequence.
   *
   * The period witness is the first index whose generated value has looped
   * forward by exactly one filter modulus:
   *
   * {{{
   *   apply(period) == head.value + tailPrimorial
   * }}}
   *
   * Under that witness, `gapList(0, period)` contains exactly one full period
   * of adjacent specification gaps. `GapCycle` requires two concrete list facts:
   * the list must be non-empty and every gap must be strictly positive. Those
   * facts come from `period > 0`, `assertGapListSize(0, period)`, and
   * `assertGapListPositive(0, period)`.
   *
   * This method is the first bridge for the Spec-vs-Cycle equivalence ticket:
   * it turns the already verified Spec gap facts into the same first-class
   * `GapCycle` object used by `CycleSieveSequence`.
   */
  def specGapCycle(period: BigInt): GapCycle = {
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)

    val gaps = gapList(BigInt(0), period)

    assert(assertGapListPositive(BigInt(0), period))
    assert(assertGapListSize(BigInt(0), period))
    assert(gaps.size == period)
    assert(gaps.nonEmpty)

    GapCycle(gaps)
  }.ensuring(result => result.memCycle.values == gapList(BigInt(0), period))

  /**
   * Exposes the positivity invariant for the full spec gap period.
   *
   * Gap positivity is the local form of `apply` being strictly increasing:
   * each element of `gapList(0, period)` is an adjacent difference
   * `apply(k + 1) - apply(k)`, and `assertGapListPositive` proves every such
   * difference is strictly greater than zero. Pipeline proofs should bridge
   * their computed gap list to this spec-certified list instead of reproving
   * positivity from sorted residues whenever they are proving equivalence to
   * the next spec stage.
   */
  def assertSpecGapPeriodPositive(period: BigInt): Boolean = {
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)

    assert(assertGapListPositive(BigInt(0), period))
    ListBoundUtils.allGreaterThan(gapList(BigInt(0), period), BigInt(0))
  }.holds

  /**
   * Proves the base case of the Spec gap-cycle integral reconstruction.
   *
   * `specGapCycle(period)` stores `gapList(0, period)` as a `GapCycle`. The
   * first value of `CycleIntegral(head.value, gaps)` is therefore:
   *
   * {{{
   *   head.value + gapList(0, period).head
   *   = apply(0) + (apply(1) - apply(0))
   *   = apply(1)
   * }}}
   *
   * This lemma intentionally proves only the first integral position. The full
   * theorem will extend the same idea across all positions using gap-list
   * periodicity and the recursive definition of `CycleIntegral`.
   */
  def assertSpecGapCycleIntegralBase(period: BigInt): Boolean = {
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)

    val gaps = gapList(BigInt(0), period)
    val gapCycle = specGapCycle(period)
    val integral = CycleIntegral(head.value, gapCycle.memCycle)

    assert(gapCycle.memCycle.values == gaps)
    assert(gaps.nonEmpty)
    assert(gaps.head == apply(BigInt(1)) - apply(BigInt(0)))
    assert(integral(BigInt(0)) == head.value + gaps.head)

    integral(BigInt(0)) == apply(BigInt(1))
  }.holds

  /**
   * Proves that every MemCycle access equals the corresponding Spec gap.
   *
   * For every position `i >= 0`, the MemCycle built from `specGapCycle(period)`
   * satisfies `memCycle(i) == apply(i + 1) - apply(i)`. This is the bridge
   * between the period-stored gaps (accessed modulo `period` through ModCycle)
   * and the infinite linear Spec gap sequence.
   *
   * The proof uses induction on `i`:
   * - Base (`i < period`): `memCycle(i)` accesses `gapList(0, period)(i)` directly
   *   (via `smallValueInCycle`), which is `apply(i+1) - apply(i)` by
   *   `assertGapListApplyEqualsGapAtPosition`.
   * - Step (`i >= period`): `memCycle(i) == memCycle(i - period)` by
   *   `valueMatchAfterManyLoops`, and the IH gives `memCycle(i - period) == gap(i - period)`,
   *   while `assertGapPeriodic(i - period, period)` gives `gap(i) == gap(i - period)`.
   */
  def assertMemCycleGapMatch(i: BigInt, period: BigInt): Boolean = {
    require(i >= BigInt(0))
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)
    decreases(i)

    val gapCycle = specGapCycle(period)
    val mem = gapCycle.memCycle

    assert(assertGapListSize(BigInt(0), period))
    assert(mem.period == period)
    assert(mem.period > BigInt(0))
    assert(mem.values == gapList(BigInt(0), period))

    if (i < period) {
      assert(MemCycleProperties.smallValueInCycle(mem, i))
      assert(assertGapListApplyEqualsGapAtPosition(BigInt(0), period, i))
      mem(i) == apply(i + BigInt(1)) - apply(i)
    } else {
      assert(MemCycleProperties.valueMatchAfterManyLoops(mem, i - period, BigInt(1)))
      assert(assertMemCycleGapMatch(i - period, period))
      assert(assertGapPeriodic(i - period, period))
      mem(i) == apply(i + BigInt(1)) - apply(i)
    }
  }.holds

  /**
   * General integral reconstruction theorem for the Spec gap cycle.
   *
   * Proves that `CycleIntegral(head.value, specGapCycle(period).memCycle)`
   * reconstructs the Spec stream: for every `k > 0`,
   * {{{
   *   CycleIntegral(head.value, specGapCycle(period).memCycle)(k - 1) == apply(k)
   * }}}
   *
   * The proof is by induction on `k`. The base case `k = 1` is
   * `assertSpecGapCycleIntegralBase`. For the inductive step:
   *   1. `assertNextPosition` gives `integral(k-1) == integral(k-2) + memCycle(k-1)`.
   *   2. The IH gives `integral(k-2) == apply(k-1)`.
   *   3. `assertMemCycleGapMatch(k-1, period)` gives
   *      `memCycle(k-1) == apply(k) - apply(k-1)`.
   *   Combining: `integral(k-1) == apply(k-1) + (apply(k) - apply(k-1)) == apply(k)`.
   */
  def assertSpecGapCycleIntegralMatchesApply(period: BigInt, k: BigInt): Boolean = {
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)
    require(k > BigInt(0))
    decreases(k)

    val gapCycle = specGapCycle(period)
    val mem = gapCycle.memCycle
    val integral = CycleIntegral(head.value, mem)

    if (k == BigInt(1)) {
      assert(assertSpecGapCycleIntegralBase(period))
      integral(BigInt(0)) == apply(BigInt(1))
    } else {
      assert(CycleIntegralProperties.assertNextPosition(integral, k - BigInt(1)))
      assert(assertSpecGapCycleIntegralMatchesApply(period, k - BigInt(1)))
      assert(assertMemCycleGapMatch(k - BigInt(1), period))
      integral(k - BigInt(1)) == apply(k)
    }
  }.holds

  /**
   * Builds the next V0 sieve stage from the next prime in `AllPrimesSoFarList`.
   *
   * This method exposes the current proof boundary as a caller obligation, in
   * the same style as `List.head` requiring a non-empty list. The caller must
   * provide the missing number-theory fact that the direct next prime is still
   * before `head * head`.
   *
   * The body does not try to rediscover that prime from the V0 generator. It
   * delegates the prime search to `AllPrimesSoFarList.next`, then proves the new
   * head is compatible with the V0 constructor: the new sorted list remains
   * descending, and the new head is coprime to the smaller tail primes.
   */
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

  /**
   * Defines the sum of gaps from `from` to `until` as the sum of individual gaps
   * `apply(i + 1) - apply(i)` for `i` from `from` to `until - 1`. By definition, this is:
   * {{{
   *  sumGap(from, until) == (apply(from + 1) - apply(from)) + (apply(from + 2) - apply(from + 1)) + ... + (apply(until) - apply(until - 1))
   * }}}
   *
   * The base case is when `from == until`, where the sum is defined to be `0` (the empty sum).
   * For the inductive case, we take the first gap `apply(from + 1) - apply(from)` and add it
   * to the sum of the remaining gaps from `from + 1` to `until`.
   *
   * @param from  From index (inclusive)
   * @param until Until index (exclusive)
   * @return BigInt representing the sum of gaps from `from` to `until`
   */
  def sumGap(from: BigInt, until: BigInt): BigInt = {
    require(from >= BigInt(0))
    require(until >= from)
    decreases(until - from)
    if (from == until) BigInt(0)
    else (apply(from + BigInt(1)) - apply(from)) + sumGap(from + BigInt(1), until)
  }

  /**
   * Proves that `sumGap(from, until)` equals `apply(until) - apply(from)` for all `from <= until`.
   *
   * This is the telescoping lemma for the gap sum. By definition, `sumGap(from, until)` is the sum of
   * the individual gaps `apply(i + 1) - apply(i)` for `i` from `from` to `until - 1`.
   * When we expand that sum, all intermediate terms cancel out, leaving only `apply(until) - apply(from)`.
   *
   * @param from  From index (inclusive)
   * @param until Until index (exclusive)
   * @return Boolean true if the assertion that the telescoping equality holds
   */
  def assertSumGapTelescopes(from: BigInt, until: BigInt): Boolean = {
    require(from >= BigInt(0))
    require(until >= from)
    decreases(until - from)
    if (from == until) {
      sumGap(from, until) == apply(until) - apply(from)
    } else {
      assert(assertSumGapTelescopes(from + BigInt(1), until))
      sumGap(from, until) == apply(until) - apply(from)
    }
  }.holds

  /**
   * Proves `sumGap(from, until) > 0` whenever `until > from`.
   *
   * This is the positivity companion to `assertSumGapTelescopes`. Each
   * summand `apply(i + 1) - apply(i)` is strictly positive by
   * `applyStrictlyIncreases`, so the finite telescoped sum is positive as
   * long as the range is non-empty. The induction decreases on
   * `until - from` and explicitly invokes the inductive hypothesis via
   * `assert`, consistent with LEARNINGS.md 2.2.
   *
   * The merged-gap prefix transformer (`mergedGapPrefix`) emits
   * `sumGap(k, nextK)` for each copied or merged step, where
   * `nextMergedGapOldIndex` guarantees `nextK > k`. This lemma turns that
   * index inequality into gap positivity, which is the foundation for
   * proving every emitted prefix gap is positive.
   */
  def assertSumGapPositive(from: BigInt, until: BigInt): Boolean = {
    require(from >= BigInt(0))
    require(until > from)
    decreases(until - from)
    if (from + BigInt(1) == until) {
      assert(applyStrictlyIncreases(from))
      sumGap(from, until) > BigInt(0)
    } else {
      assert(assertSumGapPositive(from + BigInt(1), until))
      assert(applyStrictlyIncreases(from))
      sumGap(from, until) > BigInt(0)
    }
  }.holds

  /**
   * Proves the copy-case value equality across two consecutive sieve stages.
   *
   * When the immediate old successor `apply(k + 1)` survives `nextSeq`'s new front
   * filter, the next accepted value in `nextSeq` after `apply(k)` is exactly the
   * old successor `apply(k + 1)` — the gap is copied, not merged.
   *
   * Formally: if `nextSeq.vIdx = indexOfAccepted(apply(k))`, then
   * `nextSeq(vIdx + 1) == apply(k + 1)`. The proof uses the increasing property
   * of both sequences, the no-skipped-accepted-between lemma, and the acceptance
   * witnesses in both directions, culminating in a sandwich argument that the
   * next-seq candidate `z` equals the old successor `W`.
   *
   * The `.ensuring` block exports the value equality `nextSeq(vIdx + 1) == W`.
   */
  def assertBlockShiftMultiple(k: BigInt, n: BigInt, period: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(n >= BigInt(0))
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)
    decreases(n)
    if (n == BigInt(0)) {
      apply(k + n * period) == apply(k) + n * tailPrimorial
    } else {
      val prev = n - BigInt(1)
      assert(assertBlockShiftMultiple(k, prev, period))
      assert(assertBlockShift(k + prev * period, period))
      apply(k + n * period) == apply(k) + n * tailPrimorial
    }
  }.holds

  /**
   * Extends `assertGapPeriodic` to multiple periods.
   *
   * Proves that gap(k) == gap(k + n * period) for all n >= 0, i.e., shifting
   * by any integer number of periods preserves the gap value. This is the
   * induction-on-n version of the single-period `assertGapPeriodic(k, period)`.
   *
   * The proof proceeds by induction on n. The base case (n = 0) is trivial.
   * For the inductive step, `assertGapPeriodic(k + (n-1)*period, period)` gives
   * gap(k + n*period) == gap(k + (n-1)*period), and the IH gives
   * gap(k + (n-1)*period) == gap(k).
   */
  private def assertGapPeriodicMultiple(k: BigInt, n: BigInt, period: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(n >= BigInt(0))
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)
    decreases(n)
    if (n == BigInt(0)) {
      apply(k + BigInt(1)) - apply(k) == apply(k + BigInt(1)) - apply(k)
    } else {
      assert(assertGapPeriodicMultiple(k, n - BigInt(1), period))
      assert(assertGapPeriodic(k + (n - BigInt(1)) * period, period))
      apply(k + BigInt(1) + n * period) - apply(k + n * period) == apply(k + BigInt(1)) - apply(k)
    }
  }.holds

  /**
   * Proves that the first non-multiple index found by `findFirstNonMultipleAfter`
   * is at or before any known later index `zIdx` whose value is also non-multiple.
   * Used to bound the first survivor position in the merge landing proof.
   */
}
