package v1.chapter60.sieve.seq.spec

import stainless.collection.List
import stainless.lang.*
import v1.chapter2.div.Calc
import v1.chapter2.div.properties.{AdditionAndMultiplication, ModIdempotence, ModOperations}
import v1.chapter3.list.ListUtils
import v1.chapter4.cycle.gap.GapCycle
import v1.chapter5.prime.*
import v1.chapter6.seq.sieve.SieveUtils
import v1.chapter60.sieve.seq.spec.properties.{SpecSieveSeqHeadIsPrime, SpecSieveSeqNextProperties, SpecSieveSeqPeriodProperties, SpecSieveSeqSurvivorCountProperties}

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

  /**
   * Returns the `k`-th value in the tail-filtered stream.
   *
   * The stream starts at `head`, then repeatedly walks through consecutive
   * natural numbers until it finds the next value accepted by the active tail
   * filters. This is deliberately linear: there are no gap cycles, no rotated
   * histories, and no stride arithmetic beyond the finite upper bound used to
   * prove that each scan terminates.
   *
   * For `k = 0`, the constructor invariant already proves that `head` passes
   * the tail-only filter, so the first generated value is exactly `head`.
   *
   * For `k > 0`, the previous generated value is known to be accepted and at
   * most `searchBound(k - 1)`. The next search starts at the following natural
   * number and scans up to `searchBound(k)`. Since `searchBound(k)` itself is
   * proven by `searchBoundPassesFilter(k)` to pass the tail filters, the helper
   * `searchNext` has a finite accepted endpoint and can terminate with measure
   * `upper - current`.
   */
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

  /**
   * The active divisibility filters for this stage.
   *
   * This is the most important semantic choice in V0: the filter is the tail
   * only. The head is the starting point, not a divisor to eliminate. That is
   * why `[5, 3, 2]` accepts `25`; `25` is a multiple of the head `5`, but it is
   * not a multiple of the tail primes `3` or `2`.
   */
  def filterPrimes: List[Prime] = primes.list.tail.list

  /**
   * The numeric values of the active tail filters.
   *
   * Most sieve predicates and divisibility lemmas work over `List[BigInt]`
   * rather than `List[Prime]`. This method is the single public bridge from
   * the domain list to the arithmetic list. Keeping it named makes later
   * proofs easier to read: `filterPrimes` says which primes are active, and
   * `filterValues` says which divisors the arithmetic lemmas inspect.
   */
  def filterValues: List[BigInt] =
    PrimeUtils.primeValues(filterPrimes)

  /**
   * The product of exactly the active filter primes.
   *
   * This is the period of the tail-only divisibility pattern. If a value is
   * not divisible by a tail prime, adding a multiple of this product preserves
   * that non-divisibility for every tail prime. The bounded search will use
   * this value to build a finite witness above the current candidate: a multiple
   * of this product plus one is guaranteed to have remainder one against every
   * active filter prime.
   *
   * The product is taken over `filterPrimes`, not over the whole `primes` list.
   * That distinction matters because the head is the starting point of the
   * stream, not a divisor to eliminate.
   */
  def tailPrimorial: BigInt = {
    PrimeUtils.primorialPositive(filterPrimes)
    PrimeUtils.primorial(filterPrimes)
  }.ensuring(_ > BigInt(0))

  /**
   * Inclusive search bound for the `k`-th generated value.
   *
   * The planned `apply(k)` implementation scans ordinary consecutive integers.
   * To keep that scan finite, it needs a value at or above the head where the
   * tail-filter pattern is known to repeat. This bound follows the user's
   * termination hint: start at `head`, then add `k` whole periods of the tail
   * filter product.
   *
   * For `[5, 3, 2]`, the tail product is `6`, so the first few bounds are
   * `5, 11, 17, 23, ...`. Each of those values survives the filters `3` and
   * `2`. The method only packages the arithmetic bound; the proof that this
   * bound passes the filter is kept separate so it can be developed as a named
   * lemma.
   */
  def searchBound(k: BigInt): BigInt = {
    require(k >= BigInt(0))

    head.value + k * tailPrimorial
  }.ensuring(_ >= head.value)

  /**
   * Returns true when `value` belongs to the filtered stream for this stage.
   *
   * This predicate is intentionally weaker than primality. It checks only that
   * `value` is at or beyond the generator head and that none of the tail primes
   * divides it. The implementation delegates the divisibility scan to the
   * existing verified `SieveUtils.isCoprime` predicate after converting the
   * `Prime` wrappers to their numeric values.
   *
   * The future bounded search should use this method as its stopping condition:
   * walk through consecutive candidates, emit the first candidate where
   * `accepts(candidate)` is true, and continue from the following integer.
   */
  def accepts(value: BigInt): Boolean = {
    require(value >= head.value)

    passesFilter(value)
  }

  /**
   * Proves the generator makes progress at every step.
   *
   * The completeness witness searches forward through indices until it reaches
   * a target accepted value. Stainless needs a decreasing measure for that
   * recursive search. This lemma supplies the progress fact: the next search
   * starts at `apply(k) + 1`, so its result is strictly greater than `apply(k)`.
   */
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

  /**
   * Proves that `apply` is injective: if `apply(firstIndex) == apply(secondIndex)`
   * then `firstIndex == secondIndex`.
   *
   * The proof uses `assertApplyIncreases` to derive a contradiction when
   * `firstIndex != secondIndex`:
   * - If `firstIndex < secondIndex` then `apply(firstIndex) < apply(secondIndex)`,
   * contradicting the premise.
   * - If `secondIndex < firstIndex` then the symmetric contradiction holds.
   * Therefore `firstIndex == secondIndex`.
   *
   * This is needed for cross-instance equality proofs (e.g., matching `seqIndex`
   * parameters to `indexOfAccepted` results in `assertMergedGapPrefixMatchesNext`).
   */
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

  /**
   * Returns the generated index for any accepted value at or above the head.
   *
   * This is the V0 completeness witness in executable form. The mathematical
   * statement says that every natural number accepted by the tail filters occurs
   * somewhere in the generated stream. Stainless does not need an existential
   * quantifier here; returning the index is stronger and more useful. The
   * post condition states the witness directly: the returned index is
   * non negative, and applying the generator at that index gives back `value`.
   */
  def indexOfAccepted(value: BigInt): BigInt = {
    require(value >= head.value)
    require(accepts(value))

    assert(apply(BigInt(0)) == head.value)
    assert(apply(BigInt(0)) <= value)
    findIndexForAcceptedFrom(value, BigInt(0))
  }.ensuring(res => res >= BigInt(0) && apply(res) == value && (res > BigInt(0) ==> apply(res - BigInt(1)) < value))

  /**
   * Discharges the `accepts` precondition needed by `size()`.
   *
   * The class invariant gives `isCoprime(head.value, filterValues)`.
   * Since `tailPrimorial = Primorial(filterPrimes)`, every filter prime
   * divides the tail primorial. Adding a multiple of `p` preserves the
   * remainder: `mod(head + tailPrimorial, p) == mod(head, p) != 0`.
   * Therefore `isCoprime` and consequently `accepts` hold.
   */
  def assertHeadPlusTailPrimorialAccepted(): Boolean = {
    SpecSieveSeqPeriodProperties(this).assertHeadPlusTailPrimorialAccepted()
  }.holds


  def period(): BigInt = {
    SpecSieveSeqPeriodProperties(this).period()
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
    SpecSieveSeqPeriodProperties(this).assertApplyModIsCoprime(k)
  }.holds


  def assertApplyResidueCycles(k: BigInt, p: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(p >= BigInt(0))
    require(apply(p) == head.value + tailPrimorial)
    SpecSieveSeqPeriodProperties(this).assertApplyResidueCycles(k, p)
  }.ensuring(res => {
    primorialMatchesSieveProduct(filterPrimes)
    assert(tailPrimorial == SieveUtils.product(filterValues))
    assert(assertBlockShift(k, p))
    assert(apply(k + p) == apply(k) + tailPrimorial)
    assert(AdditionAndMultiplication.APlusMultipleTimesBSameMod(apply(k), tailPrimorial, BigInt(1)))
    res && Calc.mod(apply(k + p), tailPrimorial) == Calc.mod(apply(k), tailPrimorial)
  })


  def assertGapPositive(k: BigInt): Boolean = {
    require(k >= BigInt(0))
    assert(applyStrictlyIncreases(k))
    apply(k + BigInt(1)) - apply(k) > BigInt(0)
  }.holds

  def assertGapPeriodic(k: BigInt, p: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(p >= BigInt(0))
    require(apply(p) == head.value + tailPrimorial)
    SpecSieveSeqPeriodProperties(this).assertGapPeriodic(k, p)
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
    SpecSieveSeqPeriodProperties(this).assertGapSum(p)
  }.holds


  def assertApplyEqualsHeadPlusGapSum(position: BigInt): Boolean = {
    require(position >= BigInt(0))
    SpecSieveSeqPeriodProperties(this).assertApplyEqualsHeadPlusGapSum(position)
  }.holds


  def gapList(from: BigInt, count: BigInt): List[BigInt] = {
    require(from >= BigInt(0))
    require(count >= BigInt(0))
    SpecSieveSeqPeriodProperties(this).gapList(from, count)
  }


  def assertGapListPositive(from: BigInt, count: BigInt): Boolean = {
    require(from >= BigInt(0))
    require(count >= BigInt(0))
    SpecSieveSeqPeriodProperties(this).assertGapListPositive(from, count)
  }.holds


  def assertGapListSize(from: BigInt, count: BigInt): Boolean = {
    require(from >= BigInt(0))
    require(count >= BigInt(0))
    SpecSieveSeqPeriodProperties(this).assertGapListSize(from, count)
  }.holds


  def assertGapListFirstEqualsGap(from: BigInt, count: BigInt): Boolean = {
    require(from >= BigInt(0))
    require(count > BigInt(0))
    SpecSieveSeqPeriodProperties(this).assertGapListFirstEqualsGap(from, count)
  }.holds


  def assertGapListApplyEqualsGapAtPosition(from: BigInt, count: BigInt, r: BigInt): Boolean = {
    require(from >= BigInt(0))
    require(count > BigInt(0))
    require(r >= BigInt(0))
    require(r < count)
    SpecSieveSeqPeriodProperties(this).assertGapListApplyEqualsGapAtPosition(from, count, r)
  }.holds


  def specGapCycle(period: BigInt): GapCycle = {
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)
    SpecSieveSeqPeriodProperties(this).specGapCycle(period)
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
    SpecSieveSeqPeriodProperties(this).assertSpecGapPeriodPositive(period)
  }.holds


  def assertSpecGapCycleIntegralBase(period: BigInt): Boolean = {
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)
    SpecSieveSeqPeriodProperties(this).assertSpecGapCycleIntegralBase(period)
  }.holds


  def assertMemCycleGapMatch(i: BigInt, period: BigInt): Boolean = {
    require(i >= BigInt(0))
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)
    SpecSieveSeqPeriodProperties(this).assertMemCycleGapMatch(i, period)
  }.holds


  def assertSpecGapCycleIntegralMatchesApply(period: BigInt, k: BigInt): Boolean = {
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)
    require(k > BigInt(0))
    SpecSieveSeqPeriodProperties(this).assertSpecGapCycleIntegralMatchesApply(period, k)
  }.holds


  def next: SpecSieveSequence = {
    require(primes.nextPrime.value < head.value * head.value)

    val newPrimes = primes.next

    SortedPrimeList.assertTailDescending(newPrimes.list.list)
    assert(PrimeUtils.primeIsCoprimeWithSmallerList(
      newPrimes.head.value, newPrimes.list.tail.list
    ))

    SpecSieveSequence(newPrimes)
  }

  /**
   * Projects a value emitted by `next` back into this sequence's acceptance
   * predicate.
   *
   * This is an important verifier bridge. The next stage filters by the old
   * whole prime list: its head is the newly discovered prime and its tail is
   * this stage's active filters. Therefore every value accepted by `next`
   * also survives this stage's filter tail. Scala can run both predicates just
   * fine, but Stainless treats `next.accepts(value)` and `accepts(value)` as
   * different facts until this relationship is stated explicitly. Future
   * editors should call this lemma instead of asking downstream proofs to
   * rediscover the filter-tail relationship.
   */
  def assertNextValueAcceptedByThis(k: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(primes.nextPrime.value < head.value * head.value)
    SpecSieveSeqNextProperties.assertNextValueAcceptedByThis(this, k)
  }.holds


  def assertSurvivorAcceptedByNext(v: BigInt): Boolean = {
    require(v >= head.value)
    require(accepts(v))
    require(Calc.mod(v, head.value) != BigInt(0))
    require(primes.nextPrime.value < head.value * head.value)
    SpecSieveSeqNextProperties.assertSurvivorAcceptedByNext(this, v)
  }.holds


  def assertOldAcceptedHeadNonMultipleAcceptedByNext(v: BigInt): Boolean = {
    require(primes.nextPrime.value < head.value * head.value)
    require(v >= next.head.value)
    require(accepts(v))
    require(Calc.mod(v, head.value) != BigInt(0))
    SpecSieveSeqNextProperties.assertOldAcceptedHeadNonMultipleAcceptedByNext(this, v)
  }.holds


  def assertOldAcceptedRejectedByNextIsHeadMultiple(v: BigInt): Boolean = {
    require(primes.nextPrime.value < head.value * head.value)
    require(v >= next.head.value)
    require(accepts(v))
    require(!next.accepts(v))
    SpecSieveSeqNextProperties.assertOldAcceptedRejectedByNextIsHeadMultiple(this, v)
  }.holds


  def assertOldGeneratedValueBetweenNextValuesIsHeadMultiple(k: BigInt, oldIndex: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(oldIndex >= BigInt(0))
    require(primes.nextPrime.value < head.value * head.value)
    require(apply(oldIndex) > next(k))
    require(apply(oldIndex) < next(k + BigInt(1)))
    SpecSieveSeqNextProperties.assertOldGeneratedValueBetweenNextValuesIsHeadMultiple(this, k, oldIndex)
  }.holds


  def assertNextAcceptsMatchesHeadFilterForAcceptedValue(v: BigInt): Boolean = {
    require(primes.nextPrime.value < head.value * head.value)
    require(v >= next.head.value)
    require(accepts(v))
    SpecSieveSeqNextProperties.assertNextAcceptsMatchesHeadFilterForAcceptedValue(this, v)
  }.holds


  def head: Prime = primes.head

  /**
   * Bridge lemma between the prime-domain product and the sieve-domain product.
   *
   * `tailPrimorial` is expressed with `PrimeUtils.primorial(filterPrimes)`
   * because that API already proves strict positivity for lists of `Prime`.
   * Some sieve lemmas, however, are written over `List[BigInt]` and expect the
   * same product to be named as `SieveUtils.product(filterValues)`.
   *
   * This lemma proves that those two descriptions are identical. It does not
   * change the runtime algorithm; it only gives Stainless the equality needed
   * to combine the existing positivity proof with the existing coprimality
   * preservation proof.
   */
  def primorialMatchesSieveProduct(primeList: List[Prime]): Boolean = {
    decreases(primeList.size)

    if (primeList.isEmpty) {
      PrimeUtils.primorial(primeList) == SieveUtils.product(PrimeUtils.primeValues(primeList))
    } else {
      primorialMatchesSieveProduct(primeList.tail)
      PrimeUtils.primorial(primeList) == SieveUtils.product(PrimeUtils.primeValues(primeList))
    }
  }.holds

  /**
   * Explicit coprimality-preservation lemma for adding whole filter periods.
   *
   * The existing `SieveUtils.assertExpandedCoprime` helper proves the same
   * modular facts internally, but its public result is just `true`. This local
   * helper exposes the exact Boolean needed by V0: after adding `i` multiples
   * of a product that contains every active filter value, the expanded value is
   * still coprime to the whole filter list.
   *
   * `prefixProd` accounts for the values already peeled from the front of the
   * list. At each recursive step, `modulus` is known to be
   * `prefixProd * product(values)`, so the current head value divides
   * `modulus`. That makes `i * modulus` divisible by the current head, while
   * the original `r` is not divisible by it. The existing modular lemmas then
   * show the sum keeps a non-zero remainder, and recursion handles the tail.
   */
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

  /**
   * Proof that the inclusive search bound survives the active tail filters.
   *
   * This is the concrete form of the bounded-search witness. The future
   * `apply(k)` can search only up to `searchBound(k)` because this lemma proves
   * that the bound itself is an acceptable tail-filter survivor. The scan may
   * find an earlier value, but it never needs to look beyond this one.
   */
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

  /**
   * Finds the next accepted value inside a finite consecutive window.
   *
   * This is the intentionally simple engine that `apply(k)` will use. It does
   * not jump by residues, multiply strides, or precompute gaps. It checks the
   * current natural number; if the number survives the tail filters, it returns
   * it. Otherwise it moves to the next natural number.
   *
   * Termination comes from the inclusive `upper` bound. The caller must prove
   * that `upper` itself is accepted, so the search is guaranteed to stop before
   * or at that bound. The recursive measure is the remaining window size,
   * `upper - current`, which shrinks by one on each rejected candidate.
   */
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

  /**
   * States that the half-open interval `[from, until)` contains no accepted value.
   *
   * This is the key predicate for the completeness proof. Soundness only needs
   * to know that a generated value passes the filter. Completeness also needs to
   * know that the linear search did not skip an earlier accepted value. The
   * half-open shape is intentional: if `searchNext` returns `res`, then the
   * skipped candidates are exactly `[current, res)`, while `res` itself is
   * accepted.
   */
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

  def countAcceptedBetween(from: BigInt, until: BigInt): BigInt = {
    require(from >= head.value)
    require(from <= until)
    SpecSieveSeqSurvivorCountProperties(this).countAcceptedBetween(from, until)
  }.ensuring(res => res >= BigInt(0) && res <= until - from)


  def countAcceptedHeadMultiplesBetween(from: BigInt, until: BigInt): BigInt = {
    require(from >= head.value)
    require(from <= until)
    SpecSieveSeqSurvivorCountProperties(this).countAcceptedHeadMultiplesBetween(from, until)
  }.ensuring(res => res >= BigInt(0) && res <= until - from)


  def countAcceptedHeadNonMultiplesBetween(from: BigInt, until: BigInt): BigInt = {
    require(from >= head.value)
    require(from <= until)
    SpecSieveSeqSurvivorCountProperties(this).countAcceptedHeadNonMultiplesBetween(from, until)
  }.ensuring(res => res >= BigInt(0) && res <= until - from)


  def generatedHeadMultipleIndicator(index: BigInt): BigInt = {
    require(index >= BigInt(0))
    SpecSieveSeqSurvivorCountProperties(this).generatedHeadMultipleIndicator(index)
  }.ensuring(res => res >= BigInt(0) && res <= BigInt(1))


  def countGeneratedHeadMultiplesPrefix(k: BigInt): BigInt = {
    require(k >= BigInt(0))
    SpecSieveSeqSurvivorCountProperties(this).countGeneratedHeadMultiplesPrefix(k)
  }.ensuring(res => res >= BigInt(0) && res <= k)


  def countGeneratedHeadMultiplesRange(from: BigInt, count: BigInt): BigInt = {
    require(from >= BigInt(0))
    require(count >= BigInt(0))
    SpecSieveSeqSurvivorCountProperties(this).countGeneratedHeadMultiplesRange(from, count)
  }.ensuring(res => res >= BigInt(0) && res <= count)


  def assertGeneratedHeadMultiplesPrefixExpandedCount(
    period: BigInt
  ): Boolean = {
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)
    require(Calc.mod(tailPrimorial, head.value) != BigInt(0))
    SpecSieveSeqSurvivorCountProperties(this).assertGeneratedHeadMultiplesPrefixExpandedCount(period)
  }.holds

  def assertExpandedGeneratedHeadMultipleCount(period: BigInt): Boolean = {
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)
    require(Calc.mod(tailPrimorial, head.value) != BigInt(0))
    SpecSieveSeqSurvivorCountProperties(this).assertExpandedGeneratedHeadMultipleCount(period)
  }.holds


  def assertGeneratedPrefixCount(k: BigInt): Boolean = {
    require(k >= BigInt(0))
    SpecSieveSeqSurvivorCountProperties(this).assertGeneratedPrefixCount(k)
  }.holds


  def assertGeneratedHeadMultiplePrefixCount(k: BigInt): Boolean = {
    require(k >= BigInt(0))
    SpecSieveSeqSurvivorCountProperties(this).assertGeneratedHeadMultiplePrefixCount(k)
  }.holds


  def assertExpandedOldAcceptedCount(period: BigInt): Boolean = {
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)
    SpecSieveSeqSurvivorCountProperties(this).assertExpandedOldAcceptedCount(period)
  }.holds


  def assertExpandedHeadMultipleCountFromGeneratedCount(period: BigInt): Boolean = {
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)
    SpecSieveSeqSurvivorCountProperties(this).assertExpandedHeadMultipleCountFromGeneratedCount(period)
  }.holds


  def assertSameHeadExtendedFilterCountFromRemovedCount(period: BigInt): Boolean = {
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)
    SpecSieveSeqSurvivorCountProperties(this).assertSameHeadExtendedFilterCountFromRemovedCount(period)
  }.holds


  def assertSameHeadExtendedFilterCount(period: BigInt): Boolean = {
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)
    require(Calc.mod(tailPrimorial, head.value) != BigInt(0))
    SpecSieveSeqSurvivorCountProperties(this).assertSameHeadExtendedFilterCount(period)
  }.holds


  def sameHeadSurvivorCount(period: BigInt): BigInt = {
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)
    require(Calc.mod(tailPrimorial, head.value) != BigInt(0))
    SpecSieveSeqSurvivorCountProperties(this).sameHeadSurvivorCount(period)
  }.ensuring(count => {
    assertSameHeadExtendedFilterCount(period)
    count == period * (head.value - BigInt(1))
  })


  def assertSameHeadShiftedWindowCount(period: BigInt): Boolean = {
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)
    require(Calc.mod(tailPrimorial, head.value) != BigInt(0))
    SpecSieveSeqSurvivorCountProperties(this).assertSameHeadShiftedWindowCount(period)
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

  /** True when `value` is coprime with every active filter prime. */
  def passesFilter(value: BigInt): Boolean =
    CoprimeUtils.isCoprime(value, PrimeUtils.primeValues(filterPrimes))

  def assertSingletonFilterDecision(value: BigInt, p: BigInt): Boolean = {
    require(p > BigInt(0))
    require(filterValues == List(p))
    SpecSieveSeqNextProperties.assertSingletonFilterDecision(this, value, p)
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

  /**
   * Proves that the next generated value cannot jump over an accepted value.
   *
   * This is the local completeness step. If `value` is accepted and lies after
   * `apply(k)`, then the next generated value must be at or before `value`.
   * Otherwise `value` would sit inside the skipped interval
   * `[apply(k) + 1, apply(k + 1))`, contradicting the fact that `apply(k + 1)`
   * is the first accepted value in that interval.
   */
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

  /**
   * Public first-step completeness wrapper.
   *
   * Several cross-object proofs need only the first generated value after the
   * head, not the fully general private lemma above. This wrapper exposes that
   * focused fact without leaking the recursive skipped-interval machinery:
   * every accepted candidate strictly after the head bounds `apply(1)` from
   * above. In particular, once we prove that `AllPrimesSoFarList.nextPrime`
   * passes the tail filter, this lemma gives the easy half of the conditional
   * bridge `apply(1) <= nextPrime`.
   */
   def assertApplyOneAtOrBeforeAccepted(value: BigInt): Boolean = {
    require(value > head.value)
    require(accepts(value))
    SpecSieveSeqHeadIsPrime(this).assertApplyOneAtOrBeforeAccepted(value)
  }.holds

   def assertNextPrimePassesV0Filter(primes: AllPrimesSoFarList): Boolean = {
    require(!primes.isEmpty)
    require(primes.size > 1)
    require(AllPrimesSoFarList.allPrimesSoFar(primes.list))
    SpecSieveSeqHeadIsPrime(this).assertNextPrimePassesV0Filter(primes)
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

  /** Proves `apply(from) <= apply(until)` via `applyIndexOrderPreservesValues`. */
  def assertApplyMonotonic(from: BigInt, until: BigInt): Boolean = {
    require(from >= BigInt(0))
    require(until >= from)
    assert(applyIndexOrderPreservesValues(from, until))
    apply(from) <= apply(until)
  }.holds

  /**
   * Proves that `apply` is strictly increasing over any distance:
   * if `fromIndex < toIndex` then `apply(fromIndex) < apply(toIndex)`.
   *
   * This is the strict-transitive companion to `assertApplyMonotonic` (which only
   * proves non-strict inequality) and the inductive lift of the single-step
   * `applyStrictlyIncreases`. The proof proceeds by induction on
   * `toIndex - fromIndex`: the base case is a single step (proved directly by
   * `applyStrictlyIncreases`), and the inductive case chains a single step with
   * the recursive hypothesis.
   *
   * The main consumer is `assertApplyInjective`, which needs strict increase
   * across arbitrary distances to prove the `apply` function is injective.
   */
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

  /**
   * Lifts local strict growth into a strict ordered-index comparison.
   *
   * This is the strict companion to `applyIndexOrderPreservesValues`. The skip
   * proof needs to show that the first non-multiple found after index `k`
   * really has a larger generated value than `apply(k)`. The function
   * `findFirstNonMultipleAfter` already proves the index is at least `k + 1`;
   * this lemma turns that index fact into the corresponding value fact without
   * involving filters, modulo arithmetic, or `nextSeq`.
   */
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

  def assertApplyStrictlyIncreasesBetween(from: BigInt, until: BigInt): Boolean = {
    require(from >= BigInt(0))
    require(until > from)

    assert(applyIndexStrictlyPreservesValues(from, until))

    apply(from) < apply(until)
  }.holds

  /**
   * Converts a generated-value bound back into an index bound.
   *
   * The merge proof eventually knows that the next surviving value from
   * `nextSeq` is at most `apply(bound)`, and completeness gives an old-sequence
   * index `index` for that same value. To call
   * `assertFirstNonMultipleIsAtOrBefore`, we need `index <= bound`.
   *
   * This helper proves that contrapositive-style fact using strict monotonicity:
   * if `index` were after `bound`, then `apply(bound + 1)` would be after
   * `apply(bound)` and still before or equal to `apply(index)`, contradicting
   * the input `apply(index) <= apply(bound)`.
   */
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

  def assertIndexOfAcceptedStrictlyIncreasesForAcceptedValues(
    lowerValue: BigInt,
    upperValue: BigInt
  ): Boolean = {
    require(lowerValue >= head.value)
    require(upperValue >= head.value)
    require(accepts(lowerValue))
    require(accepts(upperValue))
    require(lowerValue < upperValue)

    val lowerIndex = indexOfAccepted(lowerValue)
    val upperIndex = indexOfAccepted(upperValue)

    assert(apply(upperIndex) == upperValue)
    assert(lowerValue <= apply(upperIndex))
    assert(assertIndexOfAcceptedAtMost(lowerValue, upperIndex))
    assert(lowerIndex <= upperIndex)
    if (lowerIndex == upperIndex) {
      assert(apply(lowerIndex) == lowerValue)
      assert(apply(upperIndex) == upperValue)
      assert(lowerValue == upperValue)
    }

    lowerIndex < upperIndex
  }.holds

  /**
   * Constructs an index for an accepted value, starting from a known lower index.
   *
   * This is the constructive form of completeness. The caller supplies an
   * accepted `value` and an index `k` where the generated stream is still at or
   * below that value. If the current generated value is the target, the witness
   * is found. Otherwise, `nextDoesNotPassAcceptedValue` proves the next stream
   * value still cannot be beyond the target, and `applyStrictlyIncreases` proves
   * the numeric distance to the target strictly shrinks.
   *
   * The recursion is therefore not searching over arbitrary natural numbers. It
   * is searching over generated indices, and it terminates because every step
   * moves the generated value closer to the fixed accepted target.
   */
  private def findIndexForAcceptedFrom(value: BigInt, k: BigInt): BigInt = {
    require(value >= head.value)
    require(accepts(value))
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

  /**
   * Recursive helper for assertApplyModIsCoprime.
   *
   * Proves isCoprime(r, values) given isCoprime(value, values)
   * and modulus = prefixProd * product(values).
   *
   * The prefix-product decomposition (modelled after expandedCoprimePreservesFilter)
   * lets us prove Calc.mod(modulus, p) == 0 at each step without requiring
   * the full product to be passed: modulus = prefixProd * p * product(values.tail),
   * so modulus is divisible by p.
   */
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

  /**
   * Reverse periodic preservation.
   *
   * Proves: if isCoprime(v + modulus, values) and modulus == product(values),
   * then isCoprime(v, values).
   *
   * This is the reverse of expandedCoprimePreservesFilter. It is the key
   * lemma for the inductive step in assertBlockShift: there cannot be an
   * accepted value between apply(k) + M and apply(k+1) + M, because if there
   * were, subtracting M would give an accepted value between apply(k) and
   * apply(k+1), contradicting strict monotonicity.
   *
   * For each p in values:
   *   1. isCoprime(v + M, values) gives Calc.mod(v + M, p) != 0
   *      2. Calc.mod(M, p) == 0 (from the product equality)
   *      3. modAdd(v, p, M) + modIdempotence gives:
   *      Calc.mod(v + M, p) == Calc.mod(v, p)
   *      4. Therefore Calc.mod(v, p) != 0
   */
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

  /**
   * Proves that apply(k + p) == apply(k) + tailPrimorial for all k >= 0,
   * where p = indexOfAccepted(head + tailPrimorial).
   *
   * This is the core "loop around M" property: each block of length
   * tailPrimorial contains exactly p generated values, so shifting by
   * the period p adds exactly tailPrimorial.
   *
   * The inductive step uses two inequalities:
   *   1. apply(k+p) <= apply(k) + M (by nextDoesNotPassAcceptedValue
   *      from position k-1+p toward the accepted value apply(k) + M)
   *      2. apply(k) + M <= apply(k+p) (by reverse periodic preservation:
   *      any accepted value between apply(k)+M and apply(k+1)+M would
   *      give a contradiction with nextDoesNotPassAcceptedValue)
   */
  def assertBlockShift(k: BigInt, p: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(p >= BigInt(0))
    require(apply(p) == head.value + tailPrimorial)
    SpecSieveSeqPeriodProperties(this).assertBlockShift(k, p)
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
    SpecSieveSeqPeriodProperties(this).sumGap(from, until)
  }


  def assertSumGapTelescopes(from: BigInt, until: BigInt): Boolean = {
    require(from >= BigInt(0))
    require(until >= from)
    SpecSieveSeqPeriodProperties(this).assertSumGapTelescopes(from, until)
  }.holds


  def assertSumGapPositive(from: BigInt, until: BigInt): Boolean = {
    require(from >= BigInt(0))
    require(until > from)
    SpecSieveSeqPeriodProperties(this).assertSumGapPositive(from, until)
  }.holds


  def assertFilterPreservesNextGap(
                                            nextSeq: SpecSieveSequence,
                                            k: BigInt
                                          ): Boolean = {
    require(k >= BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == filterValues)
    require(nextSeq.head.value == head.value)
    require(nextSeq.accepts(apply(k)))
    require(Calc.mod(apply(k + BigInt(1)), nextSeq.filterValues.head) != BigInt(0))
    SpecSieveSeqNextProperties.assertFilterPreservesNextGap(this, nextSeq, k)
  }.holds

  def assertConsecutiveAcceptedByNextPreservesGap(
    nextSeq: SpecSieveSequence,
    k: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(nextSeq.filterValues.tail == filterValues)
    require(nextSeq.head.value >= head.value)
    require(apply(k) >= nextSeq.head.value)
    require(apply(k + BigInt(1)) >= nextSeq.head.value)
    require(nextSeq.accepts(apply(k)))
    require(nextSeq.accepts(apply(k + BigInt(1))))
    require(ListUtils.checkAllPositive(nextSeq.filterValues))
    SpecSieveSeqNextProperties.assertConsecutiveAcceptedByNextPreservesGap(this, nextSeq, k)
  }.holds

  def findFirstNonMultipleAfter(k: BigInt, p: BigInt, bound: BigInt): BigInt = {
    require(k >= BigInt(0))
    require(p > BigInt(0))
    require(bound > k)
    require(Calc.mod(apply(bound), p) != BigInt(0))
    SpecSieveSeqNextProperties.findFirstNonMultipleAfter(this, k, p, bound)
  }.ensuring(res => res >= k + BigInt(1) && res <= bound && Calc.mod(apply(res), p) != BigInt(0))

  /**
   * Proves `apply(k + n * period) == apply(k) + n * tailPrimorial` for any n >= 0.
   * Induction on n: base `n=0` is trivial, step uses `assertBlockShift(k + (n-1)*period, period)`
   * to propagate the shift equality one period at a time.
   */


  def assertBlockShiftMultiple(k: BigInt, n: BigInt, period: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(n >= BigInt(0))
    require(period > BigInt(0))
    require(apply(period) == head.value + tailPrimorial)
    SpecSieveSeqPeriodProperties(this).assertBlockShiftMultiple(k, n, period)
  }.holds


  def nextMergedGapOldIndex(nextSeq: SpecSieveSequence, k: BigInt, period: BigInt): BigInt = {
    require(k >= BigInt(0))
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == filterValues)
    require(nextSeq.head.value == head.value)
    require(nextSeq.accepts(apply(k)))
    require(apply(period) == head.value + tailPrimorial)
    require(Calc.mod(head.value + tailPrimorial, nextSeq.filterValues.head) != BigInt(0))
    SpecSieveSeqNextProperties.nextMergedGapOldIndex(this, nextSeq, k, period)
  }.ensuring(result =>
    result > k &&
      accepts(apply(result)) &&
      Calc.mod(apply(result), nextSeq.filterValues.head) != BigInt(0) &&
      nextSeq.accepts(apply(result)) && {
      val computedNextSeqIndex = nextSeq.indexOfAccepted(apply(k))
      nextSeq(computedNextSeqIndex + BigInt(1)) == apply(result) &&
        nextSeq(computedNextSeqIndex + BigInt(1)) - nextSeq(computedNextSeqIndex) == sumGap(k, result)
    }
  )

  /**
   * Public wrapper for the old-index step used by the next-stage filter.
   *
   * This exposes the already-verified `nextMergedGapOldIndex` result without
   * exposing the private search helpers. Starting from an old index `k` whose
   * value appears in `nextSeq`, the returned old index is the next value
   * emitted by `nextSeq`. It is strictly after `k`, survives the newly added
   * front filter, and its value equals `nextSeq(indexOfAccepted(apply(k)) + 1)`.
   *
   * Math:
   *
   *   j = nextAcceptedOldIndex(nextSeq, k, period)
   *   nextSeq(indexOfAccepted(apply(k)) + 1) = apply(j)
   *   j > k
   *   mod(apply(j), nextSeq.filterValues.head) != 0
   */


  def nextAcceptedOldIndex(
    nextSeq: SpecSieveSequence,
    k: BigInt,
    period: BigInt
  ): BigInt = {
    require(k >= BigInt(0))
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == filterValues)
    require(nextSeq.head.value == head.value)
    require(nextSeq.accepts(apply(k)))
    require(apply(period) == head.value + tailPrimorial)
    require(Calc.mod(head.value + tailPrimorial, nextSeq.filterValues.head) != BigInt(0))
    SpecSieveSeqNextProperties.nextAcceptedOldIndex(this, nextSeq, k, period)
  }.ensuring(result =>
    result > k &&
      accepts(apply(result)) &&
      Calc.mod(apply(result), nextSeq.filterValues.head) != BigInt(0) &&
      nextSeq.accepts(apply(result)) && {
      val computedNextSeqIndex = nextSeq.indexOfAccepted(apply(k))
      nextSeq(computedNextSeqIndex + BigInt(1)) == apply(result)
    }
  )

  /**
   * Every old index skipped by `nextAcceptedOldIndex` is removed by the new
   * front filter.
   *
   * This is the public, caller-friendly form of the private
   * `assertSkippedIndexBeforeFirstIsMultiple` recursion. It is the fact needed
   * to feed `GapProperties.allMultiplesInRange` on the cycle side: the new
   * sequence did not skip arbitrary values; it skipped exactly a prefix whose
   * old values are multiples of `nextSeq.filterValues.head`.
   *
   * Math:
   *
   *   k < idx < nextAcceptedOldIndex(nextSeq, k, period)
   *   ------------------------------------------------------------
   *   mod(apply(idx), nextSeq.filterValues.head) = 0
   */

  def assertSkippedBeforeNextAcceptedOldIndexIsMultiple(
    nextSeq: SpecSieveSequence,
    k: BigInt,
    idx: BigInt,
    period: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(idx > k)
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == filterValues)
    require(nextSeq.head.value == head.value)
    require(nextSeq.accepts(apply(k)))
    require(apply(period) == head.value + tailPrimorial)
    require(Calc.mod(head.value + tailPrimorial, nextSeq.filterValues.head) != BigInt(0))
    require(idx < nextAcceptedOldIndex(nextSeq, k, period))
    SpecSieveSeqNextProperties.assertSkippedBeforeNextAcceptedOldIndexIsMultiple(this, nextSeq, k, idx, period)
  }.holds

  def mergedGapPrefix(
                               nextSeq: SpecSieveSequence,
                               k: BigInt,
                               remaining: BigInt,
                               period: BigInt
                             ): List[BigInt] = {
    require(k >= BigInt(0))
    require(remaining >= BigInt(0))
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == filterValues)
    require(nextSeq.head.value == head.value)
    require(nextSeq.accepts(apply(k)))
    require(apply(period) == head.value + tailPrimorial)
    require(Calc.mod(head.value + tailPrimorial, nextSeq.filterValues.head) != BigInt(0))
    SpecSieveSeqNextProperties.mergedGapPrefix(this, nextSeq, k, remaining, period)
  }

  def assertMergedGapPrefixMatchesNext(
                                                nextSeq: SpecSieveSequence,
                                                k: BigInt,
                                                seqIndex: BigInt,
                                                remaining: BigInt,
                                                period: BigInt
                                              ): Boolean = {
    require(k >= BigInt(0))
    require(seqIndex >= BigInt(0))
    require(remaining >= BigInt(0))
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == filterValues)
    require(nextSeq.head.value == head.value)
    require(nextSeq.accepts(apply(k)))
    require(nextSeq(seqIndex) == apply(k))
    require(apply(period) == head.value + tailPrimorial)
    require(Calc.mod(head.value + tailPrimorial, nextSeq.filterValues.head) != BigInt(0))
    SpecSieveSeqNextProperties.assertMergedGapPrefixMatchesNext(this, nextSeq, k, seqIndex, remaining, period)
  }.holds

  def assertApplyOneIsPrimeIfBelowHeadSq(): Boolean = {
    require(apply(BigInt(1)) < head.value * head.value)
    SpecSieveSeqHeadIsPrime(this).assertApplyOneIsPrimeIfBelowHeadSq()
  }.holds


  def assertApplyOneEqualsNextPrime(): Boolean = {
    require(primes.nextPrime.value < head.value * head.value)
    SpecSieveSeqHeadIsPrime(this).assertApplyOneEqualsNextPrime()
  }.holds


}
