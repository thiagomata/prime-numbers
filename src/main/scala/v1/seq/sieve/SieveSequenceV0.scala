package v1.seq.sieve

import stainless.annotation.extern
import stainless.collection.List
import stainless.lang.*
import v1.Calc
import v1.div.properties.AdditionAndMultiplication
import v1.div.properties.ModIdempotence
import v1.div.properties.ModOperations
import v1.list.ListBoundUtils
import v1.list.ListUtils
import v1.prime.{AllPrimesSoFarList, Prime, PrimeUtils, SortedPrimeList}
import v1.prime.properties.PrimeProperties

import scala.annotation.tailrec

/**
 * The intentionally simple sieve-sequence model.
 *
 * `SieveSequenceV0` is not trying to prove that every generated value is prime.
 * It models one stage of a sieve as an infinite generator of natural numbers.
 * The first prime in `primes` is the starting point of that generator. The tail
 * primes are the active filters. A value is accepted exactly when it is not a
 * multiple of any tail prime.
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
 * This deliberately boring representation gives us a baseline for proving the
 * three generator properties before returning to the gap-cycle implementation:
 * soundness, completeness, and strict monotonicity. The future `apply(k)` should
 * be a bounded linear scan over consecutive natural numbers, using `accepts` as
 * the only gate for emitted values.
 */
case class SieveSequenceV0(primes: AllPrimesSoFarList) {
  require(!primes.isEmpty)
  require(primes.size > 1)
  require(SieveUtils.isCoprime(primes.head.value, PrimeUtils.primeValues(primes.list.tail.list)))

  /**
   * The first value of this generator.
   *
   * `AllPrimesSoFarList` stores primes in descending order, so the list head is
   * the newest/largest prime in the current sieve stage. V0 starts enumerating
   * at this value. It does not use the previous V2 gap-cycle history to jump
   * around; it will eventually walk forward through ordinary consecutive
   * integers from here.
   */
  def head: Prime = primes.head

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
   * Bridge lemma between the prime-domain product and the sieve-domain product.
   *
   * `filterModulus` is expressed with `PrimeUtils.primorial(filterPrimes)`
   * because that API already proves strict positivity for lists of `Prime`.
   * Some sieve lemmas, however, are written over `List[BigInt]` and expect the
   * same product to be named as `SieveUtils.product(filterValues)`.
   *
   * This lemma proves that those two descriptions are identical. It does not
   * change the runtime algorithm; it only gives Stainless the equality needed
   * to combine the existing positivity proof with the existing coprimality
   * preservation proof.
   */
  private def primorialMatchesSieveProduct(primeList: List[Prime]): Boolean = {
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
  private def expandedCoprimePreservesFilter(
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
  def filterModulus: BigInt = {
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

    head.value + k * filterModulus
  }.ensuring(_ >= head.value)

  /**
   * Proof that the inclusive search bound survives the active tail filters.
   *
   * This is the concrete form of the bounded-search witness. The future
   * `apply(k)` can search only up to `searchBound(k)` because this lemma proves
   * that the bound itself is an acceptable tail-filter survivor. The scan may
   * find an earlier value, but it never needs to look beyond this one.
   */
  def searchBoundPassesFilter(k: BigInt): Boolean = {
    require(k >= BigInt(0))

    primorialMatchesSieveProduct(filterPrimes)
    assert(filterModulus == SieveUtils.product(filterValues))
    assert(expandedCoprimePreservesFilter(
      head.value,
      k,
      filterModulus,
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
  private def noAcceptedBetween(from: BigInt, until: BigInt): Boolean = {
    require(from >= head.value)
    require(from <= until)
    decreases(until - from)

    if (from == until) {
      true
    } else {
      !accepts(from) && noAcceptedBetween(from + BigInt(1), until)
    }
  }

  /**
   * Extracts the rejection fact for one value inside a skipped interval.
   *
   * `noAcceptedBetween(from, until)` is recursive over the interval start, so
   * Stainless does not automatically know what it says about an arbitrary
   * interior value. This helper walks from `from` to `value`, carrying the
   * interval proof forward one candidate at a time. When it reaches `value`,
   * the unfolded predicate gives the exact fact needed by completeness:
   * `value` cannot be accepted.
   */
  private def noAcceptedBetweenRejects(from: BigInt, until: BigInt, value: BigInt): Boolean = {
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
  def passesFilter(value: BigInt): Boolean =
    SieveUtils.isCoprime(value, PrimeUtils.primeValues(filterPrimes))

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
   * Lifts acceptance from this sequence to a sequence with one extra front filter.
   *
   * `assertSkipUntilNonMultiple` needs to reason about a value found in the old
   * stream after skipping one or more values that are multiples of the newly
   * introduced filter. The old stream already proves that the value survives
   * `filterValues`. The extra assumption here proves the missing piece: the
   * same value is not a multiple of `nextSeq.filterValues.head`.
   *
   * When `nextSeq.filterValues.tail == filterValues`, those two facts are
   * exactly the definition of `nextSeq.accepts(value)`. Naming the bridge keeps
   * the main gap-merge proof focused on index ordering instead of repeatedly
   * unfolding the list-shaped coprimality predicate.
   */
  private def assertAcceptedByNextWhenOldAcceptedAndNewHeadNonMultiple(
    nextSeq: SieveSequenceV0,
    value: BigInt
  ): Boolean = {
    require(value >= head.value)
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == filterValues)
    require(nextSeq.head.value == head.value)
    require(accepts(value))
    require(Calc.mod(value, nextSeq.filterValues.head) != BigInt(0))

    assert(value >= nextSeq.head.value)
    assert(SieveUtils.isCoprime(value, filterValues))
    assert(SieveUtils.isCoprime(value, nextSeq.filterValues.tail))
    assert(SieveUtils.isCoprime(value, nextSeq.filterValues))
    nextSeq.accepts(value)
  }.holds

  /**
   * Projects acceptance by an extended next filter back to this sequence.
   *
   * The skip proof also needs the reverse direction for the candidate produced
   * by `nextSeq`: if the extended filter accepts `value`, then `value` must
   * survive both parts of that extended filter. The head of
   * `nextSeq.filterValues` gives the new non-multiple fact, and the tail is
   * exactly this sequence's `filterValues`, so the same value is accepted by
   * this sequence as well.
   *
   * This lemma is deliberately paired with
   * `assertAcceptedByNextWhenOldAcceptedAndNewHeadNonMultiple`. Together they
   * make the filter relationship explicit in both directions, leaving the main
   * gap-merge proof to focus on finding and ordering the first survivor.
   */
  private def assertNextAcceptedImpliesOldAcceptedAndNewHeadNonMultiple(
    nextSeq: SieveSequenceV0,
    value: BigInt
  ): Boolean = {
    require(value >= nextSeq.head.value)
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == filterValues)
    require(nextSeq.head.value == head.value)
    require(nextSeq.accepts(value))

    assert(value >= head.value)
    assert(SieveUtils.isCoprime(value, nextSeq.filterValues))
    assert(SieveUtils.assertIsCoprimeSound(value, nextSeq.filterValues))
    assert(Calc.mod(value, nextSeq.filterValues.head) != BigInt(0))
    assert(SieveUtils.isCoprime(value, nextSeq.filterValues.tail))
    assert(SieveUtils.isCoprime(value, filterValues))
    accepts(value) && Calc.mod(value, nextSeq.filterValues.head) != BigInt(0)
  }.holds

  /**
   * Proves rejection by the extended next filter when the new front filter divides.
   *
   * This is the negative companion to the two acceptance bridge lemmas above.
   * During gap merging, the old stream may contain values that still satisfy this
   * sequence's tail filter, but are multiples of the newly inserted front filter
   * in `nextSeq`. Such values must not appear in `nextSeq`.
   *
   * The proof is intentionally direct. `nextSeq.accepts(value)` is just
   * `nextSeq.passesFilter(value)` once the value is above the shared head, and
   * `passesFilter` is `SieveUtils.isCoprime` over `nextSeq.filterValues`. If the
   * head of that filter list is `p` and `value` has zero remainder modulo `p`,
   * the first branch of `isCoprime` rejects the value immediately.
   */
  private def assertRejectedByNextWhenNewHeadMultiple(
    nextSeq: SieveSequenceV0,
    value: BigInt,
    p: BigInt
  ): Boolean = {
    require(value >= nextSeq.head.value)
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.head == p)
    require(Calc.mod(value, p) == BigInt(0))

    assert(Calc.mod(value, nextSeq.filterValues.head) == BigInt(0))
    assert(!SieveUtils.isCoprime(value, nextSeq.filterValues))
    assert(!nextSeq.passesFilter(value))
    !nextSeq.accepts(value)
  }.holds

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
      assert(filterModulus > BigInt(0))
      assert(searchBound(k - BigInt(1)) < upper)
      assert(previous + BigInt(1) <= upper)
      assert(searchBoundPassesFilter(k))
      assert(accepts(upper))
      searchNext(previous + BigInt(1), upper)
    }
  }.ensuring(res => res >= head.value && res <= searchBound(k) && accepts(res))

  /**
   * Exposes the skipped-interval fact for a non-initial generated value.
   *
   * The postcondition of `searchNext` says the bounded linear scan returns the
   * first accepted candidate in its window. `apply(k)` uses that helper for
   * every `k > 0`, starting immediately after `apply(k - 1)`. This lemma names
   * that fact at the `apply` level: between the previous generated value and
   * the current generated value, there is no accepted value left behind.
   */
  private def applySkipsNoAcceptedBetween(k: BigInt): Boolean = {
    require(k > BigInt(0))

    val previous = apply(k - BigInt(1))
    val upper = searchBound(k)
    val result = apply(k)

    assert(previous <= searchBound(k - BigInt(1)))
    assert(filterModulus > BigInt(0))
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
  private def nextDoesNotPassAcceptedValue(k: BigInt, value: BigInt): Boolean = {
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

    assert(apply(BigInt(0)) == head.value)
    assert(apply(BigInt(0)) < value)
    assert(nextDoesNotPassAcceptedValue(BigInt(0), value))

    apply(BigInt(1)) <= value
  }.holds

  /**
   * Proves that `AllPrimesSoFarList.nextPrime` passes the V0 tail filter.
   *
   * The next prime after the current list head is both larger than the head and
   * coprime to all smaller primes (a distinct prime cannot be divisible by a
   * smaller distinct prime). The V0 tail filter checks exactly this coprimality
   * against the list of tail (strictly smaller) filter values at this stage, so
   * the next prime is always accepted by the V0 generator.
   *
   * This lemma is the first bridge between the direct prime search
   * (`AllPrimesSoFarList.nextPrime`) and the sequence generator
   * (`SieveSequenceV0`). It supplies the `accepts` fact needed by later lemmas
   * such as `assertApplyOneAtOrBeforeAccepted` and the conditional equality.
   */
  def assertNextPrimePassesV0Filter(primes: AllPrimesSoFarList): Boolean = {
    require(!primes.isEmpty)
    require(primes.size > 1)
    require(AllPrimesSoFarList.allPrimesSoFar(primes.list))

    val np = AllPrimesSoFarList.nextPrime(primes.list)
    val filterPrimes: List[Prime] = primes.list.tail.list

    assert(np.value > primes.head.value)
    SortedPrimeList.assertTailDescending(primes.list.list)
    PrimeUtils.primeIsCoprimeWithSmallerList(np.value, filterPrimes)
  }.holds

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
    assert(filterModulus > BigInt(0))
    assert(searchBound(k) < upper)
    assert(previous + BigInt(1) <= upper)
    assert(searchBoundPassesFilter(k + BigInt(1)))
    assert(accepts(upper))
    assert(next == searchNext(previous + BigInt(1), upper))
    assert(next >= previous + BigInt(1))
    next > previous
  }.holds

  /**
   * Lifts local strict growth into an ordered-index comparison.
   *
   * `applyStrictlyIncreases` proves the immediate step
   * `apply(i + 1) > apply(i)`. The skip-multiple proof also needs the
   * cumulative form: when one index is before another, its generated value is
   * no larger. This helper packages that induction so later proofs can convert
   * an index ordering into a value ordering without replaying the whole chain
   * of strict-growth facts.
   */
  private def applyIndexOrderPreservesValues(from: BigInt, until: BigInt): Boolean = {
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
  private def applyIndexStrictlyPreservesValues(from: BigInt, until: BigInt): Boolean = {
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
  private def valueBoundImpliesIndexBound(index: BigInt, bound: BigInt): Boolean = {
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
  }.ensuring(res => res >= k && apply(res) == value)

  /**
   * Returns the generated index for any accepted value at or above the head.
   *
   * This is the V0 completeness witness in executable form. The mathematical
   * statement says that every natural number accepted by the tail filters occurs
   * somewhere in the generated stream. Stainless does not need an existential
   * quantifier here; returning the index is stronger and more useful. The
   * postcondition states the witness directly: the returned index is
   * nonnegative, and applying the generator at that index gives back `value`.
   */
  def indexOfAccepted(value: BigInt): BigInt = {
    require(value >= head.value)
    require(accepts(value))

    assert(apply(BigInt(0)) == head.value)
    assert(apply(BigInt(0)) <= value)
    findIndexForAcceptedFrom(value, BigInt(0))
  }.ensuring(res => res >= BigInt(0) && apply(res) == value)

  /**
   * Proves that the residue of apply(k) modulo filterModulus is coprime
   * with all filter primes. This establishes the fundamental connection
   * between V0's linear-scan generator and the residue cycle: every
   * generated value, when reduced modulo the filter modulus, lands on
   * a residue that survives all filter primes.
   *
   * For each filter prime p:
   *   1. accepts(apply(k)) gives Calc.mod(apply(k), p) != 0
   *   2. Since filterModulus = product(filterValues), each p divides it.
   *      Uses the prefix-product decomposition from expandedCoprimePreservesFilter
   *      to prove Calc.mod(filterModulus, p) == 0 at each step.
   *   3. assertMultiplePreservesDivisible gives Calc.mod(q * filterModulus, p) == 0
   *   4. modZeroPlusC gives Calc.mod(q*filterModulus + r, p) == Calc.mod(r, p)
   *      (when mod(q*filterModulus, p) == 0, which follows from step 2)
   *   5. From (1) and (4): Calc.mod(r, p) != 0
   * Therefore isCoprime(r, filterValues).
   */
  def assertApplyModIsCoprime(k: BigInt): Boolean = {
    require(k >= BigInt(0))

    val value = apply(k)
    val r = Calc.mod(value, filterModulus)
    val q = Calc.div(value, filterModulus)

    primorialMatchesSieveProduct(filterPrimes)
    assert(filterModulus == SieveUtils.product(filterValues))

    assertModIsCoprimeForAll(value, r, q, filterModulus, filterValues, BigInt(1))
  }.holds

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
  private def assertModIsCoprimeForAll(
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
   *   2. Calc.mod(M, p) == 0 (from the product equality)
   *   3. modAdd(v, p, M) + modIdempotence gives:
   *      Calc.mod(v + M, p) == Calc.mod(v, p)
   *   4. Therefore Calc.mod(v, p) != 0
   */
  private def assertReverseCoprimePreservation(
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
   * Proves that apply(k + p) == apply(k) + filterModulus for all k >= 0,
   * where p = indexOfAccepted(head + filterModulus).
   *
   * This is the core "loop around M" property: each block of length
   * filterModulus contains exactly p generated values, so shifting by
   * the period p adds exactly filterModulus.
   *
   * The inductive step uses two inequalities:
   *   1. apply(k+p) <= apply(k) + M (by nextDoesNotPassAcceptedValue
   *      from position k-1+p toward the accepted value apply(k) + M)
   *   2. apply(k) + M <= apply(k+p) (by reverse periodic preservation:
   *      any accepted value between apply(k)+M and apply(k+1)+M would
   *      give a contradiction with nextDoesNotPassAcceptedValue)
   */
  private def assertBlockShift(k: BigInt, p: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(p >= BigInt(0))
    require(apply(p) == head.value + filterModulus)
    decreases(k)

    if (k == BigInt(0)) {
      true
    } else {
      primorialMatchesSieveProduct(filterPrimes)
      assert(filterModulus == SieveUtils.product(filterValues))
      assert(assertBlockShift(k - 1, p))
      true
    }
  }.ensuring(res => {
    if (k == BigInt(0)) {
      res && apply(p) == apply(k) + filterModulus
    } else {
      primorialMatchesSieveProduct(filterPrimes)
      assert(filterModulus == SieveUtils.product(filterValues))

      val target = apply(k) + filterModulus
      assert(target >= head.value)
      primorialMatchesSieveProduct(filterPrimes)
      assert(filterModulus == SieveUtils.product(filterValues))
      assert(SieveUtils.isCoprime(apply(k), filterValues))
      assert(expandedCoprimePreservesFilter(
        apply(k), BigInt(1), filterModulus, filterValues, BigInt(1)
      ))
      assert(accepts(target))
      assert(apply(k - 1 + p) < target)
      assert(nextDoesNotPassAcceptedValue(k - 1 + p, target))
      assert(apply(k + p) <= target)

      val shifted = apply(k + p) - filterModulus
      assert(shifted >= BigInt(0))
      assert(assertReverseCoprimePreservation(shifted, filterModulus, filterValues, BigInt(1)))
      assert(accepts(shifted))
      assert(apply(k - 1) < shifted)
      assert(nextDoesNotPassAcceptedValue(k - 1, shifted))
      assert(apply(k) <= shifted)
      assert(apply(k) + filterModulus <= apply(k + p))

      res && apply(k + p) == apply(k) + filterModulus
    }
  })

  /**
   * Proves that the residues of apply(k) modulo filterModulus cycle
   * with period p = indexOfAccepted(head + filterModulus).
   *
   * From assertBlockShift: apply(k + p) == apply(k) + filterModulus.
   * Then mod(apply(k+p), M) == mod(apply(k) + M, M) == mod(apply(k), M).
   */
  def assertApplyResidueCycles(k: BigInt, p: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(p >= BigInt(0))
    require(apply(p) == head.value + filterModulus)
    true
  }.ensuring(res => {
    primorialMatchesSieveProduct(filterPrimes)
    assert(filterModulus == SieveUtils.product(filterValues))
    assert(assertBlockShift(k, p))
    assert(apply(k + p) == apply(k) + filterModulus)
    assert(AdditionAndMultiplication.APlusMultipleTimesBSameMod(apply(k), filterModulus, BigInt(1)))
    res && Calc.mod(apply(k + p), filterModulus) == Calc.mod(apply(k), filterModulus)
  })

  def assertGapPositive(k: BigInt): Boolean = {
    require(k >= BigInt(0))
    assert(applyStrictlyIncreases(k))
    apply(k + BigInt(1)) - apply(k) > BigInt(0)
  }.holds

  def assertGapPeriodic(k: BigInt, p: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(p >= BigInt(0))
    require(apply(p) == head.value + filterModulus)
    true
  }.ensuring(res => {
    primorialMatchesSieveProduct(filterPrimes)
    assert(filterModulus == SieveUtils.product(filterValues))
    assert(assertBlockShift(k, p))
    assert(apply(k + p) == apply(k) + filterModulus)
    assert(assertBlockShift(k + BigInt(1), p))
    assert(apply(k + BigInt(1) + p) == apply(k + BigInt(1)) + filterModulus)
    val g1 = apply(k + BigInt(1)) - apply(k)
    val g2 = apply(k + BigInt(1) + p) - apply(k + p)
    res && g1 == g2
  })

  private def sumGap(from: BigInt, until: BigInt): BigInt = {
    require(from >= BigInt(0))
    require(until >= from)
    decreases(until - from)
    if (from == until) BigInt(0)
    else (apply(from + BigInt(1)) - apply(from)) + sumGap(from + BigInt(1), until)
  }

  private def assertSumGapTelescopes(from: BigInt, until: BigInt): Boolean = {
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
  private def assertSumGapPositive(from: BigInt, until: BigInt): Boolean = {
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

  def assertGapSum(p: BigInt): Boolean = {
    require(p >= BigInt(0))
    require(apply(p) == head.value + filterModulus)
    primorialMatchesSieveProduct(filterPrimes)
    assert(filterModulus == SieveUtils.product(filterValues))
    assert(assertSumGapTelescopes(BigInt(0), p))
    sumGap(BigInt(0), p) == filterModulus
  }.holds

  def assertApplyEqualsHeadPlusGapSum(k: BigInt): Boolean = {
    require(k >= BigInt(0))
    assert(assertSumGapTelescopes(BigInt(0), k))
    apply(k) == head.value + sumGap(BigInt(0), k)
  }.holds

  def gapList(from: BigInt, count: BigInt): List[BigInt] = {
    require(from >= BigInt(0))
    require(count >= BigInt(0))
    decreases(count)
    if (count == BigInt(0)) List.empty[BigInt]
    else (apply(from + BigInt(1)) - apply(from)) :: gapList(from + BigInt(1), count - BigInt(1))
  }

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

  def assertFilterPreservesNextPosition(
    nextSeq: SieveSequenceV0,
    k: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == filterValues)
    require(nextSeq.head.value == head.value)
    require(nextSeq.accepts(apply(k)))
    require(Calc.mod(apply(k + BigInt(1)), nextSeq.filterValues.head) != BigInt(0))
    true
  }.ensuring(res => {
    val V = apply(k)
    val W = apply(k + BigInt(1))
    val vIdx = nextSeq.indexOfAccepted(V)

    assert(accepts(W))
    assert(nextSeq.accepts(W))

    assert(applySkipsNoAcceptedBetween(k + BigInt(1)))
    assert(noAcceptedBetween(V + BigInt(1), W))

    assert(nextSeq.applyStrictlyIncreases(vIdx))
    assert(nextSeq(vIdx + BigInt(1)) > V)
    val z = nextSeq(vIdx + BigInt(1))
    assert(SieveUtils.isCoprime(z, filterValues))
    assert(accepts(z))
    assert(nextDoesNotPassAcceptedValue(k, z))
    assert(W <= z)

    assert(nextSeq.accepts(W))
    assert(nextSeq.nextDoesNotPassAcceptedValue(vIdx, W))
    assert(z <= W)

    res && nextSeq(vIdx + BigInt(1)) == W
  })

  /**
   * Proves the copied-gap corollary for the immediate-survivor case.
   *
   * The old sequence filters by `filterValues`; `nextSeq` filters by one
   * additional front value followed by the same tail. If `apply(k)` is accepted
   * by `nextSeq`, it has an index there. If the old immediate successor
   * `apply(k + 1)` is also not a multiple of the new front filter, then
   * `nextSeq` must place that successor immediately after `apply(k)`.
   *
   * Therefore the gap is copied unchanged:
   *
   *   nextSeq(vIdx + 1) - nextSeq(vIdx) == apply(k + 1) - apply(k)
   *
   * This is the local copy case used by gap-merge proofs. It deliberately
   * says nothing about the branch where `apply(k + 1)` is removed by the new
   * front filter; that branch is handled by merge/skip lemmas.
   */
  def assertFilterPreservesNextGap(
    nextSeq: SieveSequenceV0,
    k: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == filterValues)
    require(nextSeq.head.value == head.value)
    require(nextSeq.accepts(apply(k)))
    require(Calc.mod(apply(k + BigInt(1)), nextSeq.filterValues.head) != BigInt(0))

    val v = apply(k)
    val w = apply(k + BigInt(1))
    val vIdx = nextSeq.indexOfAccepted(v)

    assert(nextSeq(vIdx) == v)
    assert(assertFilterPreservesNextPosition(nextSeq, k))
    assert(nextSeq(vIdx + BigInt(1)) == w)

    nextSeq(vIdx + BigInt(1)) - nextSeq(vIdx) == w - v
  }.holds

  private def findFirstNonMultipleAfter(k: BigInt, p: BigInt, bound: BigInt): BigInt = {
    require(k >= BigInt(0))
    require(p > BigInt(0))
    require(bound > k)
    require(Calc.mod(apply(bound), p) != BigInt(0))
    decreases(bound - k)
    if (Calc.mod(apply(k + BigInt(1)), p) != BigInt(0)) k + BigInt(1)
    else {
      assert(bound > k + BigInt(1))
      findFirstNonMultipleAfter(k + BigInt(1), p, bound)
    }
  }.ensuring(res => res >= k + BigInt(1) && res <= bound && Calc.mod(apply(res), p) != BigInt(0))

  private def assertBlockShiftMultiple(k: BigInt, n: BigInt, period: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(n >= BigInt(0))
    require(period > BigInt(0))
    require(apply(period) == head.value + filterModulus)
    decreases(n)
    if (n == BigInt(0)) {
      apply(k + n * period) == apply(k) + n * filterModulus
    } else {
      val prev = n - BigInt(1)
      assert(assertBlockShiftMultiple(k, prev, period))
      assert(assertBlockShift(k + prev * period, period))
      apply(k + n * period) == apply(k) + n * filterModulus
    }
  }.holds

  private def assertFirstNonMultipleIsAtOrBefore(k: BigInt, zIdx: BigInt, p: BigInt, bound: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(zIdx > k)
    require(zIdx <= bound)
    require(p > BigInt(0))
    require(Calc.mod(apply(zIdx), p) != BigInt(0))
    require(Calc.mod(apply(bound), p) != BigInt(0))
    decreases(bound - k)
    val m = findFirstNonMultipleAfter(k, p, bound)
    if (k + BigInt(1) == m) {
      m <= zIdx
    } else {
      assert(k + BigInt(1) < m)
      assert(Calc.mod(apply(k + BigInt(1)), p) == BigInt(0))
      assert(zIdx > k + BigInt(1))
      assert(assertFirstNonMultipleIsAtOrBefore(k + BigInt(1), zIdx, p, bound))
      m <= zIdx
    }
  }.holds

  /**
   * Proves the recursive skip invariant for the old stream.
   *
   * Let `m` be the first old-stream index after `k` whose value is not a
   * multiple of the new filter `p`. Every old-stream index strictly between
   * `k` and `m` must therefore be a multiple of `p`.
   *
   * This is the recursive gap-merging backbone: when the next sequence cannot
   * copy `apply(k + 1)`, it is not because the value disappeared mysteriously;
   * it is because the new filter consumes that old gap. Repeating this fact
   * index by index accounts for exactly the run of old gaps merged before the
   * first surviving value.
   */
  private def assertSkippedIndexBeforeFirstIsMultiple(
    k: BigInt,
    idx: BigInt,
    p: BigInt,
    bound: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(p > BigInt(0))
    require(bound > k)
    require(Calc.mod(apply(bound), p) != BigInt(0))
    require(idx > k)
    require(idx < findFirstNonMultipleAfter(k, p, bound))
    decreases(idx - k)

    val m = findFirstNonMultipleAfter(k, p, bound)
    assert(k + BigInt(1) <= idx)
    assert(k + BigInt(1) < m)

    if (Calc.mod(apply(k + BigInt(1)), p) != BigInt(0)) {
      assert(m == k + BigInt(1))
      assert(false)
      Calc.mod(apply(idx), p) == BigInt(0)
    } else if (idx == k + BigInt(1)) {
      Calc.mod(apply(idx), p) == BigInt(0)
    } else {
      assert(idx > k + BigInt(1))
      assert(bound > k + BigInt(1))
      val nextM = findFirstNonMultipleAfter(k + BigInt(1), p, bound)
      assert(m == nextM)
      assert(idx < nextM)
      assert(assertSkippedIndexBeforeFirstIsMultiple(k + BigInt(1), idx, p, bound))
      Calc.mod(apply(idx), p) == BigInt(0)
    }
  }.holds

  /**
   * Anchors the next-sequence index before the first old-stream survivor.
   *
   * The full gap-merge proof starts from an alignment point:
   * `nextSeq(vIdx) == apply(k)`, where `vIdx` is the next-sequence index for
   * the old value `apply(k)`. The first old value that survives the new filter
   * is `apply(m)`, with `m = findFirstNonMultipleAfter(k, p, bound)`.
   *
   * This lemma proves the ordering fact needed by
   * `nextSeq.nextDoesNotPassAcceptedValue`: the aligned next value is strictly
   * before the first old survivor. Keeping this fact separate avoids asking
   * Stainless to rediscover strict old-stream monotonicity inside the larger
   * filter/gap proof.
   */
  private def assertNextAnchorBeforeFirstSurvivor(
    nextSeq: SieveSequenceV0,
    k: BigInt,
    p: BigInt,
    bound: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(p > BigInt(0))
    require(bound > k)
    require(Calc.mod(apply(bound), p) != BigInt(0))
    require(nextSeq.head.value == head.value)
    require(nextSeq.accepts(apply(k)))

    val vIdx = nextSeq.indexOfAccepted(apply(k))
    val m = findFirstNonMultipleAfter(k, p, bound)

    assert(m >= k + BigInt(1))
    assert(m > k)
    assert(applyIndexStrictlyPreservesValues(k, m))
    assert(apply(k) < apply(m))
    assert(nextSeq(vIdx) == apply(k))
    nextSeq(vIdx) < apply(m)
  }.holds

  /**
   * Connects the recursive old-stream skip invariant to next-sequence rejection.
   *
   * `assertSkippedIndexBeforeFirstIsMultiple` proves that every old index between
   * the aligned point `k` and the first old survivor `m` is a multiple of the new
   * filter `p`. This lemma translates that arithmetic fact into the sequence
   * language used by gap merging: those skipped old values are not accepted by
   * `nextSeq`, because `p` is the newly added front filter in `nextSeq`.
   *
   * Separating this bridge keeps the eventual `assertSkipUntilNonMultiple` proof
   * from needing to unfold both the recursive search and the next-sequence filter
   * definition in the same verification condition.
   */
  private def assertSkippedOldValueRejectedByNext(
    nextSeq: SieveSequenceV0,
    k: BigInt,
    idx: BigInt,
    p: BigInt,
    bound: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(p > BigInt(0))
    require(bound > k)
    require(Calc.mod(apply(bound), p) != BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.head == p)
    require(nextSeq.head.value == head.value)
    require(idx > k)
    require(idx < findFirstNonMultipleAfter(k, p, bound))

    assert(assertSkippedIndexBeforeFirstIsMultiple(k, idx, p, bound))
    assert(Calc.mod(apply(idx), p) == BigInt(0))
    assert(apply(idx) >= head.value)
    assert(apply(idx) >= nextSeq.head.value)
    assert(assertRejectedByNextWhenNewHeadMultiple(nextSeq, apply(idx), p))
    !nextSeq.accepts(apply(idx))
  }.holds

  /**
   * Proves the upper inequality for the skip-to-first-survivor equality.
   *
   * Let `m` be the first old-stream index after `k` whose value is not a
   * multiple of the new front filter `p`. This lemma proves that the next value
   * emitted by `nextSeq` after the aligned old value cannot pass `apply(m)`.
   *
   * The proof deliberately avoids the reverse-index/minimality argument. It only
   * packages the local completeness fact for `nextSeq`: once `apply(m)` is known
   * to be accepted by `nextSeq`, and the aligned next-sequence value is strictly
   * before `apply(m)`, `nextSeq.nextDoesNotPassAcceptedValue` gives
   * `nextSeq(vIdx + 1) <= apply(m)`.
   */
  private def assertNextValueAtOrBeforeFirstSurvivor(
    nextSeq: SieveSequenceV0,
    k: BigInt,
    p: BigInt,
    bound: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(p > BigInt(0))
    require(bound > k)
    require(Calc.mod(apply(bound), p) != BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.head == p)
    require(nextSeq.filterValues.tail == filterValues)
    require(nextSeq.head.value == head.value)
    require(nextSeq.accepts(apply(k)))

    val vIdx = nextSeq.indexOfAccepted(apply(k))
    val m = findFirstNonMultipleAfter(k, p, bound)

    assert(m >= k + BigInt(1))
    assert(m >= BigInt(0))
    assert(Calc.mod(apply(m), p) != BigInt(0))
    assert(Calc.mod(apply(m), nextSeq.filterValues.head) != BigInt(0))
    assert(accepts(apply(m)))
    assert(assertAcceptedByNextWhenOldAcceptedAndNewHeadNonMultiple(nextSeq, apply(m)))
    assert(nextSeq.accepts(apply(m)))
    assert(assertNextAnchorBeforeFirstSurvivor(nextSeq, k, p, bound))
    assert(nextSeq.nextDoesNotPassAcceptedValue(vIdx, apply(m)))
    nextSeq(vIdx + BigInt(1)) <= apply(m)
  }.holds

  /**
   * Maps the next-sequence successor back to an old-stream index after `k`.
   *
   * In the reverse half of the skip-to-first-survivor equality, we start with
   * the value emitted by `nextSeq` immediately after the aligned old value
   * `apply(k)`. Call that value `z`. Because `nextSeq` strictly increases,
   * `z` is strictly greater than `apply(k)`.
   *
   * The reverse filter bridge then tells us that `z` is also accepted by this
   * old sequence, so `indexOfAccepted(z)` is a valid old-stream index. This
   * lemma proves that the old index cannot be at or before `k`: if it were, old
   * stream monotonicity would give `z = apply(zIdx) <= apply(k)`, contradicting
   * the strict next-sequence step.
   *
   * The lemma intentionally proves only the index-order fact `zIdx > k`. The
   * later reverse inequality proof will separately use this index together with
   * `assertFirstNonMultipleIsAtOrBefore` and `applyIndexOrderPreservesValues`.
   */
  private def assertNextSuccessorOldIndexAfterAnchor(
    nextSeq: SieveSequenceV0,
    k: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == filterValues)
    require(nextSeq.head.value == head.value)
    require(nextSeq.accepts(apply(k)))

    val vIdx = nextSeq.indexOfAccepted(apply(k))
    assert(vIdx >= BigInt(0))
    assert(nextSeq(vIdx) == apply(k))
    assert(nextSeq.applyStrictlyIncreases(vIdx))

    val z = nextSeq(vIdx + BigInt(1))
    assert(z > apply(k))
    assert(nextSeq.accepts(z))
    assert(assertNextAcceptedImpliesOldAcceptedAndNewHeadNonMultiple(nextSeq, z))
    assert(accepts(z))

    val zIdx = indexOfAccepted(z)
    assert(zIdx >= BigInt(0))
    assert(apply(zIdx) == z)

    if (zIdx > k) {
      true
    } else {
      assert(zIdx <= k)
      assert(applyIndexOrderPreservesValues(zIdx, k))
      assert(apply(zIdx) <= apply(k))
      assert(z <= apply(k))
      zIdx > k
    }
  }.holds

  /**
   * Bounds the old-stream index of the next-sequence successor.
   *
   * The reverse half of the skip proof needs to call
   * `assertFirstNonMultipleIsAtOrBefore(k, zIdx, p, bound)`, so the old-stream
   * index `zIdx` for the next-sequence successor must be inside the same finite
   * search window. This lemma proves that bound without involving the
   * first-non-multiple minimality argument.
   *
   * The proof first reuses the upper inequality helper:
   * `z = nextSeq(vIdx + 1) <= apply(m)`. The search helper already guarantees
   * `m <= bound`, and old-stream monotonicity turns that into
   * `apply(m) <= apply(bound)`. Therefore `z <= apply(bound)`. Since
   * `indexOfAccepted(z)` is the old-stream index that emits `z`,
   * `valueBoundImpliesIndexBound` converts the value bound back into
   * `zIdx <= bound`.
   */
  private def assertNextSuccessorOldIndexWithinBound(
    nextSeq: SieveSequenceV0,
    k: BigInt,
    p: BigInt,
    bound: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(p > BigInt(0))
    require(bound > k)
    require(Calc.mod(apply(bound), p) != BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.head == p)
    require(nextSeq.filterValues.tail == filterValues)
    require(nextSeq.head.value == head.value)
    require(nextSeq.accepts(apply(k)))

    val vIdx = nextSeq.indexOfAccepted(apply(k))
    val z = nextSeq(vIdx + BigInt(1))
    val zIdx = indexOfAccepted(z)
    val m = findFirstNonMultipleAfter(k, p, bound)

    assert(assertNextValueAtOrBeforeFirstSurvivor(nextSeq, k, p, bound))
    assert(z <= apply(m))
    assert(m <= bound)
    assert(m >= BigInt(0))
    assert(applyIndexOrderPreservesValues(m, bound))
    assert(apply(m) <= apply(bound))
    assert(z <= apply(bound))
    assert(apply(zIdx) == z)
    assert(valueBoundImpliesIndexBound(zIdx, bound))
    zIdx <= bound
  }.holds

  /**
   * Proves the reverse ordering between the first old survivor and the next value.
   *
   * The forward helper already proves that the next sequence cannot pass the
   * first old-stream value after `k` that is not a multiple of `p`. This lemma
   * proves the opposite inequality.
   *
   * Let `z` be the value emitted by `nextSeq` immediately after `apply(k)`.
   * Because `z` is accepted by `nextSeq`, it is also accepted by this old
   * sequence and is not a multiple of the new filter `p`. The previous two
   * connector lemmas place the old-stream index of `z` strictly after `k` and
   * at or before `bound`. Therefore the first non-multiple found by
   * `findFirstNonMultipleAfter` must occur at or before that old index, and
   * old-stream monotonicity gives `apply(m) <= z`.
   */
  private def assertFirstSurvivorAtOrBeforeNextValue(
    nextSeq: SieveSequenceV0,
    k: BigInt,
    p: BigInt,
    bound: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(p > BigInt(0))
    require(bound > k)
    require(Calc.mod(apply(bound), p) != BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.head == p)
    require(nextSeq.filterValues.tail == filterValues)
    require(nextSeq.head.value == head.value)
    require(nextSeq.accepts(apply(k)))

    val vIdx = nextSeq.indexOfAccepted(apply(k))
    val z = nextSeq(vIdx + BigInt(1))
    val zIdx = indexOfAccepted(z)
    val m = findFirstNonMultipleAfter(k, p, bound)

    assert(assertNextSuccessorOldIndexAfterAnchor(nextSeq, k))
    assert(zIdx > k)
    assert(assertNextSuccessorOldIndexWithinBound(nextSeq, k, p, bound))
    assert(zIdx <= bound)
    assert(assertNextAcceptedImpliesOldAcceptedAndNewHeadNonMultiple(nextSeq, z))
    assert(accepts(z))
    assert(Calc.mod(z, p) != BigInt(0))
    assert(apply(zIdx) == z)
    assert(Calc.mod(apply(zIdx), p) != BigInt(0))
    assert(assertFirstNonMultipleIsAtOrBefore(k, zIdx, p, bound))
    assert(m <= zIdx)
    assert(applyIndexOrderPreservesValues(m, zIdx))
    assert(apply(m) <= apply(zIdx))
    apply(m) <= z
  }.holds

  /**
   * Connects both ordering directions into the skip-to-first-survivor equality.
   *
   * Starting from an old value `apply(k)` that also exists in `nextSeq`, the
   * next value in `nextSeq` is exactly the first later old-stream value that is
   * not a multiple of the new filter `p`. Earlier old values may still satisfy
   * this sequence's tail filter, but they are skipped precisely because `p`
   * divides them.
   *
   * This lemma is intentionally only the bounded equality. It does not choose
   * the bound; callers remain responsible for proving a finite search window
   * whose endpoint is itself not a multiple of `p`.
   */
  private def assertNextSuccessorIsFirstSurvivor(
    nextSeq: SieveSequenceV0,
    k: BigInt,
    p: BigInt,
    bound: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(p > BigInt(0))
    require(bound > k)
    require(Calc.mod(apply(bound), p) != BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.head == p)
    require(nextSeq.filterValues.tail == filterValues)
    require(nextSeq.head.value == head.value)
    require(nextSeq.accepts(apply(k)))

    val vIdx = nextSeq.indexOfAccepted(apply(k))
    val m = findFirstNonMultipleAfter(k, p, bound)

    assert(assertNextValueAtOrBeforeFirstSurvivor(nextSeq, k, p, bound))
    assert(nextSeq(vIdx + BigInt(1)) <= apply(m))
    assert(assertFirstSurvivorAtOrBeforeNextValue(nextSeq, k, p, bound))
    assert(apply(m) <= nextSeq(vIdx + BigInt(1)))
    nextSeq(vIdx + BigInt(1)) == apply(m)
  }.holds

  /**
   * Exposes the finite endpoint used by the period-based merge proof.
   *
   * The skipped-successor merge needs a bounded search for the first old-stream
   * value after `k` that survives the new front filter `p`. The endpoint
   * `k + p * period` is useful because one old period adds `filterModulus`, so
   * `p` whole periods add `p * filterModulus`. That shift preserves the
   * remainder modulo `p`, which means the endpoint survives whenever `apply(k)`
   * survives.
   *
   * This lemma packages those endpoint facts for callers: the bound is after
   * `k`, the divisor `p` is positive, and `apply(bound)` is not a multiple of
   * `p`.
   */
  def assertPeriodBoundIsNonMultiple(nextSeq: SieveSequenceV0, k: BigInt, period: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == filterValues)
    require(nextSeq.head.value == head.value)
    require(nextSeq.accepts(apply(k)))
    require(apply(period) == head.value + filterModulus)
    require(Calc.mod(head.value + filterModulus, nextSeq.filterValues.head) != BigInt(0))

    val p = nextSeq.filterValues.head
    val bound = k + p * period

    primorialMatchesSieveProduct(filterPrimes)
    assert(filterModulus == SieveUtils.product(filterValues))
    assert(p > BigInt(0))
    assert(bound > k)
    assert(assertBlockShiftMultiple(k, p, period))
    assert(apply(bound) == apply(k) + p * filterModulus)
    assert(assertNextAcceptedImpliesOldAcceptedAndNewHeadNonMultiple(nextSeq, apply(k)))
    assert(Calc.mod(apply(k), p) != BigInt(0))
    assert(AdditionAndMultiplication.ATimesBSameMod(apply(k), p, filterModulus))
    assert(Calc.mod(apply(k) + p * filterModulus, p) == Calc.mod(apply(k), p))

    Calc.mod(apply(bound), p) != BigInt(0)
  }.ensuring(res => {
    val p = nextSeq.filterValues.head
    val bound = k + p * period
    res && p > BigInt(0) && bound > k && Calc.mod(apply(bound), p) != BigInt(0)
  })

  /**
   * Period-based gap merge for a skipped immediate old successor.
   *
   * This is the public wrapper around the bounded merge lemma. The bounded
   * lemma needs a finite endpoint whose old-stream value is not a multiple of
   * the new front filter `p`. The period witness supplies exactly that endpoint:
   * shifting `k` by `p` whole old periods moves the value from `apply(k)` to
   * `apply(k) + p * filterModulus`, which has the same remainder modulo `p`.
   *
   * The precondition `Calc.mod(apply(k + 1), p) == 0` describes the interesting
   * merge case: the next old value is rejected by the new filter, so the next
   * sequence must skip forward. The result says it skips no more and no less
   * than the first old value after `k` that is not a multiple of `p`.
   */
  def assertSkipUntilNonMultiple(nextSeq: SieveSequenceV0, k: BigInt, period: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == filterValues)
    require(nextSeq.head.value == head.value)
    require(nextSeq.accepts(apply(k)))
    require(Calc.mod(apply(k + BigInt(1)), nextSeq.filterValues.head) == BigInt(0))
    require(apply(period) == head.value + filterModulus)
    require(Calc.mod(head.value + filterModulus, nextSeq.filterValues.head) != BigInt(0))

    val p = nextSeq.filterValues.head
    val vIdx = nextSeq.indexOfAccepted(apply(k))
    val bound = k + p * period

    primorialMatchesSieveProduct(filterPrimes)
    assert(filterModulus == SieveUtils.product(filterValues))
    assert(p > BigInt(0))
    assert(bound > k)
    assert(assertBlockShiftMultiple(k, p, period))
    assert(apply(bound) == apply(k) + p * filterModulus)
    assert(assertNextAcceptedImpliesOldAcceptedAndNewHeadNonMultiple(nextSeq, apply(k)))
    assert(Calc.mod(apply(k), p) != BigInt(0))
    assert(AdditionAndMultiplication.ATimesBSameMod(apply(k), p, filterModulus))
    assert(Calc.mod(apply(k) + p * filterModulus, p) == Calc.mod(apply(k), p))
    assert(Calc.mod(apply(bound), p) != BigInt(0))
    val m = findFirstNonMultipleAfter(k, p, bound)
    assert(assertNextSuccessorIsFirstSurvivor(nextSeq, k, p, bound))

    nextSeq(vIdx + BigInt(1)) == apply(m)
  }.holds

  /**
   * Obvious property-name alias for the merge landing point.
   *
   * This lemma intentionally restates `assertSkipUntilNonMultiple` with a name
   * that matches the gap-cycle proof ladder: when the immediate old successor
   * `apply(k + 1)` is removed by the newly added front filter, the next sequence
   * lands exactly on the first later old-stream value that survives that new
   * filter.
   *
   * Keeping this public alias makes the merge proof easier to find from the
   * mathematical property name without forcing callers to remember the helper
   * implementation name.
   */
  def assertMergeLandsOnFirstSurvivor(nextSeq: SieveSequenceV0, k: BigInt, period: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == filterValues)
    require(nextSeq.head.value == head.value)
    require(nextSeq.accepts(apply(k)))
    require(Calc.mod(apply(k + BigInt(1)), nextSeq.filterValues.head) == BigInt(0))
    require(apply(period) == head.value + filterModulus)
    require(Calc.mod(head.value + filterModulus, nextSeq.filterValues.head) != BigInt(0))

    val p = nextSeq.filterValues.head
    val vIdx = nextSeq.indexOfAccepted(apply(k))
    val bound = k + p * period

    assert(assertPeriodBoundIsNonMultiple(nextSeq, k, period))
    val m = findFirstNonMultipleAfter(k, p, bound)
    assert(assertSkipUntilNonMultiple(nextSeq, k, period))

    nextSeq(vIdx + BigInt(1)) == apply(m)
  }.holds

  /**
   * Proves the merged-gap corollary for the skipped-successor case.
   *
   * When the immediate old successor `apply(k + 1)` is removed by the new front
   * filter, `nextSeq` lands on the first later old-stream survivor `apply(m)`.
   * The new gap is therefore not a new arithmetic object; it is exactly the
   * telescope of the old adjacent gaps from `k` up to `m`.
   *
   * This is the gap-list merge shape needed by the prefix transformer: copied
   * gaps use `assertFilterPreservesNextGap`, while skipped runs use this lemma
   * to replace several old gaps with their sum.
   */
  def assertMergeGapEqualsOldGapSum(nextSeq: SieveSequenceV0, k: BigInt, period: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == filterValues)
    require(nextSeq.head.value == head.value)
    require(nextSeq.accepts(apply(k)))
    require(Calc.mod(apply(k + BigInt(1)), nextSeq.filterValues.head) == BigInt(0))
    require(apply(period) == head.value + filterModulus)
    require(Calc.mod(head.value + filterModulus, nextSeq.filterValues.head) != BigInt(0))

    val p = nextSeq.filterValues.head
    val vIdx = nextSeq.indexOfAccepted(apply(k))
    val bound = k + p * period

    assert(assertPeriodBoundIsNonMultiple(nextSeq, k, period))
    val m = findFirstNonMultipleAfter(k, p, bound)
    assert(m >= k)
    assert(assertMergeLandsOnFirstSurvivor(nextSeq, k, period))
    assert(nextSeq(vIdx) == apply(k))
    assert(nextSeq(vIdx + BigInt(1)) == apply(m))
    assert(assertSumGapTelescopes(k, m))

    nextSeq(vIdx + BigInt(1)) - nextSeq(vIdx) == sumGap(k, m)
  }.holds

  /**
   * Advances one output position in the merged old-index view.
   *
   * The future gap-prefix transformer should not scan natural numbers again;
   * it should walk this sequence's already-filtered indices and decide whether
   * each adjacent old gap is copied or whether several old gaps are merged.
   *
   * This helper performs exactly one such step from an old index `k` whose value
   * is already known to appear in `nextSeq`. If the immediate old successor
   * `apply(k + 1)` survives the new front filter, the next old index is simply
   * `k + 1`. Otherwise the step uses the bounded period witness to find the
   * first later old value that is not a multiple of the new front filter. In
   * both cases the returned index is strictly after `k`. Its value is still
   * accepted by this sequence, is not a multiple of the new front filter, and
   * is accepted by `nextSeq`. Exporting all three facts is important: callers
   * cannot rely on the internal proof assertions, so the bridge-shape invariant
   * must appear in the postcondition.
   */
  def nextMergedGapOldIndex(nextSeq: SieveSequenceV0, k: BigInt, period: BigInt): BigInt = {
    require(k >= BigInt(0))
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == filterValues)
    require(nextSeq.head.value == head.value)
    require(nextSeq.accepts(apply(k)))
    require(apply(period) == head.value + filterModulus)
    require(Calc.mod(head.value + filterModulus, nextSeq.filterValues.head) != BigInt(0))

    val p = nextSeq.filterValues.head

    if (Calc.mod(apply(k + BigInt(1)), p) != BigInt(0)) {
      assert(accepts(apply(k + BigInt(1))))
      assert(assertAcceptedByNextWhenOldAcceptedAndNewHeadNonMultiple(nextSeq, apply(k + BigInt(1))))
      assert(assertFilterPreservesNextGap(nextSeq, k))
      k + BigInt(1)
    } else {
      val bound = k + p * period

      assert(assertPeriodBoundIsNonMultiple(nextSeq, k, period))
      val m = findFirstNonMultipleAfter(k, p, bound)
      assert(m > k)
      assert(accepts(apply(m)))
      assert(Calc.mod(apply(m), p) != BigInt(0))
      assert(assertAcceptedByNextWhenOldAcceptedAndNewHeadNonMultiple(nextSeq, apply(m)))
      assert(assertMergeGapEqualsOldGapSum(nextSeq, k, period))
      m
    }
  }.ensuring(res =>
    res > k &&
      accepts(apply(res)) &&
      Calc.mod(apply(res), nextSeq.filterValues.head) != BigInt(0) &&
      nextSeq.accepts(apply(res)) &&
      {
        val vIdx = nextSeq.indexOfAccepted(apply(k))
        nextSeq(vIdx + BigInt(1)) - nextSeq(vIdx) == sumGap(k, res)
      }
  )

  /**
   * Builds a bounded prefix of the copied-or-merged gap list.
   *
   * This is the executable shape of the gap-merge process. The parameter
   * `remaining` says how many next-sequence gaps to emit, so termination is
   * independent of how many old indices are skipped in each merge. The parameter
   * `k` is the current old index whose value is already aligned with the current
   * next-sequence value; that alignment is represented by
   * `nextSeq.accepts(apply(k))`.
   *
   * Each recursive step asks `nextMergedGapOldIndex` for the next old index
   * whose value survives the new front filter. The emitted gap is the telescoped
   * old distance from `k` to that returned index. A one-index move is a copied
   * gap. A longer move is a merged gap. The returned list is therefore not
   * produced by scanning natural numbers again; it is produced by walking the
   * old sequence's accepted values and merging exactly the runs removed by the
   * new filter.
   */
  def mergedGapPrefix(
    nextSeq: SieveSequenceV0,
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
    require(apply(period) == head.value + filterModulus)
    require(Calc.mod(head.value + filterModulus, nextSeq.filterValues.head) != BigInt(0))
    decreases(remaining)

    if (remaining == BigInt(0)) {
      List.empty[BigInt]
    } else {
      val nextK = nextMergedGapOldIndex(nextSeq, k, period)

      assert(nextK > k)
      assert(nextK >= k)
      assert(nextK >= BigInt(0))
      assert(nextSeq.accepts(apply(nextK)))
      sumGap(k, nextK) :: mergedGapPrefix(nextSeq, nextK, remaining - BigInt(1), period)
    }
  }

  /**
   * Proves every gap emitted by `mergedGapPrefix` is strictly positive.
   *
   * This is the list-level lift of `assertSumGapPositive`. Each emitted gap is
   * `sumGap(currentOldIndex, nextOldIndex)`, where `nextMergedGapOldIndex`
   * guarantees `nextOldIndex > currentOldIndex`. By `assertSumGapPositive`,
   * that single gap is strictly positive, and by induction on `remaining`,
   * the entire emitted list satisfies `allGreaterThan(_, 0)`.
   *
   * The inductive step makes the head/tail split explicit via
   * `ListBoundUtils.assertGreaterThanHeadTail`, so the solver sees both the
   * head positivity (from the single-step lemma) and the tail positivity
   * (from the inductive hypothesis) as separate facts before being asked to
   * combine them.
   */
  def assertMergedGapPrefixAllPositive(
    nextSeq: SieveSequenceV0,
    k: BigInt,
    remaining: BigInt,
    period: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(remaining >= BigInt(0))
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == filterValues)
    require(nextSeq.head.value == head.value)
    require(nextSeq.accepts(apply(k)))
    require(apply(period) == head.value + filterModulus)
    require(Calc.mod(head.value + filterModulus, nextSeq.filterValues.head) != BigInt(0))
    decreases(remaining)

    val prefix = mergedGapPrefix(nextSeq, k, remaining, period)
    if (remaining == BigInt(0)) {
      ListBoundUtils.allGreaterThan(prefix, BigInt(0))
    } else {
      val nextOldIndex = nextMergedGapOldIndex(nextSeq, k, period)
      val tailPrefix = mergedGapPrefix(nextSeq, nextOldIndex, remaining - BigInt(1), period)

      assert(assertSumGapPositive(k, nextOldIndex))
      assert(assertMergedGapPrefixAllPositive(nextSeq, nextOldIndex, remaining - BigInt(1), period))
      assert(ListBoundUtils.assertGreaterThanHeadTail(prefix, BigInt(0)))
      ListBoundUtils.allGreaterThan(prefix, BigInt(0))
    }
  }.holds

  // P4 (assertPeriodEqualsResidueCount) SKIPPED
  // The property p == residues(M, filterValues).size is true by interval periodicity:
  // isCoprime(x, F) == isCoprime(Calc.mod(x, M), F), so any interval of length M
  // contains exactly R coprime values. But proving this in Stainless requires a
  // counting/interval lemma that times out on the inductive step.
  // Ticket: v0-gap-properties.md

//  /**
//   * Proves that `apply(1)` is prime when it lies below `head * head`.
//   *
//   * If `apply(1)` were composite its smallest prime divisor `d` would satisfy
//   * `d*d <= apply(1) < head*head`, so `d < head`. By the prime list completeness
//   * `d` is in `filterValues`, and `Calc.mod(apply(1), d) == 0` contradicts
//   * `accepts(apply(1))`. Therefore `apply(1)` must be prime.
//   */
//  def assertApplyOneIsPrimeIfBelowHeadSq(): Boolean = {
//    require(apply(BigInt(1)) < head.value * head.value)
//
  private def assertFilterValuesContains(d: BigInt): Boolean = {
    require(d >= 2)
    require(AllPrimesSoFarList.contains(d, primes.list.tail))
    require(Calc.mod(apply(BigInt(1)), d) == BigInt(0))
    decreases(primes.list.tail.size)

    if (primes.list.tail.isEmpty) {
      assert(false)
      true
    } else if (primes.list.tail.head.value == d) {
      assert(!filterValues.isEmpty)
      assert(filterValues.head == d)
      listContains(d, filterValues)
    } else {
      assert(AllPrimesSoFarList.contains(d, primes.list.tail.tail))
      assert(filterValues.tail == PrimeUtils.primeValues(primes.list.tail.tail.list))
      assert(assertFilterValuesContainsInTail(d, primes.list.tail.tail, filterValues.tail, apply(BigInt(1))))
      listContains(d, filterValues)
    }
  }.holds

  private def assertFilterValuesContainsInTail(
    d: BigInt,
    tail: SortedPrimeList,
    tailFilterValues: List[BigInt],
    n: BigInt
  ): Boolean = {
    require(d >= 2)
    require(tail.nonEmpty)
    require(AllPrimesSoFarList.contains(d, tail))
    require(tailFilterValues == PrimeUtils.primeValues(tail.list))
    require(Calc.mod(n, d) == BigInt(0))
    decreases(tail.size)

    if (tail.head.value == d) {
      assert(!tailFilterValues.isEmpty)
      assert(tailFilterValues.head == d)
      listContains(d, tailFilterValues)
    } else {
      assert(AllPrimesSoFarList.contains(d, tail.tail))
      assert(tailFilterValues.tail == PrimeUtils.primeValues(tail.tail.list))
      assert(assertFilterValuesContainsInTail(d, tail.tail, tailFilterValues.tail, n))
      listContains(d, tailFilterValues)
    }
  }.holds

  private def divisorInFilterValues(n: BigInt, d: BigInt, values: List[BigInt]): Boolean = {
    require(n > 1 && d >= 2)
    require(ListUtils.checkAllPositive(values))
    require(Calc.mod(n, d) == BigInt(0))
    require(listContains(d, values))
    decreases(values.size)

    if (values.isEmpty) {
      assert(false)
      !SieveUtils.isCoprime(n, values)
    } else if (values.head == d) {
      assert(Calc.mod(n, d) == BigInt(0))
      !SieveUtils.isCoprime(n, values)
    } else if (Calc.mod(n, values.head) == BigInt(0)) {
      !SieveUtils.isCoprime(n, values)
    } else {
      assert(listContains(d, values.tail))
      assert(divisorInFilterValues(n, d, values.tail))
      !SieveUtils.isCoprime(n, values)
    }
  }.holds

  private def listContains(d: BigInt, values: List[BigInt]): Boolean = {
    decreases(values.size)
    if (values.isEmpty) false
    else if (values.head == d) true
    else listContains(d, values.tail)
  }

  def assertApplyOneIsPrimeIfBelowHeadSq(): Boolean = {
    require(apply(BigInt(1)) < head.value * head.value)

    val v1 = apply(BigInt(1))
    assert(applyStrictlyIncreases(0))

    if (Prime.isPrime(v1)) {
      Prime.isPrime(v1)
    } else {
      val d = PrimeProperties.assertCompositeSmallestPrimeDivisor(v1)
      assert(d < head.value)
      assert(Calc.mod(v1, d) == BigInt(0))

      AllPrimesSoFarList.primeAtOrBelowHeadIsContained(d, primes.list)
      assert(AllPrimesSoFarList.contains(d, primes.list.tail))
      assert(assertFilterValuesContains(d))
      assert(divisorInFilterValues(v1, d, filterValues))
      assert(!SieveUtils.isCoprime(v1, filterValues))
      assert(passesFilter(v1))
      assert(false)
      Prime.isPrime(v1)
    }
  }.holds

  def assertApplyOneGtHead(): Boolean = {
    assert(applyStrictlyIncreases(BigInt(0)))
    val h = head.value
    val a1 = apply(BigInt(1))
    assert(a1 > h)
    h + BigInt(1) <= a1
  }.holds

  def assertApplyOneLeqValue(value: BigInt): Boolean = {
    require(value > head.value)
    require(accepts(value))

    val pIdx = indexOfAccepted(value)
    assert(pIdx >= BigInt(0))
    assert(apply(pIdx) == value)
    if (pIdx == 0) {
      assert(apply(BigInt(0)) == head.value)
      assert(false)
    }
    assert(pIdx >= 1)
    assert(assertApplyMonotonic(1, pIdx))
    apply(BigInt(1)) <= value
  }.holds

  /**
   * Carries the conditional branch bound from a later accepted upper value to
   * `apply(1)`.
   *
   * The conditional bridge has the shape `if (nextPrime < head * head) ...`.
   * Once a smaller wrapper proves `apply(1) <= nextPrime`, this tiny arithmetic
   * lemma exposes the bound needed by `assertApplyOneIsPrimeIfBelowHeadSq()`
   * without asking Stainless to rediscover the transitive inequality inside the
   * full cross-instance equality proof.
   */
  def assertApplyOneBelowHeadSqFromUpper(value: BigInt): Boolean = {
    require(apply(BigInt(1)) <= value)
    require(value < head.value * head.value)

    apply(BigInt(1)) < head.value * head.value
  }.holds

  /**
   * Proves `apply(1)` is prime from an already-established upper bound below
   * `head * head`.
   *
   * This is deliberately a one-call wrapper around the existing square-bound
   * primality proof. The final `nextPrime == apply(1)` lemma can call this
   * wrapper after proving `apply(1) <= nextPrime` and
   * `nextPrime < head * head`, without carrying the divisor/filter proof body
   * in the same verification condition as the cross-instance prime-search
   * facts.
   */
  def assertApplyOnePrimeFromUpperBelowHeadSq(value: BigInt): Boolean = {
    require(apply(BigInt(1)) <= value)
    require(value < head.value * head.value)

    assert(assertApplyOneBelowHeadSqFromUpper(value))
    assert(assertApplyOneIsPrimeIfBelowHeadSq())

    Prime.isPrime(apply(BigInt(1)))
  }.holds

  /**
   * Shows that the direct `AllPrimesSoFarList.nextPrime` result is accepted by
   * this V0 tail-filter generator.
   *
   * This packages the first bridge fact for the current instance: the prime
   * search result is strictly after `head`, and `assertNextPrimePassesV0Filter`
   * proves it is coprime to the active tail filters. Later wrappers can consume
   * the single `accepts(nextPrime.value)` fact instead of rebuilding the prime
   * list and filter-value connection.
   */
  def assertOwnNextPrimeAccepted(): Boolean = {
    val p = AllPrimesSoFarList.nextPrime(primes.list)

    assert(p.value > head.value)
    assert(assertNextPrimePassesV0Filter(primes))
    assert(passesFilter(p.value))

    accepts(p.value)
  }.holds

  /**
   * Proves that V0's first generated value appears no later than the direct
   * `AllPrimesSoFarList.nextPrime` result for this same prime prefix.
   *
   * This is Lemma 2 of the conditional bridge in its smallest useful form.
   * `assertOwnNextPrimeAccepted()` packages the next-prime result as a valid
   * tail-filter survivor, and `assertApplyOneLeqValue` says the first survivor
   * after `head` cannot skip past any accepted value. The result is only an
   * ordering fact; primality and equality are intentionally left to later
   * wrappers so each verification condition stays small.
   */
  def assertApplyOneAtOrBeforeOwnNextPrime(): Boolean = {
    val p = AllPrimesSoFarList.nextPrime(primes.list)

    assert(assertOwnNextPrimeAccepted())
    assert(assertApplyOneLeqValue(p.value))

    apply(BigInt(1)) <= p.value
  }.holds

  /**
   * Proves V0's first generated value is prime inside the conditional bridge
   * branch where the direct next prime is still below `head * head`.
   *
   * This avoids the global theorem "there is always a prime before `head^2`".
   * Instead, callers enter this lemma only in the branch where the direct
   * next-prime search already produced such an upper bound. The proof composes
   * the verified ordering wrapper with the single-instance square-bound
   * primality wrapper.
   */
  def assertApplyOnePrimeIfOwnNextPrimeBelowHeadSq(): Boolean = {
    val p = AllPrimesSoFarList.nextPrime(primes.list)
    require(p.value < head.value * head.value)

    assert(assertApplyOneAtOrBeforeOwnNextPrime())
    assert(assertApplyOnePrimeFromUpperBelowHeadSq(p.value))

    Prime.isPrime(apply(BigInt(1)))
  }.holds

//  /**
//   * Conditional bridge between the direct prime search and V0's first survivor.
//   *
//   * This is the equality we need without proving the global theorem that every
//   * prime prefix has a next prime before `head * head`. If the direct
//   * `AllPrimesSoFarList.nextPrime` result is below that square bound, then
//   * `apply(1)` is prime by the preceding wrapper. Since `nextPrime` also proves
//   * there are no primes in `[head + 1, nextPrime)`, `apply(1)` cannot be a
//   * smaller value in that interval. The ordering wrapper already proves
//   * `apply(1) <= nextPrime`, so equality follows.
//   */
//  def assertOwnNextPrimeEqualsApplyOneIfBeforeHeadSquared(): Boolean = {
//    val p = AllPrimesSoFarList.nextPrime(primes.list)
//
//    if (p.value < head.value * head.value) {
//      assert(assertApplyOneAtOrBeforeOwnNextPrime())
//      assert(assertApplyOnePrimeIfOwnNextPrimeBelowHeadSq())
//      assert(assertApplyOneGtHead())
//
//      val v1 = apply(BigInt(1))
//      assert(AllPrimesSoFarList.noPrimesBetween(head.value + BigInt(1), p.value))
//      if (v1 < p.value) {
//        assert(head.value + BigInt(1) <= v1)
//        assert(AllPrimesSoFarList.noPrimesBetweenExcludesValue(head.value + BigInt(1), p.value, v1))
//        assert(!Prime.isPrime(v1))
//        assert(false)
//      }
//
//      p.value == v1
//    } else {
//      true
//    }
//  }.holds

//  def assertNextPrimeEqualsApplyOneIfBeforeHeadSquared(list: SortedPrimeList): Boolean = {
//    require(list.nonEmpty)
//    require(list.size > 1)
//    require(AllPrimesSoFarList.allPrimesSoFar(list))
//
//    val primesSoFar = AllPrimesSoFarList(list)
//    assert(PrimeUtils.primeIsCoprimeWithSmallerList(list.head.value, list.tail.list))
//    val seq = SieveSequenceV0(primesSoFar)
//    val p = AllPrimesSoFarList.nextPrime(list)
//    val head = seq.head.value
//    val pVal = p.value
//
//    if (pVal < head * head) {
//      assert(pVal > head)
//
//      SortedPrimeList.assertTailDescending(list.list)
//      assert(PrimeUtils.primeIsCoprimeWithSmallerList(pVal, list.tail.list))
//      assert(seq.accepts(pVal))
//      assert(seq.assertApplyOneLeqValue(pVal))
//      assert(seq.apply(BigInt(1)) <= pVal)
//      assert(seq.apply(BigInt(1)) < head * head)
//
//      assert(seq.assertApplyOneIsPrimeIfBelowHeadSq())
//      assert(seq.assertApplyOneGtHead())
//      val v1 = seq.apply(BigInt(1))
//
//      assert(AllPrimesSoFarList.noPrimesBetween(head + BigInt(1), pVal))
//      if (v1 < pVal) {
//        assert(head + BigInt(1) <= v1)
//        AllPrimesSoFarList.noPrimesBetweenExcludesValue(head + BigInt(1), pVal, v1)
//        assert(false)
//      }
//
//      pVal == v1
//    } else {
//      true
//    }
//  }.holds
//
//  def next: SieveSequenceV0 = {
//    require(list.nonEmpty)
//    require(list.size > 1)
//    require(AllPrimesSoFarList.allPrimesSoFar(list))
//
//    val primesSoFar = AllPrimesSoFarList(list)
//    assert(PrimeUtils.primeIsCoprimeWithSmallerList(list.head.value, list.tail.list))
//    val seq = SieveSequenceV0(primesSoFar)
//    val p = AllPrimesSoFarList.nextPrime(list)
//    val head = seq.head.value
//    val pVal = p.value
//
//    if (pVal < head * head) {
//      assert(pVal > head)
//
//      SortedPrimeList.assertTailDescending(list.list)
//      assert(PrimeUtils.primeIsCoprimeWithSmallerList(pVal, list.tail.list))
//      assert(seq.accepts(pVal))
//
//      // Remaining steps to complete:
//      // 1. seq.apply(1) <= pVal (via V0 completeness — needs cross-instance)
//      // 2. seq.apply(1) < head*head (from step 1 and branch condition)
//      // 3. Prime.isPrime(seq.apply(1)) (via sqrt bound — needs cross-instance)
//      // 4. seq.apply(1) == pVal (contradiction with noPrimesBetween)
//      // Steps 1-3 require cross-instance calls to private V0 lemmas.
//      // For now, the theorem is vacuously true in both branches.
//      true
//    } else {
//      true
//    }
//  }.holds

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
  def next: SieveSequenceV0 = {
    require(primes.nextPrime.value < head.value * head.value)

    val newPrimes = primes.next

    SortedPrimeList.assertTailDescending(newPrimes.list.list)
    assert(PrimeUtils.primeIsCoprimeWithSmallerList(
      newPrimes.head.value, newPrimes.list.tail.list
    ))

    SieveSequenceV0(newPrimes)
  }
}

object SieveSequenceV0 {

}
