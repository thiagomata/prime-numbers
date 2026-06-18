package v1.seq.sieve

import stainless.annotation.extern
import stainless.collection.List
import stainless.lang.*
import v1.Calc
import v1.list.ListUtils
import v1.prime.{AllPrimesSoFarList, Prime, PrimeUtils, SortedPrimeList}

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
   * Proves the generator makes progress at every step.
   *
   * The completeness witness searches forward through indices until it reaches
   * a target accepted value. Stainless needs a decreasing measure for that
   * recursive search. This lemma supplies the progress fact: the next search
   * starts at `apply(k) + 1`, so its result is strictly greater than `apply(k)`.
   */
  private def applyStrictlyIncreases(k: BigInt): Boolean = {
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

  def next: SieveSequenceV0 = {
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
