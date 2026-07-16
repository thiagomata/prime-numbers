package v1.chapter60.sieve.seq.spec.properties

import stainless.collection.List
import stainless.lang.*
import v1.chapter2.div.Calc
import v1.chapter3.list.ListUtils
import v1.chapter5.prime.*
import v1.chapter5.prime.properties.PrimeProperties
import v1.chapter6.seq.sieve.SieveUtils
import v1.chapter60.sieve.seq.spec.SpecSieveSequence

final case class SpecSieveSeqHeadIsPrime(seq: SpecSieveSequence) {
  import seq.*

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
   * (`SpecSieveSequence`). It supplies the `accepts` fact needed by later lemmas
   * such as `assertApplyOneAtOrBeforeAccepted` and the conditional equality.
   */
   def assertNextPrimePassesV0Filter(primes: AllPrimesSoFarList): Boolean = {
    require(!primes.isEmpty)
    require(primes.size > 1)
    require(AllPrimesSoFarList.allPrimesSoFar(primes.list))

    val nextPrime = AllPrimesSoFarList.nextPrime(primes.list)
    val filterPrimes: List[Prime] = primes.list.tail.list

    assert(nextPrime.value > primes.head.value)
    SortedPrimeList.assertTailDescending(primes.list.list)
    PrimeUtils.primeIsCoprimeWithSmallerList(nextPrime.value, filterPrimes)
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
  private def assertFilterValuesContains(previousPrime: BigInt): Boolean = {
    require(previousPrime >= 2)
    require(AllPrimesSoFarList.containsValue(previousPrime, primes.list.tail))
    require(Calc.mod(apply(BigInt(1)), previousPrime) == BigInt(0))
    decreases(primes.list.tail.size)

    if (primes.list.tail.isEmpty) {
      assert(false)
      true
    } else if (primes.list.tail.head.value == previousPrime) {
      assert(!filterValues.isEmpty)
      assert(filterValues.head == previousPrime)
      listContains(previousPrime, filterValues)
    } else {
      assert(AllPrimesSoFarList.containsValue(previousPrime, primes.list.tail.tail))
      assert(filterValues.tail == PrimeUtils.primeValues(primes.list.tail.tail.list))
      assert(assertFilterValuesContainsInTail(previousPrime, primes.list.tail.tail, filterValues.tail, apply(BigInt(1))))
      listContains(previousPrime, filterValues)
    }
  }.holds

  /**
   * Tail-recursive helper for `assertFilterValuesContains`: walks the
   * `tail` prime list to find `d` among the associated `tailFilterValues`.
   */
  private def assertFilterValuesContainsInTail(
                                                d: BigInt,
                                                tail: SortedPrimeList,
                                                tailFilterValues: List[BigInt],
                                                n: BigInt
                                              ): Boolean = {
    require(d >= 2)
    require(tail.nonEmpty)
    require(AllPrimesSoFarList.containsValue(d, tail))
    require(tailFilterValues == PrimeUtils.primeValues(tail.list))
    require(Calc.mod(n, d) == BigInt(0))
    decreases(tail.size)

    if (tail.head.value == d) {
      assert(!tailFilterValues.isEmpty)
      assert(tailFilterValues.head == d)
      listContains(d, tailFilterValues)
    } else {
      assert(AllPrimesSoFarList.containsValue(d, tail.tail))
      assert(tailFilterValues.tail == PrimeUtils.primeValues(tail.tail.list))
      assert(assertFilterValuesContainsInTail(d, tail.tail, tailFilterValues.tail, n))
      listContains(d, tailFilterValues)
    }
  }.holds

  /**
   * If `d` is in `values` and `mod(n, d) == 0`, then `n` is not coprime with `values`.
   * Used to prove that a composite `apply(1)` with a divisor in `filterValues`
   * would violate `accepts(apply(1))`.
   */
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

  /**
   * Canonical value-level membership for local `List[BigInt]` filter values.
   *
   * Keep this as a thin alias to `values.contains`. Do not restore a local
   * recursive `listContains`: Chapter 5 timed out when different objects had
   * proof facts about different recursive membership predicates. These lists
   * are raw `BigInt` filter values, so their canonical predicate is Scala's
   * list membership; prime-list membership should use
   * `AllPrimesSoFarList.containsValue`.
   */
  private def containsValue(d: BigInt, values: List[BigInt]): Boolean = {
    values.contains(d)
  }

  /**
   * Compatibility alias for older local proofs.
   *
   * This method must remain an alias to `containsValue`, not another recursive
   * implementation. The name is intentionally preserved for proof readability,
   * while the verifier sees only one local value-membership predicate.
   */
  private def listContains(d: BigInt, values: List[BigInt]): Boolean = {
    containsValue(d, values)
  }

  /**
   * Proves `apply(1)` is prime when it lies below `head * head`.
   * If composite, its smallest prime divisor `d < head` would contradict
   * `accepts(apply(1))`. The precondition `apply(1) < head²` is not
   * universally dischargeable — tracked in `tickets/active/prove-apply1-is-prime.md`.
   */
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
      assert(AllPrimesSoFarList.containsValue(d, primes.list.tail))
      assert(assertFilterValuesContains(d))
      assert(divisorInFilterValues(v1, d, filterValues))
      assert(!SieveUtils.isCoprime(v1, filterValues))
      assert(passesFilter(v1))
      assert(false)
      Prime.isPrime(v1)
    }
  }.holds

  /** Proves `apply(1) >= head + 1` — the first generated value is strictly after head. */
  private def assertApplyOneGtHead(): Boolean = {
    assert(applyStrictlyIncreases(BigInt(0)))
    val h = head.value
    val a1 = apply(BigInt(1))
    assert(a1 > h)
    h + BigInt(1) <= a1
  }.holds

  /** Proves `apply(1) <= value` for any accepted value > head. */
  private def assertApplyOneLeqValue(value: BigInt): Boolean = {
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
  private def assertApplyOneBelowHeadSqFromUpper(value: BigInt): Boolean = {
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
  private def assertApplyOnePrimeFromUpperBelowHeadSq(value: BigInt): Boolean = {
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
  private def assertOwnNextPrimeAccepted(): Boolean = {
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
  private def assertApplyOneAtOrBeforeOwnNextPrime(): Boolean = {
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
  private def assertApplyOnePrimeIfOwnNextPrimeBelowHeadSq(): Boolean = {
    val p = AllPrimesSoFarList.nextPrime(primes.list)
    require(p.value < head.value * head.value)

    assert(assertApplyOneAtOrBeforeOwnNextPrime())
    assert(assertApplyOnePrimeFromUpperBelowHeadSq(p.value))

    Prime.isPrime(apply(BigInt(1)))
  }.holds

  /**
   * Proves V0's first generated value equals the next prime in the prefix.
   *
   * Under the next() precondition (nextPrime < head * head), the first generated
   * value must be exactly the next prime. The proof uses:
   * 1. assertApplyOneGtHead: head + 1 <= apply(1)
   * 2. assertApplyOneAtOrBeforeOwnNextPrime: apply(1) <= nextPrime
   * 3. assertApplyOnePrimeIfOwnNextPrimeBelowHeadSq: Prime.isPrime(apply(1))
   * 4. AllPrimesSoFarList.nextPrime's postcondition: noPrimesBetween(head+1, nextPrime)
   * Since apply(1) is prime and > head, no prime exists in (head, nextPrime),
   * so apply(1) must equal nextPrime.
   */
  def assertApplyOneEqualsNextPrime(): Boolean = {
    require(primes.nextPrime.value < head.value * head.value)

    val nextP = AllPrimesSoFarList.nextPrime(primes.list)

    assert(nextP.value > head.value)
    assert(Prime.isPrime(nextP.value))
    assert(AllPrimesSoFarList.noPrimesBetween(head.value + BigInt(1), nextP.value))

    assert(assertApplyOneGtHead())
    assert(assertApplyOneAtOrBeforeOwnNextPrime())
    assert(assertApplyOnePrimeIfOwnNextPrimeBelowHeadSq())

    assert(apply(BigInt(1)) <= nextP.value)
    assert(Prime.isPrime(apply(BigInt(1))))
    assert(head.value + BigInt(1) <= apply(BigInt(1)))

    if (apply(BigInt(1)) < nextP.value) {
      assert(AllPrimesSoFarList.noPrimesBetweenExcludesValue(
        head.value + BigInt(1), nextP.value, apply(BigInt(1))
      ))
      assert(!Prime.isPrime(apply(BigInt(1))))
      assert(false)
      apply(BigInt(1)) == nextP.value
    } else {
      apply(BigInt(1)) == nextP.value
    }
  }.holds
}
