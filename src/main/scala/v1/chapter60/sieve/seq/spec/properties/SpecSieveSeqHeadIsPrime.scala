package v1.chapter60.sieve.seq.spec.properties

import stainless.collection.List
import stainless.lang.*
import v1.chapter2.div.Calc
import v1.chapter3.list.ListUtils
import v1.chapter5.prime.*
import v1.chapter5.prime.properties.PrimeProperties
import v1.chapter60.sieve.seq.spec.SieveUtils
import v1.chapter60.sieve.seq.spec.SpecSieveSequence

object SpecSieveSeqHeadIsPrime {

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
  def assertApplyOneEqualsNextPrime(seq: SpecSieveSequence): Boolean = {
    require(seq.primes.nextPrime.value < seq.head.value * seq.head.value)

    val nextP = AllPrimesSoFarList.nextPrime(seq.primes.list)

    assert(nextP.value > seq.head.value)
    assert(Prime.isPrime(nextP.value))
    assert(AllPrimesSoFarList.noPrimesBetween(seq.head.value + BigInt(1), nextP.value))

    assert(assertApplyOneGtHead(seq))
    assert(assertApplyOneAtOrBeforeOwnNextPrime(seq))
    assert(assertApplyOnePrimeIfOwnNextPrimeBelowHeadSq(seq))

    assert(seq.apply(BigInt(1)) <= nextP.value)
    assert(Prime.isPrime(seq.apply(BigInt(1))))
    assert(seq.head.value + BigInt(1) <= seq.apply(BigInt(1)))

    if (seq.apply(BigInt(1)) < nextP.value) {
      assert(AllPrimesSoFarList.noPrimesBetweenExcludesValue(
        seq.head.value + BigInt(1), nextP.value, seq.apply(BigInt(1))
      ))
      assert(!Prime.isPrime(seq.apply(BigInt(1))))
      assert(false)
      seq.apply(BigInt(1)) == nextP.value
    } else {
      seq.apply(BigInt(1)) == nextP.value
    }
  }.holds

  /**
   * Proves `apply(1)` is prime when it lies below `head * head`.
   * If composite, its smallest prime divisor `d < head` would contradict
   * `accepts(apply(1))`. The precondition `apply(1) < head²` is not
   * universally dischargeable — tracked in `tickets/active/prove-apply1-is-prime.md`.
   */
  def assertApplyOneIsPrimeIfBelowHeadSq(seq: SpecSieveSequence): Boolean = {
    require(seq.apply(BigInt(1)) < seq.head.value * seq.head.value)

    val v1 = seq.apply(BigInt(1))
    assert(seq.applyStrictlyIncreases(0))

    if (Prime.isPrime(v1)) {
      Prime.isPrime(v1)
    } else {
      val d = PrimeProperties.assertCompositeSmallestPrimeDivisor(v1)
      assert(d < seq.head.value)
      assert(Calc.mod(v1, d) == BigInt(0))

      AllPrimesSoFarList.primeAtOrBelowHeadIsContained(d, seq.primes.list)
      assert(AllPrimesSoFarList.containsValue(d, seq.primes.list.tail))
      assert(assertFilterValuesContains(seq, d))
      assert(divisorInFilterValues(v1, d, seq.filterValues))
      assert(!SieveUtils.isCoprime(v1, seq.filterValues))
      assert(seq.passesFilter(v1))
      assert(false)
      Prime.isPrime(v1)
    }
  }.holds

  def assertApplyOneAtOrBeforeAccepted(seq: SpecSieveSequence, value: BigInt): Boolean = {
    require(value > seq.head.value)
    require(seq.accepts(value))

    assert(seq.apply(BigInt(0)) == seq.head.value)
    assert(seq.apply(BigInt(0)) < value)
    assert(seq.nextDoesNotPassAcceptedValue(BigInt(0), value))

    seq.apply(BigInt(1)) <= value
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
  def assertNextPrimePassesV0Filter(seq: SpecSieveSequence, primes: AllPrimesSoFarList): Boolean = {
    require(!primes.isEmpty)
    require(primes.size > 1)
    require(AllPrimesSoFarList.allPrimesSoFar(primes.list))

    val nextPrime = AllPrimesSoFarList.nextPrime(primes.list)
    val filterPrimes: List[Prime] = primes.list.tail.list

    assert(nextPrime.value > primes.head.value)
    SortedPrimeList.assertTailDescending(primes.list.list)
    PrimeUtils.primeIsCoprimeWithSmallerList(nextPrime.value, filterPrimes)
  }.holds

  /** Proves `apply(1) >= head + 1` — the first generated value is strictly after head. */
  private def assertApplyOneGtHead(seq: SpecSieveSequence): Boolean = {
    assert(seq.applyStrictlyIncreases(BigInt(0)))
    val h = seq.head.value
    val a1 = seq.apply(BigInt(1))
    assert(a1 > h)
    h + BigInt(1) <= a1
  }.holds

  /** Proves `apply(1) <= value` for any accepted value > head. */
  private def assertApplyOneLeqValue(seq: SpecSieveSequence, value: BigInt): Boolean = {
    require(value > seq.head.value)
    require(seq.accepts(value))

    val pIdx = seq.indexOfAccepted(value)
    assert(pIdx >= BigInt(0))
    assert(seq.apply(pIdx) == value)
    if (pIdx == 0) {
      assert(seq.apply(BigInt(0)) == seq.head.value)
      assert(false)
    }
    assert(pIdx >= 1)
    assert(seq.assertApplyMonotonic(1, pIdx))
    seq.apply(BigInt(1)) <= value
  }.holds

  private def assertFilterValuesContains(seq: SpecSieveSequence, previousPrime: BigInt): Boolean = {
    require(previousPrime >= 2)
    require(AllPrimesSoFarList.containsValue(previousPrime, seq.primes.list.tail))
    require(Calc.mod(seq.apply(BigInt(1)), previousPrime) == BigInt(0))
    decreases(seq.primes.list.tail.size)

    if (seq.primes.list.tail.isEmpty) {
      assert(false)
      true
    } else if (seq.primes.list.tail.head.value == previousPrime) {
      assert(!seq.filterValues.isEmpty)
      assert(seq.filterValues.head == previousPrime)
      listContains(previousPrime, seq.filterValues)
    } else {
      assert(AllPrimesSoFarList.containsValue(previousPrime, seq.primes.list.tail.tail))
      assert(seq.filterValues.tail == PrimeUtils.primeValues(seq.primes.list.tail.tail.list))
      assert(assertFilterValuesContainsInTail(seq, previousPrime, seq.primes.list.tail.tail, seq.filterValues.tail, seq.apply(BigInt(1))))
      listContains(previousPrime, seq.filterValues)
    }
  }.holds

  private def assertFilterValuesContainsInTail(
                                                seq: SpecSieveSequence,
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
      assert(assertFilterValuesContainsInTail(seq, d, tail.tail, tailFilterValues.tail, n))
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

  private def containsValue(d: BigInt, values: List[BigInt]): Boolean = {
    values.contains(d)
  }

  private def listContains(d: BigInt, values: List[BigInt]): Boolean = {
    containsValue(d, values)
  }

  private def assertApplyOneBelowHeadSqFromUpper(seq: SpecSieveSequence, value: BigInt): Boolean = {
    require(seq.apply(BigInt(1)) <= value)
    require(value < seq.head.value * seq.head.value)

    seq.apply(BigInt(1)) < seq.head.value * seq.head.value
  }.holds

  private def assertApplyOnePrimeFromUpperBelowHeadSq(seq: SpecSieveSequence, value: BigInt): Boolean = {
    require(seq.apply(BigInt(1)) <= value)
    require(value < seq.head.value * seq.head.value)

    assert(assertApplyOneBelowHeadSqFromUpper(seq, value))
    assert(assertApplyOneIsPrimeIfBelowHeadSq(seq))

    Prime.isPrime(seq.apply(BigInt(1)))
  }.holds

  private def assertOwnNextPrimeAccepted(seq: SpecSieveSequence): Boolean = {
    val p = AllPrimesSoFarList.nextPrime(seq.primes.list)

    assert(p.value > seq.head.value)
    assert(assertNextPrimePassesV0Filter(seq, seq.primes))
    assert(seq.passesFilter(p.value))

    seq.accepts(p.value)
  }.holds

  private def assertApplyOneAtOrBeforeOwnNextPrime(seq: SpecSieveSequence): Boolean = {
    val p = AllPrimesSoFarList.nextPrime(seq.primes.list)

    assert(assertOwnNextPrimeAccepted(seq))
    assert(assertApplyOneLeqValue(seq, p.value))

    seq.apply(BigInt(1)) <= p.value
  }.holds

  private def assertApplyOnePrimeIfOwnNextPrimeBelowHeadSq(seq: SpecSieveSequence): Boolean = {
    val p = AllPrimesSoFarList.nextPrime(seq.primes.list)
    require(p.value < seq.head.value * seq.head.value)

    assert(assertApplyOneAtOrBeforeOwnNextPrime(seq))
    assert(assertApplyOnePrimeFromUpperBelowHeadSq(seq, p.value))

    Prime.isPrime(seq.apply(BigInt(1)))
  }.holds
}
