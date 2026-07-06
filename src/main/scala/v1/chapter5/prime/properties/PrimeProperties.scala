package v1.chapter5.prime.properties

import stainless.collection.List
import stainless.lang.{BigInt, decreases}
import stainless.lang.BooleanDecorations
import v1.chapter2.div.Calc
import v1.chapter2.div.properties.AdditionAndMultiplication.ATimesBSameMod
import v1.chapter2.div.properties.{AdditionAndMultiplication, ModOperations, ModSmallDividend}
import v1.chapter3.list.ListUtils
import v1.chapter5.prime.{Prime, PrimeUtils, SortedPrimeList, CoprimeUtils, PrimeListUtils}

object PrimeProperties {

  /**
   * Find the smallest divisor of n in the range [from, n).
   *
   * Walks upward from `from` checking each integer. If it finds one that
   * divides n evenly, that's the answer. If it reaches n without finding
   * any divisor, it returns n — meaning n itself is prime (since no smaller
   * number divides it).
   *
   * This is the computational core of the Euclid proof:
   * we need to find a prime divisor of primorial + 1.
   *
   * findSmallestDivisor(n, from) = smallest d ∈ [from, n) such that mod(n, d) == 0,
   *                                or n if no such d exists.
   *
   * @param n    BigInt the number to factor (must be > 1)
   * @param from BigInt where to start looking (must be >= 2, <= n)
   * @return BigInt the smallest divisor, or n if n is prime
   */
  private def findSmallestDivisor(n: BigInt, from: BigInt): BigInt = {
    require(n > 1 && from >= 2 && from <= n)
    decreases(n - from)
    if (from >= n) n
    else if (Calc.mod(n, from) == BigInt(0)) from
    else findSmallestDivisor(n, from + 1)
  }.ensuring(res => res >= from && res <= n)

  /**
   * Lemma: what findSmallestDivisor returns matches the conditions.
   *
   * If it returns n, there was no divisor. If it returns something smaller,
   * that something actually divides n (mod is zero). This is the bridge
   * between what the function does and what we can prove about the result.
   *
   * (findSmallestDivisor(n, from) == n) ∨
   * (mod(n, findSmallestDivisor(n, from)) == 0)
   *
   * @param n    BigInt the number being factored
   * @param from BigInt the starting point of the search
   * @return Boolean true if the equivalence holds
   */
  private def findSmallestDivisorEquiv(n: BigInt, from: BigInt): Boolean = {
    require(n > 1 && from >= 2 && from <= n)
    decreases(n - from)
    if (from >= n) {
      findSmallestDivisor(n, from) == n
    } else if (Calc.mod(n, from) == BigInt(0)) {
      Calc.mod(n, from) == BigInt(0) && findSmallestDivisor(n, from) == from
    } else {
      findSmallestDivisorEquiv(n, from + 1)
    }
  }.holds

  /**
   * Lemma: if findSmallestDivisor returned n, then n really has no divisor.
   *
   * This is the key lemma that lets us say "n is prime" when the function
   * returns n. It proves that the absence of a found divisor in the search
   * really means there is none anywhere in [from, n).
   *
   * findSmallestDivisor(n, from) == n ⇒ noDivisorInRange(n, from, n)
   *
   * @param n    BigInt the number being checked
   * @param from BigInt the lower bound of the search range
   * @return Boolean true if the property holds
   */
  private def findSmallestDivisorIsNImpliesNoDivisorInRange(n: BigInt, from: BigInt): Boolean = {
    require(n > 1 && from >= 2 && from <= n)
    require(findSmallestDivisor(n, from) == n)
    decreases(n - from)
    if (from >= n) {
      Prime.noDivisorInRange(n, from, n)
    } else if (Calc.mod(n, from) == BigInt(0)) {
      findSmallestDivisorEquiv(n, from)
      false
    } else {
      findSmallestDivisorIsNImpliesNoDivisorInRange(n, from + 1)
      Prime.noDivisorInRange(n, from, n)
    }
  }.holds

  /**
   * Lemma: dividing a evenly means you can reconstruct the original.
   *
   * If b divides a (remainder zero), then the quotient times b gives a back.
   * This is the fundamental property of exact division.
   *
   * mod(a, b) == 0 ⇒ div(a, b) * b == a
   *
   * @param a BigInt the dividend
   * @param b BigInt the divisor (must be non-zero)
   * @return Boolean true if the property holds
   */
  private def assertModZeroImpliesDivTimesBEqualsA(a: BigInt, b: BigInt): Boolean = {
    require(b != 0)
    require(Calc.mod(a, b) == BigInt(0))
    Calc.div(a, b) * b == a
  }.holds

  /**
   * Lemma: if from divides n, findSmallestDivisor starting at from returns from.
   *
   * Since we know `from` is a divisor, and the search starts at `from`,
   * it will find it immediately (or an even smaller one if one existed
   * before `from`, but we're starting at `from` so the smallest in [from, n)
   * is `from` itself).
   *
   * mod(n, from) == 0 ⇒ findSmallestDivisor(n, from) == from
   *
   * @param n    BigInt the number being factored (n > 1)
   * @param from BigInt a known divisor of n (from >= 2, from < n)
   * @return Boolean true if the property holds
   */
  private def findSmallestDivisorReturnsFromIfZero(n: BigInt, from: BigInt): Boolean = {
    require(n > 1 && from >= 2 && from < n)
    require(Calc.mod(n, from) == BigInt(0))
    findSmallestDivisor(n, from) == from
  }.holds

   /**
    * Lemma: if findSmallestDivisor(n, 2) == d (and d < n), then d divides n.
    *
    * This is the reverse direction of findSmallestDivisorReturnsFromIfZero:
    * from the function result back to divisibility. By definition of the
    * function, it only returns a value d < n when mod(n, d) == 0.
    *
    * findSmallestDivisor(n, 2) == d ∧ d < n ⇒ mod(n, d) == 0
    *
    * @param n BigInt the original number (n > 1)
    * @param d BigInt the smallest divisor found (d >= 2, d < n)
    * @return Boolean true if the property holds
    */
  private def findSmallestDivisorResultModZeroFrom(n: BigInt, from: BigInt, d: BigInt): Boolean = {
    require(n > 1 && from >= 2 && from <= n)
    require(findSmallestDivisor(n, from) == d)
    require(d < n)
    decreases(n - from)
    if (from >= n) {
      true
    } else if (Calc.mod(n, from) == BigInt(0)) {
      Calc.mod(n, d) == BigInt(0)
    } else {
      findSmallestDivisorResultModZeroFrom(n, from + 1, d)
      Calc.mod(n, d) == BigInt(0)
    }
  }.holds

  private def findSmallestDivisorResultModZero(n: BigInt, d: BigInt): Boolean = {
    require(n > 1 && d >= 2 && d < n)
    require(findSmallestDivisor(n, 2) == d)
    findSmallestDivisorResultModZeroFrom(n, 2, d)
    Calc.mod(n, d) == BigInt(0)
  }.holds

  /**
   * Helper lemma: the smallest divisor d of n has no divisor in [from, d).
   *
   * By contradiction: if d had a divisor e in that range, transitivity would
   * make e a divisor of n too, and it would be smaller than d — contradicting
   * that d is the smallest. This proves d is prime (no proper divisor exists).
   *
   * findSmallestDivisor(n, 2) == d ∧ mod(n, d) == 0 ⇒ noDivisorInRange(d, from, d)
   *
   * @param n    BigInt the original number
   * @param d    BigInt the smallest divisor of n
   * @param from BigInt the lower bound of the search range in d
   * @return Boolean true if the property holds
   */
  private def assertSmallestDivisorIsPrimeDirect(n: BigInt, d: BigInt, from: BigInt): Boolean = {
    require(n > 1 && d >= 2 && from >= 2 && from <= d && d < n)
    require(findSmallestDivisor(n, from) == d)
    require(Calc.mod(n, d) == BigInt(0))
    decreases(d - from)
    if (from >= d) {
      true
    } else if (Calc.mod(d, from) == BigInt(0)) {
      assertModZeroImpliesDivTimesBEqualsA(n, d)
      assertModZeroImpliesDivTimesBEqualsA(d, from)
      val quotientN = Calc.div(n, d)
      val quotientD = Calc.div(d, from)
      assert(quotientN * d == n)
      assert(quotientD * from == d)
      assert(quotientN * quotientD * from == n)
      assert(ModSmallDividend.modSmallDividend(BigInt(0), from))
      AdditionAndMultiplication.ATimesBSameMod(BigInt(0), from, quotientN * quotientD)
      findSmallestDivisorReturnsFromIfZero(n, from)
      false
    } else if (Calc.mod(n, from) == BigInt(0)) {
      findSmallestDivisorReturnsFromIfZero(n, from)
      false
    } else {
      Prime.noDivisorInRange(d, from, from)
      assertSmallestDivisorIsPrimeDirect(n, d, from + 1)
      Prime.noDivisorInRange(d, from, d)
    }
  }.holds

  /**
   * Lemma: the smallest divisor of n (greater than 1) is prime.
   *
   * This is the crucial number-theoretic fact: any integer > 1 has a prime
   * divisor. If d is the smallest divisor of n and d > 1, then d must be
   * prime — because any proper divisor of d would also divide n and be
   * smaller than d, contradicting minimality.
   *
   * findSmallestDivisor(n, 2) == d ⇒ isPrime(d)
   *
   * @param n BigInt the original number (n > 1)
   * @param d BigInt the smallest divisor found (d >= 2, d < n)
   * @return Boolean true if d is prime
   */
  private def assertSmallestDivisorIsPrime(n: BigInt, d: BigInt): Boolean = {
    require(n > 1 && d >= 2 && d < n)
    require(findSmallestDivisor(n, 2) == d)
    findSmallestDivisorResultModZero(n, d)
    assertSmallestDivisorIsPrimeDirect(n, d, 2)
    d > 1 && Prime.noDivisorInRange(d, 2, d)
  }.holds

  /**
   * Lemma: primorial + 1 is NOT divisible by any prime in the list.
   *
   * This is the key number-theoretic fact for Euclid's theorem.
   * Since the primorial is divisible by every prime p in the list,
   * adding 1 changes the remainder from 0 to 1, which is never 0
   * (because p > 1, so 1 can't be a multiple of p).
   *
   * Equivalently: no prime in the list divides primorial + 1,
   * so any prime divisor of primorial + 1 is a NEW prime.
   *
   * For every p in primes: mod(primorial(primes) + 1, p.value) != 0
   *
   * @param primes List[Prime] a list of primes
   * @return Boolean true if no prime divides primorial + 1
   */
  def primorialPlusOneModAny(primes: List[Prime]): Boolean = {
    decreases(primes.size)
    primorialPlusOneTailLoop(List.empty, primes)
  }.holds

  /**
   * Helper: the inductive engine behind primorialPlusOneModAny.
   *
   * At each step, the combined primorial of (previous ++ current) is
   * previousPrimorial * p * tailPrimorial. We prove:
   * 1. mod(combinedPrimorial, p) == 0 (p divides the primorial, same as checkPrimorialModZeroTailLoop)
   * 2. mod(combinedPrimorial + 1, p) == mod(1, p)  (by modZeroPlusC: adding 1 shifts remainder by 1)
   * 3. mod(1, p) == 1 (since p > 1, 1 is its own remainder — modSmallDividend)
   * 4. Therefore mod(primorial + 1, p) != 0 for every p
   *
   * @param previous List[Prime] primes already processed
   * @param current  List[Prime] primes still to check
   * @return Boolean true if no prime in current divides primorial(previous ++ current) + 1
   */
  private def primorialPlusOneTailLoop(previous: List[Prime], current: List[Prime]): Boolean = {
    decreases(current.size)
    if (current.isEmpty) true
    else {
      val p = current.head.value
      val tailPrimorial = PrimeUtils.primorial(current.tail)
      val previousPrimorial = PrimeUtils.primorial(previous)
      val primorialAll = previousPrimorial * p * tailPrimorial
      // Prove: mod(primorialAll, p) == 0 (same proof as checkPrimorialModZeroTailLoop)
      assert(ModSmallDividend.modSmallDividend(BigInt(0), p))
      AdditionAndMultiplication.ATimesBSameMod(BigInt(0), p, previousPrimorial * tailPrimorial)
      assert(Calc.mod(primorialAll, p) == BigInt(0))
      // Prove: mod(primorialAll + 1, p) == mod(1, p)
      ModOperations.modZeroPlusC(primorialAll, p, BigInt(1))
      // Prove: mod(1, p) == 1 (since p > 1)
      assert(ModSmallDividend.modSmallDividend(BigInt(1), p))
      assert(Calc.mod(primorialAll + 1, p) != BigInt(0))
      Calc.mod(primorialAll + 1, p) != BigInt(0) &&
        primorialPlusOneTailLoop(previous :+ current.head, current.tail)
    }
  }.holds
  /**
   * Construct a new Prime from Euclid's construction.
   *
   * Given a non-empty list of primes, compute n = primorial(primes) + 1,
   * then find its smallest divisor d. If no divisor exists (d == n), then
   * n itself is prime. Otherwise d is a prime divisor of n. Either way,
   * the result is a prime that is NOT in the original list.
   *
   * primorial(primes) + 1 has a prime divisor not in primes
   *
   * @param primes List[Prime] a non-empty list of primes
   * @return Prime a new prime not in the original list
   */
  def newPrimeFromEuclid(primes: List[Prime]): Prime = {
    require(primes.nonEmpty)
    require(primorialPlusOneModAny(primes))

    PrimeUtils.primorialPositive(primes)
    val n = PrimeUtils.primorial(primes) + 1
    val d = findSmallestDivisor(n, 2)

    if (d == n) {
      findSmallestDivisorIsNImpliesNoDivisorInRange(n, 2)
      Prime(n)
    } else {
      assertSmallestDivisorIsPrime(n, d)
      findSmallestDivisorResultModZero(n, d)
      Prime(d)
    }
  }

  /**
   * Lemma: the Euclid-constructed prime value is not present in the input list.
   *
   * `newPrimeFromEuclid(primes)` returns a prime that is NOT in `primes`.
   * This lemma makes that non-membership fact available as a cached `.holds`
   * result, so callers can use it as the missing link in the `nextPrime`
   * construction: they know the upper bound candidate does not collide with
   * any already-stored prime.
   *
   * For the full proof chain, combine with `primeAtOrBelowHeadIsContained`
   * from `AllPrimesSoFarList` to derive `upperPrime.value > head.value`.
   */
  def newPrimeNotInList(primes: List[Prime]): Boolean = {
    require(primes.nonEmpty)
    require(primorialPlusOneModAny(primes))

    PrimeUtils.primorialPositive(primes)
    val p = newPrimeFromEuclid(primes)
    euclidTheorem(primes)

    /*
     * Re-derive d to link euclidTheorem's internal d with p.value.
     * Both newPrimeFromEuclid and euclidTheorem compute d via
     * findSmallestDivisor(n, 2) where n = primorial + 1, so
     * p.value == d and euclidTheorem proves valueNotMatchesAny(primes, d)
     * which is the same as valueNotMatchesAny(primes, p.value).
     */
    val n = PrimeUtils.primorial(primes) + 1
    val d = findSmallestDivisor(n, 2)

    valueNotMatchesAny(primes, p.value)
  }.holds

  /**
   * Bridge: `valueNotMatchesAny` (on `List[Prime]`) implies `!contains` (on `SortedPrimeList`).
   *
   * Since both predicates recurse through the same sequence of prime values in the
   * same order, this lemma proves the equivalence by structural induction.
   * The base case (empty list) is straightforward. In the recursive case,
   * `valueNotMatchesAny` gives `head.value != d`, so `contains` cannot stop at the
   * head and must recurse to the tail, where the induction hypothesis applies.
   */
  def notContainsFromValueNotMatchesAny(
    primes: List[Prime],
    sortedList: SortedPrimeList,
    d: BigInt
  ): Boolean = {
    require(sortedList.list == primes)
    require(valueNotMatchesAny(primes, d))
    decreases(primes.size)

    if (primes.isEmpty) {
      !PrimeListUtils.contains(d, sortedList)
    } else {
      assert(primes.head.value != d)
      assert(notContainsFromValueNotMatchesAny(primes.tail, sortedList.tail, d))
      assert(!PrimeListUtils.contains(d, sortedList.tail))
      !PrimeListUtils.contains(d, sortedList)
    }
  }.holds

  /**
   * Lemma: the Euclid-constructed prime is strictly greater than the list head.
   *
   * `newPrimeFromEuclid(primes)` returns a prime value `d` that is NOT contained
   * in `primes` (proved by `newPrimeNotInList` and the bridge lemma). Meanwhile,
   * `primeAtOrBelowHeadIsContained` says that any prime at or below `head.value`
   * IS contained in a complete `allPrimesSoFar` list. By contradiction, `d` must
   * be above `head.value`.
   *
   * This is the critical inequality that makes `searchNextPrimeUpTo` callable
   * with `current = head.value + 1` and `upper = newPrimeFromEuclid(...)`.
   */
  def euclidPrimeGreaterThanHead(sortedList: SortedPrimeList): Boolean = {
    require(sortedList.nonEmpty)
    require(PrimeListUtils.allPrimesSoFar(sortedList))

    val primes = sortedList.list
    val upperPrime = newPrimeFromEuclid(primes)
    val d = upperPrime.value

    newPrimeNotInList(primes)
    assert(notContainsFromValueNotMatchesAny(primes, sortedList, d))

    if (d <= sortedList.head.value) {
      // By the complete-prefix invariant, any prime at or below head
      // must already be contained — contradicting the Euclid non-membership.
      PrimeListUtils.primeAtOrBelowHeadIsContained(d, sortedList)
    }

    d > sortedList.head.value
  }.holds

  /**
   * Helper predicate to express that a value does not match any prime value in the list.
   */
  private def valueNotMatchesAny(primes: List[Prime], v: BigInt): Boolean = {
    decreases(primes.size)
    if (primes.isEmpty) true
    else primes.head.value != v && valueNotMatchesAny(primes.tail, v)
  }

  private def euclidTailLoop(
    primes: List[Prime],
    v: BigInt,
    n: BigInt,
    primorialSoFar: BigInt
  ): Boolean = {
    require(v > 1)
    require(n == primorialSoFar * PrimeUtils.primorial(primes) + BigInt(1))
    require(Calc.mod(n, v) == BigInt(0))
    decreases(primes.size)

    if (primes.isEmpty) true
    else {
      val p = primes.head.value

      PrimeUtils.primorialUnfold(primes)
      val k = primorialSoFar * PrimeUtils.primorial(primes.tail)
      assert(n == p * k + BigInt(1))

      assert(ModSmallDividend.modSmallDividend(BigInt(0), p))
      AdditionAndMultiplication.ATimesBSameMod(BigInt(0), p, k)
      assert(Calc.mod(p * k, p) == BigInt(0))
      ModOperations.modZeroPlusC(p * k, p, BigInt(1))
      assert(ModSmallDividend.modSmallDividend(BigInt(1), p))
      assert(Calc.mod(n, p) != BigInt(0))

      assert(p != v)

      p != v && euclidTailLoop(primes.tail, v, n, primorialSoFar * p)
    }
  }.ensuring(res => res && valueNotMatchesAny(primes, v))

  def euclidTheorem(primes: List[Prime]): Boolean = {
    require(primes.nonEmpty)

    primorialPlusOneModAny(primes)
    PrimeUtils.primorialPositive(primes)
    val n = PrimeUtils.primorial(primes) + 1
    val d = findSmallestDivisor(n, 2)

    if (d == n) {
      findSmallestDivisorIsNImpliesNoDivisorInRange(n, 2)
      assert(ModSmallDividend.modSmallDividend(BigInt(0), n))
      AdditionAndMultiplication.ATimesBSameMod(BigInt(0), n, BigInt(1))
      assert(Calc.mod(n, n) == BigInt(0))
      assert(euclidTailLoop(primes, n, n, BigInt(1)))
      valueNotMatchesAny(primes, n)
    } else {
      assertSmallestDivisorIsPrime(n, d)
      findSmallestDivisorResultModZero(n, d)
      assert(euclidTailLoop(primes, d, n, BigInt(1)))
      valueNotMatchesAny(primes, d)
    }
  }.holds

  def assertNoDivisorInRangeFromHelper(
    n: BigInt,
    primes: List[BigInt],
    from: BigInt,
    to: BigInt
  ): Boolean = {
    require(n > 1)
    require(from >= 2)
    require(to >= from)
    require(ListUtils.checkAllPositive(primes))
    require(CoprimeUtils.isCoprime(n, primes))
    require(CoprimeUtils.assertAllNotCoprimeInRange(to, from, primes))
    decreases(to - from)
    if (from >= to) {
      Prime.noDivisorInRange(n, from, to)
    } else {
      assert(CoprimeUtils.hasPrimeFactorInList(from, primes))
      assert(CoprimeUtils.assertHasPrimeFactorImpliesNotCoprime(from, primes))
      assert(CoprimeUtils.assertNoDivisorByFactorList(n, from, primes))
      assert(assertNoDivisorInRangeFromHelper(n, primes, from + 1, to))
      Prime.noDivisorInRange(n, from, to)
    }
  }.holds

  def assertHeadIsPrime(head: BigInt, primesTail: List[BigInt]): Boolean = {
    require(head > 1)
    require(ListUtils.checkAllPositive(primesTail))
    require(CoprimeUtils.isCoprime(head, primesTail))
    require(CoprimeUtils.assertAllNotCoprimeInRange(head, 2, primesTail))
    assertNoDivisorInRangeFromHelper(head, primesTail, 2, head)
    Prime.isPrime(head)
  }.holds

//  /**
//   * Proves that `findSmallestDivisor` finds a divisor at or before any known divisor.
//   *
//   * If `q` is a divisor of `n` and `q >= from`, then
//   * `findSmallestDivisor(n, from) <= q`. The search walks upward from `from`;
//   * when it reaches `q` it finds it.
//   */
  private def assertFindSmallestDivisorAtMost(
    n: BigInt,
    from: BigInt,
    q: BigInt
  ): Boolean = {
    require(n > 1 && from >= 2 && from <= n)
    require(q >= from && q < n)
    require(Calc.mod(n, q) == BigInt(0))
    decreases(n - from)

    if (Calc.mod(n, from) == BigInt(0)) {
      findSmallestDivisorReturnsFromIfZero(n, from)
      findSmallestDivisor(n, from) <= q
    } else {
      assert(from < n)
      assert(findSmallestDivisor(n, from) == findSmallestDivisor(n, from + 1))
      assertFindSmallestDivisorAtMost(n, from + 1, q)
      findSmallestDivisor(n, from) <= q
    }
  }.holds

  private def assertCompositeHasDivisorStrictlyBelowN(n: BigInt): Boolean = {
    require(n > 1)
    require(!Prime.isPrime(n))

    val d = findSmallestDivisor(n, 2)

    if (d < n) {
      findSmallestDivisorResultModZero(n, d)
      assert(Calc.mod(n, d) == BigInt(0))
      true
    } else {
      assert(d == n)
      findSmallestDivisorIsNImpliesNoDivisorInRange(n, 2)
      assert(Prime.isPrime(n))
      assert(false)
      true
    }
  }.holds

  def assertSmallestDivisorAtMostSqrt(n: BigInt): Boolean = {
    require(n > 1)
    require(!Prime.isPrime(n))

    assertCompositeHasDivisorStrictlyBelowN(n)

    val d = findSmallestDivisor(n, 2)
    assert(d < n)
    findSmallestDivisorResultModZero(n, d)
    assert(Calc.mod(n, d) == BigInt(0))

    assertModZeroImpliesDivTimesBEqualsA(n, d)
    val q = Calc.div(n, d)
    assert(q * d == n)

    AdditionAndMultiplication.APlusMultipleTimesBSameMod(BigInt(0), q, d)
    assert(Calc.mod(q * d, q) == BigInt(0))
    assert(Calc.mod(n, q) == BigInt(0))

    if (q < d) {
      assertFindSmallestDivisorAtMost(n, 2, q)
      assert(findSmallestDivisor(n, 2) <= q)
      assert(d <= q)
      assert(false)
      d * d <= n
    } else {
      assert(q >= d)
      assert(d * d <= d * q)
      assert(d * q == n)
      d * d <= n
    }
  }.holds

  private def assertDivisibleByFactorListNotCoprime(
    n: BigInt,
    d: BigInt,
    primes: List[BigInt]
  ): Boolean = {
    require(n > 1 && d >= 2)
    require(ListUtils.checkAllPositive(primes))
    require(Calc.mod(n, d) == BigInt(0))
    require(!CoprimeUtils.isCoprime(d, primes))

    if (CoprimeUtils.isCoprime(n, primes)) {
      CoprimeUtils.assertNoDivisorByFactorList(n, d, primes)
      assert(Calc.mod(n, d) != BigInt(0))
      assert(false)
    }

    !CoprimeUtils.isCoprime(n, primes)
  }.holds

  private def assertDivisorBelowHead(d: BigInt, head: BigInt): Boolean = {
    require(d >= 2)
    require(head >= 2)
    require(d * d < head * head)

    if (d >= head) {
      assert(head >= 0)
      assert(d >= head)
      assert(d * d >= head * d)
      assert(head * d >= head * head)
      assert(d * d >= head * head)
      assert(false)
    }
    d < head
  }.holds

  /**
   * Returns the smallest divisor of a composite `n` with d < n, prime, and d*d <= n.
   */
  def assertCompositeSmallestPrimeDivisor(n: BigInt): BigInt = {
    require(n > 1)
    require(!Prime.isPrime(n))

    assertSmallestDivisorAtMostSqrt(n)
    val d = findSmallestDivisor(n, 2)
    assertSmallestDivisorIsPrime(n, d)
    assert(d < n)
    assert(d * d <= n)
    d
}.ensuring(res => res >= 2 && res < n && Prime.isPrime(res) && res * res <= n)
}
//
//  /**
//   * Proves that `findSmallestDivisor` of a composite `n` satisfies `d * d <= n`.
//   *
//   * Let `d` be the smallest divisor of `n` and `q = n / d`. Both `d` and `q`
//   * divide `n`. By minimality of `d`, `q >= d`. Therefore `d * d <= n`.
//   */
//  def assertSmallestDivisorAtMostSqrt(n: BigInt): Boolean = {
//    require(n > 1)
//    require(!Prime.isPrime(n))
//
//    assertCompositeHasDivisorStrictlyBelowN(n)
//
//    val d = findSmallestDivisor(n, 2)
//    assert(d < n)
//    findSmallestDivisorResultModZero(n, d)
//    assert(Calc.mod(n, d) == BigInt(0))
//
//    assertModZeroImpliesDivTimesBEqualsA(n, d)
//    val q = Calc.div(n, d)
//    assert(q * d == n)
//
//    AdditionAndMultiplication.APlusMultipleTimesBSameMod(BigInt(0), q, d)
//    assert(Calc.mod(q * d, q) == BigInt(0))
//    assert(Calc.mod(n, q) == BigInt(0))
//
//    if (q < d) {
//      assertFindSmallestDivisorAtMost(n, 2, q)
//      assert(findSmallestDivisor(n, 2) <= q)
//      assert(d <= q)
//      assert(false)
//      d * d <= n
//    } else {
//      assert(q >= d)
//      assert(d * d <= d * q)
//      assert(d * q == n)
//      d * d <= n
//    }
//  }.holds
//
//  /**
//   * Proves that `assertAllNotCoprimeInRange` at `2` implies it at any `d >= 2`.
//   *
//   * The sieve completeness `assertAllNotCoprimeInRange(limit, 2, primes)` says
//   * every number in [2, limit) has a prime factor in `primes`. This lemma
//   * peels off the lower indices to expose the property at a higher starting
//   * point `d`. The recursive unfolding is safe because `assertAllNotCoprimeInRange`
//   * is a pure function — peeling one element at a time preserves its truth.
//   */
//  private def assertAllNotCoprimeInSubRange(
//    d: BigInt,
//    limit: BigInt,
//    primes: List[BigInt]
//  ): Boolean = {
//    require(d >= 2 && d <= limit)
//    require(ListUtils.checkAllPositive(primes))
//    require(CoprimeUtils.assertAllNotCoprimeInRange(limit, 2, primes))
//    decreases(d - 2)
//
//    if (d == 2) {
//      CoprimeUtils.assertAllNotCoprimeInRange(limit, d, primes)
//    } else {
//      assert(assertAllNotCoprimeInSubRange(d - 1, limit, primes))
//      assert(CoprimeUtils.assertAllNotCoprimeInRange(limit, d - 1, primes))
//      CoprimeUtils.assertAllNotCoprimeInRange(limit, d, primes)
//    }
//  }.holds
//
//  /**
//   * Proves that if `d` is not coprime to `primes` and `n` is a multiple of `d`,
//   * then `n` is also not coprime to `primes`.
//   *
//   * Used by `acceptedBelowHeadSquaredIsPrime` to extend a prime divisor `d`
//   * of `value` (which is a filter prime) to a contradiction with
//   * `CoprimeUtils.isCoprime(value, filterValues)`.
//   */
//  private def assertDivisibleByFactorListNotCoprime(
//    n: BigInt,
//    d: BigInt,
//    primes: List[BigInt]
//  ): Boolean = {
//    require(n > 1 && d >= 2)
//    require(ListUtils.checkAllPositive(primes))
//    require(Calc.mod(n, d) == BigInt(0))
//    require(!CoprimeUtils.isCoprime(d, primes))
//
//    if (CoprimeUtils.isCoprime(n, primes)) {
//      CoprimeUtils.assertNoDivisorByFactorList(n, d, primes)
//      assert(Calc.mod(n, d) != BigInt(0))
//      assert(false)
//    }
//
//    !CoprimeUtils.isCoprime(n, primes)
//  }.holds
//
//  /**
//   * Extracts `hasPrimeFactorInList(d, primes)` from a covering range.
//   *
//   * When d is in a range covered by `assertAllNotCoprimeInRange(limit, d, primes)`,
//   * the function's definition unfolds to `hasPrimeFactorInList(d, primes) && ...`.
//   * This lemma makes the first conjunct available as a named result.
//   */
//  private def assertHasPrimeFactorInRange(
//    d: BigInt,
//    limit: BigInt,
//    primes: List[BigInt]
//  ): Boolean = {
//    require(d >= 2 && d < limit)
//    require(ListUtils.checkAllPositive(primes))
//    require(CoprimeUtils.assertAllNotCoprimeInRange(limit, d, primes))
//
//    CoprimeUtils.hasPrimeFactorInList(d, primes)
//  }.holds
//
//  /**
//   * Proves that `d < head` given `d * d < head * head` and `d >= 2`.
//   *
//   * If `d >= head`, then `d * d >= head * d` (multiplying both sides by `d > 0`)
//   * and `head * d >= head * head` (multiplying both sides by `head > 0`).
//   * So `d * d >= head * head`, contradicting `d * d < head * head`.
//   * Therefore `d < head`.
//   */
//  private def assertDivisorBelowHead(d: BigInt, head: BigInt): Boolean = {
//    require(d >= 2)
//    require(head >= 2)
//    require(d * d < head * head)
//
//    if (d >= head) {
//      assert(head >= 0)
//      assert(d >= head)
//      assert(d * d >= head * d)
//      assert(head * d >= head * head)
//      assert(d * d >= head * head)
//      assert(false)
//    }
//    d < head
//  }.holds
//
//  def acceptedBelowHeadSquaredIsPrime(
//    value: BigInt,
//    head: BigInt,
//    filterValues: List[BigInt]
//  ): Boolean = {
//    require(head >= 2)
//    require(value > head)
//    require(value < head * head)
//    require(ListUtils.checkAllPositive(filterValues))
//    require(CoprimeUtils.isCoprime(value, filterValues))
//    require(CoprimeUtils.assertAllNotCoprimeInRange(head, 2, filterValues))
//
//    if (Prime.isPrime(value)) {
//      true
//    } else {
//      assertSmallestDivisorAtMostSqrt(value)
//
//      val d = findSmallestDivisor(value, 2)
//      assertSmallestDivisorIsPrime(value, d)
//      assert(d < value)
//      assert(d * d <= value)
//      assert(d * d < head * head)
//      assert(head >= 2)
//      assert(d >= 2)
//      assert(assertDivisorBelowHead(d, head))
//      assert(d < head)
//
//      assertAllNotCoprimeInSubRange(d, head, filterValues)
//      assert(CoprimeUtils.assertAllNotCoprimeInRange(head, d, filterValues))
//      assert(assertHasPrimeFactorInRange(d, head, filterValues))
//      assert(CoprimeUtils.hasPrimeFactorInList(d, filterValues))
//
//      CoprimeUtils.assertHasPrimeFactorImpliesNotCoprime(d, filterValues)
//      assert(!CoprimeUtils.isCoprime(d, filterValues))
//
//      assertDivisibleByFactorListNotCoprime(value, d, filterValues)
//      assert(!CoprimeUtils.isCoprime(value, filterValues))
//      assert(false)
//      true
//    }
//  }.holds
//
//  /**
//   * Returns the smallest divisor of a composite `n` with d < n, prime, and d*d <= n.
//   *
//   * Exposes `findSmallestDivisor` publicly so that callers (e.g. sieve-completeness
//   * proofs) can inspect `d` and check membership in filter-value lists.
//   */
//  def assertCompositeSmallestPrimeDivisor(n: BigInt): BigInt = {
//    require(n > 1)
//    require(!Prime.isPrime(n))
//
//    assertSmallestDivisorAtMostSqrt(n)
//    val d = findSmallestDivisor(n, 2)
//    assertSmallestDivisorIsPrime(n, d)
//    assert(d < n)
//    assert(d * d <= n)
//    d
//  }.ensuring(res => res >= 2 && res < n && Prime.isPrime(res) && res * res <= n)

