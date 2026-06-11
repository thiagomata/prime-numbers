package v1.prime.properties

import stainless.collection.List
import stainless.lang.{BigInt, decreases}
// import stainless.annotation.extern
import v1.Calc
import v1.prime.{Prime, PrimeUtils}
import stainless.lang.BooleanDecorations
import v1.div.properties.AdditionAndMultiplication.ATimesBSameMod
import v1.div.properties.{AdditionAndMultiplication, ModIdentity, ModOperations, ModSmallDividend}
import v1.list.ListBoundUtils
import v1.list.properties.ListProduct
import v1.prime.PrimeUtils.{primorial, primorialConcatLemma}

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
  }

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
   * Lemma: divisibility is transitive — if d divides n and e divides d, then e divides n.
   *
   * This is the workhorse of the "smallest divisor is prime" proof.
   * If n has a divisor d, and d has a divisor e, then e is also a divisor of n.
   * This lets us argue by contradiction: if the smallest divisor of n had a
   * smaller divisor, that smaller divisor would also divide n — contradiction.
   *
   * The proof works algebraically: if n = nd * d and d = de * e,
   * then n = (nd * de) * e, so e divides n.
   *
   * mod(n, d) == 0 ∧ mod(d, e) == 0 ⇒ mod(n, e) == 0
   *
   * @param n BigInt the outer dividend (n > 1)
   * @param d BigInt the middle divisor (d >= 2)
   * @param e BigInt the inner divisor (e >= 2)
   * @return Boolean true if the property holds
   */
  private def assertTransitiveDivisible(n: BigInt, d: BigInt, e: BigInt): Boolean = {
    require(n > 1 && d >= 2 && e >= 2)
    require(Calc.mod(n, d) == BigInt(0))
    require(Calc.mod(d, e) == BigInt(0))
    assertModZeroImpliesDivTimesBEqualsA(n, d)
    assertModZeroImpliesDivTimesBEqualsA(d, e)
    val nd = Calc.div(n, d)
    val de = Calc.div(d, e)
    assert(nd * d == n)
    assert(de * e == d)
    assert(nd * de * e == n)
    assert(ModSmallDividend.modSmallDividend(BigInt(0), e))
    AdditionAndMultiplication.ATimesBSameMod(BigInt(0), e, nd * de)
    Calc.mod(n, e) == BigInt(0)
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
// VERIFICATION FAILED (2026-06-11): 1990 UNKNOWN - solver can't prove mod(n,d)==0 from findSmallestDivisor(n,2)==d even with findSmallestDivisorEquiv
//  private def findSmallestDivisorResultModZero(n: BigInt, d: BigInt): Boolean = {
//    require(n > 1 && d >= 2 && d < n)
//    require(findSmallestDivisor(n, 2) == d)
//    findSmallestDivisorEquiv(n, 2)
//    Calc.mod(n, d) == BigInt(0)
//  }.holds

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
// VERIFICATION FAILED (2026-06-11): 3051 UNKNOWN - assertTransitiveDivisible in contradiction branch causes solver timeout
//  private def assertSmallestDivisorIsPrimeHelper(n: BigInt, d: BigInt, from: BigInt): Boolean = {
//    require(n > 1 && d >= 2 && from >= 2 && from <= d && d < n)
//    require(findSmallestDivisor(n, 2) == d)
//    require(Calc.mod(n, d) == BigInt(0))
//    decreases(d - from)
//    if (from >= d) {
//      Prime.noDivisorInRange(d, from, d)
//    } else if (Calc.mod(d, from) == BigInt(0)) {
//      assertTransitiveDivisible(n, d, from)
//      findSmallestDivisorReturnsFromIfZero(n, from)
//      val sd = findSmallestDivisor(n, from)
//      assert(sd == from)
//      assert(sd < d)
//      // sd == from < d, but findSmallestDivisor(n, 2) == d
//      // Contradiction: findSmallestDivisor would return from (or smaller), not d
//      false
//    } else {
//      assertSmallestDivisorIsPrimeHelper(n, d, from + 1)
//      Prime.noDivisorInRange(d, from, d)
//    }
//  }.holds

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
// DEPENDENCY FAILED (2026-06-11): depends on findSmallestDivisorResultModZero and assertSmallestDivisorIsPrimeHelper (both failed)
//  private def assertSmallestDivisorIsPrime(n: BigInt, d: BigInt): Boolean = {
//    require(n > 1 && d >= 2 && d < n)
//    require(findSmallestDivisor(n, 2) == d)
//    findSmallestDivisorEquiv(n, 2)
//    assert(Calc.mod(n, d) == BigInt(0))
//    d > 1 && assertSmallestDivisorIsPrimeHelper(n, d, 2)
//  }.holds

  /**
   * Lemma: every prime in the list divides the primorial of the list.
   *
   * For each prime p in the list, `primorial(primes) mod p.value == 0`.
   * This is because p appears as a factor in the product. The proof unfolds
   * the primorial and uses the fact that `mod(k * p, p) == 0`.
   *
   * For every p in primes: mod(primorial(primes), p.value) == 0
   *
   * @param primes List[Prime] a list of primes
   * @return Boolean true if every prime divides the primorial
   */
  def allPrimesDividePrimorial(primes: List[Prime]): Boolean = {
    decreases(primes.size)
    if (primes.isEmpty) true
    else {
      val primorial: BigInt = PrimeUtils.primorial(primes)
      val tailPrimorial: BigInt = PrimeUtils.primorial(primes.tail)
      assert(primorial == primes.head.value * tailPrimorial)
      assert(ModIdentity.modIdentity(primes.head.value))

      // mod(a + b * m, b) == mod(a, b)
      assert(AdditionAndMultiplication.ATimesBSameMod
        (
          0, // a
          primes.head.value, // b
          tailPrimorial // m
        )
      )
      assert(Calc.mod(primorial, primes.head.value) == 0)

      Calc.mod(primorial, primes.head.value) == 0 &&
        allPrimesDividePrimorial(primes.tail)
    }
  }.holds

  /**
   * Lemma: product distributes over list concatenation.
   *
   * The product of two lists appended is the same as the product of the
   * first times the product of the second. Just like primorialConcatLemma
   * but for ListProduct. Needed to keep the ListProduct and primorial
   * views consistent.
   *
   * product(list1 ++ list2) == product(list1) * product(list2)
   *
   * @param list1 List[BigInt] first list (all > 0)
   * @param list2 List[BigInt] second list (all > 0)
   * @return Boolean true if the property holds
   */
  private def productAppendLemma(list1: List[BigInt], list2: List[BigInt]): Boolean = {
    decreases(list1.size)
    require(ListBoundUtils.allGreaterThan(list1, 0))
    require(ListBoundUtils.allGreaterThan(list2, 0))
    if (list1.isEmpty) {
      ListProduct.product(list1 ++ list2) ==
        ListProduct.product(list1) * ListProduct.product(list2)
    } else {
      productAppendLemma(list1.tail, list2)
      ListProduct.product(list1 ++ list2) ==
        ListProduct.product(list1) * ListProduct.product(list2)
    }
  }.holds

  /**
   * Helper: for a product prefix * head(remaining) * product(tail(remaining)),
   * the head divides the full product.
   *
   * Walks through the list maintaining a running product of what came before.
   * At each step, the current element p divides the full product because
   * p factors out: prefix * p * suffix = p * (prefix * suffix).
   *
   * For every p in remaining: mod(prefix * p * product(remaining.tail), p) == 0
   *
   * @param remaining List[BigInt] the elements still to check (all > 0)
   * @param prefix    BigInt the product of the elements already processed
   * @return Boolean true if every remaining element divides the full product
   */
  private def loop(remaining: List[BigInt], prefix: BigInt): Boolean = {
    decreases(remaining.size)
    require(ListBoundUtils.allGreaterThan(remaining, 0))
    if (remaining.isEmpty) true
    else {
      val p = remaining.head
      val suffix = ListProduct.product(remaining.tail)
      val full = prefix * p * suffix
      assert(ModSmallDividend.modSmallDividend(BigInt(0), p))
      assert(ATimesBSameMod(BigInt(0), p, prefix * suffix))
      assert(Calc.mod(full, p) == BigInt(0))
      Calc.mod(full, p) == BigInt(0) && loop(remaining.tail, prefix * p)
    }
  }.holds

  /**
   * Lemma: for any list of positive integers, each element divides the total product.
   *
   * This is the generic version over BigInt lists (no Prime wrapper).
   * The product of the whole list mod any element is zero, because that
   * element appears as a factor in the product.
   *
   * For every e in elements: mod(product(elements), e) == 0
   *
   * @param elements List[BigInt] a list of positive integers
   * @return Boolean true if each element divides the total product
   */
  def checkProductModZero(elements: List[BigInt]): Boolean = {
    require(ListBoundUtils.allGreaterThan(elements, 0))
    loop(elements, BigInt(1))
  }.holds

  /**
   * Lemma: each prime in the list divides the primorial.
   *
   * Same as checkProductModZero, but operates on Prime objects directly
   * by extracting their values first. A convenient wrapper.
   *
   * For every p in primes: mod(primorial(primes), p.value) == 0
   *
   * @param primes List[Prime] a list of primes
   * @return Boolean true if each prime divides the primorial
   */
  def checkPrimorialModZero(primes: List[Prime]): Boolean = {
    checkProductModZero(PrimeUtils.primeValues(primes))
  }.holds

  /**
   * Lemma: the head of a non-empty prime list divides the primorial.
   *
   * A simple special case when you only care about the first prime.
   * Uses both allPrimesDividePrimorial and checkPrimorialModZero as
   * cross-checks.
   *
   * primes.nonEmpty ⇒ mod(primorial(primes), primes.head.value) == 0
   *
   * @param primes List[Prime] a non-empty list of primes
   * @return Boolean true if the head divides the primorial
   */
  def checkPrimorialModZeroHead(primes: List[Prime]): Boolean = {
    require(primes.nonEmpty)
    assert(allPrimesDividePrimorial(primes))
    assert(checkPrimorialModZero(primes))
    Calc.mod(PrimeUtils.primorial(primes), primes.head.value) == BigInt(0)
  }.holds

  /**
   * Helper: prove primorial mod p == 0 for every p, using an accumulator.
   *
   * Walks through the list maintaining the "previous" primes in an accumulator.
   * At each step, the full product is previousPrimorial * p * tailPrimorial,
   * and we prove p divides it using ATimesBSameMod. This is the core loop
   * behind checkPrimorialModZeroAll.
   *
   * For every p in current: mod(primorial(previous ++ current), p.value) == 0
   *
   * @param previous List[Prime] primes already processed (accumulator)
   * @param current  List[Prime] primes still to check
   * @return Boolean true if each prime in current divides the combined primorial
   */
  def checkPrimorialModZeroTailLoop(previous: List[Prime], current: List[Prime]): Boolean = {
    decreases(current.size)
    if (current.isEmpty) true
    else {
      val p = current.head.value
      val tailPrimorial = PrimeUtils.primorial(current.tail)
      val previousPrimorial = PrimeUtils.primorial(previous)
      val combinedPrimorial = previousPrimorial * p * tailPrimorial

      primorialConcatLemma(previous, current)
      assert(primorial(current) == p * primorial(current.tail))
      assert(primorial(previous ++ current) == previousPrimorial * p * primorial(current.tail))
      assert(primorial(previous ++ current) == combinedPrimorial)

      assert(ModSmallDividend.modSmallDividend(BigInt(0), p))
      AdditionAndMultiplication.ATimesBSameMod(
        BigInt(0), p, previousPrimorial * tailPrimorial
      )
      Calc.mod(combinedPrimorial, p) == BigInt(0) &&
        checkPrimorialModZeroTailLoop(previous :+ current.head, current.tail)
    }
  }.holds

  /**
   * Lemma: every prime in the list divides the primorial — all of them.
   *
   * Stronger than allPrimesDividePrimorial: this proves it by direct
   * structural induction with an accumulator, which makes the proof
   * accessible to Stainless for the primorial+1 lemma.
   *
   * For every p in primes: mod(primorial(primes), p.value) == 0
   *
   * @param primes List[Prime] a list of primes
   * @return Boolean true if every prime divides the primorial
   */
  def checkPrimorialModZeroAll(primes: List[Prime]): Boolean = {
    decreases(primes.size)
    checkPrimorialModZeroTailLoop(List.empty, primes)
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
      Calc.mod(primorialAll + 1, p) != BigInt(0) &&
        primorialPlusOneTailLoop(previous :+ current.head, current.tail)
    }
  }.holds

}
