package v1.prime.properties

import stainless.collection.List
import stainless.lang.{BigInt, decreases}
import v1.Calc
import v1.prime.{Prime, PrimeUtils}
import stainless.lang.BooleanDecorations
import v1.div.properties.AdditionAndMultiplication.ATimesBSameMod
import v1.div.properties.{AdditionAndMultiplication, ModIdentity, ModOperations, ModSmallDividend}
import v1.list.ListBoundUtils
import v1.list.properties.ListProduct
import v1.prime.PrimeUtils.{primorial, primorialConcatLemma}

object  OtherPrimesProperties {

  /**
   * Find the smallest divisor of n in the range [from, n).
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
   */
  private def assertModZeroImpliesDivTimesBEqualsA(a: BigInt, b: BigInt): Boolean = {
    require(b != 0)
    require(Calc.mod(a, b) == BigInt(0))
    Calc.div(a, b) * b == a
  }.holds

  /**
   * Lemma: if from divides n, findSmallestDivisor starting at from returns from.
   */
  private def findSmallestDivisorReturnsFromIfZero(n: BigInt, from: BigInt): Boolean = {
    require(n > 1 && from >= 2 && from < n)
    require(Calc.mod(n, from) == BigInt(0))
    findSmallestDivisor(n, from) == from
  }.holds

  /**
   * Lemma: if findSmallestDivisor(n, 2) == d (and d < n), then d divides n.
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
   */
  private def assertSmallestDivisorIsPrime(n: BigInt, d: BigInt): Boolean = {
    require(n > 1 && d >= 2 && d < n)
    require(findSmallestDivisor(n, 2) == d)
    findSmallestDivisorResultModZero(n, d)
    assertSmallestDivisorIsPrimeDirect(n, d, 2)
    d > 1 && Prime.noDivisorInRange(d, 2, d)
  }.holds

  /**
   * Lemma: every prime in the list divides the primorial of the list.
   */
  def allPrimesDividePrimorial(primes: List[Prime]): Boolean = {
    decreases(primes.size)
    if (primes.isEmpty) true
    else {
      val primorial: BigInt = PrimeUtils.primorial(primes)
      val tailPrimorial: BigInt = PrimeUtils.primorial(primes.tail)
      assert(primorial == primes.head.value * tailPrimorial)
      assert(ModIdentity.modIdentity(primes.head.value))

      assert(AdditionAndMultiplication.ATimesBSameMod(0, primes.head.value, tailPrimorial))
      assert(Calc.mod(primorial, primes.head.value) == 0)

      Calc.mod(primorial, primes.head.value) == 0 && allPrimesDividePrimorial(primes.tail)
    }
  }.holds

  /**
   * Helper: prove primorial mod p == 0 for every p, using an accumulator.
   */
  def checkPrimorialModZeroTailLoop(previous: List[Prime], current: List[Prime]): Boolean = {
    decreases(current.size)
    if (current.isEmpty) true
    else {
      val p = current.head.value
      val tailPrimorial = PrimeUtils.primorial(current.tail)
      val previousPrimorial = PrimeUtils.primorial(previous)
      val combinedPrimorial = previousPrimorial * p * tailPrimorial

      assert(ModSmallDividend.modSmallDividend(BigInt(0), p))
      AdditionAndMultiplication.ATimesBSameMod(BigInt(0), p, previousPrimorial * tailPrimorial)

      Calc.mod(combinedPrimorial, p) == BigInt(0) &&
        checkPrimorialModZeroTailLoop(previous :+ current.head, current.tail)
    }
  }.holds

  /**
   * Lemma: every prime in the list divides the primorial — all of them.
   */
  def checkPrimorialModZeroAll(primes: List[Prime]): Boolean = {
    decreases(primes.size)
    checkPrimorialModZeroTailLoop(List.empty, primes)
  }.holds

  /**
   * Lemma: primorial + 1 is NOT divisible by any prime in the list.
   */
  def primorialPlusOneModAny(primes: List[Prime]): Boolean = {
    decreases(primes.size)
    primorialPlusOneTailLoop(List.empty, primes)
  }.holds

  private def primorialPlusOneTailLoop(previous: List[Prime], current: List[Prime]): Boolean = {
    decreases(current.size)
    if (current.isEmpty) true
    else {
      val p = current.head.value
      val tailPrimorial = PrimeUtils.primorial(current.tail)
      val previousPrimorial = PrimeUtils.primorial(previous)
      val primorialAll = previousPrimorial * p * tailPrimorial

      assert(ModSmallDividend.modSmallDividend(BigInt(0), p))
      AdditionAndMultiplication.ATimesBSameMod(BigInt(0), p, previousPrimorial * tailPrimorial)
      assert(Calc.mod(primorialAll, p) == BigInt(0))
      ModOperations.modZeroPlusC(primorialAll, p, BigInt(1))
      assert(ModSmallDividend.modSmallDividend(BigInt(1), p))

      Calc.mod(primorialAll + 1, p) != BigInt(0) &&
        primorialPlusOneTailLoop(previous :+ current.head, current.tail)
    }
  }.holds

  /**
   * Construct a new Prime from Euclid's construction.
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

  // =========================================================================
  // ALTERNATIVE APPROACH: CONTRADICTION VIA MAXIMUM BOUND REASONING
  // =========================================================================
//
//  /**
//   * Lemma: Every individual prime element contained inside a list is
//   * bounded above by the maximum prime value located by `biggerPrime`.
//   */
//  def primeBoundedByMax(primes: List[Prime], p: Prime): Boolean = {
//    require(primes.nonEmpty)
//    require(primes.contains(p))
//    decreases(primes.size)
//
//    val maxP = PrimeUtils.biggerPrime(primes)
//    if (primes.tail.isEmpty) {
//      assert(primes.head == maxP)
//      p.value <= maxP.value
//    } else {
//      if (primes.tail.contains(p)) {
//        primeBoundedByMax(primes.tail, p)
//      } else {
//        assert(primes.head == p)
//      }
//      p.value <= maxP.value
//    }
//  }.ensuring(_ => p.value <= PrimeUtils.biggerPrime(primes).value)
//
//  /**
//   * Lemma: Any valid prime divisor of primorial(primes) + 1 must be strictly
//   * greater than the maximum prime value located inside that list.
//   */
//  def euclidDivisorIsStrictlyGreater(primes: List[Prime], d: BigInt): Boolean = {
//    require(primes.nonEmpty)
//    require(primorialPlusOneModAny(primes))
//    val n = PrimeUtils.primorial(primes) + 1
//    require(d > 1)
//    require(Calc.mod(n, d) == BigInt(0))
//
//    val M = PrimeUtils.biggerPrime(primes).value
//
//    if (d <= M) {
//      // By initializing the collision lemma from the empty list, previous ++ remaining matches 'primes'
//      divisorCollisionLemma(List.empty[Prime], primes, d)
//
//      // This forces the solver to evaluate the structural contradiction,
//      // making the d <= M branch completely un-verifiable (dead code path).
//      assert(false)
//    }
//
//    d > M
//  }.holds
//
//  /**
//   * Helper Lemma: If a number d divides primorial(primes) + 1, it cannot match
//   * or be bounded below any prime in the remaining list.
//   */
//  private def divisorCollisionLemma(previous: List[Prime], remaining: List[Prime], d: BigInt): Boolean = {
//    require(d > 1)
//    val n = PrimeUtils.primorial(previous ++ remaining) + 1
//    require(Calc.mod(n, d) == BigInt(0))
//    decreases(remaining.size)
//
//    if (remaining.isEmpty) {
//      true
//    } else {
//      val p = remaining.head.value
//
//      // We invoke our known remainder engine facts for the current head
//      val tailPrimorial = PrimeUtils.primorial(remaining.tail)
//      val previousPrimorial = PrimeUtils.primorial(previous)
//      val primorialAll = previousPrimorial * p * tailPrimorial
//
//      primorialConcatLemma(previous, remaining)
//
//      // If d matches this prime p, we expose the immediate remainder contradiction (1 == 0)
//      if (d == p) {
//        assert(Calc.mod(primorialAll, d) == BigInt(0))
//        ModOperations.modZeroPlusC(primorialAll, d, BigInt(1))
//        assert(Calc.mod(n, d) == BigInt(1)) // Contradicts require(Calc.mod(n, d) == 0)
//      }
//
//      val nextPrevious = previous :+ remaining.head
//      primorialConcatLemma(previous, List(remaining.head))
//      primorialConcatLemma(nextPrevious, remaining.tail)
//
//      // Step to the next element
//      d != p && divisorCollisionLemma(nextPrevious, remaining.tail, d)
//    }
//  }.holds
//
//  /**
//   * Euclid's theorem: There exists a prime not contained in the given non-empty list.
//   * Proved decisively via arithmetic bounds contradiction.
//   */
//  def euclidTheorem(primes: List[Prime]): Boolean = {
//    require(primes.nonEmpty)
//    require(primorialPlusOneModAny(primes))
//
//    PrimeUtils.primorialPositive(primes)
//    val n = PrimeUtils.primorial(primes) + 1
//    val d = findSmallestDivisor(n, 2)
//
//    val M = PrimeUtils.biggerPrime(primes).value
//
//    if (d == n) {
//      findSmallestDivisorIsNImpliesNoDivisorInRange(n, 2)
//      assert(Calc.mod(n, n) == BigInt(0))
//
//      // Call the lemma directly with 'n' without wrapping it in a variable assignment
//      euclidDivisorIsStrictlyGreater(primes, n)
//      assert(n > M)
//
//      if (primes.contains(Prime(n))) {
//        primeBoundedByMax(primes, Prime(n))
//        assert(n <= M)
//      }
//      !primes.contains(Prime(n))
//
//    } else {
//      assertSmallestDivisorIsPrime(n, d)
//      findSmallestDivisorResultModZero(n, d)
//      assert(Calc.mod(n, d) == BigInt(0))
//
//      // Call the lemma directly with 'd'
//      euclidDivisorIsStrictlyGreater(primes, d)
//      assert(d > M)
//
//      if (primes.contains(Prime(d))) {
//        primeBoundedByMax(primes, Prime(d))
//        assert(d <= M)
//      }
//      !primes.contains(Prime(d))
//    }
//  }.holds
}