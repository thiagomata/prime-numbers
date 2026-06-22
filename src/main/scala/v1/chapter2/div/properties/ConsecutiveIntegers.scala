package v1.chapter2.div.properties

import stainless.lang.*
import stainless.collection.List
import v1.chapter1.verification.Helper.assert
import v1.chapter2.div.Calc

object ConsecutiveIntegers {

  /**
   * Lemma: If mod(a, p) == 0 and 0 < d < p, then mod(a + d, p) != 0.
   * This proves at most one zero in any p consecutive values.
   *
   * @param a BigInt a value with remainder 0 (a >= 0)
   * @param p BigInt modulus (p > 1)
   * @param d BigInt distance (0 < d < p)
   */
  def nonzeroAfterZero(a: BigInt, p: BigInt, d: BigInt): Boolean = {
    require(p > 1)
    require(a >= 0)
    require(d > 0)
    require(d < p)
    require(Calc.mod(a, p) == 0)

    ModOperations.modAdd(a, p, d)
    ModIdempotence.modIdempotence(d, p)
    ModSmallDividend.modSmallDividend(d, p)

    Calc.mod(a + d, p) != 0
  }.holds

  /**
   * Lemma: Among p consecutive integers starting from n,
   * there exists one divisible by p.
   *
   * There exists k in [0, p) such that mod(n + k, p) == 0.
   *
   * @param n BigInt starting value (n >= 0)
   * @param p BigInt modulus (p > 1)
   */
  def existsZero(n: BigInt, p: BigInt): Boolean = {
    require(p > 1)
    require(n >= 0)

    val r = Calc.mod(n, p)

    if (r == 0) {
      Calc.mod(n, p) == 0
    } else {
      val k = p - r
      ModOperations.modAdd(n, p, k)
      ModSmallDividend.modSmallDividend(k, p)
      Calc.mod(n + k, p) == 0
    }
  }.holds

  /**
   * Lemma: Among p consecutive integers starting from n,
   * exactly one is divisible by p.
   *
   * There exists exactly one k in [0, p) such that mod(n + k, p) == 0.
   *
   * @param n BigInt starting value (n >= 0)
   * @param p BigInt modulus (p > 1)
   */
  def exactlyOneZeroInConsecutive(n: BigInt, p: BigInt): Boolean = {
    require(p > 1)
    require(n >= 0)

    val r = Calc.mod(n, p)
    val k = if (r == 0) BigInt(0) else p - r
    assert(k >= 0 && k < p)

    existsZero(n, p)
    assert(Calc.mod(n + k, p) == 0)

    Calc.mod(n + k, p) == 0
  }.holds

  /**
   * Lemma: Among p consecutive integers starting from n,
   * at most one is divisible by p.
   *
   * If mod(n + i, p) == 0 and mod(n + j, p) == 0
   * for some i, j in [0, p), then i == j.
   */
  def atMostOneZero(n: BigInt, p: BigInt, i: BigInt, j: BigInt): Boolean = {
    require(p > 1)
    require(n >= 0)
    require(i >= 0 && i < p)
    require(j >= 0 && j < p)
    require(Calc.mod(n + i, p) == 0)
    require(Calc.mod(n + j, p) == 0)

    val smaller = if (i <= j) i else j
    val larger  = if (i <= j) j else i
    val d       = larger - smaller
    assert(d >= 0 && d < p)

    if (d > 0) {
      nonzeroAfterZero(n + smaller, p, d)
    }

    i == j
  }.holds

  /**
   * Lemma: For any n and p > 1, returns the offset k in [0, p)
   * such that mod(n + k, p) == 0.
   */
  def findZeroOffset(n: BigInt, p: BigInt): BigInt = {
    require(p > 1)
    require(n >= 0)

    val r = Calc.mod(n, p)
    val k = if (r == 0) BigInt(0) else p - r
    assert(k >= 0 && k < p)

    if (r == 0) {
      assert(Calc.mod(n + k, p) == 0)
    } else {
      ModOperations.modAdd(n, p, k)
      ModSmallDividend.modSmallDividend(k, p)
      assert(Calc.mod(n + k, p) == 0)
    }
    k
  }.ensuring(k => k >= 0 && k < p && Calc.mod(n + k, p) == 0)

  /**
   * Lemma: The zero offset at block m*p is the same as at block 0.
   * Periodicity: mod(a + m*p, p) == mod(a, p).
   */
  def zeroRepeatsEveryP(n: BigInt, p: BigInt, m: BigInt): Boolean = {
    require(p > 1)
    require(n >= 0)
    require(m >= 0)

    val k = findZeroOffset(n, p)
    AdditionAndMultiplication.APlusMultipleTimesBSameMod(n + k, p, m)

    Calc.mod(n + m * p + k, p) == 0
  }.holds

  /**
   * Lemma: In the interval [n, n + (m+1)*p - 1],
   * each of the m+1 blocks of size p has a value divisible by p.
   *
   * Equivalently: count of zeros in [n, n + (m+1)*p - 1] is m+1.
   */
  def zerosInMultipleBlocks(n: BigInt, p: BigInt, m: BigInt): Boolean = {
    require(p > 1)
    require(n >= 0)
    require(m >= 0)
    decreases(m)

    val k = findZeroOffset(n, p)

    if (m == 0) {
      Calc.mod(n + k, p) == 0
    } else {
      zeroRepeatsEveryP(n, p, m)
      assert(Calc.mod(n + m * p + k, p) == 0)
      zerosInMultipleBlocks(n, p, m - 1)
    }
  }.holds

  /**
   * Lemma: In the interval [a, a + m*p - 1],
   * there are exactly m values divisible by p.
   *
   * Interval has m blocks of size p, each with one zero.
   */
  def countModZeroEqualsM(a: BigInt, p: BigInt, m: BigInt): Boolean = {
    require(p > 1)
    require(a >= 0)
    require(m >= 1)

    zerosInMultipleBlocks(a, p, m - 1)
  }.holds

  /**
   * Lemma: In the interval [a, a + m*p1*p2 - 1]:
   * - m*p2 values are divisible by p1
   * - m*p1 values are divisible by p2
   * - m values are divisible by both (p1*p2)
   */
  def twoPrimesDensity(a: BigInt, p1: BigInt, p2: BigInt, m: BigInt): Boolean = {
    require(p1 > 1)
    require(p2 > 1)
    require(a >= 0)
    require(m >= 1)

    // Interval length = m * p1 * p2
    countModZeroEqualsM(a, p1, m * p2)
    countModZeroEqualsM(a, p2, m * p1)
    countModZeroEqualsM(a, p1 * p2, m)

    true
  }.holds

  /**
   * Lemma: In the interval [a, a + m*modulus - 1],
   * exactly m * (modulus / divisor) values are divisible by divisor.
   *
   * Precondition: divisor divides modulus (modulus % divisor == 0).
   */
  def densityForDivisor(a: BigInt, modulus: BigInt, divisor: BigInt, m: BigInt): Boolean = {
    require(divisor > 1)
    require(modulus > 0)
    require(modulus % divisor == 0)
    require(a >= 0)
    require(m >= 1)

    val quotient = modulus / divisor
    countModZeroEqualsM(a, divisor, m * quotient)
  }.holds

  /**
   * Lemma: After removing multiples of p1, the density of p2
   * among survivors is still 1/p2.
   *
   * In interval [a, a + m*p1*p2 - 1]:
   * - Survivors (not divisible by p1): m*p2*(p1-1)
   * - Survivors divisible by p2: m*(p1-1)
   * - Density = survivors_p2 / total_survivors = 1/p2
   *
   * Invariant: survivors_p2 * p2 == total_survivors
   */
  def densityPreservedAfterFiltering(
    a: BigInt, p1: BigInt, p2: BigInt, m: BigInt
  ): Boolean = {
    require(p1 > 1)
    require(p2 > 1)
    require(p1 != p2)
    require(a >= 0)
    require(m >= 1)

    twoPrimesDensity(a, p1, p2, m)

    val total = m * p1 * p2
    val p1Mults = m * p2
    val p2Mults = m * p1
    val both = m

    val survivors = total - p1Mults
    val p2AmongSurvivors = p2Mults - both

    p2AmongSurvivors * p2 == survivors
  }.holds

  /**
   * Lemma: For a list of primes with modulus M = product(primes),
   * in interval [a, a + m*M - 1], each prime p divides
   * exactly m * M / p values.
   */
  def densityForPrimeList(
    a: BigInt,
    primes: List[BigInt],
    M: BigInt,
    m: BigInt
  ): Boolean = {
    require(m >= 1)
    require(a >= 0)
    require(M > 0)
    require(noMultiplesInList(primes))
    require(allPrimesDivideM(primes, M))
    decreases(primes.size)

    if (primes.isEmpty) true
    else {
      densityForDivisor(a, M, primes.head, m)
      densityForPrimeList(a, primes.tail, M, m)
    }
  }.holds

  def noMultiplesInList(primes: List[BigInt]): Boolean = {
    decreases(primes.size)
    if (primes.isEmpty || primes.tail.isEmpty) true
    else {
      primes.head > 1 &&
        noMultipleOfHead(primes.head, primes.tail) &&
        noMultiplesInList(primes.tail)
    }
  }

  def noMultipleOfHead(head: BigInt, primes: List[BigInt]): Boolean = {
    require(head > 1)
    decreases(primes.size)
    if (primes.isEmpty) true
    else primes.head % head != 0 && noMultipleOfHead(head, primes.tail)
  }

  def allPrimesDivideM(primes: List[BigInt], M: BigInt): Boolean = {
    require(M > 0)
    decreases(primes.size)
    if (primes.isEmpty) true
    else primes.head > 1 && M % primes.head == 0 && allPrimesDivideM(primes.tail, M)
  }
}
