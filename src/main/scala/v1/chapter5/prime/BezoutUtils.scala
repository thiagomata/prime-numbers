package v1.chapter5.prime

import stainless.lang.{BigInt, decreases}
import stainless.lang.BooleanDecorations
import v1.chapter2.div.Calc
import v1.chapter2.div.properties.{AdditionAndMultiplication, ModOperations}
import v1.chapter5.prime.properties.EuclidLemma

/**
 * Bezout's identity via the subtractive Euclidean algorithm.
 *
 * This module proves the contrapositive of Euclid's lemma DIRECTLY from a linear
 * combination (a*x + p*y == gcd), avoiding the "contrapositive derivation" wall
 * that defeated presentation-based attempts (5 timeouts). See ticket
 * next-gaps-size-closed-form.md.
 *
 * The subtractive form matches the codebase's DivMod style (ModLessB/ModPlusB):
 *   gcd(a, b) = a                          if a == b
 *             = gcd(a - b, b)              if a > b
 *             = gcd(a, b - a)              otherwise
 * Terminates on a + b. Bezout coefficients update cleanly under subtraction
 * (one arithmetic step, no quotient algebra).
 */
object BezoutUtils {

  /**
   * A Bezout witness: integers x, y with a*x + b*y == g, where g is a common
   * divisor of a and b. Mirrors the DivMod case-class pattern (constructor
   * invariant enforced by require).
   */
  case class Bezout(a: BigInt, b: BigInt, g: BigInt, x: BigInt, y: BigInt) {
    require(a * x + b * y == g)
  }

  /**
   * The greatest common divisor via the subtractive Euclidean algorithm.
   *
   * Math:
   *   gcd(a, b) for a, b > 0:
   *     a                       if a == b
   *     gcd(a - b, b)           if a > b
   *     gcd(a, b - a)           otherwise (b > a)
   *
   * Terminates because a + b strictly decreases each step (a-b+b < a+b, etc.).
   * Returns the gcd value; the witness (x, y) is recovered by extendedGcd.
   */
  def subtractiveGcd(a: BigInt, b: BigInt): BigInt = {
    require(a > 0)
    require(b > 0)
    decreases(a + b)
    if (a == b) {
      a
    } else if (a > b) {
      subtractiveGcd(a - b, b)
    } else {
      subtractiveGcd(a, b - a)
    }
  }.ensuring((res: BigInt) => res > 0)

  /**
   * The extended Euclidean algorithm: returns a Bezout witness (x, y) with
   * a*x + b*y == gcd(a, b), via the subtractive form.
   *
   * Math:
   *   extendedGcd(a, b) = Bezout(a, b, a, 1, 0)              if a == b
   *                     = let r = extendedGcd(a-b, b) in      if a > b
   *                       Bezout(a, b, r.g, r.x, r.y - r.x)
   *                     = let r = extendedGcd(a, b-a) in      otherwise
   *                       Bezout(a, b, r.g, r.x - r.y, r.y)
   *
   * The invariant a*x + b*y == g is preserved at each step by construction
   * (see the algebra in the body). Terminates on a + b (same as subtractiveGcd).
   */
  def extendedGcd(a: BigInt, b: BigInt): Bezout = {
    require(a > 0)
    require(b > 0)
    decreases(a + b)
    if (a == b) {
      // a*1 + b*0 == a == g.
      Bezout(a, b, a, BigInt(1), BigInt(0))
    } else if (a > b) {
      val r = extendedGcd(a - b, b)
      // r : (a-b)*r.x + b*r.y == r.g
      // unwind: a*r.x + b*(r.y - r.x) == r.g
      //   since a*r.x + b*(r.y - r.x)
      //       = a*r.x + b*r.y - b*r.x
      //       = (a-b)*r.x + b*r.y     [regroup]
      //       = r.g                    [by r's invariant]
      Bezout(a, b, r.g, r.x, r.y - r.x)
    } else {
      val r = extendedGcd(a, b - a)
      // r : a*r.x + (b-a)*r.y == r.g
      // unwind: a*(r.x - r.y) + b*r.y == r.g
      //   since a*(r.x - r.y) + b*r.y
      //       = a*r.x - a*r.y + b*r.y
      //       = a*r.x + (b-a)*r.y      [regroup]
      //       = r.g                    [by r's invariant]
      Bezout(a, b, r.g, r.x - r.y, r.y)
    }
  }.ensuring((res: Bezout) =>
    res.a == a && res.b == b && res.g > 0 &&
    a * res.x + b * res.y == res.g
  )

  /**
   * Bezout's identity, exposed as a caller-facing .holds lemma.
   *
   * Math:
   *   a > 0 && b > 0  ==>  exists g > 0, x, y with a*x + b*y == g
   *
   * Specifically, extendedGcd(a, b) returns (g, x, y) with g > 0 and
   * a*x + b*y == g. This is the linear-combination fact that the direct proof
   * of the contrapositive chases (multiply by k, reduce mod p).
   */
  def assertBezoutIdentity(a: BigInt, b: BigInt): Boolean = {
    require(a > 0)
    require(b > 0)
    val bez = extendedGcd(a, b)
    bez.g > 0 && a * bez.x + b * bez.y == bez.g
  }.holds

  /**
   * The gcd returned by extendedGcd divides both inputs.
   *
   * Math:
   *   a > 0 && b > 0  ==>  mod(a, extendedGcd(a,b).g) == 0 && mod(b, g) == 0
   *
   * The subtractive algorithm preserves common divisibility: at the base
   * (a == b) g == a divides both; each subtract step (a-b, b) keeps g a common
   * divisor because a divisor of (a-b) and b also divides (a-b)+b = a. Proved
   * by induction mirroring extendedGcd's recursion.
   */
  def assertGcdDividesBoth(a: BigInt, b: BigInt): Boolean = {
    require(a > 0)
    require(b > 0)
    decreases(a + b)
    if (a == b) {
      // g == a; a | a and a | b (since a == b).
      assert(Calc.mod(a, a) == BigInt(0))
      assert(Calc.mod(b, a) == BigInt(0))
      val bez = extendedGcd(a, b)
      assert(bez.g == a)
      Calc.mod(a, bez.g) == BigInt(0) && Calc.mod(b, bez.g) == BigInt(0)
    } else if (a > b) {
      assert(assertGcdDividesBoth(a - b, b))
      val inner = extendedGcd(a - b, b)
      assert(Calc.mod(a - b, inner.g) == BigInt(0))
      assert(Calc.mod(b, inner.g) == BigInt(0))
      // inner.g divides (a-b) and b. Then inner.g divides (a-b)+b = a, by modAdd.
      assert(ModOperations.modAdd(a - b, inner.g, b))
      assert(Calc.mod((a - b) + b, inner.g) == Calc.mod(Calc.mod(a - b, inner.g) + Calc.mod(b, inner.g), inner.g))
      assert(Calc.mod((a - b) + b, inner.g) == BigInt(0))
      assert((a - b) + b == a)
      assert(Calc.mod(a, inner.g) == BigInt(0))
      val bez = extendedGcd(a, b)
      assert(bez.g == inner.g)
      Calc.mod(a, bez.g) == BigInt(0) && Calc.mod(b, bez.g) == BigInt(0)
    } else {
      assert(assertGcdDividesBoth(a, b - a))
      val inner = extendedGcd(a, b - a)
      assert(Calc.mod(a, inner.g) == BigInt(0))
      assert(Calc.mod(b - a, inner.g) == BigInt(0))
      // inner.g divides a and (b-a). Then inner.g divides a + (b-a) = b, by modAdd.
      assert(ModOperations.modAdd(a, inner.g, b - a))
      assert(Calc.mod(a + (b - a), inner.g) == Calc.mod(Calc.mod(a, inner.g) + Calc.mod(b - a, inner.g), inner.g))
      assert(Calc.mod(a + (b - a), inner.g) == BigInt(0))
      assert(a + (b - a) == b)
      assert(Calc.mod(b, inner.g) == BigInt(0))
      val bez = extendedGcd(a, b)
      assert(bez.g == inner.g)
      Calc.mod(a, bez.g) == BigInt(0) && Calc.mod(b, bez.g) == BigInt(0)
    }
  }.holds

  /**
   * When h is positive, smaller than a prime p, and not divisible by p, the
   * gcd of h and p is 1 (they are coprime).
   *
   * Math:
   *   isPrime(p) && 0 < h < p && mod(h, p) != 0  ==>  extendedGcd(h, p).g == 1
   *
   * Proof: g = extendedGcd(h, p).g divides both h and p (assertGcdDividesBoth).
   * Since g | p and p is prime and g > 0, g is either 1 or p (any divisor of p
   * in [2, p) would contradict noDivisorInRange(p, 2, p)). If g == p, then g | h
   * gives p | h, contradicting mod(h, p) != 0 (with 0 < h < p, mod(h, p) == h).
   * Hence g == 1.
   */
  def assertCoprimeGcdOne(h: BigInt, p: BigInt): Boolean = {
    require(p >= 2)
    require(Prime.isPrime(p))
    require(h > 0)
    require(h < p)
    require(Calc.mod(h, p) != BigInt(0))
    val bez = extendedGcd(h, p)
    assert(assertGcdDividesBoth(h, p))
    assert(Calc.mod(h, bez.g) == BigInt(0))
    assert(Calc.mod(p, bez.g) == BigInt(0))
    assert(bez.g > 0)
    assert(Prime.noDivisorInRange(p, BigInt(2), p))
    // Case split on bez.g. If bez.g is in [2, p), it divides p -- but
    // noDivisorInRangeExcludesValue(p, 2, p, bez.g) says mod(p, bez.g) != 0,
    // contradicting mod(p, bez.g) == 0. So bez.g is not in [2, p). With
    // bez.g > 0 and bez.g < p (shown below), bez.g == 1.
    // First establish bez.g < p: g | h and h > 0 and g > 0 implies g <= h < p.
    assert(CoprimeUtils.assertModZeroImpliesDivTimesBEqualsA(h, bez.g))
    assert(Calc.div(h, bez.g) >= BigInt(1))
    assert(bez.g <= Calc.div(h, bez.g) * bez.g)
    assert(bez.g <= h)
    assert(bez.g < p)
    if (bez.g >= BigInt(2)) {
      // bez.g in [2, p): noDivisorInRangeExcludesValue gives mod(p, bez.g) != 0,
      // contradicting mod(p, bez.g) == 0 established above.
      assert(Prime.noDivisorInRangeExcludesValue(p, BigInt(2), p, bez.g))
      assert(Calc.mod(p, bez.g) != BigInt(0))
      bez.g == BigInt(1)
    } else {
      // bez.g > 0 and bez.g < 2, so bez.g == 1.
      bez.g == BigInt(1)
    }
  }.holds

  /**
   * The Bézout linear combination equals 1 when h and prime p are coprime.
   *
   * Math:
   *   isPrime(p) && 0 < h < p && mod(h, p) != 0
   *     ==>  exists x, y with h * x + p * y == 1
   *
   * Direct from assertCoprimeGcdOne (g == 1) and the Bézout identity (h*x + p*y == g).
   * This is the linear combination the direct contrapositive proof chases.
   */
  def assertCoprimeLinearCombinationOne(h: BigInt, p: BigInt): Boolean = {
    require(p >= 2)
    require(Prime.isPrime(p))
    require(h > 0)
    require(h < p)
    require(Calc.mod(h, p) != BigInt(0))
    val bez = extendedGcd(h, p)
    assert(assertCoprimeGcdOne(h, p))
    assert(bez.g == BigInt(1))
    assert(assertBezoutIdentity(h, p))
    assert(h * bez.x + p * bez.y == bez.g)
    h * bez.x + p * bez.y == BigInt(1)
  }.holds

  /**
   * The DIRECT proof that if a prime divides k*h and does not divide h, then it
   * divides k. (No contrapositive derivation -- the whole point of Route A.)
   *
   * Math:
   *   isPrime(p) && 0 < h < p && mod(h, p) != 0 && mod(k * h, p) == 0
   *     ==>  mod(k, p) == 0
   *
   * Proof: by B6, exists x, y with h*x + p*y == 1. Multiply by k:
   *   k*h*x + k*p*y == k.
   * Since p | k*h (given), p | k*h*x (forward, assertMultiplePreservesDivisible).
   * Trivially p | k*p*y. So p | (k*h*x + k*p*y) == k, hence mod(k, p) == 0.
   */
  /**
   * If p divides m, then p divides m*c for ANY integer c (sign-agnostic).
   *
   * Math:
   *   mod(m, p) == 0  ==>  mod(m * c, p) == 0
   *
   * m = q*p (from mod==0), so m*c = q*p*c = p*(q*c), and ATimesBSameMod(0, p, q*c)
   * gives mod(p*(q*c), p) == mod(0, p) == 0. Sign-agnostic via ATimesBSameMod.
   */
  def assertDivTimesAnyIsDiv(m: BigInt, c: BigInt, p: BigInt): Boolean = {
    require(p > 0)
    require(Calc.mod(m, p) == BigInt(0))
    val q = Calc.div(m, p)
    assert(CoprimeUtils.assertModZeroImpliesDivTimesBEqualsA(m, p))
    assert(q * p == m)
    assert(m * c == q * p * c)
    assert(AdditionAndMultiplication.ATimesBSameMod(BigInt(0), p, q * c))
    assert(Calc.mod(BigInt(0), p) == BigInt(0))
    assert(Calc.mod(p * (q * c), p) == BigInt(0))
    assert(Calc.mod(m * c, p) == Calc.mod(q * p * c, p))
    Calc.mod(m * c, p) == BigInt(0)
  }.holds

  def assertPrimeDivProductImpliesDivFactor(k: BigInt, h: BigInt, p: BigInt): Boolean = {
    require(p >= 2)
    require(Prime.isPrime(p))
    require(h > 0)
    require(h < p)
    require(Calc.mod(h, p) != BigInt(0))
    require(k >= 0)
    require(Calc.mod(k * h, p) == BigInt(0))
    val bez = extendedGcd(h, p)
    assert(assertCoprimeLinearCombinationOne(h, p))
    assert(h * bez.x + p * bez.y == BigInt(1))
    // Multiply the identity by k: k*h*x + k*p*y == k.
    val khx = k * h * bez.x
    val kpy = k * p * bez.y
    assert((h * bez.x + p * bez.y) * k == BigInt(1) * k)
    assert(h * bez.x * k + p * bez.y * k == k)
    assert(k * h * bez.x + k * p * bez.y == k)
    assert(khx + kpy == k)
    // p | k*h (given)  ==>  p | (k*h)*bez.x = khx (sign-agnostic).
    assert(assertDivTimesAnyIsDiv(k * h, bez.x, p))
    assert(Calc.mod(khx, p) == BigInt(0))
    // p | k*p*y = kpy trivially: kpy = p*(k*bez.y), and mod(p, p) == 0, so
    // assertDivTimesAnyIsDiv(p, k*bez.y, p) gives mod(p*(k*bez.y), p) == 0.
    assert(assertDivTimesAnyIsDiv(p, k * bez.y, p))
    assert(Calc.mod(p * (k * bez.y), p) == BigInt(0))
    assert(p * (k * bez.y) == kpy)
    assert(Calc.mod(kpy, p) == BigInt(0))
    // p | khx and p | kpy  ==>  p | (khx + kpy) == k.
    assert(ModOperations.modAdd(khx, p, kpy))
    assert(Calc.mod(khx + kpy, p) == Calc.mod(Calc.mod(khx, p) + Calc.mod(kpy, p), p))
    assert(Calc.mod(khx + kpy, p) == BigInt(0))
    assert(khx + kpy == k)
    Calc.mod(k, p) == BigInt(0)
  }.holds

  /**
   * Euclid's lemma contrapositive -- the statement A2's "1/head" step needs,
   * proven DIRECTLY via B7 (Bézout), not derived as a contrapositive.
   *
   * Math:
   *   isPrime(p) && mod(k, p) != 0 && mod(h, p) != 0  ==>  mod(k * h, p) != 0
   *
   * Proof: reduce h to h' = mod(h, p) in (0, p) (positive since mod(h,p) != 0).
   * Bridge mod(k*h, p) == mod(k*h', p) via ATimesBSameMod (h = q*p + h'). If
   * mod(k*h', p) == 0, B7 (with h' < p, mod(h',p)=mod(h,p)!=0) gives mod(k, p)==0,
   * contradicting the hypothesis. Hence mod(k*h', p) != 0, so mod(k*h, p) != 0.
   */
  /**
   * If p divides k*h (h arbitrary, coprime to p), then p divides k.
   * Lightweight wrapper: reduce h to mod(h,p), apply B7.
   *
   * Math:
   *   isPrime(p) && mod(h, p) != 0 && mod(k*h, p) == 0  ==>  mod(k, p) == 0
   */
  def assertPrimeDivKhImpliesDivK(k: BigInt, h: BigInt, p: BigInt): Boolean = {
    require(p >= 2)
    require(Prime.isPrime(p))
    require(k >= 0)
    require(h >= 0)
    require(Calc.mod(h, p) != BigInt(0))
    require(Calc.mod(k * h, p) == BigInt(0))
    val hPrime = Calc.mod(h, p)
    val q = Calc.div(h, p)
    assert(hPrime > 0)
    assert(hPrime < p)
    assert(Calc.mod(hPrime, p) != BigInt(0))
    assert(h == q * p + hPrime)
    assert(k * h == k * q * p + k * hPrime)
    assert(AdditionAndMultiplication.ATimesBSameMod(k * hPrime, p, k * q))
    assert(Calc.mod(k * h, p) == Calc.mod(k * hPrime, p))
    assert(Calc.mod(k * hPrime, p) == BigInt(0))
    assert(assertPrimeDivProductImpliesDivFactor(k, hPrime, p))
    Calc.mod(k, p) == BigInt(0)
  }.holds

  /**
   * Euclid's lemma contrapositive -- the statement A2's "1/head" step needs.
   *
   * Math:
   *   isPrime(p) && mod(k, p) != 0 && mod(h, p) != 0  ==>  mod(k * h, p) != 0
   *
   * Uses assertPrimeDivKhImpliesDivK (the implication). The contrapositive is
   * discharged by the solver as: mod(k*h,p)==0 would (via that implication)
   * force mod(k,p)==0, contradicting mod(k,p)!=0.
   */
  def assertPrimeProductNotDivisible(k: BigInt, h: BigInt, p: BigInt): Boolean = {
    require(p >= 2)
    require(Prime.isPrime(p))
    require(k >= 0)
    require(h >= 0)
    require(Calc.mod(k, p) != BigInt(0))
    require(Calc.mod(h, p) != BigInt(0))
    val hPrime = Calc.mod(h, p)
    val q = Calc.div(h, p)
    assert(hPrime > 0)
    assert(hPrime < p)
    assert(Calc.mod(hPrime, p) != BigInt(0))
    assert(h == q * p + hPrime)
    assert(k * h == k * q * p + k * hPrime)
    assert(AdditionAndMultiplication.ATimesBSameMod(k * hPrime, p, k * q))
    assert(Calc.mod(k * h, p) == Calc.mod(k * hPrime, p))
    // In the branch where B7's premise mod(k*hPrime,p)==0 holds, B7 (called with
    // the reduced h' < p) gives mod(k,p)==0 -- contradicting mod(k,p)!=0. Hence
    // that branch is unreachable, i.e. mod(k*hPrime,p) != 0, so mod(k*h,p) != 0.
    if (Calc.mod(k * hPrime, p) == BigInt(0)) {
      assert(assertPrimeDivProductImpliesDivFactor(k, hPrime, p))
      assert(Calc.mod(k, p) == BigInt(0))
      false
    } else {
      true
    }
  }.ensuring(_ => Calc.mod(k * h, p) != BigInt(0))
}