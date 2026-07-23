package v1.chapter5.prime.properties

import stainless.collection.List
import stainless.lang.{BigInt, decreases}
import stainless.lang.BooleanDecorations
import v1.chapter2.div.Calc
import v1.chapter2.div.DivMod
import v1.chapter2.div.properties.AdditionAndMultiplication
import v1.chapter3.list.{ListBoundUtils, ListUtils}
import v1.chapter3.list.properties.ListProduct
import v1.chapter5.prime.{Prime, CoprimeUtils, BezoutUtils}

/**
 * Euclid's lemma (the "prime divides product implies divides a factor" direction),
 * proved by the minimal-counterexample / well-founded-induction route.
 *
 * This is the single number-theory fact that the next-stage gap-count closed form
 * |G'| = |G| * (h - 1) reduces to (every route -- direct filter-count, density /
 * inclusion-exclusion, even gcd(h, M) = 1 as a precondition -- bottoms out here at
 * the "1/head" uniformity step). See ticket next-gaps-size-closed-form.md.
 *
 * Draft proof strategy: tickets/blocked/primorial-not-divisible-by-new-prime.md.
 *
 * The lemmas are built bottom-up, one per verify cycle:
 *   E1 assertDivModReconstruct      -- div(a,b)*b + mod(a,b) == a
 *   E2 assertRemainderLessThanDivisor -- 0 <= mod(a,b) < b   (for decreases)
 *   E3 assertPrimeNotDividedBySmaller
 *   E4 assertSubStepDivDb           -- the hard algebraic step
 *   E5 euclidLemmaPrime             -- composes E2-E4 + IH
 *   E6 euclidLemmaPrimeContrapositive -- the exact form A2 needs
 */
object EuclidLemma {

  /**
   * Quotient-remainder reconstruction.
   *
   * Math:
   *   div(a, b) * b + mod(a, b) == a   (for b != 0, a >= 0)
   *
   * Both Calc.div and Calc.mod solve the same DivMod(a, b, 0, a) record, whose
   * constructor invariant (DivMod.scala) is div * b + mod == a. The .solve
   * postcondition preserves a and b, so the solved record satisfies
   * solved.div * b + solved.mod == a. Since Calc.div returns solved.div and
   * Calc.mod returns solved.mod, the equality holds.
   *
   * This is the quotient-remainder equation a = q*b + r used throughout the
   * Euclid proof (e.g. p = q*a + d with q = div(p,a), d = mod(p,a)).
   */
  def assertDivModReconstruct(a: BigInt, b: BigInt): Boolean = {
    require(b != 0)
    require(a >= 0)
    val record = DivMod(a, b, BigInt(0), a)
    val solved = record.solve
    assert(solved.a == a)
    assert(solved.b == b)
    assert(solved.isValid)
    assert(solved.div == Calc.div(a, b))
    assert(solved.mod == Calc.mod(a, b))
    Calc.div(a, b) * b + Calc.mod(a, b) == a
  }.holds

  /**
   * Remainder is strictly less than a positive divisor, and non-negative.
   *
   * Math:
   *   0 <= mod(a, b) < b   (for b > 0, a >= 0)
   *
   * Direct from the Calc.mod .ensuring postcondition (Calc.scala), which
   * guarantees 0 <= mod < b when b > 0. Exposed here as a standalone fact so the
   * Euclid proof can use `decreases(a)` with d = mod(p, a) < a (the upper bound)
   * and d >= 0 (the lower bound, so the recursion is well-founded).
   */
  def assertRemainderLessThanDivisor(a: BigInt, b: BigInt): Boolean = {
    require(b > 0)
    require(a >= 0)
    val r = Calc.mod(a, b)
    r >= 0 && r < b
  }.holds

  /**
   * A prime is not divisible by any smaller integer >= 2.
   *
   * Math:
   *   isPrime(p) && 2 <= a < p  ==>  mod(p, a) != 0
   *
   * By definition isPrime(p) = noDivisorInRange(p, 2, p), which asserts
   * mod(p, k) != 0 for every k in [2, p). noDivisorInRangeExcludesValue extracts
   * the fact for a single value a in that range. Used in the Euclid proof to
   * ensure d = mod(p, a) > 0 in the recursive branch (when a < p), so the
   * induction hypothesis euclidLemmaPrime(d, b, p) is applicable.
   */
  def assertPrimeNotDividedBySmaller(p: BigInt, a: BigInt): Boolean = {
    require(p >= 2)
    require(a >= 2)
    require(a < p)
    require(Prime.isPrime(p))
    assert(Prime.noDivisorInRange(p, BigInt(2), p))
    assert(Prime.noDivisorInRangeExcludesValue(p, BigInt(2), p, a))
    Calc.mod(p, a) != BigInt(0)
  }.holds

  /**
   * The hard algebraic step of the Euclid proof.
   *
   * Math:
   *   mod(a * b, p) == 0  &&  q = div(p, a)  &&  d = mod(p, a)
   *     ==>  mod(d * b, p) == 0
   *
   * Derivation (each link a verified fact or pure arithmetic):
   *   p = q * a + d                 [E1: assertDivModReconstruct]
   *   d = p - q * a
   *   d * b = (p - q * a) * b = p * b - q * (a * b)
   *   a * b = k * p   (k = div(a * b, p))   [mod(a*b,p)==0 via assertModZeroImpliesDivTimesBEqualsA]
   *   d * b = p * b - q * (k * p) = p * (b - q * k)
   *   mod(p * (b - q * k), p) == 0          [ATimesBSameMod(0, p, c): mod(0,p)==mod(p*c,p)==0]
   *   hence mod(d * b, p) == 0              [d * b == p * (b - q * k), pure arithmetic]
   *
   * ATimesBSameMod is used (rather than assertMultipleModZero) because it
   * dispatches on the sign of the multiplier m, so b - q * k may be negative
   * without issue.
   */
  def assertSubStepDivDb(a: BigInt, b: BigInt, p: BigInt): Boolean = {
    require(p > 0)
    require(a > 0)
    require(b >= 0)
    require(Calc.mod(a * b, p) == BigInt(0))
    val q = Calc.div(p, a)
    val d = Calc.mod(p, a)
    val k = Calc.div(a * b, p)
    assert(assertDivModReconstruct(p, a))
    assert(d == p - q * a)
    assert(Calc.mod(p, a) == d)
    assert(CoprimeUtils.assertModZeroImpliesDivTimesBEqualsA(a * b, p))
    assert(a * b == k * p)
    assert(d * b == (p - q * a) * b)
    assert((p - q * a) * b == p * b - q * (a * b))
    assert(p * b - q * (a * b) == p * b - q * (k * p))
    assert(p * b - q * (k * p) == p * (b - q * k))
    assert(d * b == p * (b - q * k))
    assert(AdditionAndMultiplication.ATimesBSameMod(BigInt(0), p, b - q * k))
    assert(Calc.mod(BigInt(0), p) == BigInt(0))
    assert(Calc.mod(p * (b - q * k), p) == BigInt(0))
    Calc.mod(d * b, p) == BigInt(0)
  }.holds

  /**
   * Euclid's lemma (prime divides product implies divides a factor), stated as
   * a DISJUNCTION so the contrapositive falls out as a direct case-split
   * (Stainless cannot derive contrapositives from one-directional implications
   * within a single VC -- the "contrapositive wall").
   *
   * Math:
   *   isPrime(p) && a > 0 && b >= 0 && mod(a * b, p) == 0
   *     ==>  mod(a, p) == 0 || mod(b, p) == 0
   *
   * Proof by well-founded induction on a:
   *   - If mod(a, p) == 0: the left disjunct holds directly.
   *   - Else if a == 1: a*b == b and mod(a*b,p)==0 gives mod(b,p)==0 (right disjunct).
   *   - Else (a >= 2, p does not divide a): d = mod(p,a) with 0 < d < a (E2,E3);
   *     E4 gives mod(d*b,p)==0; the IH euclidLemmaPrime(d,b,p) yields
   *     mod(d,p)==0 || mod(b,p)==0; since d < p and isCoprime-style reasoning
   *     rules out mod(d,p)==0 (d = mod(p,a), and... actually d may be divisible
   *     by p only if d==0, but d>0 and d<p so mod(d,p)==d!=0), the right
   *     disjunct mod(b,p)==0 holds.
   */
  def euclidLemmaPrime(a: BigInt, b: BigInt, p: BigInt): Boolean = {
    require(p >= 2)
    require(Prime.isPrime(p))
    require(a > 0)
    require(b >= 0)
    require(a < p)
    require(Calc.mod(a * b, p) == BigInt(0))
    decreases(a)
    if (Calc.mod(a, p) == BigInt(0)) {
      // p | a: left disjunct holds.
      Calc.mod(a, p) == BigInt(0) || Calc.mod(b, p) == BigInt(0)
    } else if (a == BigInt(1)) {
      // a == 1: a*b == b, precondition gives mod(b,p)==0.
      assert(a * b == b)
      assert(Calc.mod(b, p) == BigInt(0))
      Calc.mod(a, p) == BigInt(0) || Calc.mod(b, p) == BigInt(0)
    } else {
      // a >= 2, p does not divide a.
      val d = Calc.mod(p, a)
      assert(assertRemainderLessThanDivisor(p, a))
      assert(d >= 0 && d < a)
      assert(a >= BigInt(2))
      assert(assertPrimeNotDividedBySmaller(p, a))
      assert(Calc.mod(p, a) != BigInt(0))
      assert(d > 0)
      assert(assertSubStepDivDb(a, b, p))
      assert(Calc.mod(d * b, p) == BigInt(0))
      // IH on d (d < a): mod(d,p)==0 || mod(b,p)==0.
      assert(euclidLemmaPrime(d, b, p))
      // d > 0 and d < p, so mod(d, p) == d != 0: the left disjunct is false,
      // hence the right disjunct mod(b, p) == 0 must hold.
      assert(d < p)
      assert(Calc.mod(d, p) == d)
      assert(Calc.mod(d, p) != BigInt(0))
      Calc.mod(a, p) == BigInt(0) || Calc.mod(b, p) == BigInt(0)
    }
  }.holds

  /**
   * Euclid consequence: if a prime divides k * h, and it does not divide k,
   * then it divides h. (The useful direction of Euclid's lemma.)
   *
   * Math:
   *   isPrime(p) && mod(k * h, p) == 0 && mod(k, p) != 0  ==>  mod(h, p) == 0
   *
   * Reduces k to k' = mod(k, p) in (0, p) (positive since mod(k,p) != 0, below
   * p by E2), bridges mod(k*h, p) == mod(k'*h, p) via ATimesBSameMod, then
   * invokes euclidLemmaPrime(k', h, p) which (since mod(k', p) = mod(k, p) != 0,
   * so the non-trivial branch fires) yields mod(h, p) == 0.
   *
   * This is the verified form of Euclid's lemma used downstream: the standalone
   * contrapositive wrapper (p∤k ∧ p∤h ⟹ p∤k*h) timed out 3x as a single VC, so
   * callers structure the contradiction locally using this implication instead.
   * See ticket next-gaps-size-closed-form.md (E6 timeout detail).
   */
  def euclidConsequence(k: BigInt, h: BigInt, p: BigInt): Boolean = {
    require(p >= 2)
    require(Prime.isPrime(p))
    require(k >= 0)
    require(h >= 0)
    require(Calc.mod(k, p) != BigInt(0))
    require(Calc.mod(k * h, p) == BigInt(0))
    val kPrime = Calc.mod(k, p)
    val q = Calc.div(k, p)
    assert(assertRemainderLessThanDivisor(k, p))
    assert(kPrime >= 0 && kPrime < p)
    assert(kPrime > 0)
    assert(assertDivModReconstruct(k, p))
    assert(k == q * p + kPrime)
    assert(k * h == q * p * h + kPrime * h)
    assert(AdditionAndMultiplication.ATimesBSameMod(kPrime * h, p, q * h))
    assert(Calc.mod(k * h, p) == Calc.mod(kPrime * h, p))
    assert(Calc.mod(kPrime * h, p) == BigInt(0))
    assert(euclidLemmaPrime(kPrime, h, p))
    // euclidLemmaPrime now returns the disjunction mod(kPrime,p)==0 || mod(h,p)==0.
    // kPrime = mod(k,p), and mod(k,p) != 0 (precondition), so by idempotence
    // mod(kPrime, p) == mod(k,p) != 0 -- the left disjunct is false, hence
    // mod(h, p) == 0.
    assert(v1.chapter2.div.properties.ModIdempotence.modIdempotence(k, p))
    assert(Calc.mod(kPrime, p) == Calc.mod(k, p))
    assert(Calc.mod(kPrime, p) != BigInt(0))
    Calc.mod(h, p) == BigInt(0)
  }.holds

  /**
   * Euclid's lemma, contrapositive form -- the statement the next-stage gap-count
   * closed form needs. Derived as a DIRECT case-split on the disjunction returned
   * by euclidLemmaPrime, NOT as a derived implication (the derivation route timed
   * out 3x -- the "contrapositive wall").
   *
   * Math:
   *   isPrime(p) && mod(k, p) != 0 && mod(h, p) != 0  ==>  mod(k * h, p) != 0
   *
   * Proof: reduce k to k' = mod(k, p) in (0, p). Bridge mod(k*h, p) == mod(k'*h, p).
   * euclidLemmaPrime(k', h, p) yields mod(k',p)==0 || mod(h,p)==0. Since k' = mod(k,p)
   * and mod(k,p) != 0, idempotence gives mod(k',p) != 0 -- the left disjunct is false.
   * Since mod(h,p) != 0 (precondition), the right disjunct is false too. Hence the
   * disjunction's premise mod(k'*h, p)==0 cannot hold, i.e. mod(k*h, p) != 0.
   */
  // euclidContrapositive (p∤k ∧ p∤h ⟹ p∤k*h) is now proven via the Bézout theory
  // in BezoutUtils.assertPrimeProductNotDivisible -- the direct linear-combination
  // proof (Route A) broke through the "contrapositive wall" that defeated the 5
  // presentation-based attempts here. See ticket next-gaps-size-closed-form.md.

  /**
   * A prime h does not divide the product of a list of smaller positive values.
   *
   * Math:
   *   isPrime(h) && (forall p in primes, 0 < p < h)
   *     ==>  mod(product(primes), h) != 0
   *
   * Proof by induction on primes using BezoutUtils.assertPrimeProductNotDivisible
   * (the verified contrapositive). Base: product([]) == 1, mod(1, h) != 0. Step:
   * mod(head, h) != 0 (head < h) and mod(product(tail), h) != 0 (IH), so by the
   * contrapositive mod(head * product(tail), h) != 0, i.e. mod(product(primes), h) != 0.
   *
   * This is the "h does not divide product(tailPrimes)" / gcd(h, M) = 1 fact
   * (M = product(tailPrimes)) that the CRT / 1-per-head uniformity step needs.
   */
  /**
   * Two-factor non-divisibility: if prime h divides neither of two factors (the
   * second < h), it does not divide their product. Lightweight, non-recursive
   * wrapper so the recursive assertPrimeNotDivideProduct does not unfold the
   * Bézout chain (B7) at every induction level.
   *
   * Math:
   *   isPrime(h) && 0 < head < h && mod(head, h) != 0 && mod(other, h) != 0
   *     ==>  mod(head * other, h) != 0
   *
   * Proof: by contradiction via BezoutUtils.assertPrimeDivProductImpliesDivFactor
   * (B7) with k=other, h_=head, p=h. If mod(head*other, h)==0 and mod(head,h)!=0,
   * B7 gives mod(other, h)==0, contradicting mod(other, h) != 0.
   */
  def assertTwoFactorsProductNotDiv(head: BigInt, other: BigInt, h: BigInt): Boolean = {
    require(h >= 2)
    require(Prime.isPrime(h))
    require(head > 0)
    require(head < h)
    require(other >= 0)
    require(Calc.mod(head, h) != BigInt(0))
    require(Calc.mod(other, h) != BigInt(0))
    if (Calc.mod(head * other, h) == BigInt(0)) {
      assert(BezoutUtils.assertPrimeDivProductImpliesDivFactor(other, head, h))
      assert(Calc.mod(other, h) == BigInt(0))
      false
    } else {
      true
    }
  }.ensuring(_ => Calc.mod(head * other, h) != BigInt(0))

  // DRAFT (commented out -- times out at the recursive composition, 3 attempts).
  // Goal: isPrime(h) && allLessThan(primes, h) ==> mod(product(primes), h) != 0.
  // The base case and the two-factor step (assertTwoFactorsProductNotDiv, verified
  // 18/18) are both sound; the timeout is connecting the IH conclusion
  // mod(product(tail),h)!=0 to the wrapper's precondition on the local tailProduct,
  // within the recursive VC. The contrapositive (B8) and Bézout theory are verified
  // (11948/0/0); this is a composition issue, not a math wall.
  // def assertPrimeNotDivideProduct(h: BigInt, primes: List[BigInt]): Boolean = {
  //   require(h >= 2)
  //   require(Prime.isPrime(h))
  //   require(ListUtils.checkAllPositive(primes))
  //   require(ListBoundUtils.allLessThan(primes, h))
  //   decreases(primes.size)
  //   if (primes.isEmpty) {
  //     assert(ListProduct.product(primes) == BigInt(1))
  //     Calc.mod(ListProduct.product(primes), h) != BigInt(0)
  //   } else {
  //     val head = primes.head
  //     val tail = primes.tail
  //     val tailProduct = ListProduct.product(tail)
  //     assert(ListProduct.product(primes) == head * tailProduct)
  //     assert(ListBoundUtils.allLessThan(tail, h))
  //     assert(v1.chapter2.div.properties.ModSmallDividend.modSmallDividend(head, h))
  //     assert(Calc.mod(head, h) == head)
  //     assert(Calc.mod(head, h) != BigInt(0))
  //     val tailNotDiv: Boolean = assertPrimeNotDivideProduct(h, tail)
  //     assert(tailNotDiv)
  //     assert(Calc.mod(tailProduct, h) != BigInt(0))
  //     assert(assertTwoFactorsProductNotDiv(head, tailProduct, h))
  //     Calc.mod(ListProduct.product(primes), h) != BigInt(0)
  //   }
  // }.holds

  /**
   * A prime h does not divide the product of a list of smaller positive values.
   *
   * Math:
   *   isPrime(h) && (forall p in primes, 0 < p < h)
   *     ==>  mod(product(primes), h) != 0
   *
   * Restructured to avoid the recursive-composition timeout: the inductive step
   * uses B7 (BezoutUtils.assertPrimeDivProductImpliesDivFactor) DIRECTLY in a
   * contradiction branch inside a .ensuring postcondition, matching the structure
   * that worked for assertPrimeProductNotDivisible (B8). B7's premise
   * mod(tailProduct*head, h)==0 is satisfiable inside the if-branch, so its
   * precondition discharges; the .ensuring makes the conclusion visible.
   */
  // def assertPrimeNotDivideProduct(h: BigInt, primes: List[BigInt]): Boolean = {
  //   require(primes.nonEmpty)
  //   require(h >= 2)
  //   require(Prime.isPrime(h))
  //   require(ListUtils.checkAllPositive(primes))
  //   require(ListBoundUtils.allLessThan(primes, h))
  //   decreases(primes.size)
  //   primes match {
  //     case Nil() =>
  //       assert(ListProduct.product(primes) == BigInt(1))
  //       Calc.mod(ListProduct.product(primes), h) != BigInt(0)
  //     case Cons(head, tail) =>
  //       val tailProduct = ListProduct.product(tail)
  //       assert(ListProduct.product(primes) == head * tailProduct)
  //       assert(ListBoundUtils.allLessThan(tail, h))
  //       assert(v1.chapter2.div.properties.ModSmallDividend.modSmallDividend(head, h))
  //       assert(Calc.mod(head, h) == head)
  //       assert(Calc.mod(head, h) != BigInt(0))
  //       // IH: mod(product(tail), h) != 0 (recursive call; .ensuring propagates).
  //       assert(assertPrimeNotDivideProduct(h, tail))
  //       // Contradiction branch: if mod(head*tailProduct, h) == 0, B7 (with
  //       // k=tailProduct, h_=head, p=h; head<h) gives mod(tailProduct, h)==0,
  //       // contradicting the IH. So mod(head*tailProduct, h) != 0.
  //       if (Calc.mod(head * tailProduct, h) == BigInt(0)) {
  //         assert(BezoutUtils.assertPrimeDivProductImpliesDivFactor(tailProduct, head, h))
  //         assert(Calc.mod(tailProduct, h) == BigInt(0))
  //         false
  //       } else {
  //         true
  //       }
  //       true
  //   }
  // }.ensuring(_ => Calc.mod(ListProduct.product(primes), h) != BigInt(0))

  /**
   * Peel step (non-recursive): if h divides head * tailProduct and h does not
   * divide head, then h divides tailProduct. Thin wrapper over euclidConsequence.
   *
   * Math:
   *   isPrime(h) && mod(head * tailProduct, h) == 0 && mod(head, h) != 0
   *     ==>  mod(tailProduct, h) == 0
   *
   * Verified in isolation (12/12), but its CONTRAPOSITIVE (the form
   * assertPrimeNotDivideProduct needs: mod(head,h)!=0 && mod(tailProduct,h)!=0
   * ==> mod(head*tailProduct,h)!=0) cannot be derived by Stainless from this
   * implication within one VC -- the same "contrapositive wall" as E6. Kept as
   * a verified building block; assertPrimeNotDivideProduct is parked below as
   * an UNVERIFIED draft documenting the route, awaiting a direct (non-
   * contrapositive) proof of the product non-divisibility.
   */
  def assertPeelDividesTail(head: BigInt, tailProduct: BigInt, h: BigInt): Boolean = {
    require(h >= 2)
    require(Prime.isPrime(h))
    require(head >= 0)
    require(tailProduct >= 0)
    require(Calc.mod(head * tailProduct, h) == BigInt(0))
    require(Calc.mod(head, h) != BigInt(0))
    assert(euclidConsequence(head, tailProduct, h))
    Calc.mod(tailProduct, h) == BigInt(0)
  }.holds

  // DRAFT -- not verified. Attempted 3x, all time out at the contrapositive
  // step (Stainless cannot derive mod(head*tailProduct,h)!=0 from the peel
  // step's implication + mod(tailProduct,h)!=0). Needs a DIRECT proof of
  // product non-divisibility, not one routed through euclidConsequence's
  // contrapositive. Parked per stop-and-ask; see ticket next-gaps-size-closed-
  // form.md (stage 1 timeout).
  //
  // Goal: isPrime(h) && allLessThan(primes, h) ==> mod(product(primes), h) != 0
  // def assertPrimeNotDivideProduct(h: BigInt, primes: List[BigInt]): Boolean = { ... }
}
