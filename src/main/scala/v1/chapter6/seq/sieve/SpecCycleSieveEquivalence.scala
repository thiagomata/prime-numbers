package v1.chapter6.seq.sieve

import stainless.lang.*
import v1.chapter2.div.{Calc, DivMod}
import v1.chapter2.div.properties.{ModIdempotence, ModOperations}
import v1.chapter3.list.{ListBoundUtils, ListUtils, SortedList}
import v1.chapter4.cycle.gap.GapCycle
import v1.chapter4.cycle.integral.recursive.CycleIntegral
import v1.chapter5.prime.{Prime, PrimeUtils}

/**
 * Local bridge lemmas for proving that the specification sieve and the
 * cycle-based sieve describe the same stream.
 *
 * The goal of this object is organizational as much as mathematical. Many of
 * the facts needed by the final equivalence theorem already exist elsewhere,
 * but importing them directly into one large proof makes the dependency shape
 * hard to see. These wrappers give the equivalence proof local names for each
 * prerequisite and verify, one by one, that the existing facts are usable from
 * this context.
 */
object SpecCycleSieveEquivalence {


  private def primorialMatchesSieveProduct(primeList: stainless.collection.List[Prime]): Boolean = {
    decreases(primeList.size)

    if (primeList.isEmpty) {
      PrimeUtils.primorial(primeList) == SieveUtils.product(PrimeUtils.primeValues(primeList))
    } else {
      primorialMatchesSieveProduct(primeList.tail)
      PrimeUtils.primorial(primeList) == SieveUtils.product(PrimeUtils.primeValues(primeList))
    }
  }.holds

  /**
   * Converts the prime-list correspondence assumption into head equality.
   *
   * `SpecSieveSequence` stores primes as `Prime` wrappers through
   * `AllPrimesSoFarList`; `CycleSieveSequence` stores the same stage as raw
   * `BigInt` values. When the cycle-side list is exactly
   * `PrimeUtils.primeValues(spec.primes.list.list)`, both sequence heads are
   * the same number.
   */
  def assertHeadsMatchFromPrimeValues(
    spec: SpecSieveSequence,
    cycle: CycleSieveSequence
  ): Boolean = {
    require(PrimeUtils.primeValues(cycle.primes.list.list) == PrimeUtils.primeValues(spec.primes.list.list))

    assert(spec.primes.list.list.nonEmpty)
    assert(PrimeUtils.primeValues(spec.primes.list.list).head == spec.head.value)
    assert(PrimeUtils.primeValues(cycle.primes.list.list).head == spec.head.value)

    spec.head.value == cycle.head
  }.holds

  /**
   * Bridges the base case of the two `apply` methods.
   *
   * Both sequence implementations define index 0 as the current head. The only
   * representation work needed here is the head bridge above, which converts the
   * Spec `Prime` head into the cycle-side raw `BigInt` head.
   */
  def assertApplyZeroMatchesFromPrimeValues(
    spec: SpecSieveSequence,
    cycle: CycleSieveSequence
  ): Boolean = {
    require(PrimeUtils.primeValues(cycle.primes.list.list) == PrimeUtils.primeValues(spec.primes.list.list))

    assert(assertHeadsMatchFromPrimeValues(spec, cycle))
    assert(spec(BigInt(0)) == spec.head.value)
    assert(cycle(BigInt(0)) == cycle.head)

    spec(BigInt(0)) == cycle(BigInt(0))
  }.holds

  /**
   * Exposes the positive-index branch of `CycleSieveSequence.apply`.
   *
   * The cycle implementation treats index 0 specially as the current head. Every
   * positive index is reconstructed by the stored `CycleIntegral`, shifted by one
   * because integral position 0 corresponds to sequence index 1.
   */
  def assertCycleApplyPositiveIsIntegral(
    cycle: CycleSieveSequence,
    position: BigInt
  ): Boolean = {
    require(position > BigInt(0))

    cycle(position) == cycle.integral(position - BigInt(1))
  }.holds

  /**
   * Exposes the `CycleIntegral` stored by the cycle implementation.
   *
   * `CycleSieveSequence` defines its integral from the current head and the
   * stored gap cycle memory. Naming that equality locally lets later proofs
   * compare the Cycle-side integral with the Spec-side integral built from
   * `specGapCycle(period)` without repeatedly unfolding the class field.
   */
  def assertCycleIntegralUsesGapCycle(
                                       cycle: CycleSieveSequence
                                     ): Boolean = {
    cycle.integral == CycleIntegral(cycle.head, cycle.gapCycle.memCycle)
  }.holds

  /**
   * Proves positive-index apply equivalence from equal heads and equal gaps.
   *
   * This is the conditional checkpoint for the whole equivalence ticket. It
   * deliberately does not prove where the cycle-side gaps came from. Instead,
   * it states the smallest useful bridge: once the Spec stream and Cycle stream
   * have the same head and the same stored `MemCycle`, every positive `apply`
   * position is reconstructed by the same `CycleIntegral`.
   */
  def assertSpecCycleApplyPositiveMatchesFromSameHeadAndGaps(
    spec: SpecSieveSequence,
    cycle: CycleSieveSequence,
    period: BigInt,
    position: BigInt
  ): Boolean = {
    require(position > BigInt(0))
    require(period > BigInt(0))
    require(spec(period) == spec.head.value + spec.filterModulus)
    require(spec.head.value == cycle.head)
    require(spec.specGapCycle(period).memCycle == cycle.gapCycle.memCycle)

    val specGapCycle = spec.specGapCycle(period)
    val specIntegral = CycleIntegral(spec.head.value, specGapCycle.memCycle)

    assert(spec.assertSpecGapCycleIntegralMatchesApply(period, position))
    assert(assertCycleApplyPositiveIsIntegral(cycle, position))
    assert(assertCycleIntegralUsesGapCycle(cycle))
    assert(specIntegral == cycle.integral)

    spec(position) == cycle(position)
  }.holds

  /**
   * Proves apply equivalence for every index from equal heads and equal gaps.
   *
   * This is the all-index wrapper around the positive-index theorem above. At
   * index 0 both sequences return their head. At every positive index, both
   * sequences are reconstructed from the same initial value and the same stored
   * `MemCycle`, so the positive theorem applies directly.
   */
  def assertSpecCycleApplyMatchesFromSameHeadAndGaps(
    spec: SpecSieveSequence,
    cycle: CycleSieveSequence,
    period: BigInt,
    position: BigInt
  ): Boolean = {
    require(position >= BigInt(0))
    require(period > BigInt(0))
    require(spec(period) == spec.head.value + spec.filterModulus)
    require(spec.head.value == cycle.head)
    require(spec.specGapCycle(period).memCycle == cycle.gapCycle.memCycle)

    if (position == BigInt(0)) {
      assert(spec(BigInt(0)) == spec.head.value)
      assert(cycle(BigInt(0)) == cycle.head)
      spec(position) == cycle(position)
    } else {
      assert(
        assertSpecCycleApplyPositiveMatchesFromSameHeadAndGaps(
          spec,
          cycle,
          period,
          position
        )
      )
      spec(position) == cycle(position)
    }
  }.holds

  /**
   * Proves two cycles with the same head and gap cycle produce the same values.
   *
   * `apply(k)` is a deterministic function of `(head, gapCycle.memCycle)`.
   * Two cycles sharing both produce identical sequences at every position.
   */
  def assertCycleApplyMatchesFromSameHeadAndGaps(
    cycle1: CycleSieveSequence,
    cycle2: CycleSieveSequence,
    position: BigInt
  ): Boolean = {
    require(position >= BigInt(0))
    require(cycle1.head == cycle2.head)
    require(cycle1.gapCycle.memCycle == cycle2.gapCycle.memCycle)

    cycle1(position) == cycle2(position)
  }.holds

  /**
   * Exposes the raw-prime shape of `SpecSieveSequence.next`.
   *
   * The Spec next stage is built by prepending `spec.primes.nextPrime` to the
   * current complete-prime prefix. On the raw `BigInt` representation used by
   * `CycleSieveSequence`, that means the next Spec prime list has the next head
   * value at the front and the current Spec prime values as its tail.
   */
  def assertSpecNextPrimeValuesExtendCurrent(
    spec: SpecSieveSequence
  ): Boolean = {
    require(spec.primes.nextPrime.value < spec.head.value * spec.head.value)

    val nextSpec = spec.next
    val currentValues = PrimeUtils.primeValues(spec.primes.list.list)
    val nextValues = PrimeUtils.primeValues(nextSpec.primes.list.list)

    assert(nextValues.head == nextSpec.head.value)
    assert(nextValues.tail == currentValues)

    nextValues == nextSpec.head.value :: currentValues
  }.holds

  /**
   * Bridges the raw prime-list shape of the conditional next stage.
   *
   * This lemma does not prove that the cycle-side `apply(1)` is the Spec next
   * prime. That is the hard next-head theorem we still want to isolate. Instead,
   * it follows the conditional style used by `SpecSieveSequence.next` and
   * `CycleSieveSequence.nextWithGapCycle`: if the caller supplies that next-head
   * equality, and if the supplied gap cycle satisfies the constructor
   * obligations required by `nextWithGapCycle`, then the next Cycle stage stores
   * exactly the same raw prime values as `spec.next`.
   */
  def assertConditionalNextPrimeValuesMatch(
    spec: SpecSieveSequence,
    cycle: CycleSieveSequence,
    newGapCycle: GapCycle
  ): Boolean = {
    require(PrimeUtils.primeValues(cycle.primes.list.list) == PrimeUtils.primeValues(spec.primes.list.list))
    require(spec.primes.nextPrime.value < spec.head.value * spec.head.value)
    require(cycle.apply(BigInt(1)) == spec.next.head.value)
    require(SieveUtils.isCoprime(cycle.apply(BigInt(1)) + newGapCycle.memCycle(0), cycle.primesValues))
    require(Calc.mod(cycle.apply(BigInt(1)) + newGapCycle.memCycle(0), cycle.apply(BigInt(1))) != BigInt(0))
    require(Calc.mod(cycle.primorial, cycle.apply(BigInt(1))) != BigInt(0))

    val nextSpec = spec.next
    val nextCycle = cycle.nextWithGapCycle(newGapCycle)

    assert(assertSpecNextPrimeValuesExtendCurrent(spec))
    assert(PrimeUtils.primeValues(nextCycle.primes.list.list) ==
      PrimeUtils.primeValues(nextSpec.primes.list.list))

    PrimeUtils.primeValues(nextCycle.primes.list.list) ==
      PrimeUtils.primeValues(nextSpec.primes.list.list)
  }.holds

  def assertConditionalNextApplyMatchesFromSameHeadAndGaps(
    spec: SpecSieveSequence,
    cycle: CycleSieveSequence,
    newGapCycle: GapCycle,
    nextPeriod: BigInt,
    position: BigInt
  ): Boolean = {
    require(position >= BigInt(0))
    require(nextPeriod > BigInt(0))
    require(PrimeUtils.primeValues(cycle.primes.list.list) == PrimeUtils.primeValues(spec.primes.list.list))
    require(spec.primes.nextPrime.value < spec.head.value * spec.head.value)
    require(cycle.apply(BigInt(1)) == spec.next.head.value)
    require(SieveUtils.isCoprime(cycle.apply(BigInt(1)) + newGapCycle.memCycle(0), cycle.primesValues))
    require(Calc.mod(cycle.apply(BigInt(1)) + newGapCycle.memCycle(0), cycle.apply(BigInt(1))) != BigInt(0))
    require(Calc.mod(cycle.primorial, cycle.apply(BigInt(1))) != BigInt(0))

    val nextSpec = spec.next
    val nextCycle = cycle.nextWithGapCycle(newGapCycle)

    require(nextSpec(nextPeriod) == nextSpec.head.value + nextSpec.filterModulus)
    require(nextSpec.specGapCycle(nextPeriod).memCycle == nextCycle.gapCycle.memCycle)

    assert(assertConditionalNextPrimeValuesMatch(spec, cycle, newGapCycle))
    assert(PrimeUtils.primeValues(nextCycle.primes.list.list) == PrimeUtils.primeValues(nextSpec.primes.list.list))
    assert(assertHeadsMatchFromPrimeValues(nextSpec, nextCycle))
    assert(nextSpec.head.value == nextCycle.head)
    assert(
      assertSpecCycleApplyMatchesFromSameHeadAndGaps(
        nextSpec,
        nextCycle,
        nextPeriod,
        position
      )
    )

    nextSpec(position) == nextCycle(position)
  }.holds

  /**
   * Proves the current Cycle `apply(1)` equals the next Spec stage head.
   *
   * Under the current-stage equivalence assumptions (same head, same gap cycle)
   * and the Spec next precondition, the Cycle-side first generated value equals
   * the Spec-side next head. This is item 1 of the "Work On These Next" list.
   */
  def assertCurrentApplyOneEqualsSpecNextHead(
    spec: SpecSieveSequence,
    cycle: CycleSieveSequence,
    period: BigInt
  ): Boolean = {
    require(period > BigInt(0))
    require(spec(period) == spec.head.value + spec.filterModulus)
    require(spec.head.value == cycle.head)
    require(spec.specGapCycle(period).memCycle == cycle.gapCycle.memCycle)
    require(spec.primes.nextPrime.value < spec.head.value * spec.head.value)

    assert(assertSpecCycleApplyMatchesFromSameHeadAndGaps(spec, cycle, period, BigInt(1)))
    assert(spec(BigInt(1)) == cycle(BigInt(1)))

    assert(spec.assertApplyOneEqualsNextPrime())
    assert(spec(BigInt(1)) == spec.next.head.value)

    cycle(BigInt(1)) == spec.next.head.value
  }.holds

  /**
   * Proves the next-stage acceptance predicate matches cycle-side coprimality.
   *
   * The next Spec stage filters by the current stage's full prime list (the
   * current primes minus the new head, which is `cycle.primes` on the cycle
   * side). Under the prime-list correspondence and the next() precondition:
   *
   * spec.next.accepts(value) == SieveUtils.isCoprime(value, cycle.primes)
   *
   * This is item 2 of the "Work On These Next" list.
   */
  def assertNextAcceptsMatchesCyclePrimesCoprime(
    spec: SpecSieveSequence,
    cycle: CycleSieveSequence,
    value: BigInt
  ): Boolean = {
    require(PrimeUtils.primeValues(cycle.primes.list.list) == PrimeUtils.primeValues(spec.primes.list.list))
    require(spec.primes.nextPrime.value < spec.head.value * spec.head.value)
    require(value >= spec.next.head.value)

    assert(spec.primes.list.list.nonEmpty)
    assert(spec.next.primes.list.tail.list == spec.primes.list.list)
    assert(spec.next.filterPrimes == spec.next.primes.list.tail.list)
    assert(spec.next.filterValues == PrimeUtils.primeValues(spec.next.filterPrimes))
    assert(spec.next.filterValues == PrimeUtils.primeValues(spec.primes.list.list))
    assert(spec.next.filterValues == PrimeUtils.primeValues(cycle.primes.list.list))

    spec.next.accepts(value) == SieveUtils.isCoprime(value, PrimeUtils.primeValues(cycle.primes.list.list))
  }.holds

  /**
   * Proves the walked gap list contains only positive values.
   *
   * This uses the `.ensuring` postcondition of `nextGapsWalk`, which
   * delegates to `collectGaps`'s `.ensuring`.
   */
  def assertWalkGapsAllPositive(cycle: CycleSieveSequence): Boolean = {
    val walkedGaps = SieveSequenceNextLevel.nextGapsWalk(cycle)
    ListBoundUtils.allGreaterThan(walkedGaps, BigInt(0))
  }.holds

  /**
   * Converts the prime-list correspondence assumption into filter equality.
   *
   * The cycle sequence keeps the head prime at `cycle.primes.head`, so its
   * active filters are `cycle.primes.tail`. The Spec sequence names the same
   * active filters as `spec.filterValues`. When the full prime lists correspond,
   * these two filter lists are equal.
   */
  def assertFilterValuesMatchTailPrimes(
    spec: SpecSieveSequence,
    cycle: CycleSieveSequence
  ): Boolean = {
    require(PrimeUtils.primeValues(cycle.primes.list.list) == PrimeUtils.primeValues(spec.primes.list.list))

    assert(spec.primes.list.list.nonEmpty)
    assert(
      PrimeUtils.primeValues(spec.primes.list.list).tail ==
        PrimeUtils.primeValues(spec.primes.list.list.tail)
    )
    assert(spec.filterPrimes == spec.primes.list.list.tail)
    assert(spec.filterValues == PrimeUtils.primeValues(spec.primes.list.list.tail))
    assert(cycle.primesTailValues == spec.filterValues)

    cycle.primesTailValues == spec.filterValues
  }.holds

  /**
   * Rewrites Spec acceptance into the cycle-side tail-coprime predicate.
   *
   * This is the first semantic bridge after the representation bridges above.
   * Spec acceptance is defined as "at or above the head and coprime to
   * `spec.filterValues`". Once the prime-list correspondence tells us that
   * `cycle.primes.tail` is the same list as `spec.filterValues`, the arithmetic
   * predicate is literally the same one used by the cycle-side residue pipeline.
   */
  def assertSpecAcceptsMatchesCycleTailCoprime(
    spec: SpecSieveSequence,
    cycle: CycleSieveSequence,
    value: BigInt
  ): Boolean = {
    require(PrimeUtils.primeValues(cycle.primes.list.list) == PrimeUtils.primeValues(spec.primes.list.list))
    require(value >= spec.head.value)

    assert(assertFilterValuesMatchTailPrimes(spec, cycle))
    assert(cycle.primesTailValues == spec.filterValues)
    assert(spec.accepts(value) == SieveUtils.isCoprime(value, spec.filterValues))

    spec.accepts(value) == SieveUtils.isCoprime(value, cycle.primesTailValues)
  }.holds

  /**
   * Exposes one-value completeness of the residue list.
   *
   * The residue pipeline starts by enumerating every value in
   * `[0, modulus)` that is coprime to the filter list. `SieveUtils` already
   * verifies this through `assertGenerateResiduesContainsCoprime`; this local
   * alias names the exact shape needed by the Spec/Cycle equivalence proof.
   *
   * This is only the completeness half of the "residues are exactly coprime"
   * property: if a residue passes the filter, then the generated residue list
   * contains it. The soundness half, from membership back to coprimality, should
   * stay separate so Stainless can verify each direction independently.
   */
  def assertResiduesContainCoprimeBelowModulus(
    modulus: BigInt,
    filters: stainless.collection.List[BigInt],
    residue: BigInt
  ): Boolean = {
    require(residue >= BigInt(0))
    require(residue < modulus)
    require(modulus > BigInt(0))
    require(ListUtils.checkAllPositive(filters))
    require(SieveUtils.isCoprime(residue, filters))

    assert(SieveUtils.assertGenerateResiduesContainsCoprime(
      residue,
      BigInt(0),
      modulus,
      filters
    ))

    SieveUtils.residues(modulus, filters).contains(residue)
  }.holds

  /**
   * Proves one-value soundness for the recursive residue generator.
   *
   * `generateResidues(from, modulus, filters)` walks forward from `from` to
   * `modulus`, adding a value exactly when it is coprime to `filters`. This
   * helper exposes the membership direction of that construction: any value
   * found in the generated list must have passed the same coprime test.
   *
   * The public `residues` function is just `generateResidues(0, ...)`; keeping
   * this recursive helper separate makes the later top-level soundness alias a
   * direct call instead of a proof that has to rediscover the generator's shape.
   */
  def assertGenerateResiduesContainOnlyCoprime(
    modulus: BigInt,
    filters: stainless.collection.List[BigInt],
    residue: BigInt,
    from: BigInt
  ): Boolean = {
    require(from >= BigInt(0))
    require(from <= modulus)
    require(modulus > BigInt(0))
    require(ListUtils.checkAllPositive(filters))
    require(SieveUtils.generateResidues(from, modulus, filters).contains(residue))
    decreases(modulus - from)

    if (from == modulus) {
      false
    } else {
      val rest = SieveUtils.generateResidues(from + BigInt(1), modulus, filters)
      if (SieveUtils.isCoprime(from, filters)) {
        if (residue == from) {
          SieveUtils.isCoprime(residue, filters)
        } else {
          assert(rest.contains(residue))
          assert(assertGenerateResiduesContainOnlyCoprime(modulus, filters, residue, from + BigInt(1)))
          SieveUtils.isCoprime(residue, filters)
        }
      } else {
        assert(rest.contains(residue))
        assert(assertGenerateResiduesContainOnlyCoprime(modulus, filters, residue, from + BigInt(1)))
        SieveUtils.isCoprime(residue, filters)
      }
    }
  }.holds

  /**
   * One-value soundness for the public `residues` function.
   *
   * If `residues(modulus, filters)` contains `residue`, then
   * `SieveUtils.isCoprime(residue, filters)` holds. This is the soundness
   * counterpart to `assertResiduesContainCoprimeBelowModulus`.
   *
   * The proof delegates to `assertGenerateResiduesContainOnlyCoprime` which
   * performs the same induction over the generator's structure.
   */
  def assertResiduesAreCoprimeBelowModulus(
    modulus: BigInt,
    filters: stainless.collection.List[BigInt],
    residue: BigInt
  ): Boolean = {
    require(residue >= BigInt(0))
    require(residue < modulus)
    require(modulus > BigInt(0))
    require(ListUtils.checkAllPositive(filters))
    require(SieveUtils.residues(modulus, filters).contains(residue))

    assert(SieveUtils.generateResidues(BigInt(0), modulus, filters) ==
      SieveUtils.residues(modulus, filters))
    assert(SieveUtils.generateResidues(BigInt(0), modulus, filters).contains(residue))
    assert(assertGenerateResiduesContainOnlyCoprime(modulus, filters, residue, BigInt(0)))

    SieveUtils.isCoprime(residue, filters)
  }.holds

  /**
   * Per-prime variant: if `v` is coprime to `p` and `p` divides `modulus`,
   * then `Calc.mod(v, modulus)` is also coprime to `p`.
   *
   * The proof uses `DivMod` to decompose `v = q*modulus + r`, then uses
   * `modAdd` with `assertMultiplePreservesDivisible` to show
   * `Calc.mod(v, p) == Calc.mod(r, p)`, which preserves the non-zero status.
   */
  def assertModPreservesCoprimeForPrime(
    v: BigInt,
    modulus: BigInt,
    p: BigInt
  ): Boolean = {
    require(v >= BigInt(0))
    require(modulus > BigInt(0))
    require(p > BigInt(0))
    require(Calc.mod(modulus, p) == BigInt(0))
    require(Calc.mod(v, p) != BigInt(0))

    val dm = DivMod(v, modulus, BigInt(0), v).solve
    val r = dm.mod

    assert(SieveUtils.assertMultiplePreservesDivisible(dm.div, modulus, p))
    assert(Calc.mod(dm.div * modulus, p) == BigInt(0))
    assert(ModOperations.modAdd(dm.div * modulus, p, r))
    assert(ModIdempotence.modIdempotence(r, p))

    Calc.mod(r, p) != BigInt(0)
  }.holds

  /**
   * Per-list variant: checks every prime in `remaining` individually.
   *
   * For each prime `p` in `remaining`, uses `assertAllFromPrefix(prefixProd, remaining)`
   * to get `Calc.mod(prefixProd * product(remaining), p) == 0`, then lifts this to
   * `Calc.mod(modulus, p) == 0` via `assertMultiplePreservesDivisible` with the
   * known product of the prefix primes. This avoids the impossible precondition
   * `modulus == product(remaining)` on the recursive call.
   */
  def assertModPreservesCoprimeRec(
    v: BigInt,
    modulus: BigInt,
    prefixProd: BigInt,
    remaining: stainless.collection.List[BigInt]
  ): Boolean = {
    require(v >= BigInt(0))
    require(modulus > BigInt(0))
    require(prefixProd > BigInt(0))
    require(ListUtils.checkAllPositive(remaining))
    require(modulus == prefixProd * SieveUtils.product(remaining))
    require(SieveUtils.isCoprime(v, remaining))
    decreases(remaining.size)

    val dm = DivMod(v, modulus, BigInt(0), v).solve
    val r = dm.mod

    if (remaining.isEmpty) {
      SieveUtils.isCoprime(r, remaining)
    } else {
      val p = remaining.head
      assert(SieveUtils.assertHeadDividesProduct(remaining))
      assert(Calc.mod(SieveUtils.product(remaining), p) == BigInt(0))
      assert(SieveUtils.assertMultiplePreservesDivisible(prefixProd, SieveUtils.product(remaining), p))
      assert(Calc.mod(modulus, p) == BigInt(0))
      assert(SieveUtils.assertIsCoprimeForAll(v, remaining))
      assert(Calc.mod(v, p) != BigInt(0))

      assert(assertModPreservesCoprimeForPrime(v, modulus, p))
      assert(Calc.mod(r, p) != BigInt(0))

      val tailOk = assertModPreservesCoprimeRec(v, modulus, prefixProd * p, remaining.tail)
      assert(tailOk)
      SieveUtils.isCoprime(r, remaining)
    }
  }.holds

  /**
   * Proves that `mod` preserves coprimality.
   *
   * If `v` is coprime to every prime in `primes`, and `modulus` is the product
   * of those same primes, then `Calc.mod(v, modulus)` is also coprime to
   * `primes`. This holds because any prime `p` dividing `Calc.mod(v, modulus)`
   * would also divide `v` (since `v = q*modulus + r` and `p | modulus`).
   */
  def assertModPreservesCoprime(
    v: BigInt,
    modulus: BigInt,
    primes: stainless.collection.List[BigInt]
  ): Boolean = {
    require(v >= BigInt(0))
    require(modulus > BigInt(0))
    require(ListUtils.checkAllPositive(primes))
    require(modulus == SieveUtils.product(primes))
    require(SieveUtils.isCoprime(v, primes))

    val dm = DivMod(v, modulus, BigInt(0), v).solve
    val r = dm.mod

    assert(assertModPreservesCoprimeRec(v, modulus, BigInt(1), primes))
    SieveUtils.isCoprime(r, primes)
  }.holds

  /**
   * Exposes expanded-value coprimality as a reusable postcondition.
   *
   * If `r` is coprime to every remaining prime and `modulus` is a positive
   * multiple of each of those primes, then adding `i * modulus` cannot make the
   * value divisible by any remaining prime. The `prefixProd` parameter carries
   * the product of primes already consumed by the recursion, matching the shape
   * used by `SieveUtils.assertExpandedCoprimeViaPrefix`.
   */
  private def assertExpandedValueCoprimeViaPrefix(
    r: BigInt,
    i: BigInt,
    modulus: BigInt,
    primes: stainless.collection.List[BigInt],
    prefixProd: BigInt
  ): Boolean = {
    require(i >= BigInt(0))
    require(modulus > BigInt(0))
    require(prefixProd > BigInt(0))
    require(ListUtils.checkAllPositive(primes))
    require(modulus == prefixProd * SieveUtils.product(primes))
    require(SieveUtils.isCoprime(r, primes))
    decreases(primes.size)

    val expanded = r + i * modulus

    if (primes.isEmpty) {
      SieveUtils.isCoprime(expanded, primes)
    } else {
      val p = primes.head
      val factor = prefixProd * SieveUtils.product(primes.tail)
      assert(SieveUtils.assertProductNonNegative(primes.tail))
      assert(SieveUtils.product(primes.tail) >= BigInt(0))
      assert(factor >= BigInt(0))
      assert(SieveUtils.assertMultipleModZero(factor, p))
      assert(Calc.mod(modulus, p) == BigInt(0))
      assert(SieveUtils.assertIsCoprimeForAll(r, primes))
      assert(Calc.mod(r, p) != BigInt(0))
      assert(SieveUtils.assertMultiplePreservesDivisible(i, modulus, p))
      assert(Calc.mod(i * modulus, p) == BigInt(0))
      assert(SieveUtils.assertAddPreservesNotZeroMod(r, p, i * modulus))
      assert(Calc.mod(expanded, p) != BigInt(0))
      assert(
        assertExpandedValueCoprimeViaPrefix(
          r,
          i,
          modulus,
          primes.tail,
          prefixProd * p
        )
      )

      SieveUtils.isCoprime(expanded, primes)
    }
  }.holds

  /**
   * Natural-shape wrapper for expanded-value coprimality.
   *
   * This is the caller-facing form of `assertExpandedValueCoprimeViaPrefix`:
   * when `modulus` is exactly the product of the prime filter list, every
   * expanded value `r + i * modulus` preserves coprimality with that list.
   */
  private def assertExpandedValueCoprime(
    r: BigInt,
    i: BigInt,
    modulus: BigInt,
    primes: stainless.collection.List[BigInt]
  ): Boolean = {
    require(i >= BigInt(0))
    require(modulus > BigInt(0))
    require(ListUtils.checkAllPositive(primes))
    require(modulus == SieveUtils.product(primes))
    require(SieveUtils.isCoprime(r, primes))

    assert(assertExpandedValueCoprimeViaPrefix(r, i, modulus, primes, BigInt(1)))
    SieveUtils.isCoprime(r + i * modulus, primes)
  }.holds

  /**
   * Proves soundness for one generated residue offset block.
   *
   * `generateResidues(from, modulus, primes)` only keeps residues that are
   * coprime to `primes`. After adding `i * modulus` to every kept residue, each
   * resulting value is still coprime to `primes` by
   * `assertExpandedValueCoprime`.
   */
  private def assertGeneratedOffsetContainsOnlyCoprime(
    modulus: BigInt,
    primes: stainless.collection.List[BigInt],
    value: BigInt,
    from: BigInt,
    i: BigInt
  ): Boolean = {
    require(from >= BigInt(0))
    require(from <= modulus)
    require(i >= BigInt(0))
    require(modulus > BigInt(0))
    require(ListUtils.checkAllPositive(primes))
    require(modulus == SieveUtils.product(primes))
    require(
      SieveUtils.addOffset(
        SieveUtils.generateResidues(from, modulus, primes),
        i * modulus
      ).contains(value)
    )
    decreases(modulus - from)

    val offset = i * modulus

    if (from == modulus) {
      false
    } else {
      val rest = SieveUtils.generateResidues(from + BigInt(1), modulus, primes)
      if (SieveUtils.isCoprime(from, primes)) {
        if (value == from + offset) {
          assert(assertExpandedValueCoprime(from, i, modulus, primes))
          SieveUtils.isCoprime(value, primes)
        } else {
          assert(SieveUtils.addOffset(rest, offset).contains(value))
          assert(
            assertGeneratedOffsetContainsOnlyCoprime(
              modulus,
              primes,
              value,
              from + BigInt(1),
              i
            )
          )
          SieveUtils.isCoprime(value, primes)
        }
      } else {
        assert(SieveUtils.addOffset(rest, offset).contains(value))
        assert(
          assertGeneratedOffsetContainsOnlyCoprime(
            modulus,
            primes,
            value,
            from + BigInt(1),
            i
          )
        )
        SieveUtils.isCoprime(value, primes)
      }
    }
  }.holds

  /**
   * Proves that addOffset preserves membership.
   *
   * If `list` contains `x`, then adding `offset` to every element of `list`
   * produces a list that contains `x + offset`.
   */
  private def assertAddOffsetContains(
    list: stainless.collection.List[BigInt],
    x: BigInt,
    offset: BigInt
  ): Boolean = {
    require(list.contains(x))
    require(offset >= BigInt(0))
    decreases(list.size)
    if (list.isEmpty) {
      false
    } else if (list.head == x) {
      SieveUtils.addOffset(list, offset).contains(x + offset)
    } else {
      assert(list.tail.contains(x))
      assert(assertAddOffsetContains(list.tail, x, offset))
      SieveUtils.addOffset(list, offset).contains(x + offset)
    }
  }.holds

  /**
   * Proves that `left ++ right` contains every element of `right`.
   */
  private def assertAppendContainsRight(
    left: stainless.collection.List[BigInt],
    right: stainless.collection.List[BigInt],
    x: BigInt
  ): Boolean = {
    require(right.contains(x))
    decreases(left.size)
    if (left.isEmpty) {
      (left ++ right).contains(x)
    } else {
      assert(assertAppendContainsRight(left.tail, right, x))
      (left ++ right).contains(x)
    }
  }.holds

  /**
   * Proves that `expandSingleResidue` at position `i` contains `r + i * mod`.
   */
  private def assertExpandSingleResidueContains(
    residues: stainless.collection.List[BigInt],
    r: BigInt,
    mod: BigInt,
    p: BigInt,
    i: BigInt
  ): Boolean = {
    require(residues.contains(r))
    require(mod > BigInt(0))
    require(p > BigInt(0))
    require(i >= BigInt(0))
    require(i < p)
    decreases(p - i)

    val offset = i * mod
    val currentSet = SieveUtils.addOffset(residues, offset)
    assert(assertAddOffsetContains(residues, r, offset))
    assert(currentSet.contains(r + offset))

    if (i + BigInt(1) >= p) {
      SieveUtils.expandSingleResidue(residues, mod, p, i).contains(r + offset)
    } else {
      val rest = SieveUtils.expandSingleResidue(residues, mod, p, i + BigInt(1))
      SieveUtils.expandSingleResidue(residues, mod, p, i).contains(r + offset)
    }
  }.holds

  /**
   * Proves that `expandResidues` contains every value `r + q * mod` for
   * `r ∈ residues` and `0 ≤ q < p`.
   */
  private def assertExpandResiduesContainsShifted(
    residues: stainless.collection.List[BigInt],
    r: BigInt,
    mod: BigInt,
    p: BigInt,
    q: BigInt
  ): Boolean = {
    require(residues.contains(r))
    require(mod > BigInt(0))
    require(p > BigInt(0))
    require(q >= BigInt(0))
    require(q < p)

    assert(assertExpandSingleResidueContains(residues, r, mod, p, BigInt(0)))
    assert(assertExpandSingleResidueContains(residues, r, mod, p, q))
    assert(assertExpandResiduesExtendsTo(residues, mod, p, BigInt(0), q, r + q * mod))

    SieveUtils.expandResidues(residues, mod, p).contains(r + q * mod)
  }.holds

  /**
   * Proves that `expandSingleResidue(..., i).contains(x)` implies
   * `expandSingleResidue(..., j).contains(x)` for any `j ≤ i ≤ p`.
   * Used to propagate membership from deeper levels to the top level.
   */
  private def assertExpandResiduesExtendsTo(
    residues: stainless.collection.List[BigInt],
    mod: BigInt,
    p: BigInt,
    i: BigInt,
    q: BigInt,
    x: BigInt
  ): Boolean = {
    require(mod > BigInt(0))
    require(p > BigInt(0))
    require(i >= BigInt(0))
    require(i <= q)
    require(q < p)
    require(SieveUtils.expandSingleResidue(residues, mod, p, q).contains(x))
    decreases(q - i)

    if (i == q) {
      SieveUtils.expandSingleResidue(residues, mod, p, i).contains(x)
    } else {
      val currentSet = SieveUtils.addOffset(residues, i * mod)
      val rest = SieveUtils.expandSingleResidue(residues, mod, p, i + BigInt(1))
      assert(assertExpandResiduesExtendsTo(residues, mod, p, i + BigInt(1), q, x))
      assert(rest.contains(x))
      assert(assertAppendContainsRight(currentSet, rest, x))
      SieveUtils.expandSingleResidue(residues, mod, p, i).contains(x)
    }
  }.holds

  /**
   * Proves the expanded residue set covers exactly one period of coprime values.
   *
   * Forward direction (already in `SieveUtils`): every value in the expanded set
   * is coprime to `seq.primes.tail` and bounded by `seq.head * seq.modulus`.
   *
   * Reverse direction (proved here): given a value `v` in
   * `[0, seq.head * seq.modulus)` that is coprime to `seq.primes.tail`, `v`
   * appears in `expandResidues(residues, seq.modulus, seq.head)`.
   */
  def assertExpandedResiduesRepresentPeriod(
    seq: CycleSieveSequence,
    value: BigInt
  ): Boolean = {
    require(value >= BigInt(0))
    require(value < seq.head * seq.modulus)
    require(SieveUtils.isCoprime(value, seq.primesTailValues))

    val residues = SieveUtils.residues(seq.modulus, seq.primesTailValues)
    val expanded = SieveUtils.expandResidues(residues, seq.modulus, seq.head)

    val dm = DivMod(value, seq.modulus, BigInt(0), value).solve
    val r = dm.mod
    val q = dm.div

    assert(r >= BigInt(0))
    assert(r < seq.modulus)
    assert(q >= BigInt(0))
    assert(q < seq.head)

    assert(primorialMatchesSieveProduct(seq.primes.list.tail.list))
    assert(seq.modulus == SieveUtils.product(seq.primesTailValues))
    assert(assertModPreservesCoprime(value, seq.modulus, seq.primesTailValues))
    assert(SieveUtils.isCoprime(r, seq.primesTailValues))

    assert(assertResiduesContainCoprimeBelowModulus(seq.modulus, seq.primesTailValues, r))
    assert(residues.contains(r))

    assert(assertExpandResiduesContainsShifted(residues, r, seq.modulus, seq.head, q))

    expanded.contains(value)
  }.holds

  /**
   * Forward membership for filterList: if `value ∈ list` and `value % divisor != 0`,
   * then `value ∈ filterList(list, divisor)`.
   */
  private def assertFilterListContainsIf(
    list: stainless.collection.List[BigInt],
    value: BigInt,
    divisor: BigInt
  ): Boolean = {
    require(divisor > BigInt(0))
    require(list.contains(value))
    require(Calc.mod(value, divisor) != BigInt(0))
    decreases(list.size)
    if (list.isEmpty) {
      false
    } else if (list.head == value) {
      SieveUtils.filterList(list, divisor).contains(value)
    } else {
      assert(list.tail.contains(value))
      assert(assertFilterListContainsIf(list.tail, value, divisor))
      SieveUtils.filterList(list, divisor).contains(value)
    }
  }.holds

  /**
   * Reverse membership for filterList: if `value ∈ filterList(list, divisor)`,
   * then `value ∈ list` and `value % divisor != 0`.
   */
  private def assertFilterListContainsOnlyIf(
    list: stainless.collection.List[BigInt],
    value: BigInt,
    divisor: BigInt
  ): Boolean = {
    require(divisor > BigInt(0))
    require(SieveUtils.filterList(list, divisor).contains(value))
    decreases(list.size)
    if (list.isEmpty) {
      false
    } else {
      val rest = SieveUtils.filterList(list.tail, divisor)
      if (Calc.mod(list.head, divisor) != BigInt(0)) {
        if (list.head == value) {
          Calc.mod(value, divisor) != BigInt(0) && list.contains(value)
        } else {
          assert(rest.contains(value))
          assert(assertFilterListContainsOnlyIf(list.tail, value, divisor))
          Calc.mod(value, divisor) != BigInt(0) && list.contains(value)
        }
      } else {
        assert(rest.contains(value))
        assert(assertFilterListContainsOnlyIf(list.tail, value, divisor))
        Calc.mod(value, divisor) != BigInt(0) && list.contains(value)
      }
    }
  }.holds

  /**
   * Reverse direction for nextFiltered: if `value` is in `[0, head*modulus)`
   * and coprime to `head :: primes.tail`, then `value ∈ nextFiltered(seq)`.
   *
   * Uses E2 to get `value ∈ nextExpanded(seq)`, then `assertFilterListContainsIf`
   * to propagate through `filterList`.
   */
  def assertNextFilteredContainsCoprime(
    seq: CycleSieveSequence,
    value: BigInt
  ): Boolean = {
    require(value >= BigInt(0))
    require(value < seq.head * seq.modulus)
    require(SieveUtils.isCoprime(value, seq.head :: seq.primesTailValues))

    val expanded = SieveSequenceNextLevel.nextExpanded(seq)

    assert(assertExpandedResiduesRepresentPeriod(seq, value))
    assert(expanded.contains(value))
    assert(Calc.mod(value, seq.head) != BigInt(0))
    assert(assertFilterListContainsIf(expanded, value, seq.head))

    SieveSequenceNextLevel.nextFiltered(seq).contains(value)
  }.holds

  /**
   * Proves that `insertSorted(x, list)` always contains `x`.
   */
  private def assertInsertSortedContainsSelf(
    x: BigInt,
    list: stainless.collection.List[BigInt]
  ): Boolean = {
    decreases(list.size)
    if (list.isEmpty) {
      SortedList.insertSorted(x, list).contains(x)
    } else if (x <= list.head) {
      SortedList.insertSorted(x, list).contains(x)
    } else {
      assert(assertInsertSortedContainsSelf(x, list.tail))
      SortedList.insertSorted(x, list).contains(x)
    }
  }.holds

  /**
   * Proves that `insertSorted` preserves existing membership.
   * If `list` contains `y`, then `insertSorted(x, list)` also contains `y`.
   */
  private def assertInsertSortedPreservesMembership(
    x: BigInt,
    list: stainless.collection.List[BigInt],
    y: BigInt
  ): Boolean = {
    require(list.contains(y))
    decreases(list.size)
    if (list.isEmpty) {
      false
    } else if (x <= list.head) {
      SortedList.insertSorted(x, list).contains(y)
    } else {
      if (list.head == y) {
        SortedList.insertSorted(x, list).contains(y)
      } else {
        assert(list.tail.contains(y))
        assert(assertInsertSortedPreservesMembership(x, list.tail, y))
        SortedList.insertSorted(x, list).contains(y)
      }
    }
  }.holds

  /**
   * Proves that `insertSorted` does not invent values.
   *
   * Any value found after inserting `x` was either already present in the
   * original list or is exactly `x`. This is the soundness counterpart to
   * `assertInsertSortedPreservesMembership`.
   */
  private def assertInsertSortedContainsOnlyExisting(
    x: BigInt,
    list: stainless.collection.List[BigInt],
    y: BigInt
  ): Boolean = {
    require(SortedList.insertSorted(x, list).contains(y))
    decreases(list.size)
    if (list.isEmpty) {
      y == x
    } else if (x <= list.head) {
      if (y == x) {
        true
      } else {
        assert(list.contains(y))
        list.contains(y) || y == x
      }
    } else {
      if (y == list.head) {
        list.contains(y) || y == x
      } else {
        assert(SortedList.insertSorted(x, list.tail).contains(y))
        assert(assertInsertSortedContainsOnlyExisting(x, list.tail, y))
        list.contains(y) || y == x
      }
    }
  }.holds

  /**
   * Proves that `sortFiltered` preserves membership.
   */
  private def assertSortFilteredContains(
    list: stainless.collection.List[BigInt],
    x: BigInt
  ): Boolean = {
    require(list.contains(x))
    decreases(list.size)
    if (list.isEmpty) {
      false
    } else if (list.head == x) {
      assert(assertInsertSortedContainsSelf(list.head, SortedList.sortFiltered(list.tail)))
      SortedList.sortFiltered(list).contains(x)
    } else {
      assert(list.tail.contains(x))
      assert(assertSortFilteredContains(list.tail, x))
      assert(assertInsertSortedPreservesMembership(list.head, SortedList.sortFiltered(list.tail), x))
      SortedList.sortFiltered(list).contains(x)
    }
  }.holds

  /**
   * Proves that `sortFiltered` does not invent values.
   *
   * Sorting repeatedly inserts the current head into the sorted tail. Since
   * `insertSorted` only contributes the inserted value or values already in the
   * tail, every value in the sorted output came from the original list.
   */
  private def assertSortFilteredContainsOnlyExisting(
    list: stainless.collection.List[BigInt],
    x: BigInt
  ): Boolean = {
    require(SortedList.sortFiltered(list).contains(x))
    decreases(list.size)
    if (list.isEmpty) {
      false
    } else {
      val sortedTail = SortedList.sortFiltered(list.tail)
      assert(assertInsertSortedContainsOnlyExisting(list.head, sortedTail, x))
      if (x == list.head) {
        list.contains(x)
      } else {
        assert(sortedTail.contains(x))
        assert(assertSortFilteredContainsOnlyExisting(list.tail, x))
        list.contains(x)
      }
    }
  }.holds

  /**
   * Proves that `nextSorted(seq)` contains every coprime bounded value.
   *
   * Note: currently unused (no callers). Retained as a working lemma; one of
   * its VCs times out in the full-chapter run — see ticket
   * `fix-ch6-timeout-file-by-file.md`.
   */
  def assertNextSortedContainsCoprime(
    seq: CycleSieveSequence,
    value: BigInt
  ): Boolean = {
    require(value >= BigInt(0))
    require(value < seq.head * seq.modulus)
    require(SieveUtils.isCoprime(value, seq.head :: seq.primesTailValues))

    assert(assertNextFilteredContainsCoprime(seq, value))
    assert(SieveSequenceNextLevel.nextFiltered(seq).contains(value))
    assert(assertSortFilteredContains(SieveSequenceNextLevel.nextFiltered(seq), value))

    SieveSequenceNextLevel.nextSorted(seq).list.contains(value)
  }.holds

  /**
   * Forward membership for the sorted pipeline stage.
   *
   * `nextSorted` is only `nextFiltered` wrapped by `SortedList.fromUnsorted`.
   * This lemma exposes the one-value soundness direction: sorting may reorder
   * survivors, but it does not create any new survivor value.
   *
   * Note: currently unused (no callers). Retained as a working lemma; several
   * of its precondition VCs time out in the full-chapter run — see ticket
   * `fix-ch6-timeout-file-by-file.md`.
   */
  def assertNextSortedOnlyContainsFiltered(
    seq: CycleSieveSequence,
    value: BigInt
  ): Boolean = {
    require(seq.modulus > 0)
    require(SieveSequenceNextLevel.nextSorted(seq).list.contains(value))

    assert(assertSortFilteredContainsOnlyExisting(SieveSequenceNextLevel.nextFiltered(seq), value))
    SieveSequenceNextLevel.nextFiltered(seq).contains(value)
  }.holds
}
