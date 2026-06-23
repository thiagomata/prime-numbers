package v1.chapter6.seq.sieve

import stainless.lang.*
import v1.chapter2.div.{Calc, DivMod}
import v1.chapter2.div.properties.{ModIdempotence, ModOperations}
import v1.chapter3.list.ListUtils
import v1.chapter4.cycle.gap.GapCycle
import v1.chapter4.cycle.integral.recursive.CycleIntegral
import v1.chapter5.prime.PrimeUtils

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
    require(cycle.primes == PrimeUtils.primeValues(spec.primes.list.list))

    assert(spec.primes.list.list.nonEmpty)
    assert(PrimeUtils.primeValues(spec.primes.list.list).head == spec.head.value)
    assert(cycle.primes.head == spec.head.value)

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
    require(cycle.primes == PrimeUtils.primeValues(spec.primes.list.list))

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
    require(cycle.primes == PrimeUtils.primeValues(spec.primes.list.list))
    require(spec.primes.nextPrime.value < spec.head.value * spec.head.value)
    require(cycle.apply(BigInt(1)) == spec.next.head.value)
    require(SieveUtils.isCoprime(cycle.apply(BigInt(1)) + newGapCycle.memCycle(0), cycle.primes))
    require(Calc.mod(cycle.apply(BigInt(1)) + newGapCycle.memCycle(0), cycle.apply(BigInt(1))) != BigInt(0))
    require(Calc.mod(SieveUtils.product(cycle.primes), cycle.apply(BigInt(1))) != BigInt(0))

    val nextSpec = spec.next
    val nextCycle = cycle.nextWithGapCycle(newGapCycle)

    assert(assertSpecNextPrimeValuesExtendCurrent(spec))
    assert(PrimeUtils.primeValues(nextSpec.primes.list.list) == nextSpec.head.value :: PrimeUtils.primeValues(spec.primes.list.list))
    assert(nextCycle.primes == cycle.apply(BigInt(1)) :: cycle.primes)
    assert(nextCycle.primes == nextSpec.head.value :: PrimeUtils.primeValues(spec.primes.list.list))

    nextCycle.primes == PrimeUtils.primeValues(nextSpec.primes.list.list)
  }.holds

  /**
   * Proves next-stage apply equivalence for the verified conditional path.
   *
   * This lemma deliberately avoids `CycleSieveSequence.next()`, because that
   * method is still `@extern` and would be opaque to Stainless. Instead it uses
   * `nextWithGapCycle`, whose constructor path is verified under explicit
   * preconditions.
   *
   * The remaining hard facts are named as assumptions: the Cycle-side next head
   * must be the Spec next head, and the supplied gap cycle must match the Spec
   * next gap cycle for the requested period. Under those assumptions, the
   * previously verified same-head/same-gaps theorem proves equality for the
   * requested index.
   */
  def assertConditionalNextApplyMatchesFromSameHeadAndGaps(
    spec: SpecSieveSequence,
    cycle: CycleSieveSequence,
    newGapCycle: GapCycle,
    nextPeriod: BigInt,
    position: BigInt
  ): Boolean = {
    require(position >= BigInt(0))
    require(nextPeriod > BigInt(0))
    require(cycle.primes == PrimeUtils.primeValues(spec.primes.list.list))
    require(spec.primes.nextPrime.value < spec.head.value * spec.head.value)
    require(cycle.apply(BigInt(1)) == spec.next.head.value)
    require(SieveUtils.isCoprime(cycle.apply(BigInt(1)) + newGapCycle.memCycle(0), cycle.primes))
    require(Calc.mod(cycle.apply(BigInt(1)) + newGapCycle.memCycle(0), cycle.apply(BigInt(1))) != BigInt(0))
    require(Calc.mod(SieveUtils.product(cycle.primes), cycle.apply(BigInt(1))) != BigInt(0))

    val nextSpec = spec.next
    val nextCycle = cycle.nextWithGapCycle(newGapCycle)

    require(nextSpec(nextPeriod) == nextSpec.head.value + nextSpec.filterModulus)
    require(nextSpec.specGapCycle(nextPeriod).memCycle == nextCycle.gapCycle.memCycle)

    assert(assertConditionalNextPrimeValuesMatch(spec, cycle, newGapCycle))
    assert(nextCycle.primes == PrimeUtils.primeValues(nextSpec.primes.list.list))
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
    require(cycle.primes == PrimeUtils.primeValues(spec.primes.list.list))

    assert(spec.primes.list.list.nonEmpty)
    assert(
      PrimeUtils.primeValues(spec.primes.list.list).tail ==
        PrimeUtils.primeValues(spec.primes.list.list.tail)
    )
    assert(spec.filterPrimes == spec.primes.list.list.tail)
    assert(spec.filterValues == PrimeUtils.primeValues(spec.primes.list.list.tail))
    assert(cycle.primes.tail == spec.filterValues)

    cycle.primes.tail == spec.filterValues
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
    require(cycle.primes == PrimeUtils.primeValues(spec.primes.list.list))
    require(value >= spec.head.value)

    assert(assertFilterValuesMatchTailPrimes(spec, cycle))
    assert(cycle.primes.tail == spec.filterValues)
    assert(spec.accepts(value) == SieveUtils.isCoprime(value, spec.filterValues))

    spec.accepts(value) == SieveUtils.isCoprime(value, cycle.primes.tail)
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
  private def assertModPreservesCoprimeForPrime(
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
  private def assertModPreservesCoprimeRec(
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
  private def assertModPreservesCoprime(
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
      // currentSet contains r + offset, and expandSingleResidue(..., i) starts with currentSet
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
    // assertExpandSingleResidueContains proves for i=0, which only contains r + 0*mod = r
    // I need r + q*mod for arbitrary q. The previous lemma only proves for i = q.
    
    // Actually, assertExpandSingleResidueContains proves expandSingleResidue(..., i).contains(r + i*mod)
    // So for i = q: expandSingleResidue(..., q).contains(r + q*mod)
    // But I need expandResidues(..., p).contains(r + q*mod)
    // expandResidues = expandSingleResidue(..., 0)
    // I need to show that expandSingleResidue(..., 0) contains all values from expandSingleResidue(..., q)
    
    // This requires the "++ preserves right-side membership" lemma iterated q times.
    assert(assertExpandSingleResidueContains(residues, r, mod, p, q))
    // expandSingleResidue(..., q).contains(r + q*mod)
    
    // Now I need to show that expandSingleResidue(..., 0) contains everything from expandSingleResidue(..., q)
    // By structural induction: expandSingleResidue(..., i) = currentSet ++ expandSingleResidue(..., i+1)
    // So expandSingleResidue(..., 0) = currentSet_0 ++ currentSet_1 ++ ... ++ currentSet_{q-1} ++ expandSingleResidue(..., q)
    // By q applications of assertAppendContainsRight, r + q*mod is in the result
    
    // I need a recursive helper for this
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
    require(SieveUtils.isCoprime(value, seq.primes.tail))

    val residues = SieveUtils.residues(seq.modulus, seq.primes.tail)
    val expanded = SieveUtils.expandResidues(residues, seq.modulus, seq.head)

    val dm = DivMod(value, seq.modulus, BigInt(0), value).solve
    val r = dm.mod
    val q = dm.div

    assert(r >= BigInt(0))
    assert(r < seq.modulus)
    assert(q >= BigInt(0))
    assert(q < seq.head)

    assert(assertModPreservesCoprime(value, seq.modulus, seq.primes.tail))
    assert(SieveUtils.isCoprime(r, seq.primes.tail))

    assert(assertResiduesContainCoprimeBelowModulus(seq.modulus, seq.primes.tail, r))
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
    require(SieveUtils.isCoprime(value, seq.head :: seq.primes.tail))

    val expanded = SieveSequenceNextLevel.nextExpanded(seq)

    assert(assertExpandedResiduesRepresentPeriod(seq, value))
    assert(expanded.contains(value))
    assert(Calc.mod(value, seq.head) != BigInt(0))
    assert(assertFilterListContainsIf(expanded, value, seq.head))

    SieveSequenceNextLevel.nextFiltered(seq).contains(value)
  }.holds

}
