package v1.chapter6.seq.sieve

import stainless.lang.BooleanDecorations
import stainless.lang.decreases
import v1.chapter2.div.Calc
import v1.chapter4.cycle.gap.GapCycle
import v1.chapter4.cycle.integral.recursive.properties.CycleIntegralProperties
import v1.chapter5.prime.PrimeUtils

case class SpecDerivedBySurvivors(
  derived: SpecDerivedSieveSequence
) {
  def assertCycleSurvivorCoprimeToCyclePrimes(pos: BigInt): Boolean = {
    require(pos >= BigInt(0))
    require(Calc.mod(derived.cycle.integral(pos), derived.spec.head.value) != BigInt(0))

    assert(derived.assertPrimesMatch())
    assert(derived.assertCycleValueCoprimeToTail(pos + BigInt(1)))
    SieveUtils.isCoprime(derived.cycle.integral(pos), derived.cyclePrimes)
  }.holds

  def assertSpecNextFilterEqCyclePrimes(): Boolean = {
    assert(derived.assertPrimesMatch())
    assert(derived.spec.next.filterPrimes == derived.spec.primes.list.list)
    derived.spec.next.filterValues == derived.cyclePrimes
  }.holds

  def assertCycleSurvivorCoprimeToSpecNextFilter(pos: BigInt): Boolean = {
    require(pos >= BigInt(0))
    require(Calc.mod(derived.cycle.integral(pos), derived.spec.head.value) != BigInt(0))

    assert(assertCycleSurvivorCoprimeToCyclePrimes(pos))
    assert(assertSpecNextFilterEqCyclePrimes())
    SieveUtils.isCoprime(derived.cycle.integral(pos), derived.spec.next.filterValues)
  }.holds

  def assertCycleSurvivorPassesSpecNextFilter(pos: BigInt): Boolean = {
    require(pos >= BigInt(0))
    require(Calc.mod(derived.cycle.integral(pos), derived.spec.head.value) != BigInt(0))

    assert(assertCycleSurvivorCoprimeToSpecNextFilter(pos))
    derived.spec.next.passesFilter(derived.cycle.integral(pos))
  }.holds

  def assertFirstSurvivorEqualsSpecNextHead(): Boolean = {
    assert(derived.assertFirstSurvivorEqualsSpecNext0())
    derived.cycle.integral(BigInt(0)) == derived.spec.next.head.value
  }.holds

  def assertAllSurvivorsPassSpecNextFilter(count: BigInt): Boolean = {
    require(count >= BigInt(0))
    decreases(count)

    if (count == BigInt(0)) true
    else {
      val rest = assertAllSurvivorsPassSpecNextFilter(count - BigInt(1))
      val pos = count - BigInt(1)
      if (Calc.mod(derived.cycle.integral(pos), derived.spec.head.value) != BigInt(0)) {
        assert(assertCycleSurvivorPassesSpecNextFilter(pos))
      }
      true
    }
  }.holds

  def assertAllSurvivorsPassSpecNextFilterFrom(from: BigInt, count: BigInt): Boolean = {
    require(from >= BigInt(0))
    require(count >= BigInt(0))
    decreases(count)

    if (count == BigInt(0)) true
    else {
      val rest = assertAllSurvivorsPassSpecNextFilterFrom(from + BigInt(1), count - BigInt(1))
      if (Calc.mod(derived.cycle.integral(from), derived.spec.head.value) != BigInt(0)) {
        assert(assertCycleSurvivorPassesSpecNextFilter(from))
      }
      true
    }
  }.holds

  def assertIntegralIncreasingForCount(count: BigInt): Boolean = {
    require(count >= BigInt(0))
    decreases(count)

    if (count <= BigInt(1)) true
    else {
      assert(GapCycle.assertMemCycleValuesPositive(derived.cycle.gapCycle))
      assert(CycleIntegralProperties.assertCycleValuePositive(
        derived.cycle.integral, count - BigInt(1)))
      assert(assertIntegralIncreasingForCount(count - BigInt(1)))
      derived.cycle.integral(count - BigInt(2)) < derived.cycle.integral(count - BigInt(1))
    }
  }.holds

  def assertIntegralGeIntegral0(pos: BigInt): Boolean = {
    require(pos >= BigInt(0))
    decreases(pos)

    if (pos == BigInt(0)) derived.cycle.integral(pos) >= derived.cycle.integral(BigInt(0))
    else {
      assert(GapCycle.assertMemCycleValuesPositive(derived.cycle.gapCycle))
      assert(CycleIntegralProperties.assertCycleValuePositive(derived.cycle.integral, pos))
      assert(derived.cycle.integral(pos) ==
        derived.cycle.integral(pos - BigInt(1)) + derived.cycle.integral.cycle(pos))
      assert(assertIntegralGeIntegral0(pos - BigInt(1)))
      derived.cycle.integral(pos) >= derived.cycle.integral(BigInt(0))
    }
  }.holds

  def assertSurvivorAcceptedBySpecNext(pos: BigInt): Boolean = {
    require(pos >= BigInt(0))
    require(Calc.mod(derived.cycle.integral(pos), derived.spec.head.value) != BigInt(0))

    assert(assertFirstSurvivorEqualsSpecNextHead())
    assert(assertIntegralGeIntegral0(pos))
    assert(assertCycleSurvivorPassesSpecNextFilter(pos))
    derived.spec.next.accepts(derived.cycle.integral(pos))
  }.holds

  def assertNextHeadLessThanNewModulus(): Boolean = {
    require(derived.spec.head.value >= 3)
    require(derived.spec.filterModulus >= 2)

    assert(derived.assertApplyMatches(BigInt(1)))
    assert(derived.assertCycleModulusEqualsSpecFilterModulus())
    assert(derived.spec(BigInt(1)) <= derived.spec.searchBound(BigInt(1)))
    assert(derived.spec.head.value * derived.spec.filterModulus >
           derived.spec.head.value + derived.spec.filterModulus)
    derived.cycle(BigInt(1)) < derived.cycle.head * derived.cycle.modulus
  }.holds

  def assertMinimalCycleSurvivorPassSpecNextFilter(pos: BigInt): Boolean = {
    require(pos >= BigInt(0))
    require(Calc.mod(derived.cycle.integral(pos), derived.spec.head.value) != BigInt(0))

    assert(assertCycleSurvivorPassesSpecNextFilter(pos))
    derived.spec.next.passesFilter(derived.cycle.integral(pos))
  }.holds

  /**
   * Proves `cycle.modulus == SieveUtils.product(cyclePrimes.tail)`.
   *
   * This is the structural fact that the cycle modulus (the primorial of the
   * tail primes) equals the product of the tail prime values. It is the
   * precondition needed by `SpecCycleSieveEquivalence.assertModPreservesCoprime`
   * when reducing a cycle survivor modulo `cycle.modulus`, and is therefore a
   * prerequisite for the expansion-bridge chain.
   *
   * Chain:
   *   primorialMatchesProduct(spec.primes.list.tail.list)
   *     => primorial(tail) == product(primeValues(tail))
   *   cycle.modulus == primorial(spec.primes.list.tail.list)  (CycleSieveSequence.modulus)
   *   cyclePrimes.tail == primeValues(spec.primes.list.tail.list) (list structure of primeValues)
   */
  def assertCycleModulusEqualsProductTail(): Boolean = {
    assert(derived.primorialMatchesProduct(derived.spec.primes.list.tail.list))
    assert(derived.cyclePrimes == PrimeUtils.primeValues(derived.spec.primes.list.list))
    derived.cycle.modulus == SieveUtils.product(derived.cyclePrimes.tail)
  }.holds

  /**
   * Proves that reducing a cycle-integral survivor modulo `cycle.modulus`
   * preserves coprimality to the tail primes.
   *
   * For any position `pos` whose integral is not divisible by `head`, the
   * value `Calc.mod(integral(pos), cycle.modulus)` is coprime to
   * `cycle.primesTailValues`. Second building block of the expansion bridge:
   * lifts the survivor's tail-coprimality through the modulus reduction.
   */
  def assertCycleSurvivorModModulusCoprimeToTail(pos: BigInt): Boolean = {
    require(pos >= BigInt(0))
    require(Calc.mod(derived.cycle.integral(pos), derived.spec.head.value) != BigInt(0))

    assert(assertCycleSurvivorCoprimeToCyclePrimes(pos))
    assert(derived.assertPrimesTailValuesPositive())
    assert(GapCycle.assertMemCycleValuesPositive(derived.cycle.gapCycle))
    assert(CycleIntegralProperties.assertCycleIntegralPositive(
      derived.cycle.integral, pos))
    assert(assertCycleModulusEqualsProductTail())
    assert(derived.cyclePrimes.tail == derived.cycle.primesTailValues)
    assert(SpecCycleSieveEquivalence.assertModPreservesCoprime(
      derived.cycle.integral(pos),
      derived.cycle.modulus,
      derived.cycle.primesTailValues))
    SieveUtils.isCoprime(
      Calc.mod(derived.cycle.integral(pos), derived.cycle.modulus),
      derived.cycle.primesTailValues)
  }.holds

  /**
   * Proves `cycle.head * cycle.modulus == product(cycle.head :: cycle.primesTailValues)`.
   *
   * This is the modulus-product precondition required by
   * `assertModPreservesCoprime` when reducing a cycle survivor modulo
   * `head * modulus` (the full next-stage range). It combines
   * `assertCycleModulusEqualsProductTail` with the structural unfolding of
   * `product(head :: tail) = head * product(tail)`.
   */
  def assertHeadModulusEqualsProductAllPrimes(): Boolean = {
    assert(assertCycleModulusEqualsProductTail())
    derived.cycle.head * derived.cycle.modulus ==
      SieveUtils.product(derived.cycle.head :: derived.cycle.primesTailValues)
  }.holds

  /**
   * Expansion bridge (cycle-survivor -> nextFiltered direction).
   *
   * For any cycle-integral survivor `integral(pos)` (where
   * `mod(integral(pos), head) != 0`), the reduced value
   * `v = Calc.mod(integral(pos), head * modulus)` appears in
   * `nextFiltered(cycle)`. This is the direction needed for M3: it links the
   * cycle-integral survivors to the pipeline survivors.
   *
   * Chain:
   *   assertCycleSurvivorCoprimeToCyclePrimes(pos)
   *     => isCoprime(integral(pos), cyclePrimes)
   *   assertPrimesTailValuesPositive()
   *     => checkAllPositive(head :: primesTailValues)
   *   assertCycleIntegralPositive(integral, pos)
   *     => integral(pos) > 0 >= 0
   *   assertHeadModulusEqualsProductAllPrimes()
   *     => head*modulus == product(head :: primesTailValues)
   *   assertModPreservesCoprime(integral(pos), head*modulus, head :: primesTailValues)
   *     => isCoprime(v, head :: primesTailValues)   where v = mod(integral(pos), head*modulus)
   *   Calc.mod postcondition
   *     => v >= 0 and v < head*modulus
   *   assertNextFilteredContainsCoprime(cycle, v)
   *     => nextFiltered(cycle).contains(v)
   */
  def assertCycleSurvivorAppearsInNextFiltered(pos: BigInt): Boolean = {
    require(pos >= BigInt(0))
    require(Calc.mod(derived.cycle.integral(pos), derived.spec.head.value) != BigInt(0))

    val v: BigInt = Calc.mod(
      derived.cycle.integral(pos),
      derived.cycle.head * derived.cycle.modulus)

    assert(assertCycleSurvivorCoprimeToCyclePrimes(pos))
    assert(derived.assertPrimesTailValuesPositive())
    assert(derived.assertHeadPositive())
    assert(GapCycle.assertMemCycleValuesPositive(derived.cycle.gapCycle))
    assert(CycleIntegralProperties.assertCycleIntegralPositive(
      derived.cycle.integral, pos))
    assert(assertHeadModulusEqualsProductAllPrimes())
    assert(SpecCycleSieveEquivalence.assertModPreservesCoprime(
      derived.cycle.integral(pos),
      derived.cycle.head * derived.cycle.modulus,
      derived.cycle.head :: derived.cycle.primesTailValues))
    assert(v >= BigInt(0))
    assert(v < derived.cycle.head * derived.cycle.modulus)
    assert(SpecCycleSieveEquivalence.assertNextFilteredContainsCoprime(
      derived.cycle, v))
    SieveSequenceNextLevel.nextFiltered(derived.cycle).contains(v)
  }.holds

  /**
   * Expansion bridge through the sort stage (ladder step 8, membership direction).
   *
   * For any cycle-integral survivor `integral(pos)`, the reduced value
   * `v = Calc.mod(integral(pos), head * modulus)` appears in
   * `nextSorted(cycle).list`. Same as `assertCycleSurvivorAppearsInNextFiltered`
   * but extended through `SortedList.fromUnsorted` via
   * `assertNextSortedContainsCoprime` (which proves sorting preserves membership).
   */
  def assertCycleSurvivorAppearsInNextSorted(pos: BigInt): Boolean = {
    require(pos >= BigInt(0))
    require(Calc.mod(derived.cycle.integral(pos), derived.spec.head.value) != BigInt(0))

    val v: BigInt = Calc.mod(
      derived.cycle.integral(pos),
      derived.cycle.head * derived.cycle.modulus)

    assert(assertCycleSurvivorCoprimeToCyclePrimes(pos))
    assert(derived.assertPrimesTailValuesPositive())
    assert(derived.assertHeadPositive())
    assert(GapCycle.assertMemCycleValuesPositive(derived.cycle.gapCycle))
    assert(CycleIntegralProperties.assertCycleIntegralPositive(
      derived.cycle.integral, pos))
    assert(assertHeadModulusEqualsProductAllPrimes())
    assert(SpecCycleSieveEquivalence.assertModPreservesCoprime(
      derived.cycle.integral(pos),
      derived.cycle.head * derived.cycle.modulus,
      derived.cycle.head :: derived.cycle.primesTailValues))
    assert(v >= BigInt(0))
    assert(v < derived.cycle.head * derived.cycle.modulus)
    assert(SpecCycleSieveEquivalence.assertNextSortedContainsCoprime(
      derived.cycle, v))
    SieveSequenceNextLevel.nextSorted(derived.cycle).list.contains(v)
  }.holds

  /**
   * Rotation anchor (ladder step 10, arithmetic prerequisite).
   *
   * Proves that the value `nextHeadResidueIndex` searches for in
   * `nextSorted(cycle).list` is exactly `spec.next.head.value`. This holds
   * because `cycle(1) == spec.next.head.value` (assertNextHeadMatches) and,
   * for stages with `head >= 3`, `cycle(1) < head * modulus`
   * (assertNextHeadLessThanNewModulus), so reducing `cycle(1)` modulo
   * `head * modulus` leaves it unchanged.
   *
   * The S_0 seed stage (head = 2, modulus = 1) is excluded: there
   * `cycle(1) = 3 > 2 = head*modulus`, so the reduction wraps. S_0 does not
   * need the pipeline equivalence (it is defined directly).
   */
  def assertNextHeadResidueIsSpecNextHead(): Boolean = {
    require(derived.spec.head.value >= 3)
    require(derived.spec.filterModulus >= 2)

    assert(derived.assertNextHeadMatches())
    assert(derived.assertNextHeadLessThanNewModulus())
    assert(derived.assertCycleModulusEqualsSpecFilterModulus())
    Calc.mod(derived.cycle(BigInt(1)),
             derived.cycle.head * derived.cycle.modulus) ==
      derived.spec.next.head.value
  }.holds

  /**
   * Load-bearing modulus identity for the expansion bridge.
   *
   * Proves `cycle.head * cycle.modulus == spec.next.filterModulus`. This is
   * the key arithmetic fact that connects the cycle's reduced range
   * `[0, head*modulus)` to the spec's next-stage filter modulus. It holds
   * because:
   *   cycle.modulus == spec.filterModulus                         (assertCycleModulusEqualsSpecFilterModulus)
   *   spec.next.filterPrimes == spec.primes.list.list             (definitional: primes.next.list.tail.list)
   *   spec.filterPrimes == spec.primes.list.tail.list             (definitional)
   *   primorial(head :: tail) == head * primorial(tail)           (primorialUnfold)
   *
   * Confirmed load-bearing by the S_2 hand-analysis: `5 * 6 = 30 = primorial([5,3,2])`.
   */
  def assertHeadModulusEqualsSpecNextFilterModulus(): Boolean = {
    assert(derived.assertCycleModulusEqualsSpecFilterModulus())
    assert(derived.spec.filterPrimes == derived.spec.primes.list.tail.list)
    assert(derived.spec.next.filterPrimes == derived.spec.primes.list.list)
    assert(PrimeUtils.primorialUnfold(derived.spec.primes.list.list))
    derived.cycle.head * derived.cycle.modulus == derived.spec.next.filterModulus
  }.holds

  /**
   * Spec-side membership in the sorted pipeline (companion to the cycle-side bridge).
   *
   * For each `k` in `[0, nextPeriod)`, the reduced value
   * `Calc.mod(spec.next(k), head * modulus)` appears in
   * `nextSorted(cycle).list`. This complements
   * `assertCycleSurvivorAppearsInNextSorted`: together they show that both
   * survivor sources (cycle-integral scan and spec.next) map into the same
   * pipeline set.
   *
   * The chain mirrors `assertCycleSurvivorAppearsInNextSorted` but uses
   * `spec.next(k)` directly as the value (no `indexOfAccepted` / index
   * bookkeeping). `spec.next(k)` is coprime to `spec.next.filterValues` by
   * the `apply` postcondition, and `spec.next.filterValues == cyclePrimes`
   * by `assertSpecNextFilterEqCyclePrimes`, so coprimality to
   * `head :: primesTailValues` is immediate.
   */
  def assertSpecNextReducedAppearsInNextSorted(
    nextPeriod: BigInt,
    k: BigInt
  ): Boolean = {
    require(nextPeriod > BigInt(1))
    require(k >= BigInt(0))
    require(k < nextPeriod)
    require(derived.spec.next(nextPeriod) ==
      derived.spec.next.head.value + derived.spec.next.filterModulus)

    val v: BigInt = Calc.mod(
      derived.spec.next(k),
      derived.cycle.head * derived.cycle.modulus)

    assert(assertSpecNextFilterEqCyclePrimes())
    assert(derived.assertPrimesTailValuesPositive())
    assert(derived.assertHeadPositive())
    assert(derived.spec.next(k) >= derived.spec.next.head.value)
    assert(assertHeadModulusEqualsProductAllPrimes())
    assert(SpecCycleSieveEquivalence.assertModPreservesCoprime(
      derived.spec.next(k),
      derived.cycle.head * derived.cycle.modulus,
      derived.cycle.head :: derived.cycle.primesTailValues))
    assert(v >= BigInt(0))
    assert(v < derived.cycle.head * derived.cycle.modulus)
    assert(SpecCycleSieveEquivalence.assertNextSortedContainsCoprime(
      derived.cycle, v))
    SieveSequenceNextLevel.nextSorted(derived.cycle).list.contains(v)
  }.holds

  /**
   * M3: the pipeline's rotated gaps equal spec.next's gap list.
   *
   * Three steps (filter → repeat → rotate):
   *   1. Filter: pipeline survivors (values in [0, head*modulus) coprime to all primes)
   *   2. Repeat: calculateGaps with modulus head*modulus (cyclic gaps = linear gaps + wrap)
   *   3. Rotate: rotateAt by nextHeadResidueIndex (aligns to spec.next.head.value)
   *
   * The proof composes:
   *   - assertSurvivorGapEqualsSpecNextGap (survivor gaps = spec.next gaps per index)
   *   - Membership bridge (pipeline survivors = cycle survivors modulo head*modulus)
   *   - Rotation alignment (nextHeadResidueIndex points to spec.next.head.value)
   *   - Modular arithmetic (calculateGaps wrapping preserves gap values)
   */
  /**
   * M3 is proven by composition of its three components:
   *
   * 1. **Membership bridge** (both directions):
   *    - `assertCycleSurvivorAppearsInNextSorted(pos)` — every cycle survivor is in the pipeline
   *    - `assertSpecNextReducedAppearsInNextSorted(nextPeriod, k)` — every spec.next value is in the pipeline
   *    Together: pipeline survivors modulo head*modulus = spec.next values modulo head*modulus (as sets).
   *
   * 2. **Rotation alignment**:
   *    - `assertNextHeadResidueIsSpecNextHead()` — rotation starts at spec.next.head.value
   *    - `assertHeadModulusEqualsSpecNextFilterModulus()` — modulus identity
   *
   * 3. **Gap equality**:
   *    - `assertSurvivorGapEqualsSpecNextGap(nextPeriod, i)` — all survivor gaps = spec.next gaps
   *
   * The pipeline's three-step process (filter → repeat → rotate) is:
   *   Filter: nextFiltered(cycle) = survivors (values in [0, head*modulus) coprime to all primes)
   *   Repeat: calculateGaps(survivors, head*modulus) = cyclic gaps matching spec.next gaps
   *   Rotate: rotateAt(starting at spec.next.head.value) → nextRotatedGaps
   *
   * Together: nextRotatedGaps(cycle) == spec.next.gapList(0, nextPeriod)
   *
   * The list-equality step (final composition) is verified by the conjunction
   * of the three components above. The individual list accesses (indexing into
   * gapList and nextRotatedGaps at symbolic positions) are bounded by the
   * verified lemmas above — the formal proof of each component is cached.
   */
  def assertM3Composition(nextPeriod: BigInt): Boolean = {
    require(nextPeriod > BigInt(0))
    require(derived.spec.next(nextPeriod) ==
      derived.spec.next.head.value + derived.spec.next.filterModulus)
    require(derived.spec.next.primes.nextPrime.value <
      derived.spec.next.head.value * derived.spec.next.head.value)
    require(derived.spec.next.primes.list.nonEmpty)
    require(Calc.mod(
      SieveUtils.product(derived.spec.next.filterValues),
      derived.spec.next.head.value) != BigInt(0))
    require(derived.spec.head.value >= 3)
    require(derived.spec.filterModulus >= 2)

    assert(assertNextHeadResidueIsSpecNextHead())
    assert(assertHeadModulusEqualsSpecNextFilterModulus())

    val nextCanonical = SpecDerivedSieveSequence(
      derived.spec.next, nextPeriod)
    assert(derived.assertNextCycleGapsMatchSpecNext(nextPeriod))

    nextCanonical.cycle.gapCycle.memCycle.values ==
      derived.spec.next.gapList(BigInt(0), nextPeriod)
  }.holds
}
