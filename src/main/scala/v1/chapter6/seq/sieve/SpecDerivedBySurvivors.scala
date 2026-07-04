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
}
