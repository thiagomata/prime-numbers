package v1.chapter6.seq.sieve

import stainless.lang.BooleanDecorations
import v1.chapter2.div.Calc
import v1.chapter5.prime.PrimeUtils
import v1.chapter6.seq.sieve.SieveUtils

object SieveCycleAfterProof {

  /**
   * Proves that every cycle-integral survivor (value not divisible by `head`)
   * is coprime with the full prime list.
   */
// bad agent
//  def assertCycleSurvivorCoprimeToCyclePrimes(
//    seq: SpecDerivedSieveSequence,
//    pos: BigInt
//  ): Boolean = {
//    require(pos >= BigInt(0))
//    require(Calc.mod(seq.cycle.integral(pos), seq.spec.head.value) != BigInt(0))
//
//    seq.assertCycleValueCoprimeToTail(pos + BigInt(1))
//    SieveUtils.isCoprime(seq.cycle.integral(pos), seq.cyclePrimes)
//  }.holds

  /**
   * Proves `spec.next.filterValues == cyclePrimes`.
   */
// bad agent
//  def assertSpecNextFilterEqCyclePrimes(
//    seq: SpecDerivedSieveSequence
//  ): Boolean = {
//    assert(seq.assertPrimesMatch())
//    assert(seq.primes.list.list == seq.spec.primes.list.list)
//    assert(seq.spec.next.filterPrimes == seq.spec.primes.list.list)
//    assert(seq.cyclePrimes == PrimeUtils.primeValues(seq.primes.list.list))
//    assert(seq.spec.next.filterValues ==
//      PrimeUtils.primeValues(seq.spec.next.filterPrimes))
//    seq.spec.next.filterValues == seq.cyclePrimes
//  }.holds

  /**
   * Every cycle-integral survivor is coprime with spec.next's filter values.
   */
// bad agent
//  def assertCycleSurvivorCoprimeToSpecNextFilter(
//    seq: SpecDerivedSieveSequence,
//    pos: BigInt
//  ): Boolean = {
//    require(pos >= BigInt(0))
//    require(Calc.mod(seq.cycle.integral(pos), seq.spec.head.value) != BigInt(0))
//
//    assert(assertSpecNextFilterEqCyclePrimes(seq))
//    assert(assertCycleSurvivorCoprimeToCyclePrimes(seq, pos))
//
//    SieveUtils.isCoprime(seq.cycle.integral(pos), seq.spec.next.filterValues)
//  }.holds

  /**
   * Every cycle-integral survivor passes the next-stage filter.
   *
   * Unlike `accepts`, `passesFilter` does NOT require `value >= head.value`,
   * which avoids the strict-monotonicity proof that times out for symbolic
   * positions.
   */
//  def assertCycleSurvivorPassesSpecNextFilter(
//    seq: SpecDerivedSieveSequence,
//    pos: BigInt
//  ): Boolean = {
//    require(pos >= BigInt(0))
//    require(Calc.mod(seq.cycle.integral(pos), seq.spec.head.value) != BigInt(0))
//
//    assert(assertCycleSurvivorCoprimeToSpecNextFilter(seq, pos))
//    seq.spec.next.passesFilter(seq.cycle.integral(pos))
//  }.holds

  /**
   * Proves the first cycle-integral survivor equals `spec.next.head.value`.
   *
   * `cycle.integral(0) = cycle(1) = spec(1) = spec.next.head.value`.
   */
// bad agent
//  def assertFirstSurvivorEqualsSpecNextHead(
//    seq: SpecDerivedSieveSequence
//  ): Boolean = {
//    assert(seq.assertNextHeadMatches())
//    assert(seq.cycle(BigInt(1)) == seq.spec.next.head.value)
//    seq.cycle.integral(BigInt(0)) == seq.spec.next.head.value
//  }.holds
}
