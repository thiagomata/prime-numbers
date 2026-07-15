package v1.chapter6.seq.sieve

import stainless.collection.List
import stainless.lang.BigInt
import v1.chapter3.list.ListUtils
import v1.chapter5.prime.{Prime, PrimeUtils}

/**
 * Legacy raw-list acceptance helpers.
 *
 * This object is not a stateful sieve sequence and should not be the starting
 * point for new proofs. It exposes a head/tail split over `List[BigInt]`, but it
 * drops the `AllPrimesSoFarList` invariants that current Chapter 6 proofs rely
 * on. That makes it easy to state predicates that look like sieve semantics
 * while missing the typed prime-prefix structure carried by `SpecSieveSequence`
 * and `CycleSieveSequence`.
 *
 * Keep this file as historical scaffolding unless a cleanup pass explicitly
 * retires it. For the full mathematical stream, use `SpecSieveSequence`. For
 * the concrete gap-cycle stream, use `CycleSieveSequence`.
 */
object SieveSequenceByPrimes {

  def head(primes: List[BigInt]): BigInt = {
    require(primes.nonEmpty)
    primes.head
  }

  def wheelPrimes(primes: List[BigInt]): List[BigInt] = {
    require(primes.nonEmpty)
    primes.tail
  }

  def modulus(primes: List[BigInt]): BigInt = {
    require(primes.nonEmpty)
    SieveUtils.product(wheelPrimes(primes))
  }

  def accepts(value: BigInt, primes: List[BigInt]): Boolean = {
    require(primes.nonEmpty)
    require(ListUtils.checkAllPositive(wheelPrimes(primes)))
    value >= head(primes) && SieveUtils.isCoprime(value, wheelPrimes(primes))
  }

  def acceptsPrimeList(value: BigInt, primes: List[Prime]): Boolean = {
    require(primes.nonEmpty)
    accepts(value, PrimeUtils.primeValues(primes))
  }

}
