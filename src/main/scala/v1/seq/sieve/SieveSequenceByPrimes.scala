package v1.seq.sieve

import stainless.collection.List
import stainless.lang.BigInt
import v1.list.ListUtils
import v1.prime.{Prime, PrimeUtils}

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
