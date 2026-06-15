package v1.seq.sieve

import stainless.collection.List
import stainless.lang.{BigInt, decreases}
import v1.list.{ListBoundUtils, ListUtils}
import v1.prime.{Prime, PrimeUtils}

case class CompletePrimePrefix(primes: List[Prime]) {
  require(primes.size > 1)
  require(
    CompletePrimePrefix.containsAllPrimesUpTo(
      PrimeUtils.biggerPrime(primes).value,
      PrimeUtils.primeValues(primes)
    )
  )

  val head: Prime = PrimeUtils.biggerPrime(primes)
  val values: List[BigInt] = PrimeUtils.primeValues(primes)
  val wheelPrimes: List[BigInt] =
    CompletePrimePrefix.previousPrimeValues(primes, head.value)

  def accepts(value: BigInt): Boolean = {
    require(value >= head.value)
    SieveUtils.isCoprime(value, wheelPrimes)
  }
}

object CompletePrimePrefix {

  def containsAllPrimesUpTo(max: BigInt, values: List[BigInt]): Boolean = {
    require(max >= 2)
    containsAllPrimesBetween(BigInt(2), max, values)
  }

  def containsAllPrimesBetween(from: BigInt, max: BigInt, values: List[BigInt]): Boolean = {
    require(from >= 0)
    require(max >= from)
    decreases(max - from)
    val currentPresent = !Prime.isPrime(from) || values.contains(from)
    if (from == max) {
      currentPresent
    } else {
      currentPresent && containsAllPrimesBetween(from + BigInt(1), max, values)
    }
  }

  def previousPrimeValues(primes: List[Prime], max: BigInt): List[BigInt] = {
    decreases(primes.size)
    if (primes.isEmpty) {
      List()
    } else {
      val previousTail = previousPrimeValues(primes.tail, max)
      if (primes.head.value < max) primes.head.value :: previousTail
      else previousTail
    }
  }.ensuring(result =>
    ListUtils.checkAllPositive(result) &&
      ListBoundUtils.allGreaterThan(result, BigInt(1))
  )
}
