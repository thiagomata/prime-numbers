package v1.seq.sieve

import stainless.annotation.extern
import stainless.collection.List
import stainless.lang.*
import v1.Calc
import v1.div.properties.{AdditionAndMultiplication, ModIdentity, ModOperations}
import v1.list.ListUtils
import v1.prime.{Prime, PrimeUtils}

import scala.annotation.tailrec

case class SieveSequenceV0(primes: List[Prime]) {
  require(primes.nonEmpty)

  val head: Prime = PrimeUtils.biggerPrime(primes)

  val primorial: BigInt = PrimeUtils.primorial(primes)

// DEPENDENCY FAILED (2026-06-11): depends on search (internal error), kept commented as dependency
//  def apply(pos: BigInt): BigInt = {
//    require(pos >= 0)
//    decreases(pos)
//    if (pos == 0) head.apply()
//    else {
//      this.search(
//        pos - 1,
//        head.value + 1
//      )
//    }
//  }
// VERIFICATION FAILED (2026-06-11): 4605 UNKNOWN - solver timeout on almost all VCs, heavy assertion chain causes solver breakdown
//  private def thereAreNonMultiples(amount: BigInt): Boolean = {
//    require(amount >= 1)
//    assert(ModIdentity.modIdentity(primorial))
//    assert(AdditionAndMultiplication.APlusMultipleTimesBSameMod(primorial, amount, BigInt(1)))
//    assert(ModOperations.modAdd(primorial, primorial, BigInt(1)))
//    assert(Calc.mod(primorial, primorial) == BigInt(0))
//    assert(Calc.mod(primorial + 1, primorial) == BigInt(1))
//    assert(!PrimeUtils.isMultiple(primorial * amount + 1, primes))
//    if amount == 1 then true else {
//      thereAreNonMultiples(amount - 1)
//    }
//  }.holds

// INTERNAL ERROR (2026-06-11): Stainless crashes with choose type inference error on @extern with recursive postcondition
//  @extern
//  private def search(pos: BigInt, biggerOrEqualThan: BigInt): BigInt = {
//    require(pos >= 0)
//    require(biggerOrEqualThan >= head.value + 1)
//    decreases((pos + 1) * primorial - (biggerOrEqualThan - head.value))
//    if (!PrimeUtils.isMultiple(biggerOrEqualThan, primes)) {
//      if (pos == 0) biggerOrEqualThan
//      else search(pos - 1, biggerOrEqualThan + BigInt(1))
//    } else search(pos, biggerOrEqualThan + BigInt(1))
//  }.ensuring(
//    result => !PrimeUtils.isMultiple(result, primes) && {
//      if (pos == 0) result > head.value
//      else {
//        val prev = search(pos - 1, biggerOrEqualThan)
//        result > prev
//      }
//    }
//  )
}

object SieveSequenceV0 {




  def notDivisibleByAny(n: BigInt, primes: List[BigInt]): Boolean = {
    require(n > 1)
    require(ListUtils.checkAllPositive(primes))
    decreases(primes.size)
    if (primes.isEmpty) true
    else if (Calc.mod(n, primes.head) == BigInt(0)) false
    else notDivisibleByAny(n, primes.tail)
  }

// COMPILATION ERROR (2026-06-11): List(BigInt(2)) is List[BigInt], need List[Prime]
//  def S_0(): SieveSequenceV0 = SieveSequenceV0(List(BigInt(2)))
}
