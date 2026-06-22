package v1.chapter5.prime

import stainless.lang.decreases
import AllPrimesSoFarList.allPrimesSoFar
import stainless.collection.List
import v1.chapter5.prime.properties.PrimeProperties

import scala.annotation.tailrec

case class AllPrimesSoFarList(list: SortedPrimeList) {
  require(AllPrimesSoFarList.allPrimesSoFar(list))

  def isEmpty: Boolean = list.isEmpty
  def size: BigInt = list.size
  def head: Prime = { require(list.nonEmpty); list.head }

  def nextPrime: Prime = {
    require(list.nonEmpty)
    AllPrimesSoFarList.nextPrime(list)
  }

  def next: AllPrimesSoFarList = {
    require(list.nonEmpty)

    val newPrime = AllPrimesSoFarList.nextPrime(list)

    val newSortedList = SortedPrimeList(newPrime :: list.list)

    AllPrimesSoFarList(newSortedList)
  }

  def last: Prime = { require(list.nonEmpty); list.last }
  def apply(index: BigInt): Prime = { require(index >= 0 && index < list.size); list(index) }

  def insert(prime: Prime): AllPrimesSoFarList = {
    require(allPrimesSoFar(list.insert(prime)))
    AllPrimesSoFarList(list.insert(prime))
  }

  def tail: AllPrimesSoFarList = {
    require(list.nonEmpty)
    assert(SortedPrimeList.isDescending(list.list))
    assert(allPrimesSoFar(list.tail))
    AllPrimesSoFarList(list.tail)
  }

  def equals(other: AllPrimesSoFarList): Boolean = {
    if (this.size != other.size) {
      false
    } else {
      AllPrimesSoFarList.equalsHelper(this.list, other.list)
    }
  }

}

object AllPrimesSoFarList {
  def allPrimesSoFar(list: SortedPrimeList): Boolean = {
    if list.isEmpty then
      true
    else
      loopCheckAllPrimesSoFar(list)
  }

  def loopCheckAllPrimesSoFar(list: SortedPrimeList): Boolean = {
    decreases(list.size)
    if list.isEmpty then true else
    if list.size == 1 then {
      list.head.value == BigInt(2)
    } else {
      val current = list.head.value
      if (!Prime.isPrime(current)) {
        false
      } else {
        assert(list.head.value > list.tail.head.value)
        noPrimesBetween(list.tail.head.value + 1, current) && loopCheckAllPrimesSoFar(list.tail)
      }
    }
  }

  @tailrec
  def noPrimesBetween(from: BigInt, to: BigInt): Boolean = {
    decreases(to - from)
    require(from >= 0)
    require(to >= from)
    if (from == to) {
      true
    } else {
      if (Prime.isPrime(from)) {
        false
      } else {
        noPrimesBetween(from + 1, to)
      }
    }
  }

  /**
   * Turns the recursive gap check into a pointwise fact for one value.
   *
   * `noPrimesBetween(from, to)` checks every natural number in the half-open
   * interval `[from, to)`. Callers often know that a candidate sits somewhere
   * in that interval, but Stainless needs this explicit induction to reuse the
   * result at the candidate itself.
   */
  def noPrimesBetweenExcludesValue(from: BigInt, to: BigInt, value: BigInt): Boolean = {
    require(from >= 0)
    require(to >= from)
    require(value >= from)
    require(value < to)
    require(noPrimesBetween(from, to))
    decreases(to - from)

    if (value == from) {
      assert(!Prime.isPrime(from))
      !Prime.isPrime(value)
    } else {
      assert(from < to)
      assert(value >= from + BigInt(1))
      assert(noPrimesBetween(from + BigInt(1), to))
      noPrimesBetweenExcludesValue(from + BigInt(1), to, value)
    }
  }.ensuring(res => res && !Prime.isPrime(value))

  /**
   * Linearly finds the first prime in a bounded candidate window.
   *
   * The prime list is deliberately not part of this loop. The caller supplies a
   * known prime `upper` as a finite witness, and the loop moves only the natural
   * number counter `current`. Each rejected counter value contributes one local
   * fact, `!Prime.isPrime(current)`, and the postcondition folds those local
   * facts into the range fact needed by the future `nextPrime` constructor:
   * no prime exists in the half-open interval `[current, result)`.
   */
  def nextPrime(list: SortedPrimeList): Prime = {
    require(list.nonEmpty)
    require(allPrimesSoFar(list))

    PrimeProperties.primorialPlusOneModAny(list.list)
    val upperPrime = PrimeProperties.newPrimeFromEuclid(list.list)

    // Prove: upperPrime.value > list.head.value
    PrimeProperties.newPrimeNotInList(list.list)
    assert(PrimeProperties.notContainsFromValueNotMatchesAny(list.list, list, upperPrime.value))

    if (upperPrime.value <= list.head.value) {
      AllPrimesSoFarList.primeAtOrBelowHeadIsContained(upperPrime.value, list)
    }

    AllPrimesSoFarList.searchNextPrimeUpTo(list.head.value + BigInt(1), upperPrime)
  }.ensuring(res =>
    res.value > list.head.value &&
      Prime.isPrime(res.value) &&
      AllPrimesSoFarList.noPrimesBetween(list.head.value + BigInt(1), res.value)
  )

  def searchNextPrimeUpTo(current: BigInt, upper: Prime): Prime = {
    require(current >= 0)
    require(current <= upper.value)
    decreases(upper.value - current)

    if (Prime.isPrime(current)) {
      val result = Prime(current)
      assert(noPrimesBetween(current, result.value))
      result
    } else {
      assert(Prime.isPrime(upper.value))
      assert(current < upper.value)
      val result = searchNextPrimeUpTo(current + BigInt(1), upper)
      assert(noPrimesBetween(current + BigInt(1), result.value))
      assert(!Prime.isPrime(current))
      assert(noPrimesBetween(current, result.value))
      result
    }
  }.ensuring(res =>
    res.value >= current &&
      res.value <= upper.value &&
      Prime.isPrime(res.value) &&
      noPrimesBetween(current, res.value)
  )

  /**
   * Projects the complete-prime-prefix invariant into direct membership.
   *
   * `allPrimesSoFar` stores completeness as local gaps: the head is prime,
   * there are no primes between the tail head and the current head, and the
   * tail is complete by the same rule. This lemma exposes the caller-facing
   * form of that invariant: any prime value at or below the current head must
   * already occur in the descending list.
   */
  def primeAtOrBelowHeadIsContained(value: BigInt, list: SortedPrimeList): Boolean = {
    require(list.nonEmpty)
    require(allPrimesSoFar(list))
    require(value >= 0)
    require(Prime.isPrime(value))
    require(value <= list.head.value)
    decreases(list.size)

    if (value == list.head.value) {
      contains(value, list)
    } else if (list.size == BigInt(1)) {
      assert(list.head.value == BigInt(2))
      assert(value < BigInt(2))
      assert(!Prime.isPrime(value))
      contains(value, list)
    } else {
      assert(loopCheckAllPrimesSoFar(list))
      assert(noPrimesBetween(list.tail.head.value + BigInt(1), list.head.value))
      if (value > list.tail.head.value) {
        assert(value >= list.tail.head.value + BigInt(1))
        assert(value < list.head.value)
        assert(noPrimesBetweenExcludesValue(list.tail.head.value + BigInt(1), list.head.value, value))
        assert(!Prime.isPrime(value))
        contains(value, list)
      } else {
        assert(allPrimesSoFar(list.tail))
        assert(primeAtOrBelowHeadIsContained(value, list.tail))
        assert(contains(value, list.tail))
        contains(value, list)
      }
    }
  }.ensuring(res => res && contains(value, list))


//  @tailrec
//  def loopCheckAllPrimesSoFar(current: BigInt, list: SortedPrimeList): Boolean = {
//    if (current < 2) {
//      true
//    } else {
//      checkCurrent(current, list) &&
//        loopCheckAllPrimesSoFar(current - 1, list)
//    }
//  }
//
//  def checkCurrent(current: BigInt, list: SortedPrimeList): Boolean = {
//    if (Prime.isPrime(current)) {
//      contains(current, list)
//    } else {
//      true
//    }
//  }

  @tailrec
  def contains(current: BigInt, list: SortedPrimeList): Boolean = {
    decreases(list.size)
    if (list.isEmpty) {
      false
    } else if (list.head.value == current) {
      true
    } else {
      contains(current, list.tail)
    }
  }

  @tailrec
  def equalsHelper(list1: SortedPrimeList, list2: SortedPrimeList): Boolean = {
    if (list1.isEmpty && list2.isEmpty) {
      true
    } else if (list1.isEmpty || list2.isEmpty) {
      false
    } else if (list1.head.value != list2.head.value) {
      false
    } else {
      equalsHelper(list1.tail, list2.tail)
    }
  }
}
