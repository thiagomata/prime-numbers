package v1.chapter5.prime

import stainless.collection.List
import stainless.lang.{BigInt, decreases}
import scala.annotation.tailrec

object PrimeListUtils {

  def allPrimesSoFar(list: SortedPrimeList): Boolean = {
    if list.isEmpty then
      true
    else
      loopCheckAllPrimesSoFar(list)
  }

  @tailrec
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
}
