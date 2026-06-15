package v1.prime

import stainless.lang.decreases
import v1.prime.AllPrimesSoFarList.allPrimesSoFar
import stainless.collection.List

import scala.annotation.tailrec

case class AllPrimesSoFarList(list: SortedPrimeList) {
  require(AllPrimesSoFarList.allPrimesSoFar(list))

  def isEmpty: Boolean = list.isEmpty
  def size: BigInt = list.size
  def head: Prime = { require(list.nonEmpty); list.head }
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