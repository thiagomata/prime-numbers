package v1.prime

import org.scalatest.flatspec.FlatSpec
import org.scalatest.matchers.should.Matchers
import stainless.collection.List
import v1.chapter5.prime.{AllPrimesSoFarList, Prime, SortedPrimeList}

import scala.language.postfixOps


class AllPrimesSoFarListTest  extends FlatSpec with Matchers {

  "empty" should "return when empty" in {
    AllPrimesSoFarList(SortedPrimeList.empty).isEmpty should be(true)
    AllPrimesSoFarList(SortedPrimeList(
      List(Prime(5), Prime(3), Prime(2))
    )).isEmpty should be(false)
  }

  "all primes so far" should "return true for empty list" in {
    AllPrimesSoFarList.allPrimesSoFar(SortedPrimeList.empty) should be(true)
  }

  "all primes so far" should "return true for list of primes with all primes up to the last one" in {
    AllPrimesSoFarList.allPrimesSoFar(SortedPrimeList(
      List(Prime(5), Prime(3), Prime(2))
    )) should be(true)
  }

  "all primes so far" should "return false for list with missing primes in the middle" in {
    AllPrimesSoFarList.allPrimesSoFar(SortedPrimeList(
      List(Prime(5), Prime(2))
    )) should be(false)
  }

  "all primes so far" should "return false for list with missing primes in the tail" in {
    AllPrimesSoFarList.allPrimesSoFar(SortedPrimeList(
      List(Prime(5), Prime(3))
    )) should be(false)
  }

  "all primes so far" should "return true for list with range primes" in {
    AllPrimesSoFarList.allPrimesSoFar(SortedPrimeList(
      List(Prime(7), Prime(5), Prime(3), Prime(2)),
    )) should be(true)
  }

  "add" should "add the next prime if valid" in {
    val newList = AllPrimesSoFarList(
      SortedPrimeList(List(Prime(5), Prime(3), Prime(2)))
    ).insert(Prime(7))

    val expectedList = AllPrimesSoFarList(
       SortedPrimeList(List(Prime(7), Prime(5), Prime(3), Prime(2)))
    )

    newList.equals(expectedList) should be(true)
  }

  "tail" should "tail the prime list" in {
    val newList = AllPrimesSoFarList(
      SortedPrimeList(List(Prime(5), Prime(3), Prime(2)))
    ).tail

    val expectedList = AllPrimesSoFarList(
      SortedPrimeList(List(Prime(3), Prime(2)))
    )

    newList.equals(expectedList) should be(true)
  }

  "nextPrime" should "return the next prime after head for [5, 3, 2]" in {
    val list = AllPrimesSoFarList(
      SortedPrimeList(List(Prime(5), Prime(3), Prime(2)))
    )
    list.nextPrime.value should be(7)
  }

  "nextPrime" should "return the next prime after head for [7, 5, 3, 2]" in {
    val list = AllPrimesSoFarList(
      SortedPrimeList(List(Prime(7), Prime(5), Prime(3), Prime(2)))
    )
    list.nextPrime.value should be(11)
  }

  "nextPrime" should "return a prime greater than head for [3, 2]" in {
    val list = AllPrimesSoFarList(
      SortedPrimeList(List(Prime(3), Prime(2)))
    )
    val p = list.nextPrime
    (p.value > 3) should be(true)
    Prime.isPrime(p.value) should be(true)
  }

  "nextPrime" should "return 3 for [2]" in {
    val list = AllPrimesSoFarList(
      SortedPrimeList(List(Prime(2)))
    )
    list.nextPrime.value should be(3)
  }
}
