package v1.seq.sieve

import stainless.collection.List
import stainless.lang.*

import scala.annotation.tailrec

object SieveUtils {
  def product(list: List[BigInt]): BigInt = {
    decreases(list.size)
    if (list.isEmpty) BigInt(1)
    else list.head * product(list.tail)
  }

  @tailrec
  def checkAllBiggerThanValue(list: List[BigInt], value: BigInt): Boolean = {
    decreases(list.size)
    if (list.isEmpty) true
    else list.head > value && checkAllBiggerThanValue(list.tail, value)
  }

  def checkAllPositive(list: List[BigInt]): Boolean = {
    checkAllBiggerThanValue(list, BigInt(0))
  }

  def checkAllBiggerThanOne(list: List[BigInt]): Boolean = {
    checkAllBiggerThanValue(list, BigInt(1))
  }

  @tailrec
  def isCoprime(value: BigInt, primes: List[BigInt]): Boolean = {
    require(checkAllPositive(primes))
    decreases(primes.size)
    if (primes.isEmpty) true
    else if (value % primes.head == BigInt(0)) false
    else isCoprime(value, primes.tail)
  }

  def residues(modulus: BigInt, primes: List[BigInt]): List[BigInt] = {
    require(modulus > 0)
    require(checkAllPositive(primes))
    generateResidues(BigInt(0), modulus, primes)
  }

  def generateResidues(i: BigInt, modulus: BigInt, primes: List[BigInt]): List[BigInt] = {
    require(i >= 0)
    require(i <= modulus)
    require(modulus > 0)
    require(checkAllPositive(primes))
    decreases(modulus - i)
    if (i == modulus) List.empty
    else {
      val rest = generateResidues(i + 1, modulus, primes)
      if (isCoprime(i, primes)) i :: rest else rest
    }
  }

  def filterList(list: List[BigInt], divisor: BigInt): List[BigInt] = {
    require(divisor > 0)
    decreases(list.size)
    if (list.isEmpty) List.empty
    else {
      val rest = filterList(list.tail, divisor)
      if (list.head % divisor != 0) list.head :: rest
      else rest
    }
  }

  def sortFiltered(list: List[BigInt]): List[BigInt] = {
    decreases(list.size)
    if (list.isEmpty) List.empty
    else insertSorted(list.head, sortFiltered(list.tail))
  }

  def insertSorted(x: BigInt, list: List[BigInt]): List[BigInt] = {
    decreases(list.size)
    if (list.isEmpty) List(x)
    else if (x <= list.head) x :: list
    else list.head :: insertSorted(x, list.tail)
  }

  def addOffset(list: List[BigInt], offset: BigInt): List[BigInt] = {
    decreases(list.size)
    if (list.isEmpty) List.empty
    else (list.head + offset) :: addOffset(list.tail, offset)
  }

  def expandResidues(residues: List[BigInt], mod: BigInt, p: BigInt): List[BigInt] = {
    require(mod > 0)
    require(p > 0)
    expandSingleResidue(residues, mod, p, BigInt(0))
  }

  def expandSingleResidue(residues: List[BigInt], mod: BigInt, p: BigInt, i: BigInt): List[BigInt] = {
    require(i >= 0 && i < p)
    require(p > 0)
    decreases(p - i)
    val offset = i * mod
    val currentSet = addOffset(residues, offset)
    if (i + 1 >= p) currentSet
    else currentSet ++ expandSingleResidue(residues, mod, p, i + 1)
  }

  def calculateGaps(sorted: List[BigInt], modulus: BigInt): List[BigInt] = {
    require(modulus > 0)
    if (sorted.isEmpty) List.empty
    else if (sorted.size == 1) List(modulus)
    else {
      val innerGaps = pairwiseGaps(sorted)
      val wrapGap = modulus - sorted.last + sorted.head
      innerGaps ++ List(wrapGap)
    }
  }

  def pairwiseGaps(list: List[BigInt]): List[BigInt] = {
    decreases(list.size)
    if (list.size < 2) List.empty
    else if (list.size == 2) List(list(1) - list(0))
    else (list(1) - list(0)) :: pairwiseGaps(list.tail)
  }

  def getAt(list: List[BigInt], index: BigInt): BigInt = {
    require(index >= 0)
    require(index < list.size)
    decreases(index)
    if (index == BigInt(0)) list.head
    else getAt(list.tail, index - 1)
  }

  def residueAt(sorted: List[BigInt], index: BigInt): BigInt = {
    if (sorted.isEmpty || index < 0 || index >= sorted.size) BigInt(0)
    else getAt(sorted, index)
  }

  def nextResidueIndex(sorted: List[BigInt], currentIndex: BigInt, value: BigInt): BigInt = {
    require(currentIndex <= sorted.size)
    if (sorted.isEmpty) BigInt(0)
    else findResidueIndex(sorted, currentIndex, value)
  }

  @tailrec
  def findResidueIndex(list: List[BigInt], idx: BigInt, value: BigInt): BigInt = {
    require(list.nonEmpty)
    decreases(list.size)
    if (list.head > value) idx
    else if (list.tail.isEmpty) BigInt(0)
    else findResidueIndex(list.tail, idx + 1, value)
  }

  def splitAt(list: List[BigInt], index: BigInt): (List[BigInt], List[BigInt]) = {
    require(index >= 0 && index <= list.size)
    decreases(index)
    if (index == BigInt(0)) (List.empty, list)
    else {
      val (front, back) = splitAt(list.tail, index - 1)
      (list.head :: front, back)
    }
  }

  def rotateAt(list: List[BigInt], index: BigInt): List[BigInt] = {
    if (list.isEmpty || index < 0 || index >= list.size) List.empty
    else if (index == BigInt(0)) list
    else {
      val (front, back) = splitAt(list, index)
      back ++ front
    }
  }

  def assertValueNeverDecreases(a: BigInt, b: BigInt): Boolean = {
    require(a >= 1 && b >= 1)
    a * b >= a && a * b >= b && a * b >= BigInt(1)
  }.holds

  def assertProductEqualOrBiggerThanElements(list: List[BigInt]): Boolean = {
    require(checkAllBiggerThanOne(list))
    decreases(list.size)
    if (list.isEmpty) {
      product(list) == BigInt(1)
    }
    else {
      assertProductEqualOrBiggerThanElements(list.tail)
      assert(product(list.tail) >= BigInt(1))
      assert(list.head > BigInt(1))
      assert(assertValueNeverDecreases(list.head, product(list.tail)))
      assert(product(list) == list.head * product(list.tail))
      product(list) >= BigInt(1) &&
        product(list) >= list.head
    }
  }.holds
}
