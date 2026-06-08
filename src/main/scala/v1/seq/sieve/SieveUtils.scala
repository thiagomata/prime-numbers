package v1.seq.sieve

import stainless.collection.List
import stainless.lang.*

import v1.list.ListUtils
import v1.list.properties.ListUtilsProperties
import scala.annotation.tailrec

object SieveUtils {
  def product(list: List[BigInt]): BigInt = {
    decreases(list.size)
    if (list.isEmpty) BigInt(1)
    else list.head * product(list.tail)
  }

  @tailrec
  def isCoprime(value: BigInt, primes: List[BigInt]): Boolean = {
    require(ListUtils.checkAllPositive(primes))
    decreases(primes.size)
    if (primes.isEmpty) true
    else if (value % primes.head == BigInt(0)) false
    else isCoprime(value, primes.tail)
  }

  def residues(modulus: BigInt, primes: List[BigInt]): List[BigInt] = {
    require(modulus > 0)
    require(ListUtils.checkAllPositive(primes))
    generateResidues(BigInt(0), modulus, primes)
  }

  def generateResidues(i: BigInt, modulus: BigInt, primes: List[BigInt]): List[BigInt] = {
    require(i >= 0)
    require(i <= modulus)
    require(modulus > 0)
    require(ListUtils.checkAllPositive(primes))
    decreases(modulus - i)
    if (i == modulus) List.empty
    else {
      val rest = generateResidues(i + 1, modulus, primes)
      if (isCoprime(i, primes)) i :: rest else rest
    }
  }.ensuring(res => CycleUtils.checkNonNegative(res) && CycleUtils.allLessThan(res, modulus))

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
    if (sorted.isEmpty) List(modulus)
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

  @tailrec
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
    require(currentIndex >= BigInt(0))
    require(currentIndex <= sorted.size)
    if (sorted.isEmpty) BigInt(0)
    else findResidueIndex(sorted, currentIndex, value)
  }.ensuring(_ >= BigInt(0))

  def findResidueIndex(list: List[BigInt], idx: BigInt, value: BigInt): BigInt = {
    require(list.nonEmpty)
    require(idx >= BigInt(0))
    decreases(list.size)
    if (list.head >= value) idx
    else if (list.tail.isEmpty) BigInt(0)
    else findResidueIndex(list.tail, idx + 1, value)
  }.ensuring(_ >= BigInt(0))

//  def splitAt(list: List[BigInt], index: BigInt): (List[BigInt], List[BigInt]) = {
//    require(index >= 0 && index <= list.size)
//    decreases(index)
//    if (index == BigInt(0)) (List.empty, list)
//    else {
//      val (front, back) = splitAt(list.tail, index - 1)
//      (list.head :: front, back)
//    }
//  }

  @tailrec
  def rotateAt(list: List[BigInt], index: BigInt): List[BigInt] = {
    require(index >= 0)
    decreases(index)
    if (list.isEmpty || index == BigInt(0)) list
    else if (index >= list.size) rotateAt(list, index - list.size)
    else {
      val (front, back) = ListUtils.splitAt(list, index)
      back ++ front
    }
  }
  def assertRotateAtPreservesNonEmpty(list: List[BigInt], index: BigInt): Boolean = {
    require(list.nonEmpty)
    require(index >= 0)
    decreases(index)
    if (list.isEmpty || index == BigInt(0)) {
      rotateAt(list, index).nonEmpty
    } else if (index >= list.size) {
      assert(assertRotateAtPreservesNonEmpty(list, index - list.size))
      rotateAt(list, index).nonEmpty
    } else {
      rotateAt(list, index).nonEmpty
    }
  }.holds

  def isAscending(list: List[BigInt]): Boolean = {
    decreases(list.size)
    if (list.isEmpty || list.tail.isEmpty) true
    else if (list.head > list.tail.head) false
    else isAscending(list.tail)
  }

  def assertInsertSortedAscending(x: BigInt, list: List[BigInt]): Boolean = {
    require(isAscending(list))
    decreases(list.size)
    if (list.isEmpty) {
      isAscending(insertSorted(x, list))
    } else if (x <= list.head) {
      isAscending(insertSorted(x, list))
    } else {
      assert(isAscending(list.tail))
      assert(assertInsertSortedAscending(x, list.tail))
      assert(isAscending(insertSorted(x, list.tail)))
      isAscending(insertSorted(x, list))
    }
  }.holds

  def assertSortFilteredAscending(list: List[BigInt]): Boolean = {
    decreases(list.size)
    if (list.isEmpty) {
      isAscending(sortFiltered(list))
    } else {
      assert(assertSortFilteredAscending(list.tail))
      assert(isAscending(sortFiltered(list.tail)))
      assert(assertInsertSortedAscending(list.head, sortFiltered(list.tail)))
      isAscending(sortFiltered(list))
    }
  }.holds

  def assertAddOffsetNonNegative(list: List[BigInt], offset: BigInt): Boolean = {
    require(CycleUtils.checkNonNegative(list))
    require(offset >= 0)
    decreases(list.size)
    if (list.isEmpty) {
      CycleUtils.checkNonNegative(addOffset(list, offset))
    } else {
      assert(assertAddOffsetNonNegative(list.tail, offset))
      CycleUtils.checkNonNegative(addOffset(list, offset))
    }
  }.holds

  def assertAddOffsetAllLessThan(list: List[BigInt], bound: BigInt, offset: BigInt): Boolean = {
    require(CycleUtils.allLessThan(list, bound))
    require(offset >= 0)
    decreases(list.size)
    if (list.isEmpty) {
      CycleUtils.allLessThan(addOffset(list, offset), bound + offset)
    } else {
      assert(assertAddOffsetAllLessThan(list.tail, bound, offset))
      CycleUtils.allLessThan(addOffset(list, offset), bound + offset)
    }
  }.holds

  def assertExpandSingleRange(residues: List[BigInt], mod: BigInt, p: BigInt, i: BigInt): Boolean = {
    require(CycleUtils.checkNonNegative(residues))
    require(CycleUtils.allLessThan(residues, mod))
    require(mod > 0)
    require(p > 0)
    require(i >= 0 && i < p)
    decreases(p - i)
    val currentSet = addOffset(residues, i * mod)
    assertAddOffsetNonNegative(residues, i * mod)
    assertAddOffsetAllLessThan(residues, mod, i * mod)
    assert(CycleUtils.assertAllLessThanTransitive(currentSet, (i + 1) * mod, p * mod))
    if (i + 1 >= p) {
      CycleUtils.checkNonNegative(expandSingleResidue(residues, mod, p, i)) &&
        CycleUtils.allLessThan(expandSingleResidue(residues, mod, p, i), p * mod)
    } else {
      assert(assertExpandSingleRange(residues, mod, p, i + 1))
      val rest = expandSingleResidue(residues, mod, p, i + 1)
      CycleUtils.assertCheckNonNegativeAppend(currentSet, rest)
      CycleUtils.assertAllLessThanAppend(currentSet, rest, p * mod)
      CycleUtils.checkNonNegative(expandSingleResidue(residues, mod, p, i)) &&
        CycleUtils.allLessThan(expandSingleResidue(residues, mod, p, i), p * mod)
    }
  }.holds

  def assertExpandResiduesRange(residues: List[BigInt], mod: BigInt, p: BigInt): Boolean = {
    require(CycleUtils.checkNonNegative(residues))
    require(CycleUtils.allLessThan(residues, mod))
    require(mod > 0)
    require(p > 0)
    assert(assertExpandSingleRange(residues, mod, p, BigInt(0)))
    CycleUtils.checkNonNegative(expandResidues(residues, mod, p)) &&
      CycleUtils.allLessThan(expandResidues(residues, mod, p), mod * p)
  }.holds

  def assertFilterListNonNegative(list: List[BigInt], divisor: BigInt): Boolean = {
    require(CycleUtils.checkNonNegative(list))
    require(divisor > 0)
    decreases(list.size)
    if (list.isEmpty) {
      CycleUtils.checkNonNegative(filterList(list, divisor))
    } else {
      assert(assertFilterListNonNegative(list.tail, divisor))
      CycleUtils.checkNonNegative(filterList(list, divisor))
    }
  }.holds

  def assertFilterListAllLessThan(list: List[BigInt], bound: BigInt, divisor: BigInt): Boolean = {
    require(CycleUtils.allLessThan(list, bound))
    require(divisor > 0)
    decreases(list.size)
    if (list.isEmpty) {
      CycleUtils.allLessThan(filterList(list, divisor), bound)
    } else {
      assert(assertFilterListAllLessThan(list.tail, bound, divisor))
      CycleUtils.allLessThan(filterList(list, divisor), bound)
    }
  }.holds

  def assertInsertSortedNonNegative(x: BigInt, list: List[BigInt]): Boolean = {
    require(x >= 0)
    require(CycleUtils.checkNonNegative(list))
    decreases(list.size)
    if (list.isEmpty) {
      CycleUtils.checkNonNegative(insertSorted(x, list))
    } else if (x <= list.head) {
      CycleUtils.checkNonNegative(insertSorted(x, list))
    } else {
      assert(assertInsertSortedNonNegative(x, list.tail))
      CycleUtils.checkNonNegative(insertSorted(x, list))
    }
  }.holds

  def assertSortFilteredNonNegative(list: List[BigInt]): Boolean = {
    require(CycleUtils.checkNonNegative(list))
    decreases(list.size)
    if (list.isEmpty) {
      CycleUtils.checkNonNegative(sortFiltered(list))
    } else {
      assert(CycleUtils.checkNonNegative(list.tail))
      assert(assertSortFilteredNonNegative(list.tail))
      assert(assertInsertSortedNonNegative(list.head, sortFiltered(list.tail)))
      CycleUtils.checkNonNegative(sortFiltered(list))
    }
  }.holds

  def assertInsertSortedAllLessThan(x: BigInt, list: List[BigInt], bound: BigInt): Boolean = {
    require(x < bound)
    require(CycleUtils.allLessThan(list, bound))
    decreases(list.size)
    if (list.isEmpty) {
      CycleUtils.allLessThan(insertSorted(x, list), bound)
    } else if (x <= list.head) {
      CycleUtils.allLessThan(insertSorted(x, list), bound)
    } else {
      assert(assertInsertSortedAllLessThan(x, list.tail, bound))
      CycleUtils.allLessThan(insertSorted(x, list), bound)
    }
  }.holds

  def assertSortFilteredAllLessThan(list: List[BigInt], bound: BigInt): Boolean = {
    require(CycleUtils.allLessThan(list, bound))
    decreases(list.size)
    if (list.isEmpty) {
      CycleUtils.allLessThan(sortFiltered(list), bound)
    } else {
      assert(CycleUtils.allLessThan(list.tail, bound))
      assert(assertSortFilteredAllLessThan(list.tail, bound))
      assert(assertInsertSortedAllLessThan(list.head, sortFiltered(list.tail), bound))
      CycleUtils.allLessThan(sortFiltered(list), bound)
    }
  }.holds

  def assertValueNeverDecreases(a: BigInt, b: BigInt): Boolean = {
    require(a >= 1 && b >= 1)
    a * b >= a && a * b >= b && a * b >= BigInt(1)
  }.holds

  def assertSumPairwiseGaps(list: List[BigInt]): Boolean = {
    require(list.nonEmpty)
    decreases(list.size)
    if (list.size == 1) {
      ListUtils.sum(pairwiseGaps(list)) == BigInt(0)
    } else if (list.size == 2) {
      ListUtils.sum(pairwiseGaps(list)) == list(1) - list(0)
    } else {
      val tailResult = assertSumPairwiseGaps(list.tail)
      val headGap = list(1) - list.head
      val tailSum = ListUtils.sum(pairwiseGaps(list.tail))
      val totalSum = headGap + tailSum
      ListUtils.sum(pairwiseGaps(list)) == totalSum &&
        totalSum == list.last - list.head
    }
  }.holds

  def assertCalculateGapsSum(sorted: List[BigInt], modulus: BigInt): Boolean = {
    require(modulus > 0)
    decreases(sorted.size)
    if (sorted.isEmpty) {
      true
    } else if (sorted.size == 1) {
      ListUtils.sum(calculateGaps(sorted, modulus)) == modulus
    } else {
      assertSumPairwiseGaps(sorted)
      ListUtilsProperties.listCombine(
        pairwiseGaps(sorted),
        List(modulus - sorted.last + sorted.head)
      )
      ListUtils.sum(calculateGaps(sorted, modulus)) == modulus
    }
  }.holds

  def assertProductEqualOrBiggerThanElements(list: List[BigInt]): Boolean = {
    require(ListUtils.checkAllBiggerThanOne(list))
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
