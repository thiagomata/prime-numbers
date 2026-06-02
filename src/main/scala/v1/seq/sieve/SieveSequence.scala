package v1.seq.sieve

import stainless.collection.List
import stainless.lang.decreases
import v1.cycle.integral.recursive.CycleIntegral
import v1.cycle.memory.MemCycle

case class SieveSequence(
  head: BigInt,
  primes: List[BigInt],
  integral: CycleIntegral
) {
  require(head > 0)
  require(integral.cycle.size > 0)
  require(integral.cycle.values.forall(_ > 0))
  require(primes.forall(p => p > 0))
  require(integral.initialValue == BigInt(0))

  def apply(position: BigInt): BigInt = {
    require(position >= 0)
    if (position == 0) head
    else head + integral(position - 1)
  }

  def first: BigInt = head
  def knownPrimeLimit: BigInt = head * head
  def modulus: BigInt = SieveSequence.product(primes)

  def cycle: MemCycle = integral.cycle

  def next(): SieveSequence = {
    SieveSequence.nextLevel(head, primes, cycle)
  }
}

object SieveSequence {
  def S_0(): SieveSequence = {
    SieveSequence(
      head = BigInt(2),
      primes = List.empty,
      integral = CycleIntegral(BigInt(0), MemCycle(List(BigInt(1))))
    )
  }

  def apply(head: BigInt, cycle: MemCycle): SieveSequence = {
    require(head > 0)
    require(cycle.size > 0)
    require(cycle.values.forall(_ > 0))
    SieveSequence(
      head = head,
      primes = List.empty,
      integral = CycleIntegral(BigInt(0), cycle)
    )
  }

  def product(list: List[BigInt]): BigInt = {
    decreases(list.size)
    if (list.isEmpty) BigInt(1)
    else list.head * product(list.tail)
  }

  def nextLevel(head: BigInt, primes: List[BigInt], cycle: MemCycle): SieveSequence = {
    require(head > 0)
    require(primes.forall(p => p > 0))
    require(cycle.size > 0)
    require(cycle.values.forall(_ > 0))

    val p = head
    val m = product(primes)
    val newModulus = p * m

    val currentResidues = residues(m, primes)
    val expanded = expandResidues(currentResidues, m, p)
    val filtered = filterList(expanded, p)
    val sortedFiltered = sortFiltered(filtered)
    val allGaps = calculateGaps(sortedFiltered, newModulus)

    val headMod = head % newModulus
    val startIndex = nextResidueIndex(sortedFiltered, BigInt(0), headMod)
    val rotatedGaps = rotateAt(allGaps, startIndex)

    val nextResidueVal = residueAt(sortedFiltered, startIndex)
    val newHead = head + (nextResidueVal - headMod)

    SieveSequence(
      head = newHead,
      primes = head :: primes,
      integral = CycleIntegral(BigInt(0), MemCycle(rotatedGaps))
    )
  }

  private def residues(modulus: BigInt, primes: List[BigInt]): List[BigInt] = {
    require(modulus > 0)
    generateResidues(BigInt(0), modulus, primes)
  }

  private def generateResidues(i: BigInt, modulus: BigInt, primes: List[BigInt]): List[BigInt] = {
    require(i >= 0)
    require(i <= modulus)
    require(modulus > 0)
    decreases(modulus - i)
    if (i == modulus) List.empty
    else {
      val rest = generateResidues(i + 1, modulus, primes)
      if (isCoprime(i, primes)) i :: rest else rest
    }
  }

  private def isCoprime(value: BigInt, primes: List[BigInt]): Boolean = {
    require(primes.forall(p => p > 0))
    decreases(primes.size)
    if (primes.isEmpty) true
    else if (value % primes.head == BigInt(0)) false
    else isCoprime(value, primes.tail)
  }

  private def expandResidues(residues: List[BigInt], mod: BigInt, p: BigInt): List[BigInt] = {
    require(mod > 0)
    require(p > 0)
    expandSingleResidue(residues, mod, p, BigInt(0))
  }

  private def expandSingleResidue(residues: List[BigInt], mod: BigInt, p: BigInt, i: BigInt): List[BigInt] = {
    require(i >= 0 && i < p)
    require(p > 0)
    decreases(p - i)
    val offset = i * mod
    val currentSet = addOffset(residues, offset)
    if (i + 1 >= p) currentSet
    else currentSet ++ expandSingleResidue(residues, mod, p, i + 1)
  }

  private def addOffset(list: List[BigInt], offset: BigInt): List[BigInt] = {
    decreases(list.size)
    if (list.isEmpty) List.empty
    else (list.head + offset) :: addOffset(list.tail, offset)
  }

  private def filterList(list: List[BigInt], divisor: BigInt): List[BigInt] = {
    require(divisor > 0)
    decreases(list.size)
    if (list.isEmpty) List.empty
    else {
      val rest = filterList(list.tail, divisor)
      if (list.head % divisor != 0) list.head :: rest
      else rest
    }
  }

  private def sortFiltered(list: List[BigInt]): List[BigInt] = {
    decreases(list.size)
    if (list.isEmpty) List.empty
    else insertSorted(list.head, sortFiltered(list.tail))
  }

  private def insertSorted(x: BigInt, list: List[BigInt]): List[BigInt] = {
    decreases(list.size)
    if (list.isEmpty) List(x)
    else if (x <= list.head) x :: list
    else list.head :: insertSorted(x, list.tail)
  }

  private def calculateGaps(sorted: List[BigInt], modulus: BigInt): List[BigInt] = {
    require(modulus > 0)
    if (sorted.isEmpty) List.empty
    else if (sorted.size == 1) List(modulus)
    else {
      val innerGaps = pairwiseGaps(sorted)
      val wrapGap = modulus - sorted.last + sorted.head
      innerGaps ++ List(wrapGap)
    }
  }

  private def pairwiseGaps(list: List[BigInt]): List[BigInt] = {
    decreases(list.size)
    if (list.size < 2) List.empty
    else if (list.size == 2) List(list(1) - list(0))
    else (list(1) - list(0)) :: pairwiseGaps(list.tail)
  }

  private def nextResidueIndex(sorted: List[BigInt], currentIndex: BigInt, value: BigInt): BigInt = {
    require(currentIndex <= sorted.size)
    if (sorted.isEmpty) BigInt(0)
    else findResidueIndex(sorted, currentIndex, value)
  }

  private def findResidueIndex(list: List[BigInt], idx: BigInt, value: BigInt): BigInt = {
    require(list.nonEmpty)
    decreases(list.size)
    if (list.head > value) idx
    else if (list.tail.isEmpty) BigInt(0)
    else findResidueIndex(list.tail, idx + 1, value)
  }

  private def residueAt(sorted: List[BigInt], index: BigInt): BigInt = {
    if (sorted.isEmpty || index < 0 || index >= sorted.size) BigInt(0)
    else getAt(sorted, index)
  }

  private def getAt(list: List[BigInt], index: BigInt): BigInt = {
    require(index >= 0)
    require(index < list.size)
    decreases(index)
    if (index == BigInt(0)) list.head
    else getAt(list.tail, index - 1)
  }

  private def rotateAt(list: List[BigInt], index: BigInt): List[BigInt] = {
    if (list.isEmpty || index < 0 || index >= list.size) List.empty
    else if (index == BigInt(0)) list
    else {
      val (front, back) = splitAt(list, index)
      back ++ front
    }
  }

  private def splitAt(list: List[BigInt], index: BigInt): (List[BigInt], List[BigInt]) = {
    require(index >= 0 && index <= list.size)
    decreases(index)
    if (index == BigInt(0)) (List.empty, list)
    else {
      val (front, back) = splitAt(list.tail, index - 1)
      (list.head :: front, back)
    }
  }
}
