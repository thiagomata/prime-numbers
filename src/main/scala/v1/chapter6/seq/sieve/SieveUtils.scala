package v1.chapter6.seq.sieve

import stainless.collection.List
import stainless.lang.*
import v1.chapter2.div.Calc
import v1.chapter2.div.properties.AdditionAndMultiplication
import v1.chapter3.list.{ListBoundUtils, ListUtils, SortedList}
import v1.chapter3.list.properties.{ListUtilsProperties, RotationProperties}
import v1.chapter5.prime.{BezoutUtils, CoprimeUtils, Prime}
import scala.annotation.tailrec

object SieveUtils {
  def product(list: List[BigInt]): BigInt = {
    decreases(list.size)
    if (list.isEmpty) BigInt(1)
    else list.head * product(list.tail)
  }

  /**
   * Alias to the canonical chapter 5 coprimality predicate.
   *
   * Chapter 6 used to carry a structurally identical local implementation.
   * Scala accepted that duplication, but Stainless treated
   * `SieveUtils.isCoprime` and `CoprimeUtils.isCoprime` as different logical
   * functions, forcing bridge proofs to rediscover equivalence between the two.
   * Keeping this method as an alias preserves the chapter 6 API while ensuring
   * every caller reasons through the same predicate.
   */
  def isCoprime(value: BigInt, primes: List[BigInt]): Boolean = {
    require(ListUtils.checkAllPositive(primes))
    CoprimeUtils.isCoprime(value, primes)
  }

  def assertIsCoprimeSound(value: BigInt, primes: List[BigInt]): Boolean = {
    require(ListUtils.checkAllPositive(primes))
    require(isCoprime(value, primes))
    decreases(primes.size)
    if (primes.isEmpty) true
    else {
      Calc.mod(value, primes.head) != BigInt(0) &&
      assertIsCoprimeSound(value, primes.tail)
    }
  }.holds

  def assertModZeroImpliesDivTimesBEqualsA(a: BigInt, b: BigInt): Boolean = {
    require(b != 0)
    require(Calc.mod(a, b) == BigInt(0))
    Calc.div(a, b) * b == a
  }.holds

  def assertModZero(n: BigInt): Boolean = {
    require(n != BigInt(0))
    Calc.mod(BigInt(0), n) == BigInt(0)
  }.holds

  def assertMultipleModZero(k: BigInt, n: BigInt): Boolean = {
    require(n != BigInt(0))
    require(k >= BigInt(0))
    AdditionAndMultiplication.APlusMultipleTimesBSameMod(BigInt(0), n, k)
    assert(assertModZero(n))
    Calc.mod(k * n, n) == BigInt(0)
  }.holds

  def assertAddPreservesNotZeroMod(v: BigInt, p: BigInt, add: BigInt): Boolean = {
    require(p > 0)
    require(add >= 0)
    require(Calc.mod(v, p) != BigInt(0))
    require(Calc.mod(add, p) == BigInt(0))
    assert(assertModZeroImpliesDivTimesBEqualsA(add, p))
    val k = Calc.div(add, p)
    assert(k >= 0)
    AdditionAndMultiplication.APlusMultipleTimesBSameMod(v, p, k)
    Calc.mod(v + add, p) != BigInt(0)
  }.holds

  def assertProductNonNegative(list: List[BigInt]): Boolean = {
    require(ListUtils.checkAllPositive(list))
    decreases(list.size)
    if (list.isEmpty) {
      product(list) >= BigInt(0)
    } else {
      assert(assertProductNonNegative(list.tail))
      assert(product(list.tail) >= BigInt(0))
      assert(list.head >= BigInt(0))
      product(list) >= BigInt(0)
    }
  }.holds

  def assertHeadDividesProduct(list: List[BigInt]): Boolean = {
    require(list.nonEmpty)
    require(ListUtils.checkAllPositive(list))
    assert(assertProductNonNegative(list))
    assert(assertProductNonNegative(list.tail))
    assert(assertMultipleModZero(product(list.tail), list.head))
    Calc.mod(product(list), list.head) == BigInt(0)
  }.holds

  def assertAllElementsDivideProduct(list: List[BigInt]): Boolean = {
    require(ListUtils.checkAllPositive(list))
    assert(assertAllFromPrefix(BigInt(1), list))
    true
  }.holds

  def assertAllFromPrefix(prefixProd: BigInt, list: List[BigInt]): Boolean = {
    require(ListUtils.checkAllPositive(list))
    require(prefixProd > BigInt(0))
    decreases(list.size)
    if (list.isEmpty) true
    else {
      assert(assertProductNonNegative(list.tail))
      assert(product(list.tail) >= BigInt(0))
      val factor = prefixProd * product(list.tail)
      assert(factor >= BigInt(0))
      assert(assertMultipleModZero(factor, list.head))
      val totalProd = prefixProd * product(list)
      assert(totalProd == prefixProd * list.head * product(list.tail))
      assert(Calc.mod(totalProd, list.head) == BigInt(0))
      assert(assertAllFromPrefix(prefixProd * list.head, list.tail))
      true
    }
  }.holds

  def assertMultiplePreservesDivisible(a: BigInt, b: BigInt, p: BigInt): Boolean = {
    require(a >= 0)
    require(b >= 0)
    require(p > 0)
    require(Calc.mod(b, p) == BigInt(0))
    assert(assertModZeroImpliesDivTimesBEqualsA(b, p))
    val k = Calc.div(b, p)
    assert(k >= 0)
    assert(a * k >= 0)
    assert(assertMultipleModZero(a * k, p))
    Calc.mod(a * b, p) == BigInt(0)
  }.holds

  def assertExpandedCoprime(r: BigInt, i: BigInt, modulus: BigInt, primes: List[BigInt]): Boolean = {
    require(i >= 0)
    require(modulus > 0)
    require(modulus == product(primes))
    require(ListUtils.checkAllPositive(primes))
    require(isCoprime(r, primes))
    if (primes.isEmpty) true
    else assertExpandedCoprimeViaPrefix(r, i, modulus, primes, BigInt(1))
  }.holds

  def assertExpandedCoprimeViaPrefix(r: BigInt, i: BigInt, modulus: BigInt, primes: List[BigInt], prefixProd: BigInt): Boolean = {
    require(i >= 0)
    require(modulus > 0)
    require(prefixProd > BigInt(0))
    require(ListUtils.checkAllPositive(primes))
    require(modulus == prefixProd * product(primes))
    require(isCoprime(r, primes))
    decreases(primes.size)
    if (primes.isEmpty) true
    else {
      val p = primes.head
      val factor = prefixProd * product(primes.tail)
      assert(assertProductNonNegative(primes.tail))
      assert(product(primes.tail) >= BigInt(0))
      assert(factor >= BigInt(0))
      assert(assertMultipleModZero(factor, p))
      assert(Calc.mod(modulus, p) == BigInt(0))
      assert(assertIsCoprimeForAll(r, primes))
      assert(Calc.mod(r, p) != BigInt(0))
      assert(assertMultiplePreservesDivisible(i, modulus, p))
      assert(Calc.mod(i * modulus, p) == BigInt(0))
      assert(assertAddPreservesNotZeroMod(r, p, i * modulus))
      assert(Calc.mod(r + i * modulus, p) != BigInt(0))
      assert(assertExpandedCoprimeViaPrefix(r, i, modulus, primes.tail, prefixProd * p))
      true
    }
  }.holds

  def assertExpandedForAllJHelper(r: BigInt, modulus: BigInt, p: BigInt, j: BigInt, primes: List[BigInt]): Boolean = {
    require(j >= 0 && j < p)
    require(p > 0)
    require(modulus > 0)
    require(modulus == product(primes))
    require(ListUtils.checkAllPositive(primes))
    require(isCoprime(r, primes))
    decreases(p - j)
    assert(assertExpandedCoprime(r, j, modulus, primes))
    if (j + 1 >= p) true
    else {
      assert(assertExpandedForAllJHelper(r, modulus, p, j + 1, primes))
      true
    }
  }.holds

  def assertExpandedForAllJ(r: BigInt, modulus: BigInt, p: BigInt, primes: List[BigInt]): Boolean = {
    require(p > 0)
    require(modulus > 0)
    require(modulus == product(primes))
    require(ListUtils.checkAllPositive(primes))
    require(isCoprime(r, primes))
    assert(assertExpandedForAllJHelper(r, modulus, p, BigInt(0), primes))
    true
  }.holds

  def assertAllRExpandedCoprime(modulus: BigInt, p: BigInt, primes: List[BigInt]): Boolean = {
    require(p > 0)
    require(modulus > 0)
    require(modulus == product(primes))
    require(ListUtils.checkAllPositive(primes))
    assert(assertAllRExpandedCoprimeRec(BigInt(0), modulus, p, primes))
    true
  }.holds

  def assertAllRExpandedCoprimeRec(r: BigInt, modulus: BigInt, p: BigInt, primes: List[BigInt]): Boolean = {
    require(r >= 0)
    require(r <= modulus)
    require(p > 0)
    require(modulus > 0)
    require(modulus == product(primes))
    require(ListUtils.checkAllPositive(primes))
    decreases(modulus - r)
    if (r >= modulus) true
    else {
      assert(assertAllRExpandedCoprimeRec(r + 1, modulus, p, primes))
      if (isCoprime(r, primes)) {
        assert(assertExpandedForAllJ(r, modulus, p, primes))
      }
      true
    }
  }.holds

  def assertDivTransitive(c: BigInt, b: BigInt, a: BigInt): Boolean = {
    require(a > BigInt(0) && b > BigInt(0) && c >= BigInt(0))
    require(Calc.mod(c, b) == BigInt(0))
    require(Calc.mod(b, a) == BigInt(0))
    assert(assertModZeroImpliesDivTimesBEqualsA(c, b))
    assert(assertModZeroImpliesDivTimesBEqualsA(b, a))
    val cb = Calc.div(c, b)
    val ba = Calc.div(b, a)
    assert(cb * b == c)
    assert(ba * a == b)
    assert(cb * ba * a == c)
    assert(assertMultipleModZero(cb * ba, a))
    Calc.mod(c, a) == BigInt(0)
  }.holds

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
      if (Calc.mod(list.head, divisor) != BigInt(0)) list.head :: rest
      else rest
    }
  }

  def countMultiples(list: List[BigInt], divisor: BigInt): BigInt = {
    require(divisor > 0)
    decreases(list.size)
    if (list.isEmpty) BigInt(0)
    else {
      val rest = countMultiples(list.tail, divisor)
      assert(rest >= BigInt(0))
      assert(rest <= list.tail.size)
      if (Calc.mod(list.head, divisor) == BigInt(0)) {
        assert(rest + BigInt(1) <= list.size)
        rest + BigInt(1)
      } else {
        assert(rest <= list.size)
        rest
      }
    }
  }.ensuring(res => res >= BigInt(0) && res <= list.size)

  def countZeroOffsets(r: BigInt, step: BigInt, p: BigInt, i: BigInt): BigInt = {
    require(step >= 0)
    require(p > 0)
    require(i >= 0 && i <= p)
    decreases(p - i)
    if (i == p) BigInt(0)
    else {
      val rest = countZeroOffsets(r, step, p, i + BigInt(1))
      assert(rest >= BigInt(0))
      assert(rest <= p - (i + BigInt(1)))
      if (Calc.mod(r + i * step, p) == BigInt(0)) {
        assert(rest + BigInt(1) <= p - i)
        rest + BigInt(1)
      } else {
        assert(rest <= p - i)
        rest
      }
    }
  }.ensuring(res => res >= BigInt(0) && res <= p - i)

  def countOffsetHits(list: List[BigInt], step: BigInt, p: BigInt, i: BigInt): BigInt = {
    require(step >= 0)
    require(p > 0)
    require(i >= 0)
    decreases(list.size)
    if (list.isEmpty) BigInt(0)
    else {
      val rest = countOffsetHits(list.tail, step, p, i)
      assert(rest >= BigInt(0))
      assert(rest <= list.tail.size)
      if (Calc.mod(list.head + i * step, p) == BigInt(0)) {
        assert(rest + BigInt(1) <= list.size)
        rest + BigInt(1)
      } else {
        assert(rest <= list.size)
        rest
      }
    }
  }.ensuring(res => res >= BigInt(0) && res <= list.size)

  def countExpandedOffsetHits(list: List[BigInt], step: BigInt, p: BigInt, i: BigInt): BigInt = {
    require(step >= 0)
    require(p > 0)
    require(i >= 0 && i <= p)
    decreases(p - i)
    if (i == p) BigInt(0)
    else {
      val current = countOffsetHits(list, step, p, i)
      val rest = countExpandedOffsetHits(list, step, p, i + BigInt(1))
      assert(current >= BigInt(0))
      assert(current <= list.size)
      assert(rest >= BigInt(0))
      assert(rest <= list.size * (p - (i + BigInt(1))))
      assert(current + rest <= list.size * (p - i))
      current + rest
    }
  }.ensuring(res => res >= BigInt(0) && res <= list.size * (p - i))

  def assertCountZeroOffsetsFromWitness(
    r: BigInt,
    step: BigInt,
    p: BigInt,
    i: BigInt,
    witness: BigInt
  ): Boolean = {
    require(p >= 2)
    require(Prime.isPrime(p))
    require(r >= 0)
    require(step >= 0)
    require(Calc.mod(step, p) != BigInt(0))
    require(i >= 0 && i <= p)
    require(witness >= 0 && witness < p)
    require(Calc.mod(r + witness * step, p) == BigInt(0))
    decreases(p - i)

    if (i == p) {
      assert(i > witness)
      assert(countZeroOffsets(r, step, p, i) == BigInt(0))
      countZeroOffsets(r, step, p, i) ==
        (if (i <= witness) BigInt(1) else BigInt(0))
    } else {
      val rest = countZeroOffsets(r, step, p, i + BigInt(1))
      assert(assertCountZeroOffsetsFromWitness(r, step, p, i + BigInt(1), witness))
      assert(rest == (if (i + BigInt(1) <= witness) BigInt(1) else BigInt(0)))

      if (Calc.mod(r + i * step, p) == BigInt(0)) {
        BezoutUtils.assertCoprimeStepAtMostOneZero(r, step, p, i, witness)
        assert(i == witness)
        assert(i + BigInt(1) > witness)
        assert(rest == BigInt(0))
        assert(countZeroOffsets(r, step, p, i) == rest + BigInt(1))
        countZeroOffsets(r, step, p, i) ==
          (if (i <= witness) BigInt(1) else BigInt(0))
      } else {
        if (i == witness) {
          assert(r + i * step == r + witness * step)
          assert(Calc.mod(r + i * step, p) == BigInt(0))
        }
        assert(i != witness)
        if (i < witness) {
          assert(i + BigInt(1) <= witness)
          assert(rest == BigInt(1))
          assert(countZeroOffsets(r, step, p, i) == rest)
          countZeroOffsets(r, step, p, i) ==
            (if (i <= witness) BigInt(1) else BigInt(0))
        } else {
          assert(i > witness)
          assert(i + BigInt(1) > witness)
          assert(rest == BigInt(0))
          assert(countZeroOffsets(r, step, p, i) == rest)
          countZeroOffsets(r, step, p, i) ==
            (if (i <= witness) BigInt(1) else BigInt(0))
        }
      }
    }
  }.holds

  def assertCountZeroOffsetsOne(r: BigInt, step: BigInt, p: BigInt): Boolean = {
    require(p >= 2)
    require(Prime.isPrime(p))
    require(r >= 0)
    require(step >= 0)
    require(Calc.mod(step, p) != BigInt(0))

    val witness = BezoutUtils.coprimeStepZeroOffset(r, step, p)
    assert(witness >= BigInt(0))
    assert(witness < p)
    assert(Calc.mod(r + witness * step, p) == BigInt(0))
    assert(assertCountZeroOffsetsFromWitness(r, step, p, BigInt(0), witness))
    assert(BigInt(0) <= witness)
    countZeroOffsets(r, step, p, BigInt(0)) == BigInt(1)
  }.holds

  def assertCountMultiplesExpandSingleton(
    r: BigInt,
    step: BigInt,
    p: BigInt,
    i: BigInt
  ): Boolean = {
    require(step >= 0)
    require(p > 0)
    require(i >= 0 && i < p)
    decreases(p - i)

    val singleton = List(r)
    val currentSet = addOffset(singleton, i * step)
    if (i + BigInt(1) >= p) {
      assert(countMultiples(currentSet, p) == countZeroOffsets(r, step, p, i))
      countMultiples(expandSingleResidue(singleton, step, p, i), p) ==
        countZeroOffsets(r, step, p, i)
    } else {
      val rest = expandSingleResidue(singleton, step, p, i + BigInt(1))
      assert(assertCountMultiplesExpandSingleton(r, step, p, i + BigInt(1)))
      assert(countMultiples(rest, p) == countZeroOffsets(r, step, p, i + BigInt(1)))
      assert(assertCountMultiplesAppend(currentSet, rest, p))
      assert(countMultiples(currentSet ++ rest, p) ==
        countMultiples(currentSet, p) + countMultiples(rest, p))
      assert(countMultiples(currentSet, p) ==
        (if (Calc.mod(r + i * step, p) == BigInt(0)) BigInt(1) else BigInt(0)))
      countMultiples(expandSingleResidue(singleton, step, p, i), p) ==
        countZeroOffsets(r, step, p, i)
    }
  }.holds

  def assertCountMultiplesExpandSingletonOne(r: BigInt, step: BigInt, p: BigInt): Boolean = {
    require(p >= 2)
    require(Prime.isPrime(p))
    require(r >= 0)
    require(step >= 0)
    require(Calc.mod(step, p) != BigInt(0))

    assert(assertCountMultiplesExpandSingleton(r, step, p, BigInt(0)))
    assert(countMultiples(expandSingleResidue(List(r), step, p, BigInt(0)), p) ==
      countZeroOffsets(r, step, p, BigInt(0)))
    assert(assertCountZeroOffsetsOne(r, step, p))
    countMultiples(expandSingleResidue(List(r), step, p, BigInt(0)), p) == BigInt(1)
  }.holds

  def assertCountMultiplesAddOffset(
    list: List[BigInt],
    step: BigInt,
    p: BigInt,
    i: BigInt
  ): Boolean = {
    require(step >= 0)
    require(p > 0)
    require(i >= 0)
    decreases(list.size)
    if (list.isEmpty) {
      countMultiples(addOffset(list, i * step), p) ==
        countOffsetHits(list, step, p, i)
    } else {
      val restOffset = addOffset(list.tail, i * step)
      val restHits = countOffsetHits(list.tail, step, p, i)
      assert(assertCountMultiplesAddOffset(list.tail, step, p, i))
      assert(countMultiples(restOffset, p) == restHits)
      if (Calc.mod(list.head + i * step, p) == BigInt(0)) {
        assert(countMultiples(addOffset(list, i * step), p) ==
          countMultiples(restOffset, p) + BigInt(1))
        assert(countOffsetHits(list, step, p, i) == restHits + BigInt(1))
        countMultiples(addOffset(list, i * step), p) ==
          countOffsetHits(list, step, p, i)
      } else {
        assert(countMultiples(addOffset(list, i * step), p) ==
          countMultiples(restOffset, p))
        assert(countOffsetHits(list, step, p, i) == restHits)
        countMultiples(addOffset(list, i * step), p) ==
          countOffsetHits(list, step, p, i)
      }
    }
  }.holds

  def assertCountMultiplesExpandByOffsetHits(
    list: List[BigInt],
    step: BigInt,
    p: BigInt,
    i: BigInt
  ): Boolean = {
    require(step >= 0)
    require(p > 0)
    require(i >= 0 && i < p)
    decreases(p - i)

    val currentSet = addOffset(list, i * step)
    if (i + BigInt(1) >= p) {
      assert(i + BigInt(1) == p)
      assert(assertCountMultiplesAddOffset(list, step, p, i))
      assert(countMultiples(currentSet, p) == countOffsetHits(list, step, p, i))
      assert(countExpandedOffsetHits(list, step, p, i) == countOffsetHits(list, step, p, i))
      countMultiples(expandSingleResidue(list, step, p, i), p) ==
        countExpandedOffsetHits(list, step, p, i)
    } else {
      val rest = expandSingleResidue(list, step, p, i + BigInt(1))
      assert(assertCountMultiplesExpandByOffsetHits(list, step, p, i + BigInt(1)))
      assert(countMultiples(rest, p) == countExpandedOffsetHits(list, step, p, i + BigInt(1)))
      assert(assertCountMultiplesAppend(currentSet, rest, p))
      assert(assertCountMultiplesAddOffset(list, step, p, i))
      assert(countMultiples(currentSet, p) == countOffsetHits(list, step, p, i))
      assert(countMultiples(currentSet ++ rest, p) ==
        countMultiples(currentSet, p) + countMultiples(rest, p))
      assert(countExpandedOffsetHits(list, step, p, i) ==
        countOffsetHits(list, step, p, i) + countExpandedOffsetHits(list, step, p, i + BigInt(1)))
      countMultiples(expandSingleResidue(list, step, p, i), p) ==
        countExpandedOffsetHits(list, step, p, i)
    }
  }.holds

  def assertCountExpandedOffsetHitsCons(
    list: List[BigInt],
    step: BigInt,
    p: BigInt,
    i: BigInt
  ): Boolean = {
    require(!list.isEmpty)
    require(step >= 0)
    require(p > 0)
    require(i >= 0 && i <= p)
    decreases(p - i)

    if (i == p) {
      assert(countZeroOffsets(list.head, step, p, i) == BigInt(0))
      assert(countExpandedOffsetHits(list, step, p, i) == BigInt(0))
      assert(countExpandedOffsetHits(list.tail, step, p, i) == BigInt(0))
      countExpandedOffsetHits(list, step, p, i) ==
        countZeroOffsets(list.head, step, p, i) +
          countExpandedOffsetHits(list.tail, step, p, i)
    } else {
      val tailHits = countOffsetHits(list.tail, step, p, i)
      assert(assertCountExpandedOffsetHitsCons(list, step, p, i + BigInt(1)))
      assert(countExpandedOffsetHits(list, step, p, i + BigInt(1)) ==
        countZeroOffsets(list.head, step, p, i + BigInt(1)) +
          countExpandedOffsetHits(list.tail, step, p, i + BigInt(1)))
      assert(countExpandedOffsetHits(list, step, p, i) ==
        countOffsetHits(list, step, p, i) +
          countExpandedOffsetHits(list, step, p, i + BigInt(1)))
      assert(countExpandedOffsetHits(list.tail, step, p, i) ==
        tailHits + countExpandedOffsetHits(list.tail, step, p, i + BigInt(1)))

      if (Calc.mod(list.head + i * step, p) == BigInt(0)) {
        assert(countOffsetHits(list, step, p, i) == tailHits + BigInt(1))
        assert(countZeroOffsets(list.head, step, p, i) ==
          countZeroOffsets(list.head, step, p, i + BigInt(1)) + BigInt(1))
        countExpandedOffsetHits(list, step, p, i) ==
          countZeroOffsets(list.head, step, p, i) +
            countExpandedOffsetHits(list.tail, step, p, i)
      } else {
        assert(countOffsetHits(list, step, p, i) == tailHits)
        assert(countZeroOffsets(list.head, step, p, i) ==
          countZeroOffsets(list.head, step, p, i + BigInt(1)))
        countExpandedOffsetHits(list, step, p, i) ==
          countZeroOffsets(list.head, step, p, i) +
            countExpandedOffsetHits(list.tail, step, p, i)
      }
    }
  }.holds

  def assertCountExpandedOffsetHitsOnePerResidue(
    list: List[BigInt],
    step: BigInt,
    p: BigInt
  ): Boolean = {
    require(p >= 2)
    require(Prime.isPrime(p))
    require(step >= 0)
    require(Calc.mod(step, p) != BigInt(0))
    require(CycleUtils.checkNonNegative(list))
    decreases(list.size)

    if (list.isEmpty) {
      countExpandedOffsetHits(list, step, p, BigInt(0)) == list.size
    } else {
      assert(list.head >= BigInt(0))
      assert(CycleUtils.checkNonNegative(list.tail))
      assert(assertCountExpandedOffsetHitsCons(list, step, p, BigInt(0)))
      assert(countExpandedOffsetHits(list, step, p, BigInt(0)) ==
        countZeroOffsets(list.head, step, p, BigInt(0)) +
          countExpandedOffsetHits(list.tail, step, p, BigInt(0)))
      assert(assertCountZeroOffsetsOne(list.head, step, p))
      assert(countZeroOffsets(list.head, step, p, BigInt(0)) == BigInt(1))
      assert(assertCountExpandedOffsetHitsOnePerResidue(list.tail, step, p))
      assert(countExpandedOffsetHits(list.tail, step, p, BigInt(0)) == list.tail.size)
      assert(list.size == list.tail.size + BigInt(1))
      countExpandedOffsetHits(list, step, p, BigInt(0)) == list.size
    }
  }.holds

  def assertCountMultiplesExpandOnePerResidue(
    list: List[BigInt],
    step: BigInt,
    p: BigInt
  ): Boolean = {
    require(p >= 2)
    require(Prime.isPrime(p))
    require(step >= 0)
    require(Calc.mod(step, p) != BigInt(0))
    require(CycleUtils.checkNonNegative(list))

    assert(assertCountMultiplesExpandByOffsetHits(list, step, p, BigInt(0)))
    assert(countMultiples(expandSingleResidue(list, step, p, BigInt(0)), p) ==
      countExpandedOffsetHits(list, step, p, BigInt(0)))
    assert(assertCountExpandedOffsetHitsOnePerResidue(list, step, p))
    assert(countExpandedOffsetHits(list, step, p, BigInt(0)) == list.size)
    countMultiples(expandSingleResidue(list, step, p, BigInt(0)), p) == list.size
  }.holds

  def assertFilterExpandSingleResidueSizeByDensity(
    list: List[BigInt],
    step: BigInt,
    p: BigInt
  ): Boolean = {
    require(p >= 2)
    require(Prime.isPrime(p))
    require(step >= 0)
    require(Calc.mod(step, p) != BigInt(0))
    require(CycleUtils.checkNonNegative(list))

    val expanded = expandSingleResidue(list, step, p, BigInt(0))
    assert(assertFilterListSizeByCount(expanded, p))
    assert(filterList(expanded, p).size == expanded.size - countMultiples(expanded, p))
    assert(assertCountMultiplesExpandOnePerResidue(list, step, p))
    assert(countMultiples(expanded, p) == list.size)
    assert(assertExpandSingleResidueSize(list, step, p, BigInt(0)))
    assert(expanded.size == list.size * p)
    assert(filterList(expanded, p).size == list.size * p - list.size)
    assert(list.size * p - list.size == list.size * (p - BigInt(1)))
    filterList(expanded, p).size == list.size * (p - BigInt(1))
  }.holds

  def assertFilterExpandResiduesSizeByDensity(
    list: List[BigInt],
    step: BigInt,
    p: BigInt
  ): Boolean = {
    require(p >= 2)
    require(Prime.isPrime(p))
    require(step > 0)
    require(Calc.mod(step, p) != BigInt(0))
    require(CycleUtils.checkNonNegative(list))

    assert(assertFilterExpandSingleResidueSizeByDensity(list, step, p))
    filterList(expandResidues(list, step, p), p).size == list.size * (p - BigInt(1))
  }.holds

  def assertFilterListSizeByCount(list: List[BigInt], divisor: BigInt): Boolean = {
    require(divisor > 0)
    decreases(list.size)
    if (list.isEmpty) {
      filterList(list, divisor).size == list.size - countMultiples(list, divisor)
    } else {
      val restFiltered = filterList(list.tail, divisor)
      val restCount = countMultiples(list.tail, divisor)
      assert(restCount >= BigInt(0))
      assert(restCount <= list.tail.size)
      assert(assertFilterListSizeByCount(list.tail, divisor))
      assert(restFiltered.size == list.tail.size - restCount)

      if (Calc.mod(list.head, divisor) != BigInt(0)) {
        assert(countMultiples(list, divisor) == restCount)
        assert(filterList(list, divisor).size == restFiltered.size + BigInt(1))
        assert(list.size == list.tail.size + BigInt(1))
        filterList(list, divisor).size == list.size - countMultiples(list, divisor)
      } else {
        assert(countMultiples(list, divisor) == restCount + BigInt(1))
        assert(filterList(list, divisor).size == restFiltered.size)
        assert(list.size == list.tail.size + BigInt(1))
        filterList(list, divisor).size == list.size - countMultiples(list, divisor)
      }
    }
  }.holds

  def assertCountMultiplesAppend(
    left: List[BigInt],
    right: List[BigInt],
    divisor: BigInt
  ): Boolean = {
    require(divisor > 0)
    decreases(left.size)
    if (left.isEmpty) {
      countMultiples(left ++ right, divisor) ==
        countMultiples(left, divisor) + countMultiples(right, divisor)
    } else {
      val tailAppend = left.tail ++ right
      val tailCount = countMultiples(left.tail, divisor)
      val rightCount = countMultiples(right, divisor)
      assert(assertCountMultiplesAppend(left.tail, right, divisor))
      assert(countMultiples(tailAppend, divisor) == tailCount + rightCount)

      if (Calc.mod(left.head, divisor) == BigInt(0)) {
        assert(countMultiples(left, divisor) == tailCount + BigInt(1))
        assert(countMultiples(left ++ right, divisor) == countMultiples(tailAppend, divisor) + BigInt(1))
        countMultiples(left ++ right, divisor) ==
          countMultiples(left, divisor) + countMultiples(right, divisor)
      } else {
        assert(countMultiples(left, divisor) == tailCount)
        assert(countMultiples(left ++ right, divisor) == countMultiples(tailAppend, divisor))
        countMultiples(left ++ right, divisor) ==
          countMultiples(left, divisor) + countMultiples(right, divisor)
      }
    }
  }.holds

  def assertFilterNonEmpty(list: List[BigInt], divisor: BigInt): Boolean = {
    require(divisor > 0)
    decreases(list.size)
    if (list.isEmpty) true
    else if (Calc.mod(list.head, divisor) != BigInt(0)) {
      assert(assertFilterNonEmpty(list.tail, divisor))
    } else {
      assert(assertFilterNonEmpty(list.tail, divisor))
    }
    true
  }.holds

  def assertIsCoprimeForAll(n: BigInt, primes: List[BigInt]): Boolean = {
    require(ListUtils.checkAllPositive(primes))
    require(isCoprime(n, primes))
    decreases(primes.size)
    if (primes.isEmpty) true
    else {
      assert(assertIsCoprimeForAll(n, primes.tail))
      Calc.mod(n, primes.head) != BigInt(0)
    }
  }.holds

  /**
   * The value 1 is coprime to every list of primes strictly greater than 1.
   *
   * Plain math:
   *   For each p > 1, mod(1, p) == 1 != 0, so the recursive coprimality
   *   predicate never short-circuits to false. By induction on the list,
   *   isCoprime(1, primes) holds for every such list.
   *
   * This is an isolated inductive helper: proving the recursive predicate
   * isCoprime(1, primes) directly at a call site times out, but a cached
   * same-class lemma with the ModSmallDividend hint discharges each step.
   * Both allGreaterThan(primes, 1) (for the math) and checkAllPositive(primes)
   * (for isCoprime's contract) are required, avoiding a recursive predicate
   * bridge between the two.
   */
  def assertIsCoprimeOne(primes: List[BigInt]): Boolean = {
    require(ListBoundUtils.allGreaterThan(primes, BigInt(1)))
    require(ListUtils.checkAllPositive(primes))
    decreases(primes.size)
    if (primes.isEmpty) {
      CoprimeUtils.isCoprime(BigInt(1), primes)
    } else {
      assert(primes.head > BigInt(1))
      assert(v1.chapter2.div.properties.ModSmallDividend.modSmallDividend(BigInt(1), primes.head))
      assert(Calc.mod(BigInt(1), primes.head) == BigInt(1))
      assert(Calc.mod(BigInt(1), primes.head) != BigInt(0))
      assert(ListBoundUtils.allGreaterThan(primes.tail, BigInt(1)))
      assert(ListUtils.checkAllPositive(primes.tail))
      assert(assertIsCoprimeOne(primes.tail))
      CoprimeUtils.isCoprime(BigInt(1), primes)
    }
  }.holds

  def findPrimeFactorInList(n: BigInt, primes: List[BigInt]): BigInt = {
    require(ListUtils.checkAllPositive(primes))
    require(!isCoprime(n, primes))
    decreases(primes.size)
    if (primes.isEmpty) BigInt(0)
    else if (Calc.mod(n, primes.head) == BigInt(0)) primes.head
    else findPrimeFactorInList(n, primes.tail)
  }

  def assertPrimeFactorDivides(n: BigInt, primes: List[BigInt]): Boolean = {
    require(ListUtils.checkAllPositive(primes))
    require(!isCoprime(n, primes))
    decreases(primes.size)
    if (primes.isEmpty) true
    else if (Calc.mod(n, primes.head) == BigInt(0))
      Calc.mod(n, findPrimeFactorInList(n, primes)) == BigInt(0)
    else {
      assert(assertPrimeFactorDivides(n, primes.tail))
      Calc.mod(n, findPrimeFactorInList(n, primes)) == BigInt(0)
    }
  }.holds

  def assertNoDivisorByFactorList(n: BigInt, d: BigInt, primes: List[BigInt]): Boolean = {
    require(n > 1)
    require(d >= 2)
    require(ListUtils.checkAllPositive(primes))
    require(isCoprime(n, primes))
    require(!isCoprime(d, primes))
    decreases(primes.size)

    if (primes.isEmpty) true
    else {
      val p = primes.head
      if (Calc.mod(d, p) == BigInt(0)) {
        assert(assertIsCoprimeForAll(n, primes))
        if (Calc.mod(n, d) == BigInt(0)) {
          assert(assertModZeroImpliesDivTimesBEqualsA(n, d))
          assert(assertModZeroImpliesDivTimesBEqualsA(d, p))
          val nd = Calc.div(n, d)
          val dp = Calc.div(d, p)
          assert(nd * d == n)
          assert(dp * p == d)
          assert(nd * dp * p == n)
          assert(nd * dp >= 0)
          assert(assertMultipleModZero(nd * dp, p))
          false
        } else {
          true
        }
      } else {
        assert(assertNoDivisorByFactorList(n, d, primes.tail))
        Calc.mod(n, d) != BigInt(0)
      }
    }
  }.holds

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

  def assertCalculateGapsSize(sorted: List[BigInt], modulus: BigInt): Boolean = {
    require(modulus > 0)
    require(sorted.nonEmpty)
    if (sorted.size == 1) {
      calculateGaps(sorted, modulus).size == BigInt(1)
    } else {
      assert(assertPairwiseGapsSize(sorted))
      calculateGaps(sorted, modulus).size == sorted.size
    }
  }.holds

  def pairwiseGaps(list: List[BigInt]): List[BigInt] = {
    decreases(list.size)
    if (list.size < 2) List.empty
    else if (list.size == 2) List(list(1) - list(0))
    else (list(1) - list(0)) :: pairwiseGaps(list.tail)
  }

  def assertPairwiseGapsSize(list: List[BigInt]): Boolean = {
    require(list.size >= 1)
    decreases(list.size)
    if (list.size == 1) {
      pairwiseGaps(list).size == 0
    } else if (list.size == 2) {
      pairwiseGaps(list).size == 1
    } else {
      assert(assertPairwiseGapsSize(list.tail))
      pairwiseGaps(list).size == list.size - 1
    }
  }.holds

  /**
   * Pairwise gaps of a strictly ascending list are positive.
   *
   * Math:
   *
   *   isAscending(L) => forall i < size(L)-1:
   *     L(i + 1) - L(i) > 0
   *
   * `pairwiseGaps` stores exactly those adjacent differences, so every emitted
   * gap is greater than zero. This is the local positivity step for
   * `calculateGaps`; it deliberately avoids the wrap gap and pipeline range
   * obligations.
   */
  def assertPairwiseGapsAllPositive(list: List[BigInt]): Boolean = {
    require(list.nonEmpty)
    require(SortedList.isAscending(list))
    decreases(list.size)

    val gaps = pairwiseGaps(list)
    if (list.size <= BigInt(1)) {
      ListBoundUtils.allGreaterThan(gaps, BigInt(0))
    } else if (list.size == BigInt(2)) {
      assert(SortedList.assertIsAscendingAtIndex(list, BigInt(0)))
      assert(list(BigInt(1)) > list(BigInt(0)))
      assert(list(BigInt(1)) - list(BigInt(0)) > BigInt(0))
      ListBoundUtils.allGreaterThan(gaps, BigInt(0))
    } else {
      assert(SortedList.assertIsAscendingAtIndex(list, BigInt(0)))
      assert(list(BigInt(1)) > list(BigInt(0)))
      assert(list(BigInt(1)) - list(BigInt(0)) > BigInt(0))
      assert(SortedList.assertTailAscending(list))
      assert(SortedList.isAscending(list.tail))
      assert(assertPairwiseGapsAllPositive(list.tail))
      assert(ListBoundUtils.allGreaterThan(pairwiseGaps(list.tail), BigInt(0)))
      ListBoundUtils.allGreaterThan(gaps, BigInt(0))
    }
  }.holds

  /**
   * The wrap gap of an upper-bounded sorted residue list is positive.
   *
   * Math:
   *
   *   sorted.last < modulus
   *   sorted.head >= 0
   *   ------------------------------
   *   modulus - sorted.last + sorted.head > 0
   *
   * This isolates the final gap in `calculateGaps`. The upper bound arrives as
   * the recursive predicate `allLessThan(sorted, modulus)`, so the proof first
   * exposes the pointwise fact at index `size - 1` and then rewrites it through
   * `last`.
   */
  def assertWrapGapPositive(sorted: List[BigInt], modulus: BigInt): Boolean = {
    require(modulus > BigInt(0))
    require(sorted.nonEmpty)
    require(ListBoundUtils.allLessThan(sorted, modulus))
    require(sorted.head >= BigInt(0))

    assert(ListUtilsProperties.assertLastEqualsLastPosition(sorted))
    assert(sorted.last == sorted(sorted.size - BigInt(1)))
    assert(ListBoundUtils.assertLessThanAtIndex(sorted, modulus, sorted.size - BigInt(1)))
    assert(sorted(sorted.size - BigInt(1)) < modulus)
    assert(sorted.last < modulus)
    assert(modulus - sorted.last > BigInt(0))
    assert(modulus - sorted.last + sorted.head > BigInt(0))
    modulus - sorted.last + sorted.head > BigInt(0)
  }.holds

  /**
   * `calculateGaps` emits only positive gaps for a sorted residue list inside a
   * positive modulus.
   *
   * Math:
   *
   *   adjacent gaps: sorted(i + 1) - sorted(i) > 0
   *   wrap gap:      modulus - sorted.last + sorted.head > 0
   *   -----------------------------------------------------
   *   all gaps emitted by calculateGaps(sorted, modulus) > 0
   *
   * The proof composes the pairwise-gap and wrap-gap lemmas instead of asking
   * Stainless to rediscover sorting, bounds, and append preservation in the
   * same VC.
   */
  def assertCalculateGapsAllPositive(sorted: List[BigInt], modulus: BigInt): Boolean = {
    require(modulus > BigInt(0))
    require(sorted.nonEmpty)
    require(SortedList.isAscending(sorted))
    require(ListBoundUtils.allLessThan(sorted, modulus))
    require(sorted.head >= BigInt(0))

    val gaps = calculateGaps(sorted, modulus)
    if (sorted.size == BigInt(1)) {
      assert(gaps == List(modulus))
      assert(modulus > BigInt(0))
      ListBoundUtils.allGreaterThan(gaps, BigInt(0))
    } else {
      val pw = pairwiseGaps(sorted)
      val wrapGap = modulus - sorted.last + sorted.head
      assert(gaps == pw ++ List(wrapGap))
      assert(assertPairwiseGapsAllPositive(sorted))
      assert(ListBoundUtils.allGreaterThan(pw, BigInt(0)))
      assert(assertWrapGapPositive(sorted, modulus))
      assert(wrapGap > BigInt(0))
      assert(ListBoundUtils.allGreaterThan(List(wrapGap), BigInt(0)))
      assert(ListBoundUtils.assertAppendGreaterThan(pw, List(wrapGap), BigInt(0)))
      ListBoundUtils.allGreaterThan(gaps, BigInt(0))
    }
  }.holds

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

  /*
   * Delegates to the canonical ch3 definition (ListUtils.splitAt). Kept as a
   * thin wrapper so existing ch6 callers compile unchanged; the canonical
   * implementation and its recombination lemma live in ch3 (LEARNINGS §5.3:
   * avoid duplicate predicate surfaces that Stainless treats as distinct).
   */
  def splitAt(list: List[BigInt], index: BigInt): (List[BigInt], List[BigInt]) = {
    require(index >= 0 && index <= list.size)
    ListUtils.splitAt(list, index)
  }

  /* Delegates to the canonical ch3 lemma (ListBoundUtils.assertSplitAtPreservesAllGreaterThan). */
  def assertSplitAtPreservesAllGreaterThan(list: List[BigInt], index: BigInt, value: BigInt): Boolean = {
    require(index >= 0 && index <= list.size)
    require(ListBoundUtils.allGreaterThan(list, value))
    ListBoundUtils.assertSplitAtPreservesAllGreaterThan(list, index, value)
  }.holds

  /* Delegates to the canonical ch3 definition (ListUtils.rotateAt). */
  def rotateAt(list: List[BigInt], index: BigInt): List[BigInt] = {
    require(index >= 0)
    ListUtils.rotateAt(list, index)
  }

  /* Delegates to the canonical ch3 lemma (RotationProperties.assertRotateSameLowerBound). */
  def assertRotateAtPreservesAllGreaterThan(list: List[BigInt], index: BigInt, value: BigInt): Boolean = {
    require(index >= 0)
    require(ListBoundUtils.allGreaterThan(list, value))
    RotationProperties.assertRotateSameLowerBound(list, index, value)
  }.holds

  /*
   * Non-emptiness follows from same-size (rotation preserves size); delegates
   * to the canonical ch3 lemma.
   */
  def assertRotateAtPreservesNonEmpty(list: List[BigInt], index: BigInt): Boolean = {
    require(list.nonEmpty)
    require(index >= 0)
    assert(RotationProperties.assertRotateSameSize(list, index))
    assert(rotateAt(list, index).size == list.size)
    rotateAt(list, index).nonEmpty
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

  /**
   * addOffset preserves list size.
   *
   * Math:
   *   addOffset(list, offset).size == list.size
   *
   * Structural induction on list: addOffset conses one element per input
   * element, so the output length equals the input length. No precondition
   * on offset or the list contents is needed.
   */
  def assertAddOffsetSize(list: List[BigInt], offset: BigInt): Boolean = {
    decreases(list.size)
    if (list.isEmpty) {
      addOffset(list, offset).size == list.size
    } else {
      assert(assertAddOffsetSize(list.tail, offset))
      addOffset(list, offset).size == list.size
    }
  }.holds

  /**
   * Append preserves list size.
   *
   * Math:
   *   (left ++ right).size == left.size + right.size
   *
   * Structural induction on left. Each cons of left contributes exactly one
   * element to the front of (left ++ right), so the total length is the sum.
   * No precondition on the list contents is needed.
   */
  def assertAppendSize(left: List[BigInt], right: List[BigInt]): Boolean = {
    decreases(left.size)
    if (left.isEmpty) {
      (left ++ right).size == left.size + right.size
    } else {
      assert(assertAppendSize(left.tail, right))
      (left ++ right).size == left.size + right.size
    }
  }.holds

  /**
   * Size of the expanded residue list.
   *
   * Math:
   *   expandSingleResidue(residues, mod, p, i).size == residues.size * (p - i)
   *
   * By induction on (p - i). The expansion lays down one addOffset block of
   * size residues.size per remaining index, from i up to p-1 inclusive, giving
   * (p - i) blocks. The base case (i == p-1) is a single addOffset block; the
   * inductive case appends the current block (size residues.size, by
   * assertAddOffsetSize) to the rest (size residues.size * (p - i - 1), by the
   * induction hypothesis), and assertAppendSize sums them to
   * residues.size * (p - i).
   */
  def assertExpandSingleResidueSize(
    residues: List[BigInt], mod: BigInt, p: BigInt, i: BigInt
  ): Boolean = {
    require(i >= 0 && i < p)
    require(p > 0)
    decreases(p - i)
    val currentSet = addOffset(residues, i * mod)
    assert(assertAddOffsetSize(residues, i * mod))
    if (i + 1 >= p) {
      currentSet.size == residues.size * (p - i)
    } else {
      assert(assertExpandSingleResidueSize(residues, mod, p, i + 1))
      val rest = expandSingleResidue(residues, mod, p, i + 1)
      assert(assertAppendSize(currentSet, rest))
      (currentSet ++ rest).size == residues.size * (p - i)
    }
  }.holds

  /**
   * Size of the top-level expanded residue list.
   *
   * Math:
   *   expandResidues(residues, mod, p).size == residues.size * p
   *
   * Direct corollary of assertExpandSingleResidueSize at i == 0, since
   * expandResidues delegates to expandSingleResidue(residues, mod, p, 0) and
   * p - 0 == p.
   */
  def assertExpandResiduesSize(
    residues: List[BigInt], mod: BigInt, p: BigInt
  ): Boolean = {
    require(mod > 0)
    require(p > 0)
    assert(assertExpandSingleResidueSize(residues, mod, p, BigInt(0)))
    expandResidues(residues, mod, p).size == residues.size * p
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
      ListUtils.listCombine(
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

  def hasPrimeFactorInList(d: BigInt, primes: List[BigInt]): Boolean = {
    require(ListUtils.checkAllPositive(primes))
    decreases(primes.size)
    if (primes.isEmpty) false
    else if (Calc.mod(d, primes.head) == BigInt(0)) true
    else hasPrimeFactorInList(d, primes.tail)
  }

  def assertHasPrimeFactorImpliesNotCoprime(d: BigInt, primes: List[BigInt]): Boolean = {
    require(ListUtils.checkAllPositive(primes))
    require(hasPrimeFactorInList(d, primes))
    decreases(primes.size)
    if (primes.isEmpty) {
      false
    } else if (Calc.mod(d, primes.head) == BigInt(0)) {
      Calc.mod(d, primes.head) == BigInt(0) && !isCoprime(d, primes)
    } else {
      assert(assertHasPrimeFactorImpliesNotCoprime(d, primes.tail))
      !isCoprime(d, primes)
    }
  }.holds

  def assertGenerateResiduesAllCoprime(i: BigInt, modulus: BigInt, primes: List[BigInt]): Boolean = {
    require(i >= 0)
    require(i <= modulus)
    require(modulus > 0)
    require(ListUtils.checkAllPositive(primes))
    decreases(modulus - i)
    if (i == modulus) true
    else {
      val rest = generateResidues(i + 1, modulus, primes)
      assert(assertGenerateResiduesAllCoprime(i + 1, modulus, primes))
      if (isCoprime(i, primes)) {
        assert(assertIsCoprimeForAll(i, primes))
      }
      true
    }
  }.holds

  def assertResiduesAllCoprime(modulus: BigInt, primes: List[BigInt]): Boolean = {
    require(modulus > 0)
    require(ListUtils.checkAllPositive(primes))
    assert(assertGenerateResiduesAllCoprime(BigInt(0), modulus, primes))
    true
  }.holds

  /**
   * Proves that generateResidues(i, modulus, primes) contains v
   * when i <= v < modulus and isCoprime(v, primes).
   *
   * This establishes the completeness of the residues list:
   * every coprime value in [0, modulus) appears in the list.
   */
  def assertGenerateResiduesContainsCoprime(
    v: BigInt,
    i: BigInt,
    modulus: BigInt,
    primes: List[BigInt]
  ): Boolean = {
    require(i >= 0)
    require(i <= modulus)
    require(v >= i)
    require(v < modulus)
    require(modulus > 0)
    require(ListUtils.checkAllPositive(primes))
    require(isCoprime(v, primes))
    decreases(modulus - i)

    if (i == modulus) {
      false
    } else if (i == v) {
      generateResidues(i, modulus, primes).contains(i)
    } else {
      assert(assertGenerateResiduesContainsCoprime(v, i + 1, modulus, primes))
      generateResidues(i, modulus, primes).contains(v)
    }
  }.holds

  /**
   * Top-level residues completeness lemma.
   * Proves that residues(modulus, primes) contains every coprime value
   * in [0, modulus).
   */
  def assertResiduesComplete(modulus: BigInt, primes: List[BigInt]): Boolean = {
    require(modulus > 0)
    require(ListUtils.checkAllPositive(primes))
    assertResiduesCompleteRec(BigInt(0), modulus, primes)
  }.holds

  /**
   * The residues list is non-empty whenever modulus >= 2 and every listed
   * prime is strictly greater than 1.
   *
   * Plain math:
   *   For modulus >= 2, the value 1 lies in [0, modulus). Since every prime
   *   p > 1 satisfies mod(1, p) == 1 != 0, the value 1 is coprime to the list
   *   (assertIsCoprimeOne). By the completeness lemma, residues(modulus, primes)
   *   contains 1, hence is non-empty.
   *
   * This discharges the nextResidues(seq).nonEmpty precondition of the
   * filtered-size density theorem for real sieve states whose tail primes
   * come from PrimeUtils.primeValues (which ensures allGreaterThan(_, 1)).
   */
  def assertResiduesNonEmpty(modulus: BigInt, primes: List[BigInt]): Boolean = {
    require(modulus >= BigInt(2))
    require(ListBoundUtils.allGreaterThan(primes, BigInt(1)))
    require(ListUtils.checkAllPositive(primes))
    assert(assertIsCoprimeOne(primes))
    assert(CoprimeUtils.isCoprime(BigInt(1), primes))
    assert(assertGenerateResiduesContainsCoprime(BigInt(1), BigInt(0), modulus, primes))
    residues(modulus, primes).nonEmpty
  }.holds

  def assertResiduesCompleteRec(
    i: BigInt,
    modulus: BigInt,
    primes: List[BigInt]
  ): Boolean = {
    require(i >= 0)
    require(i <= modulus)
    require(modulus > 0)
    require(ListUtils.checkAllPositive(primes))
    decreases(modulus - i)

    if (i == modulus) true
    else {
      if (isCoprime(i, primes)) {
        assert(assertGenerateResiduesContainsCoprime(i, BigInt(0), modulus, primes))
      }
      assertResiduesCompleteRec(i + 1, modulus, primes)
    }
  }.holds

  def assertNoDivisorInRangeHelper(
    n: BigInt,
    primes: List[BigInt],
    from: BigInt,
    to: BigInt
  ): Boolean = {
    require(n > 1)
    require(from >= 2)
    require(to >= from)
    require(ListUtils.checkAllPositive(primes))
    require(isCoprime(n, primes))
    require(assertAllNotCoprimeInRange(to, from, primes))
    decreases(to - from)
    if (from >= to) true
    else {
      assert(hasPrimeFactorInList(from, primes))
      assert(assertHasPrimeFactorImpliesNotCoprime(from, primes))
      assert(assertNoDivisorByFactorList(n, from, primes))
      Calc.mod(n, from) != BigInt(0) &&
        assertNoDivisorInRangeHelper(n, primes, from + 1, to)
    }
  }.holds

  def assertAllNotCoprimeInRange(limit: BigInt, d: BigInt, primes: List[BigInt]): Boolean = {
    require(limit >= 2)
    require(d >= 2)
    require(d <= limit)
    require(ListUtils.checkAllPositive(primes))
    decreases(limit - d)
    if (d >= limit) true
    else {
      hasPrimeFactorInList(d, primes) && assertAllNotCoprimeInRange(limit, d + 1, primes)
    }
  }
}
