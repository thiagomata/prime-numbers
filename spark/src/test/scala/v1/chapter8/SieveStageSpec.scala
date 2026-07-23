package v1.chapter8

import org.scalatest.funsuite.AnyFunSuite

class SieveStageSpec extends AnyFunSuite {

  test("base stage has head=2, gaps=[1], modulus=1") {
    val s = SieveStage.base
    assert(s.head === 2L)
    assert(s.gaps === Array(1L))
    assert(s.modulus === 1L)
    assert(s.period === 1)
    assert(s.tailPrimes.isEmpty)
  }

  test("base stage first 10 values are 2,3,4,...,11") {
    val vals = SieveStage.base.firstNValues(10)
    assert(vals === Array(2L, 3L, 4L, 5L, 6L, 7L, 8L, 9L, 10L, 11L))
  }

  test("S1 has head=3, gaps=[2], modulus=2") {
    val (s, _) = SieveStage.base.nextStage()
    assert(s.head === 3L)
    assert(s.gaps === Array(2L))
    assert(s.modulus === 2L)
    assert(s.period === 1)
    assert(s.tailPrimes === Array(2L))
  }

  test("S1 first 10 values are 3,5,7,9,11,13,15,17,19,21") {
    val (s, _) = SieveStage.base.nextStage()
    val vals = s.firstNValues(10)
    assert(vals === Array(3L, 5L, 7L, 9L, 11L, 13L, 15L, 17L, 19L, 21L))
  }

  test("S2 has head=5, gaps=[2,4], modulus=6, period=2") {
    val (s1, _) = SieveStage.base.nextStage()
    val (s2, _) = s1.nextStage()
    assert(s2.head === 5L)
    assert(s2.gaps === Array(2L, 4L))
    assert(s2.modulus === 6L)
    assert(s2.period === 2)
  }

  test("S2 first 10 values are 5,7,11,13,17,19,23,25,29,31") {
    val (s1, _) = SieveStage.base.nextStage()
    val (s2, _) = s1.nextStage()
    val vals = s2.firstNValues(10)
    assert(vals === Array(5L, 7L, 11L, 13L, 17L, 19L, 23L, 25L, 29L, 31L))
  }

  test("S3 has head=7, modulus=30, period=8") {
    val (s1, _) = SieveStage.base.nextStage()
    val (s2, _) = s1.nextStage()
    val (s3, _) = s2.nextStage()
    assert(s3.head === 7L)
    assert(s3.modulus === 30L)
    assert(s3.period === 8)
    assert(s3.gaps.length === 8)
  }

  test("S3 gaps sum to modulus") {
    val (s1, _) = SieveStage.base.nextStage()
    val (s2, _) = s1.nextStage()
    val (s3, _) = s2.nextStage()
    assert(s3.gaps.sum === s3.modulus)
  }

  test("S3 first 8 values are coprime to 2,3,5") {
    val (s1, _) = SieveStage.base.nextStage()
    val (s2, _) = s1.nextStage()
    val (s3, _) = s2.nextStage()
    val vals = s3.firstNValues(8)
    vals.foreach { v =>
      assert(v % 2 != 0, s"$v is divisible by 2")
      assert(v % 3 != 0, s"$v is divisible by 3")
      assert(v % 5 != 0, s"$v is divisible by 5")
    }
  }

  test("isCoprime works correctly") {
    assert(SieveStage.isCoprime(1L, Array(2L, 3L, 5L)) === true)
    assert(SieveStage.isCoprime(2L, Array(2L, 3L, 5L)) === false)
    assert(SieveStage.isCoprime(3L, Array(2L, 3L, 5L)) === false)
    assert(SieveStage.isCoprime(7L, Array(2L, 3L, 5L)) === true)
    assert(SieveStage.isCoprime(0L, Array(2L)) === false)
  }

  test("computeResidues for base stage are [0]") {
    val residues = SieveStage.base.computeResidues()
    assert(residues === Array(0L))
  }

  test("computeResidues for S1 are [1]") {
    val (s1, _) = SieveStage.base.nextStage()
    val residues = s1.computeResidues()
    assert(residues === Array(1L))
  }

  test("S1 lineage: single gap [2] is merge from [1]") {
    val (_, lineage) = SieveStage.base.nextStage()
    assert(lineage.length === 1)
    assert(lineage(0).gap === 2L)
    assert(lineage(0).origin === "merge")
    assert(lineage(0).mergeCount >= 1)
  }

  test("S2 lineage: gap 2 is copy, gap 4 is merge") {
    val (s1, _) = SieveStage.base.nextStage()
    val (s2, s2Lineage) = s1.nextStage()
    assert(s2.gaps === Array(2L, 4L))
    assert(s2Lineage(0).origin === "copy")
    assert(s2Lineage(0).mergeCount === 1)
    assert(s2Lineage(1).origin === "merge")
    assert(s2Lineage(1).mergeCount > 0)
  }

  test("S3 lineage has copies and merges") {
    val (s1, _) = SieveStage.base.nextStage()
    val (s2, _) = s1.nextStage()
    val (_, s3Lineage) = s2.nextStage()
    val copies = s3Lineage.count(_.origin == "copy")
    val merges = s3Lineage.count(_.origin == "merge")
    assert(copies > 0, "S3 should have some copied gaps")
    assert(merges > 0, "S3 should have some merged gaps")
  }
}
