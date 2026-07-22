package v1.chapter8

import org.scalatest.funsuite.AnyFunSuite

class GapLineageSpec extends AnyFunSuite {

  test("compressAround2: [6,4,2,4,2,4,6,2] => [10,2,4,2,10,2]") {
    val input = Array(6L, 4L, 2L, 4L, 2L, 4L, 6L, 2L)
    val result = GapLineage.compressAround2(input)
    assert(result === Array(10L, 2L, 4L, 2L, 10L, 2L))
  }

  test("compressAround2: [2] => [2]") {
    assert(GapLineage.compressAround2(Array(2L)) === Array(2L))
  }

  test("compressAround2: [4] => [4]") {
    assert(GapLineage.compressAround2(Array(4L)) === Array(4L))
  }

  test("compressAround2: [2,4] => [2,4]") {
    assert(GapLineage.compressAround2(Array(2L, 4L)) === Array(2L, 4L))
  }

  test("compressAround2: [4,2] => [4,2]") {
    assert(GapLineage.compressAround2(Array(4L, 2L)) === Array(4L, 2L))
  }

  test("compressAround2: [6,4] => [10]") {
    assert(GapLineage.compressAround2(Array(6L, 4L)) === Array(10L))
  }

  test("compressAround2: empty => empty") {
    assert(GapLineage.compressAround2(Array.empty) === Array.empty)
  }

  test("GapStageStats has correct fields") {
    val stats = GapStageStats(
      stage = 0, head = 2, period = 1, modulus = 1,
      gapCount = 1, copyCount = 0, mergeCount = 0,
      newGapValues = 1, lostGapValues = 0,
      maxAge = 1, avgAge = 1.0,
      twoGapCount = 0, twoGapSurvived = 0
    )
    assert(stats.stage === 0)
    assert(stats.twoGapCount === 0)
  }

  test("computeStats counts 2-gaps correctly") {
    val gaps = Array(6L, 4L, 2L, 4L, 2L, 4L, 6L, 2L)
    val lineage = gaps.zipWithIndex.map { case (g, i) =>
      GapLineage(i, g, if (g == 2) "copy" else "merge", if (g == 2) 2 else 1, 0, Array.empty, Array.empty)
    }
    val stats = GapLineage.computeStats(3, 7, 8, 30, gaps, lineage, 0)
    assert(stats.twoGapCount === 3)
    assert(stats.twoGapSurvived === 3)
  }
}
