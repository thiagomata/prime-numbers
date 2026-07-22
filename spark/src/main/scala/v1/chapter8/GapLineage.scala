package v1.chapter8

/**
 * Lineage metadata for a single gap in a sieve stage.
 *
 * Tracks how each gap was formed (copy vs merge), how old it is,
 * and which previous-stage gaps it descended from.
 */
case class GapLineage(
  index: Int,
  gap: Long,
  origin: String,       // "copy", "merge", or "new"
  age: Int,             // consecutive stages persisted; resets to 1 on merge
  mergeCount: Int,      // 0 for copies, 1+ for merges
  mergeAncestors: Array[Int],  // indices of old gaps that were merged
  ancestorValues: Array[Long]  // values of old gaps that were merged
) extends Serializable

/**
 * Aggregated gap statistics for one stage.
 */
case class GapStageStats(
  stage: Int,
  head: Long,
  period: Int,
  modulus: Long,
  gapCount: Int,
  copyCount: Int,
  mergeCount: Int,
  newGapValues: Int,
  lostGapValues: Int,
  maxAge: Int,
  avgAge: Double,
  twoGapCount: Int,
  twoGapSurvived: Int
) extends Serializable

object GapLineage {

  /**
   * Compress gap cycle around 2-gaps.
   * Consecutive non-2 gaps are summed; 2-gaps are kept as-is.
   *
   * Example: [6,4,2,4,2,4,6,2] => [10,2,4,2,10,2]
   */
  def compressAround2(gaps: Array[Long]): Array[Long] = {
    if (gaps.isEmpty) return Array.empty

    val result = scala.collection.mutable.ArrayBuffer[Long]()
    var runningSum = 0L
    var span = 0

    var i = 0
    while (i < gaps.length) {
      if (gaps(i) == 2) {
        if (span > 0) {
          result += runningSum
          runningSum = 0L
          span = 0
        }
        result += 2L
      } else {
        runningSum += gaps(i)
        span += 1
      }
      i += 1
    }
    if (span > 0) {
      result += runningSum
    }

    // Handle wrap-around: if first and last are both non-2, merge them
    val arr = result.toArray
    if (arr.length >= 2 && arr.head != 2 && arr.last != 2) {
      val merged = arr.head + arr.last
      Array(merged) ++ arr.tail.dropRight(1)
    } else {
      arr
    }
  }

  /**
   * Compute aggregate gap statistics for a stage.
   */
  def computeStats(
    stage: Int,
    head: Long,
    period: Int,
    modulus: Long,
    gaps: Array[Long],
    lineage: Array[GapLineage],
    prevTwoGapCount: Int
  ): GapStageStats = {
    val copyCount = lineage.count(_.origin == "copy")
    val mergeCount = lineage.count(_.origin == "merge")

    val ages = lineage.map(_.age)
    val maxAge = if (ages.nonEmpty) ages.max else 0
    val avgAge = if (ages.nonEmpty) ages.map(_.toDouble).sum / ages.length else 0.0

    val twoGapCount = gaps.count(_ == 2)
    val twoGapSurvived = lineage.count(l => l.gap == 2 && l.origin == "copy")

    GapStageStats(
      stage = stage,
      head = head,
      period = period,
      modulus = modulus,
      gapCount = gaps.length,
      copyCount = copyCount,
      mergeCount = mergeCount,
      newGapValues = 0,
      lostGapValues = 0,
      maxAge = maxAge,
      avgAge = avgAge,
      twoGapCount = twoGapCount,
      twoGapSurvived = twoGapSurvived
    )
  }
}
