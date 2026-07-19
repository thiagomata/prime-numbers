package v1.chapter8

/**
 * Spark-native sieve pipeline.
 *
 * Each phase is a standalone method that transforms RDDs.
 * Phase outputs can be persisted to files for isolated testing.
 *
 * Phases:
 *   1. Block processing → RDD[(blockIdx, localIdx, gap, origin)]
 *   2. Sort + carry patch (broadcast)
 *   3. Rotation (broadcast R)
 *   4. Write (DataFrame .write.csv)
 *   5. Collect gap Longs for SieveStage
 */
object SievePipeline {

  import BlockProcessing._

  // ═══════════════════════════════════════════════════════════════
  // Phase 1: Block processing
  // Input:  SieveStage
  // Output: RDD[GapEntry] — one row per gap, distributed
  // ═══════════════════════════════════════════════════════════════

  def phase1BlockProcessing(
    spark: org.apache.spark.sql.SparkSession,
    current: SieveStage
  ): (org.apache.spark.rdd.RDD[GapEntry], Array[BlockMetadata]) = {
    val sc = spark.sparkContext
    val h = current.head.toInt
    val m = current.modulus
    val residues = current.computeResidues()
    val T = residues.length
    val residueGaps = computeResidueGaps(residues, m, T)

    val residuesBc = sc.broadcast(residues)
    val gapsBc = sc.broadcast(residueGaps)
    val hBc = sc.broadcast(h.toLong)
    val mBc = sc.broadcast(m)

    val rdd = sc.parallelize(0 until h, numSlices = h).flatMap { k =>
      BlockProcessing.processBlock(k.toLong, residuesBc.value, gapsBc.value, hBc.value, mBc.value, T)
    }

    // Collect block metadata — O(h), tiny
    val meta = sc.parallelize(0 until h, numSlices = math.min(h, 4)).map { k =>
      BlockProcessing.blockMeta(k.toLong, residuesBc.value, gapsBc.value, hBc.value, mBc.value, T)
    }.collect()

    // Don't destroy broadcasts here — the gapRdd is lazy and still references them.
    // Let them be garbage collected after the RDD chain completes.

    (rdd, meta)
  }

  // ═══════════════════════════════════════════════════════════════
  // Phase 2: Sort by block+localIndex + carry patch
  // Input:  RDD[GapEntry], Array[BlockMetadata]
  // Output: RDD[GapEntry] — sorted, carry-patched
  // ═══════════════════════════════════════════════════════════════

  def phase2SortAndCarry(
    spark: org.apache.spark.sql.SparkSession,
    gapRdd: org.apache.spark.rdd.RDD[GapEntry],
    blockMeta: Array[BlockMetadata]
  ): org.apache.spark.rdd.RDD[GapEntry] = {
    val sc = spark.sparkContext

    // Build carry map from metadata.
    val carryMap = new Array[(Long, Int)](blockMeta.length)
    carryMap(0) = (0L, 0)
    var i = 1
    while (i < blockMeta.length) {
      carryMap(i) = (blockMeta(i - 1).tailAccumGap, blockMeta(i - 1).tailAccumCount)
      i += 1
    }
    val finalCarryGap = blockMeta.last.tailAccumGap
    val finalCarryCount = blockMeta.last.tailAccumCount

    val carryBc = sc.broadcast(carryMap)
    val finalCarryBc = sc.broadcast((finalCarryGap, finalCarryCount))

    // Apply carries via mapPartitionsWithIndex.
    // Each partition corresponds to one block (k = partition index).
    gapRdd.mapPartitionsWithIndex { case (partIdx, iter) =>
      val carry = carryBc.value(partIdx)
      val (finalGap, finalCnt) = finalCarryBc.value
      var pos = 0
      iter.map { entry =>
        val isFirst = (pos == 0)
        val (patchedGap, patchedOrigin) =
          if (partIdx == 0 && isFirst && finalCnt > 0) (entry.gap + finalGap, "merge")
          else if (isFirst && carry._2 > 0) (entry.gap + carry._1, "merge")
          else (entry.gap, entry.origin)
        pos += 1
        GapEntry(entry.blockIdx, entry.localIdx, patchedGap, patchedOrigin)
      }
    }
  }

  // ═══════════════════════════════════════════════════════════════
  // Full pipeline: chains all phases
  // ═══════════════════════════════════════════════════════════════

  def nextStage(
    spark: org.apache.spark.sql.SparkSession,
    current: SieveStage,
    outputDir: String,
    stageIndex: Int
  ): (SieveStage, Array[GapLineage]) = {
    val nextHV = current.head + current.gaps(0)
    val residues = current.computeResidues()
    val R = findRotation(nextHV, current.head, current.modulus, residues)
    val newModulus = current.modulus * current.head

    val (rdd, meta) = phase1BlockProcessing(spark, current)
    val patched = phase2SortAndCarry(spark, rdd, meta)
    val gapsUnrotated = patched.map(_.gap).collect()
    val rotatedGaps = rotateArray(gapsUnrotated, R)

    val newTail = Array(current.head) ++ current.tailPrimes
    val next = SieveStage(nextHV, newTail, newModulus, rotatedGaps.length, rotatedGaps)
    (next, Array.empty)
  }

  // ═══════════════════════════════════════════════════════════════
  // Phase 3: Rotation (identity — no shuffle needed)
  // Rotation is applied on the driver after phase5 collect.
  // ═══════════════════════════════════════════════════════════════

  def phase3Rotation(
    spark: org.apache.spark.sql.SparkSession,
    patchedRdd: org.apache.spark.rdd.RDD[GapEntry],
    rotationIndex: Int,
    totalGaps: Int
  ): org.apache.spark.rdd.RDD[GapEntry] = patchedRdd

  // ═══════════════════════════════════════════════════════════════
  // Phase 4: Write to CSV via DataFrame
  // Input:  RDD[GapEntry]
  // Output: CSV directory on disk
  // ═══════════════════════════════════════════════════════════════

  def phase4Write(
    spark: org.apache.spark.sql.SparkSession,
    rotatedRdd: org.apache.spark.rdd.RDD[GapEntry],
    outputPath: String
  ): Unit = {
    import spark.implicits._
    val df = rotatedRdd.map(e => (e.localIdx, e.gap, e.origin)).toDF("index", "gap", "origin")
    df.write.mode("overwrite").option("header", "true").option("compression", "gzip").csv(outputPath)
  }

  // ═══════════════════════════════════════════════════════════════
  // Phase 5: Collect gap Longs for SieveStage
  // Input:  RDD[GapEntry]
  // Output: Array[Long] — on driver, 288MB for stage 9
  // ═══════════════════════════════════════════════════════════════

  def phase5CollectGaps(
    spark: org.apache.spark.sql.SparkSession,
    rotatedRdd: org.apache.spark.rdd.RDD[GapEntry]
  ): Array[Long] = {
    rotatedRdd.map(_.gap).collect()
  }

  // ═══════════════════════════════════════════════════════════════
  // Helpers
  // ═══════════════════════════════════════════════════════════════

  def computeResidueGaps(residues: Array[Long], m: Long, T: Int): Array[Long] = {
    if (T <= 1) return Array(m)
    val gaps = new Array[Long](T)
    var i = 0
    while (i < T - 1) { gaps(i) = residues(i + 1) - residues(i); i += 1 }
    gaps(T - 1) = m - residues(T - 1) + residues(0)
    gaps
  }

  def findRotation(nextHeadValue: Long, h: Long, m: Long, residues: Array[Long]): Int = {
    var count = 0; var found = false; var k = 0L
    while (k < h && !found) { var i = 0
      while (i < residues.length && !found) {
        val v = residues(i) + k * m
        if (v % h != 0) { if (v == nextHeadValue) found = true; else count += 1 }
        i += 1 }; k += 1 }
    count
  }

  /** Rotate array on the driver — O(n), no shuffle. */
  def rotateArray(arr: Array[Long], r: Int): Array[Long] = {
    if (r == 0 || arr.isEmpty) return arr
    val n = arr.length; val rot = r % n
    val res = new Array[Long](n)
    var i = 0; while (i < n) { res(i) = arr((i + rot) % n); i += 1 }
    res
  }
}
