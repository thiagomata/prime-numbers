package v1.chapter8

import org.apache.spark.sql.SparkSession
import org.apache.spark.rdd.RDD

/**
 * Spark-powered sieve pipeline.
 *
 * Block-parallel approach: each block k in [0, h) is processed independently
 * on a Spark executor. Within each block, the walk uses the residue gaps
 * (derived from the current stage's gap cycle) to check filter conditions
 * and merge gaps around filtered positions.
 *
 * Block processing is distributed via Spark RDDs.
 * Only O(h) block summaries come to the driver for assembly.
 *
 * Scaling note: the gap cycle (T elements) is held in SieveStage.gaps.
 * For stages beyond ~12, T exceeds driver memory. At that point,
 * SieveStage.gaps would need to become an RDD itself — a data model change
 * that goes beyond this pipeline.
 */
object SparkSievePipeline {

  private case class BlockResult(
    gaps: Array[Long],
    origins: Array[String],
    firstFiltered: Boolean,
    lastFiltered: Boolean,
    tailAccumGap: Long,
    tailAccumCount: Int
  ) extends Serializable

  def nextStage(spark: SparkSession, current: SieveStage): (SieveStage, Array[GapLineage]) = {
    val sc = spark.sparkContext
    val h = current.head
    val m = current.modulus
    val newModulus = m * h

    val residues = current.computeResidues()
    val T = residues.length
    val residueGaps = computeResidueGaps(residues, m, T)

    // Broadcast gap data to executors
    val residuesBc = sc.broadcast(residues)
    val gapsBc = sc.broadcast(residueGaps)

    // Phase 1: parallel block processing via Spark RDD
    val blockResults: Array[BlockResult] = sc
      .parallelize(0L until h, numSlices = math.min(h.toInt, 8))
      .map(k => processBlock(k, residuesBc.value, gapsBc.value, h, m, T))
      .collect()

    residuesBc.destroy()
    gapsBc.destroy()

    // Phase 2: assemble h block boundaries on driver
    val (assembledGaps, assembledOrigins) = assembleBlocks(blockResults, h)

    // Phase 3: rotate to align with next head
    val nextHeadValue = current.head + current.gaps(0)
    val rotationIndex = findRotation(assembledGaps, nextHeadValue, h, m, residues)

    val rotatedGaps = rotateLong(assembledGaps, rotationIndex)
    val rotatedOrigins = rotateString(assembledOrigins, rotationIndex)

    val lineage = rotatedGaps.zip(rotatedOrigins).zipWithIndex.map {
      case ((gap, origin), idx) =>
        GapLineage(idx, gap, origin, 1, if (origin == "copy") 1 else 2, Array.empty, Array.empty)
    }

    val newTailPrimes = Array(current.head) ++ current.tailPrimes
    val next = SieveStage(nextHeadValue, newTailPrimes, newModulus, rotatedGaps.length, rotatedGaps)
    (next, lineage)
  }

  /**
   * Walk one block: check destination filter state at each position.
   * Uses ascending residue order — gaps between consecutive residues
   * are the residue gaps. Filter: (residue + k*m) % h == 0.
   */
  private def processBlock(
    k: Long,
    residues: Array[Long],
    residueGaps: Array[Long],
    h: Long,
    m: Long,
    T: Int
  ): BlockResult = {
    val outGaps = scala.collection.mutable.ArrayBuffer[Long]()
    val outOrigins = scala.collection.mutable.ArrayBuffer[String]()

    var accumGap = 0L
    var accumCount = 0

    val kmModH = (k * (m % h)) % h

    for (i <- 0 until T) {
      val gapOut = residueGaps(i)
      val nextI = (i + 1) % T
      val nextK = if (nextI == 0) k + 1 else k
      val nextVal = residues(nextI) + nextK * m
      val nextFiltered = (nextVal % h == 0)

      if (nextFiltered) {
        accumGap += gapOut
        accumCount += 1
      } else {
        if (accumCount > 0) {
          outGaps += (accumGap + gapOut)
          outOrigins += "merge"
        } else {
          outGaps += gapOut
          outOrigins += "copy"
        }
        accumGap = 0L
        accumCount = 0
      }
    }

    val firstVal = residues(0) + k * m
    val lastVal = residues(T - 1) + k * m

    BlockResult(
      gaps = outGaps.toArray,
      origins = outOrigins.toArray,
      firstFiltered = (firstVal % h == 0),
      lastFiltered = (lastVal % h == 0),
      tailAccumGap = accumGap,
      tailAccumCount = accumCount
    )
  }

  /**
   * Assemble block boundaries on driver — O(h) work.
   */
  private def assembleBlocks(
    blocks: Array[BlockResult],
    h: Long
  ): (Array[Long], Array[String]) = {
    val allGaps = scala.collection.mutable.ArrayBuffer[Long]()
    val allOrigins = scala.collection.mutable.ArrayBuffer[String]()

    var carryGap = 0L
    var carryCount = 0

    for (k <- 0 until h.toInt) {
      val block = blocks(k)

      if (carryCount > 0 && block.firstFiltered) {
        if (block.gaps.nonEmpty) {
          allGaps += (carryGap + block.gaps(0))
          allOrigins += "merge"
          allGaps ++= block.gaps.tail
          allOrigins ++= block.origins.tail
        }
        carryGap = block.tailAccumGap
        carryCount = block.tailAccumCount

      } else if (carryCount > 0) {
        if (block.gaps.nonEmpty) {
          allGaps += (carryGap + block.gaps(0))
          allOrigins += "merge"
          allGaps ++= block.gaps.tail
          allOrigins ++= block.origins.tail
        }
        carryGap = block.tailAccumGap
        carryCount = block.tailAccumCount

      } else {
        allGaps ++= block.gaps
        allOrigins ++= block.origins
        carryGap = block.tailAccumGap
        carryCount = block.tailAccumCount
      }
    }

    if (carryCount > 0 && allGaps.nonEmpty) {
      allGaps(0) = carryGap + allGaps(0)
      allOrigins(0) = "merge"
    }

    (allGaps.toArray, allOrigins.toArray)
  }

  /**
   * Find rotation index: count survivors before nextHeadValue in ascending order.
   * Walks a small number of blocks to find the target.
   */
  private def findRotation(
    assembledGaps: Array[Long],
    nextHeadValue: Long,
    h: Long,
    m: Long,
    residues: Array[Long]
  ): Int = {
    // Count survivors in ascending order until we reach nextHeadValue
    var count = 0
    var found = false
    var k = 0L
    while (k < h && !found) {
      var i = 0
      while (i < residues.length && !found) {
        val v = residues(i) + k * m
        if (v % h != 0) {
          // This is a survivor
          if (v == nextHeadValue) {
            found = true
          } else {
            count += 1
          }
        }
        i += 1
      }
      k += 1
    }
    count
  }

  private def computeResidueGaps(residues: Array[Long], m: Long, T: Int): Array[Long] = {
    if (T <= 1) return Array(m)
    val gaps = new Array[Long](T)
    var i = 0
    while (i < T - 1) {
      gaps(i) = residues(i + 1) - residues(i)
      i += 1
    }
    gaps(T - 1) = m - residues(T - 1) + residues(0)
    gaps
  }

  private def rotateLong(arr: Array[Long], n: Int): Array[Long] = {
    if (n == 0 || arr.isEmpty) return arr
    val len = arr.length
    val r = new Array[Long](len)
    var i = 0
    while (i < len) { r(i) = arr((i + n) % len); i += 1 }
    r
  }

  private def rotateString(arr: Array[String], n: Int): Array[String] = {
    if (n == 0 || arr.isEmpty) return arr
    val len = arr.length
    val r = new Array[String](len)
    var i = 0
    while (i < len) { r(i) = arr((i + n) % len); i += 1 }
    r
  }
}
