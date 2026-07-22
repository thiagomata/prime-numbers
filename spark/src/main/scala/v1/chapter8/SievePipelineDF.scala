package v1.chapter8

import org.apache.spark.sql.{SparkSession, DataFrame}
import java.io.{File, BufferedReader, InputStreamReader, FileInputStream}
import java.util.zip.GZIPInputStream

/**
 * DataFrame-native sieve pipeline.
 *
 * Phase 1: expandBlocks → (blockIndex, pos, gap, nextFiltered)
 * Phase 2: walkAndMerge → (blockIndex, gap, origin, mergeCount)
 * Phase 3: applyCarryChain → (blockIndex, gap, origin, mergeCount)
 * Write:   writeRotatedCsv → gzip CSV output
 */
object SievePipelineDF {

  /** Phase 1: for each block k, emit expanded positions with filter flags. */
  def expandBlocks(
    spark: SparkSession,
    head: Long,
    modulus: Long,
    residues: Array[Long],
    residueGaps: Array[Long]
  ): DataFrame = {
    import spark.implicits._

    val hBc = spark.sparkContext.broadcast(head)
    val mBc = spark.sparkContext.broadcast(modulus)
    val resBc = spark.sparkContext.broadcast(residues)
    val gapsBc = spark.sparkContext.broadcast(residueGaps)
    val T = residues.length

    val rdd = spark.sparkContext.parallelize(0L until head, head.toInt).flatMap { blockIdx =>
      val gaps = gapsBc.value
      val hVal = hBc.value
      val mVal = mBc.value
      val res = resBc.value

      val buf = new scala.collection.mutable.ArrayBuffer[(Long, Int, Long, Boolean)](T)
      var i = 0
      while (i < T) {
        val nextI = (i + 1) % T
        val nextBlockIdx = if (nextI == 0) blockIdx + 1 else blockIdx
        val nextVal = res(nextI) + nextBlockIdx * mVal
        val nextFiltered = (nextVal % hVal == 0)
        buf += ((blockIdx, i, gaps(i), nextFiltered))
        i += 1
      }
      buf.iterator
    }

    rdd.toDF("blockIdx", "pos", "gap", "nextFiltered")
  }

  /** Phase 2: accumulate gaps at filtered positions, emit at survivors. */
  def walkAndMerge(df: DataFrame): DataFrame = {
    import df.sparkSession.implicits._
    val rdd = df.rdd.mapPartitions { iter =>
      val rows = iter.toArray
      val buf = new scala.collection.mutable.ArrayBuffer[(Long, Long, String, Int)]()
      var accumGap = 0L
      var accumCount = 0
      var i = 0
      while (i < rows.length) {
        val gap = rows(i).getLong(2)
        val nextFiltered = rows(i).getBoolean(3)
        if (nextFiltered) {
          accumGap += gap
          accumCount += 1
        } else {
          val emitGap = if (accumCount > 0) accumGap + gap else gap
          val origin = if (accumCount > 0) "merge" else "copy"
          buf += ((rows(i).getLong(0), emitGap, origin, accumCount))
          accumGap = 0L
          accumCount = 0
        }
        i += 1
      }
      buf.iterator
    }
    rdd.toDF("blockIdx", "gap", "origin", "mergeCount")
  }

  /** Phase 3: patch first gap of each block with carry from previous block's tail. */
  def applyCarryChain(df: DataFrame, head: Long, modulus: Long, T: Int, residues: Array[Long], residueGaps: Array[Long]): DataFrame = {
    import df.sparkSession.implicits._

    // Compute carry INTO each block from residues (O(h) on driver)
    val carries = new Array[(Long, Int)](head.toInt)
    var carryGap = 0L
    var carryCount = 0
    var k = 0
    while (k < head.toInt) {
      carries(k) = (carryGap, carryCount)
      var accumGap = 0L
      var accumCount = 0
      var i = 0
      while (i < T) {
        val nextI = (i + 1) % T
        val nextK = if (nextI == 0) k + 1 else k
        val nextVal = residues(nextI) + nextK * modulus
        val nextFiltered = (nextVal % head == 0)
        if (nextFiltered) { accumGap += residueGaps(i); accumCount += 1 }
        else { accumGap = 0L; accumCount = 0 }
        i += 1
      }
      carryGap = accumGap
      carryCount = accumCount
      k += 1
    }
    // Wrap-around: block h-1's tail carries to block 0
    if (carryCount > 0) {
      carries(0) = (carries(0)._1 + carryGap, carries(0)._2 + carryCount)
    }

    val carriesBc = df.sparkSession.sparkContext.broadcast(carries)

    val patchedRdd = df.rdd.mapPartitions { iter =>
      val rows = iter.toArray
      val carriesVal = carriesBc.value
      val buf = new scala.collection.mutable.ArrayBuffer[(Long, Long, String, Int)]()
      var i = 0
      while (i < rows.length) {
        val k = rows(i).getLong(0)
        val isFirstInBlock = (i == 0 || rows(i - 1).getLong(0) != k)
        val gap = rows(i).getLong(1)
        val origin = rows(i).getString(2)
        val mc = rows(i).getInt(3)

        val (cg, cc) = carriesVal(k.toInt)
        if (isFirstInBlock && cc > 0) {
          buf += ((k, gap + cg, "merge", mc + cc))
        } else {
          buf += ((k, gap, origin, mc))
        }
        i += 1
      }
      buf.iterator
    }

    patchedRdd.toDF("blockIdx", "gap", "origin", "mergeCount")
  }

  // ═══════════════════════════════════════════════════════════════
  // File output
  // ═══════════════════════════════════════════════════════════════

  case class GapsInfo(
    path: String,
    head: Long,
    nextHeadValue: Long,
    modulus: Long,
    tailPrimes: Array[Long],
    period: Int,
    firstGap: Long,
    rotationIndex: Int
  )

  def writeRotatedCsv(
    df: DataFrame,
    rotationIndex: Int,
    outputDir: String,
    stageIndex: Int,
    head: Long,
    nextHeadValue: Long,
    modulus: Long,
    tailPrimes: Array[Long]
  ): GapsInfo = {
    import df.sparkSession.implicits._

    val path = new java.io.File(outputDir, f"stage_$stageIndex%03d/gaps").getAbsolutePath

    // Add global index via RDD zipWithIndex (preserves partition order)
    val indexed = df.rdd.zipWithIndex().map { case (row, idx) =>
      (idx, row.getLong(1), row.getString(2), row.getInt(3))
    }.toDF("gidx", "gap", "origin", "mergeCount")

    indexed.write.mode("overwrite").option("header", "true").option("compression", "gzip").csv(path)

    val period = df.count().toInt
    val firstGap = {
      val withIdx = df.rdd.zipWithIndex().map { case (row, idx) => (row.getLong(1), idx) }
      withIdx.filter(_._2 == rotationIndex % math.max(period, 1)).map(_._1).collect().headOption.getOrElse(0L)
    }

    GapsInfo(path, head, nextHeadValue, modulus, tailPrimes, period, firstGap, rotationIndex)
  }

  /** Stream gaps, compress runs of non-2 gaps into their sum. */
  def compressAroundTwos(gapsDir: String, outputPath: String): Unit = {
    import java.io.{BufferedReader, FileInputStream, InputStreamReader}
    import java.util.zip.{GZIPInputStream, GZIPOutputStream}
    val dir = new java.io.File(gapsDir)
    val parts = dir.listFiles().filter(_.getName.startsWith("part-")).sortBy(_.getName)
    val pw = new java.io.PrintWriter(new GZIPOutputStream(new java.io.FileOutputStream(new java.io.File(outputPath))))
    var idx = 0
    var runningSum = 0L
    var spanCount = 0
    try {
      pw.println("index,gap,originalSpan")
      for (part <- parts) {
        try {
          val is = new GZIPInputStream(new FileInputStream(part))
          val reader = new BufferedReader(new InputStreamReader(is))
          reader.readLine()
          var line = reader.readLine()
          while (line != null) {
            val gap = line.split(",")(1).toLong
            if (gap == 2) {
              if (spanCount > 0) { pw.println(s"$idx,$runningSum,$spanCount"); idx += 1; runningSum = 0L; spanCount = 0 }
              pw.println(s"$idx,$gap,1"); idx += 1
            } else {
              runningSum += gap; spanCount += 1
            }
            line = reader.readLine()
          }
          reader.close()
        } catch { case _: Exception => }
      }
      if (spanCount > 0) { pw.println(s"$idx,$runningSum,$spanCount"); idx += 1 }
    } finally pw.close()
  }

  /** Write the first maxRows rows from a partitioned gzip CSV directory. */
  def writePartitionedCsvSample(inputDir: String, outputPath: String, maxRows: Int): Unit = {
    val dir = new java.io.File(inputDir)
    val parts = dir.listFiles().filter(_.getName.startsWith("part-")).sortBy(_.getName)
    writeCsvSample(parts, outputPath, maxRows)
  }

  /** Write the first maxRows rows from a single gzip CSV file. */
  def writeGzipCsvSample(inputPath: String, outputPath: String, maxRows: Int): Unit = {
    writeCsvSample(Array(new java.io.File(inputPath)), outputPath, maxRows)
  }

  private def writeCsvSample(parts: Array[java.io.File], outputPath: String, maxRows: Int): Unit = {
    val outFile = new java.io.File(outputPath)
    outFile.getParentFile.mkdirs()
    val pw = new java.io.PrintWriter(outFile)
    var wroteHeader = false
    var rowsWritten = 0
    try {
      for (part <- parts if rowsWritten < maxRows) {
        val is = new GZIPInputStream(new FileInputStream(part))
        val reader = new BufferedReader(new InputStreamReader(is))
        try {
          val header = reader.readLine()
          if (!wroteHeader && header != null) {
            pw.println(header)
            wroteHeader = true
          }
          var line = reader.readLine()
          while (line != null && rowsWritten < maxRows) {
            pw.println(line)
            rowsWritten += 1
            line = reader.readLine()
          }
        } finally reader.close()
      }
    } finally pw.close()
  }

  /** Count gaps equal to 2 (streaming). */
  def countTwos(gapsDir: String): Int = {
    val dir = new java.io.File(gapsDir)
    val parts = dir.listFiles().filter(_.getName.startsWith("part-")).toSeq
    if (parts.isEmpty) return 0
    var total = 0
    for (part <- parts) {
      try {
        val is = new GZIPInputStream(new FileInputStream(part))
        val reader = new BufferedReader(new InputStreamReader(is))
        reader.readLine()
        var line = reader.readLine()
        while (line != null) {
          if (line.split(",")(1).toLong == 2) total += 1
          line = reader.readLine()
        }
        reader.close()
      } catch { case _: Exception => }
    }
    total
  }

  /**
   * Read first n values of the sequence by streaming gap files.
   * Skips `rotationIndex` gaps to start from the correct rotated position.
   */
  def readFirstValues(gapsDir: String, head: Long, n: Int, rotationIndex: Int = 0): Array[Long] = {
    val dir = new java.io.File(gapsDir)
    val parts = dir.listFiles().filter(_.getName.startsWith("part-")).sortBy(_.getName)
    val result = new scala.collection.mutable.ArrayBuffer[Long]()
    result += head
    var acc = head
    var remaining = n - 1
    var skipped = 0

    for (part <- parts) {
      if (remaining > 0) {
        try {
          val is = new GZIPInputStream(new FileInputStream(part))
          val reader = new BufferedReader(new InputStreamReader(is))
          reader.readLine()
          var line = reader.readLine()
          while (line != null && remaining > 0) {
            if (skipped < rotationIndex) {
              skipped += 1
            } else {
              val gap = line.split(",")(1).toLong
              acc += gap
              result += acc
              remaining -= 1
            }
            line = reader.readLine()
          }
          reader.close()
        } catch { case _: Exception => }
      }
    }
    result.toArray
  }

  /** Collect gaps in memory + rotate (for tests). */
  def collectGaps(df: DataFrame, rotationIndex: Int): Array[Long] = {
    import df.sparkSession.implicits._
    val gaps = df.select("gap").as[Long].collect()
    if (rotationIndex == 0 || gaps.isEmpty) gaps else {
      val n = gaps.length; val rot = rotationIndex % n
      val r = new Array[Long](n); var i = 0
      while (i < n) { r(i) = gaps((i + rot) % n); i += 1 }
      r
    }
  }
}
