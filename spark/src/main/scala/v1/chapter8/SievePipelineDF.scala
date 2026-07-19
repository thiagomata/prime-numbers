package v1.chapter8

import org.apache.spark.sql.{SparkSession, DataFrame}
import java.io.{File, BufferedReader, InputStreamReader, FileInputStream}
import java.util.zip.GZIPInputStream

/**
 * DataFrame-native sieve pipeline.
 *
 * Phase 1: Expand → (k, i, gap, nextFiltered)
 * Phase 2: Walk → (k, gap, origin)
 * Phase 3: Carry chain → patched gaps
 * Phase 4: Collect → rotate on driver → SieveStage
 */
object SievePipelineDF {

  // Phase 1: Expand positions. For each block k and position i:
  //   gap = residueGaps(i) — distance to next position
  //   nextFiltered = (residues((i+1)%T) + (if wrap then k+1 else k)*m) % h == 0
  def phase1Expand(
    spark: SparkSession,
    h: Long,
    m: Long,
    residues: Array[Long],
    residueGaps: Array[Long]
  ): DataFrame = {
    import spark.implicits._

    val hBc = spark.sparkContext.broadcast(h)
    val mBc = spark.sparkContext.broadcast(m)
    val resBc = spark.sparkContext.broadcast(residues)
    val gapsBc = spark.sparkContext.broadcast(residueGaps)
    val T = residues.length

    val rdd = spark.sparkContext.parallelize(0L until h, h.toInt).flatMap { k =>
      val gaps = gapsBc.value
      val hVal = hBc.value
      val mVal = mBc.value
      val res = resBc.value

      val buf = new scala.collection.mutable.ArrayBuffer[(Long, Int, Long, Boolean)](T)
      var i = 0
      while (i < T) {
        val nextI = (i + 1) % T
        val nextK = if (nextI == 0) k + 1 else k
        val nextVal = res(nextI) + nextK * mVal
        val nextFiltered = (nextVal % hVal == 0)
        buf += ((k, i, gaps(i), nextFiltered))
        i += 1
      }
      buf.iterator
    }

    rdd.toDF("k", "pos", "gap", "nextFiltered")
  }

  // Phase 2: Walk. For each block, accumulate gaps when nextFiltered=true,
  // emit gap when nextFiltered=false.
  def phase2Walk(df: DataFrame): DataFrame = {
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
    rdd.toDF("k", "gap", "origin", "mergeCount")
  }

  // Phase 3: Carry chain via broadcast map (O(h) on driver, gaps stay in RDD).
  // Pre-compute carries from residue gaps metadata (modulus, h, T).
  // Each block k needs: carryGap, carryCount INTO block k.
  // carry(0) = 0, carry(k) = block(k-1).tailAccum.
  // Compute tailAccum for each block from the Phase 1 expand logic.
  def phase3Carry(df: DataFrame, h: Long, m: Long, T: Int, residues: Array[Long], residueGaps: Array[Long]): DataFrame = {
    import df.sparkSession.implicits._

    // Compute carry INTO each block from residues (O(h) on driver)
    val carries = new Array[(Long, Int)](h.toInt)
    var carryGap = 0L
    var carryCount = 0
    var k = 0
    while (k < h.toInt) {
      carries(k) = (carryGap, carryCount)
      // Compute block k's tail by walking the same way as Phase 1 + Phase 2
      var accumGap = 0L
      var accumCount = 0
      var i = 0
      while (i < T) {
        val nextI = (i + 1) % T
        val nextK = if (nextI == 0) k + 1 else k
        val nextVal = residues(nextI) + nextK * m
        val nextFiltered = (nextVal % h == 0)
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

    patchedRdd.toDF("k", "gap", "origin", "mergeCount")
  }

  // ═══════════════════════════════════════════════════════════════
  // File-based output — no driver array
  // ═══════════════════════════════════════════════════════════════

  case class GapsInfo(
    path: String,
    head: Long,
    nextHeadValue: Long,
    modulus: Long,
    tailPrimes: Array[Long],
    period: Int,
    firstGap: Long,
    rotationIndex: Int  // added: for readFirstValues to start from rotated position
  )

  def writeRotatedCsv(
    df: DataFrame,
    R: Int,
    outputDir: String,
    stageIndex: Int,
    head: Long,
    nextHV: Long,
    modulus: Long,
    tailPrimes: Array[Long]
  ): GapsInfo = {
    import df.sparkSession.implicits._

    // Write gaps and origin in partition order (block order).
    // No index column — preserves natural row order.
    val path = new java.io.File(outputDir, f"stage_$stageIndex%03d/gaps").getAbsolutePath

    // Add global index via RDD zipWithIndex (preserves partition order)
    val indexed = df.rdd.zipWithIndex().map { case (row, idx) =>
      (idx, row.getLong(1), row.getString(2), row.getInt(3))
    }.toDF("gidx", "gap", "origin", "mergeCount")

    indexed.write.mode("overwrite").option("header", "true").option("compression", "gzip").csv(path)

    // Compute period and first gap from the DataFrame (not the file — avoids stale data)
    val period = df.count().toInt
    val firstGap = {
      val withIdx = df.rdd.zipWithIndex().map { case (row, idx) => (row.getLong(1), idx) }
      withIdx.filter(_._2 == R % math.max(period, 1)).map(_._1).collect().headOption.getOrElse(0L)
    }

    GapsInfo(path, head, nextHV, modulus, tailPrimes, period, firstGap, R)
  }

  private def readFirstGap(dir: java.io.File): Long = {
    val part = dir.listFiles().find(_.getName.startsWith("part-"))
      .getOrElse(sys.error(s"No part file in $dir"))
    val is = new GZIPInputStream(new FileInputStream(part))
    val reader = new BufferedReader(new InputStreamReader(is))
    reader.readLine() // skip header
    val line = reader.readLine()
    reader.close()
    line.split(",")(0).toLong
  }

  private def firstFileCount(dir: java.io.File): Int = {
    val part = dir.listFiles().find(_.getName.startsWith("part-"))
      .getOrElse(sys.error(s"No part file in $dir"))
    val is = new GZIPInputStream(new FileInputStream(part))
    val reader = new BufferedReader(new InputStreamReader(is))
    reader.readLine() // skip header
    var count = 0
    while (reader.readLine() != null) count += 1
    reader.close()
    count
  }

  /** Read gap at global index n from first part file (streaming). */
  private def readGapAt(dir: java.io.File, n: Int): Long = {
    val part = dir.listFiles().find(_.getName.startsWith("part-"))
      .getOrElse(sys.error(s"No part file in $dir"))
    val is = new GZIPInputStream(new FileInputStream(part))
    val reader = new BufferedReader(new InputStreamReader(is))
    reader.readLine() // skip header
    var lineNo = 0
    var line = reader.readLine()
    while (line != null && lineNo < n) { line = reader.readLine(); lineNo += 1 }
    reader.close()
    if (line != null) line.split(",")(1).toLong else 0L
  }

  /** Stream gaps from all part files, compress around 2-gaps, write to single gzip CSV.
    *  Consecutive non-2 gaps are summed; 2-gaps pass through.
    *  Example: [6,4,2,4,2,4,6,2] → [10,2,4,2,10,2]
    *  No lists in memory — pure streaming. */
  def compressAround2(gapsDir: String, outputPath: String): Unit = {
    import java.io.{BufferedReader, FileInputStream, InputStreamReader}
    import java.util.zip.GZIPInputStream
    import java.util.zip.GZIPOutputStream
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
          reader.readLine() // skip header
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

  def countTwoGaps(gapsDir: String): Int = {
    val dir = new java.io.File(gapsDir)
    val parts = dir.listFiles().filter(_.getName.startsWith("part-")).toSeq
    if (parts.isEmpty) return 0
    var total = 0
    for (part <- parts) {
      try {
        val is = new GZIPInputStream(new FileInputStream(part))
        val reader = new BufferedReader(new InputStreamReader(is))
        reader.readLine() // skip header
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
  def readFirstValues(gapsDir: String, headPrime: Long, n: Int, rotationIdx: Int = 0): Array[Long] = {
    val dir = new java.io.File(gapsDir)
    val parts = dir.listFiles().filter(_.getName.startsWith("part-")).sortBy(_.getName)
    val result = new scala.collection.mutable.ArrayBuffer[Long]()
    result += headPrime
    var acc = headPrime
    var remaining = n - 1  // need to read n-1 gaps
    var skipped = 0
    val skip = rotationIdx  // skip the first `rotationIdx` gaps (rotation offset)

    for (part <- parts) {
      if (remaining > 0) {
        try {
          val is = new GZIPInputStream(new FileInputStream(part))
          val reader = new BufferedReader(new InputStreamReader(is))
          reader.readLine() // skip header
          var line = reader.readLine()
          while (line != null && remaining > 0) {
            if (skipped < skip) {
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

  /** Collect gaps (for tests that compare against pure). */
  def collectGaps(df: DataFrame, R: Int): Array[Long] = {
    import df.sparkSession.implicits._
    val gaps = df.select("gap").as[Long].collect()
    if (R == 0 || gaps.isEmpty) gaps else {
      val n = gaps.length; val rot = R % n
      val r = new Array[Long](n); var i = 0
      while (i < n) { r(i) = gaps((i + rot) % n); i += 1 }
      r
    }
  }
}
