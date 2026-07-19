package v1.chapter8

import org.apache.spark.sql.SparkSession
import java.io.File

object Runner2 {

  def main(args: Array[String]): Unit = {
    val numStages = args.headOption.map(_.toInt).getOrElse(10)
    val outputDir = if (args.length > 1) args(1) else "data/sieve-df"
    val baseDir = new File(outputDir)
    baseDir.mkdirs()

    val spark = SparkSession.builder()
      .appName("SieveDFGenerator")
      .master("local[1]")
      .config("spark.driver.maxResultSize", "4g")
      .getOrCreate()
    spark.sparkContext.setLogLevel("WARN")

    try {
      var curHead = SieveStage.base.head
      var curMod = SieveStage.base.modulus
      var curTail = SieveStage.base.tailPrimes
      var curPeriod = SieveStage.base.period
      var curFirstGap = SieveStage.base.gaps(0)

      println(s"Sieve Sequence (DataFrame)  Stages: $numStages  Output: $outputDir")
      println()

      // Stage 0: printed but computed by definition
      val stage0Dir = new File(baseDir, "stage_000")
      stage0Dir.mkdirs()
      writeValues(new File(stage0Dir, "values.csv.gz"), 2L, Array(2L, 3L, 4L, 5L, 6L, 7L, 8L, 9L, 10L, 11L))
      println(f"Stage   0: head=     2  period=       1  modulus=                   1  gaps=       1  twoGaps=       0")

      for (i <- 1 to numStages) {
        val h = curHead
        val m = curMod
        val nextHV = h + curFirstGap
        val residues = computeResidues(h, m, curTail)
        val T = residues.length
        val residueGaps = computeGaps(residues, m)
        val R = rotation(h, m, residues, nextHV)
        val newMod = h * m

        val expanded = SievePipelineDF.phase1Expand(spark, h, m, residues, residueGaps)
        val walked = SievePipelineDF.phase2Walk(expanded)
        val patched = SievePipelineDF.phase3Carry(walked, h, m, T, residues, residueGaps)

        val info = SievePipelineDF.writeRotatedCsv(patched, R, outputDir, i, h, nextHV, m, curTail)

        val twoGapCount = SievePipelineDF.countTwoGaps(info.path)

        println(f"Stage $i%3d: head=${info.nextHeadValue}%6d  period=${info.period}%8d  modulus=$newMod%20d  gaps=${info.period}%8d  twoGaps=$twoGapCount%8d")

        val values = SievePipelineDF.readFirstValues(info.path, info.nextHeadValue, 1000, info.rotationIndex)
        writeValues(new File(outputDir, f"stage_$i%03d/values.csv.gz"), info.nextHeadValue, values)

        // 2-gap compressed gaps (streaming from the gap file)
        val twoFocusedPath = new File(outputDir, f"stage_$i%03d/gaps-2.csv.gz").getAbsolutePath
        SievePipelineDF.compressAround2(info.path, twoFocusedPath)

        curHead = info.nextHeadValue
        curMod = newMod
        curTail = Array(h) ++ curTail
        curPeriod = info.period
        curFirstGap = info.firstGap
      }

      println(s"\nDone in $outputDir/")
    } finally {
      spark.stop()
    }
  }

  private def computeResidues(h: Long, m: Long, tailPrimes: Array[Long]): Array[Long] = {
    val buf = scala.collection.mutable.ArrayBuffer[Long]()
    var r = 0L
    while (r < m) {
      if (isCoprime(r, tailPrimes)) buf += r
      r += 1
    }
    buf.toArray
  }

  private def isCoprime(v: Long, primes: Array[Long]): Boolean = {
    var i = 0
    while (i < primes.length) {
      if (primes(i) != 0 && v % primes(i) == 0) return false
      i += 1
    }
    true
  }

  private def computeGaps(residues: Array[Long], m: Long): Array[Long] = {
    val T = residues.length
    if (T <= 1) return Array(m)
    val g = new Array[Long](T)
    var i = 0
    while (i < T - 1) { g(i) = residues(i + 1) - residues(i); i += 1 }
    g(T - 1) = m - residues(T - 1) + residues(0); g
  }

  private def rotation(h: Long, m: Long, residues: Array[Long], nextHV: Long): Int = {
    var count = 0; var found = false; var k = 0L
    while (k < h && !found) { var i = 0
      while (i < residues.length && !found) {
        val v = residues(i) + k * m
        if (v % h != 0) { if (v == nextHV) found = true; else count += 1 }
        i += 1 }; k += 1 }
    count
  }

  private def writeValues(file: java.io.File, head: Long, values: Array[Long]): Unit = {
    import java.util.zip.GZIPOutputStream
    val pw = new java.io.PrintWriter(new GZIPOutputStream(new java.io.FileOutputStream(file)))
    try {
      pw.println("index,value")
      var i = 0
      while (i < values.length) { pw.println(s"$i,${values(i)}"); i += 1 }
    } finally pw.close()
  }
}
