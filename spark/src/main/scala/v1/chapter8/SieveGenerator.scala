package v1.chapter8

import org.apache.spark.sql.SparkSession
import java.io.File

/**
 * Generates sieve sequence stages using the DataFrame pipeline.
 * Writes gaps (partitioned gzip CSV), values, and 2-gap compressed views.
 */
object SieveGenerator {

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
      // Track current stage metadata (no gap array stored on driver)
      var currentHead = SieveStage.base.head
      var currentModulus = SieveStage.base.modulus
      var currentTailPrimes = SieveStage.base.tailPrimes
      var currentFirstGap = SieveStage.base.gaps(0)

      println(s"Sieve Sequence (DataFrame)  Stages: $numStages  Output: $outputDir")
      println()

      // Stage 0: defined by construction
      val stage0Dir = new File(baseDir, "stage_000")
      stage0Dir.mkdirs()
      writeValuesCsv(new File(stage0Dir, "values.csv.gz"), 2L, Array(2L, 3L, 4L, 5L, 6L, 7L, 8L, 9L, 10L, 11L))
      println(f"Stage   0: head=     2  period=       1  modulus=                   1  gaps=       1  twos=       0")

      for (i <- 1 to numStages) {
        val head = currentHead
        val modulus = currentModulus
        val nextHeadValue = head + currentFirstGap
        val residues = computeResiduesForward(modulus, currentTailPrimes)
        val T = residues.length
        val residueGaps = computeResidueGaps(residues, modulus)
        val rotationOffset = countSurvivorsBefore(head, modulus, residues, nextHeadValue)
        val nextModulus = head * modulus

        val expanded = SievePipelineDF.expandBlocks(spark, head, modulus, residues, residueGaps)
        val walked = SievePipelineDF.walkAndMerge(expanded)
        val patched = SievePipelineDF.applyCarryChain(walked, head, modulus, T, residues, residueGaps)

        val info = SievePipelineDF.writeRotatedCsv(patched, rotationOffset, outputDir, i,
          head, nextHeadValue, modulus, currentTailPrimes)

        val twoCount = SievePipelineDF.countTwos(info.path)

        println(f"Stage $i%3d: head=${info.nextHeadValue}%6d  period=${info.period}%8d  modulus=$nextModulus%20d  gaps=${info.period}%8d  twos=$twoCount%8d")

        val values = SievePipelineDF.readFirstValues(info.path, info.nextHeadValue, 1000, info.rotationIndex)
        writeValuesCsv(new File(outputDir, f"stage_$i%03d/values.csv.gz"), info.nextHeadValue, values)

        val twoCompressedPath = new File(outputDir, f"stage_$i%03d/gaps-2.csv.gz").getAbsolutePath
        SievePipelineDF.compressAroundTwos(info.path, twoCompressedPath)

        currentHead = info.nextHeadValue
        currentModulus = nextModulus
        currentTailPrimes = Array(head) ++ currentTailPrimes
        currentFirstGap = info.firstGap
      }

      println(s"\nDone in $outputDir/")
    } finally {
      spark.stop()
    }
  }

  /** Compute residue gaps — differences between consecutive ascending residues. */
  private def computeResidueGaps(residues: Array[Long], modulus: Long): Array[Long] = {
    val T = residues.length
    if (T <= 1) return Array(modulus)
    val g = new Array[Long](T)
    var i = 0
    while (i < T - 1) { g(i) = residues(i + 1) - residues(i); i += 1 }
    g(T - 1) = modulus - residues(T - 1) + residues(0); g
  }

  /**
   * Count survivors before the next head value in the expanded residues.
   * This gives the rotation offset: how many positions to shift so that
   * the gap starting at nextHeadValue becomes first.
   */
  private def countSurvivorsBefore(head: Long, modulus: Long, residues: Array[Long], nextHeadValue: Long): Int = {
    var count = 0; var found = false; var blockIdx = 0L
    while (blockIdx < head && !found) { var i = 0
      while (i < residues.length && !found) {
        val v = residues(i) + blockIdx * modulus
        if (v % head != 0) { if (v == nextHeadValue) found = true; else count += 1 }
        i += 1 }; blockIdx += 1 }
    count
  }

  /** Values in [0, modulus) coprime to all tail primes (ascending). */
  private def computeResiduesForward(modulus: Long, tailPrimes: Array[Long]): Array[Long] = {
    val buf = scala.collection.mutable.ArrayBuffer[Long]()
    var r = 0L
    while (r < modulus) {
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

  private def writeValuesCsv(file: java.io.File, head: Long, values: Array[Long]): Unit = {
    import java.util.zip.GZIPOutputStream
    val pw = new java.io.PrintWriter(new GZIPOutputStream(new java.io.FileOutputStream(file)))
    try {
      pw.println("index,value")
      var i = 0
      while (i < values.length) { pw.println(s"$i,${values(i)}"); i += 1 }
    } finally pw.close()
  }
}
