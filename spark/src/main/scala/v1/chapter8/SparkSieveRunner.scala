package v1.chapter8

import org.apache.spark.sql.SparkSession
import java.io.File

/**
 * Entry point for the sieve sequence data generator.
 *
 * Usage: sbt "spark/runMain v1.chapter8.SparkSieveRunner [numStages] [outputDir]"
 *
 * Generates sieve stages iteratively using Spark for the heavy
 * expand-filter-sort pipeline, writing gaps (with lineage),
 * 2-gap compressed gaps, first 1000 values, and summary stats to CSV
 * via Spark DataFrames.
 */
object SparkSieveRunner {

  def main(args: Array[String]): Unit = {
    val numStages = args.headOption.map(_.toInt).getOrElse(10)
    val outputDir = if (args.length > 1) args(1) else "data/sieve-spark"
    val valuesPerStage = 1000

    println(s"Sieve Sequence Data Generator (Spark)")
    println(s"  Stages: $numStages")
    println(s"  Output: $outputDir")
    println(s"  Values per stage: $valuesPerStage")
    println()

    val baseDir = new File(outputDir)
    baseDir.mkdirs()

    val spark = SparkSession.builder()
      .appName("SieveSequenceGenerator")
      .master("local[*]")
      .getOrCreate()
    spark.sparkContext.setLogLevel("WARN")

    try {
      var stage = SieveStage.base
      var pendingLineage: Array[GapLineage] = Array.empty
      var prevTwoGapCount = 0
      val summaryRows = scala.collection.mutable.ArrayBuffer[(Int, Long, Int, Long, Int, String, String, String)]()
      val allStats = scala.collection.mutable.ArrayBuffer[GapStageStats]()


      for (i <- 0 to numStages) {
        val stageDir = new File(baseDir, f"stage_$i%03d")
        stageDir.mkdirs()

        val lineage = if (i == 0) {
          stage.gaps.zipWithIndex.map { case (g, idx) =>
            GapLineage(idx, g, "new", 1, 0, Array.empty, Array.empty)
          }
        } else {
          pendingLineage
        }

        val copyCount = lineage.count(_.origin == "copy")
        val mergeCount = lineage.count(_.origin == "merge")
        val twoGapCount = stage.gaps.count(_ == 2)

        println(f"Stage $i%3d: head=${stage.head}%6d  period=${stage.period}%8d  modulus=${stage.modulus}%20d  gaps=${stage.gaps.length}%8d  copy=$copyCount%5d  merge=$mergeCount%5d  twoGaps=$twoGapCount%5d")

        val stats = GapLineage.computeStats(i, stage.head, stage.period, stage.modulus, stage.gaps, lineage, prevTwoGapCount)
        allStats += stats

        val values = stage.firstNValues(valuesPerStage)
        val compressed = GapLineage.compressAround2(stage.gaps)

        // Write CSV via Spark DataFrames
        SieveDataWriter.writeGaps(spark, stageDir, stage.gaps, lineage)
        SieveDataWriter.writeGaps2Focused(spark, stageDir, compressed)
        SieveDataWriter.writeValues(spark, stageDir, values)

        val gapsPath = f"$outputDir/stage_$i%03d/gaps"
        val gaps2Path = f"$outputDir/stage_$i%03d/gaps_2focused"
        val valuesPath = f"$outputDir/stage_$i%03d/values"
        summaryRows += ((i, stage.head, stage.period, stage.modulus, stage.gaps.length, gapsPath, gaps2Path, valuesPath))

        prevTwoGapCount = twoGapCount

        if (stage.modulus < 0) {
          println(s"\nWARNING: Modulus overflow detected at stage $i. Stopping.")
          return
        }

        if (i < numStages) {
          // Use Spark pipeline for heavy expand-filter-sort
          val (next, nextLin) = SparkSievePipeline.nextStage(spark, stage)
          stage = next
          pendingLineage = nextLin
        }
      }

      // Write summary via Spark DataFrames
      SieveDataWriter.writeSummary(spark, baseDir, summaryRows.toSeq)
      SieveDataWriter.writeGapStats(spark, baseDir, allStats.toSeq)

      println(s"\nDone. Generated ${numStages + 1} stages in $outputDir/")
    } finally {
      spark.stop()
    }
  }
}
