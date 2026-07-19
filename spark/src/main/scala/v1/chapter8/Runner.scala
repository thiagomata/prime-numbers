package v1.chapter8

import org.apache.spark.sql.SparkSession
import java.io.File

object Runner {

  def main(args: Array[String]): Unit = {
    val numStages = args.headOption.map(_.toInt).getOrElse(10)
    val outputDir = if (args.length > 1) args(1) else "data/sieve-spark2"
    val baseDir = new File(outputDir)
    baseDir.mkdirs()

    val spark = SparkSession.builder()
      .appName("SieveSequenceGenerator")
      .master("local[*]")
      .config("spark.driver.maxResultSize", "4g")
      .config("spark.driver.memory", "4g")
      .getOrCreate()
    spark.sparkContext.setLogLevel("WARN")

    try {
      var stage = SieveStage.base

      println(s"Sieve Sequence (Spark)  Stages: $numStages  Output: $outputDir")
      println()

      for (i <- 0 to numStages) {
        val twoGapCount = stage.gaps.count(_ == 2)
        println(f"Stage $i%3d: head=${stage.head}%6d  period=${stage.period}%8d  modulus=${stage.modulus}%20d  gaps=${stage.gaps.length}%8d  twoGaps=$twoGapCount%8d")

        val stageDir = new File(baseDir, f"stage_$i%03d")
        stageDir.mkdirs()

        // Write values (always small - 1000 elements)
        val values = stage.firstNValues(1000)
        val valuesPath = new File(stageDir, "values.csv.gz")
        writeValues(valuesPath, values)

        if (stage.modulus < 0) {
          println(s"\nWARNING: Modulus overflow.")
          return
        }

        if (i < numStages) {
          val (next, _) = SievePipeline.nextStage(spark, stage, outputDir, i + 1)
          stage = next
        }
      }

      println(s"\nDone in $outputDir/")
    } finally {
      spark.stop()
    }
  }

  private def writeValues(file: File, values: Array[Long]): Unit = {
    import java.util.zip.GZIPOutputStream
    val pw = new java.io.PrintWriter(new GZIPOutputStream(new java.io.FileOutputStream(file)))
    try {
      pw.println("index,value")
      var i = 0
      while (i < values.length) {
        pw.println(s"$i,${values(i)}")
        i += 1
      }
    } finally pw.close()
  }
}
