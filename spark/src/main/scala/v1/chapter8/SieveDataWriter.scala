package v1.chapter8

import org.apache.spark.sql.SparkSession
import java.io.File

object SieveDataWriter {

  def writeGaps(spark: SparkSession, dir: File, gaps: Array[Long], lineage: Array[GapLineage]): Unit = {
    import spark.implicits._
    val rows = gaps.indices.map { i =>
      val l = if (i < lineage.length) lineage(i) else GapLineage(i, gaps(i), "unknown", 0, 0, Array.empty, Array.empty)
      GapRow(l.index, l.gap, l.origin, l.age, l.mergeCount, l.mergeAncestors.mkString(";"), l.ancestorValues.mkString(";"))
    }.toSeq.toDS()
    rows.coalesce(1).write.mode("overwrite").option("header", "true").csv(new File(dir, "gaps").getAbsolutePath)
  }

  def writeGaps2Focused(spark: SparkSession, dir: File, compressed: Array[Long]): Unit = {
    import spark.implicits._
    val rows = compressed.indices.map { i =>
      Gap2FocusedRow(i, compressed(i), 1)
    }.toSeq.toDS()
    rows.coalesce(1).write.mode("overwrite").option("header", "true").csv(new File(dir, "gaps_2focused").getAbsolutePath)
  }

  def writeValues(spark: SparkSession, dir: File, values: Array[Long]): Unit = {
    import spark.implicits._
    val rows = values.indices.map { i =>
      ValueRow(i, values(i))
    }.toSeq.toDS()
    rows.coalesce(1).write.mode("overwrite").option("header", "true").csv(new File(dir, "values").getAbsolutePath)
  }

  def writeSummary(spark: SparkSession, baseDir: File, stages: Seq[(Int, Long, Int, Long, Int, String, String, String)]): Unit = {
    import spark.implicits._
    val rows = stages.map { case (s, h, p, m, gc, gf, g2f, vf) =>
      StageSummaryRow(s, h, p, m, gc, gf, g2f, vf)
    }.toDS()
    rows.coalesce(1).write.mode("overwrite").option("header", "true").csv(new File(baseDir, "stages_summary").getAbsolutePath)
  }

  def writeGapStats(spark: SparkSession, baseDir: File, stats: Seq[GapStageStats]): Unit = {
    import spark.implicits._
    val rows = stats.map { s =>
      GapStatsRow(s.stage, s.head, s.period, s.modulus, s.gapCount, s.copyCount, s.mergeCount,
        s.newGapValues, s.lostGapValues, s.maxAge, s.avgAge, s.twoGapCount, s.twoGapSurvived)
    }.toDS()
    rows.coalesce(1).write.mode("overwrite").option("header", "true").csv(new File(baseDir, "gap_stats").getAbsolutePath)
  }
}
