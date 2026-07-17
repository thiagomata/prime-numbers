package v1.chapter8

import org.apache.spark.sql.SparkSession
import org.scalatest.BeforeAndAfterAll
import org.scalatest.funsuite.AnyFunSuite

class SparkSievePipelineSpec extends AnyFunSuite with BeforeAndAfterAll {

  lazy val spark: SparkSession = SparkSession.builder()
    .appName("SievePipelineTests")
    .master("local[1]")
    .config("spark.ui.enabled", "false")
    .config("spark.driver.host", "127.0.0.1")
    .getOrCreate()

  override def afterAll(): Unit = {
    if (spark != null) spark.stop()
    super.afterAll()
  }

  private def assertStagesMatch(pure: SieveStage, s: SieveStage, label: String): Unit = {
    assert(s.head === pure.head, s"$label head")
    assert(s.gaps === pure.gaps, s"$label gaps: Spark=${s.gaps.mkString(",")} Pure=${pure.gaps.mkString(",")}")
    assert(s.modulus === pure.modulus, s"$label modulus")
    assert(s.period === pure.period, s"$label period")
  }

  private def assertLineagesMatch(pure: Array[GapLineage], s: Array[GapLineage], label: String): Unit = {
    assert(s.length === pure.length, s"$label lineage length")
    assert(s.map(_.origin) === pure.map(_.origin), s"$label origins: Spark=${s.map(_.origin).mkString(",")} Pure=${pure.map(_.origin).mkString(",")}")
    assert(s.map(_.gap) === pure.map(_.gap), s"$label lineage gaps")
  }

  test("S0->S1: Spark matches pure") {
    val (pS1, pL1) = SieveStage.base.nextStage()
    val (sS1, sL1) = SparkSievePipeline.nextStage(spark, SieveStage.base)
    assertStagesMatch(pS1, sS1, "S1")
    assertLineagesMatch(pL1, sL1, "S1 lineage")
  }

  test("S0->S2: Spark matches pure") {
    val (pS1, _) = SieveStage.base.nextStage()
    val (pS2, pL2) = pS1.nextStage()
    val (sS1, _) = SparkSievePipeline.nextStage(spark, SieveStage.base)
    val (sS2, sL2) = SparkSievePipeline.nextStage(spark, sS1)
    assertStagesMatch(pS2, sS2, "S2")
    assertLineagesMatch(pL2, sL2, "S2 lineage")
  }

  test("S0->S3: 4 stages all match") {
    var pStage = SieveStage.base
    var sStage = SieveStage.base
    for (i <- 0 until 4) {
      val (ps, pl) = pStage.nextStage()
      val (ss, sl) = SparkSievePipeline.nextStage(spark, sStage)
      assertStagesMatch(ps, ss, s"Stage ${i+1}")
      assertLineagesMatch(pl, sl, s"Stage ${i+1} lineage")
      pStage = ps
      sStage = ss
    }
  }
}
