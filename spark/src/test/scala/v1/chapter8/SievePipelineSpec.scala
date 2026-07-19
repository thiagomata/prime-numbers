package v1.chapter8

import org.apache.spark.sql.SparkSession
import org.scalatest.BeforeAndAfterAll
import org.scalatest.funsuite.AnyFunSuite

class SievePipelineSpec extends AnyFunSuite with BeforeAndAfterAll {

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

  private def runFullPipeline(current: SieveStage): SieveStage = {
    val nextHV = current.head + current.gaps(0)
    val residues = current.computeResidues()
    val R = SievePipeline.findRotation(nextHV, current.head, current.modulus, residues)

    val (rdd, meta) = SievePipeline.phase1BlockProcessing(spark, current)
    val patched = SievePipeline.phase2SortAndCarry(spark, rdd, meta)
    val gapsUnrotated = patched.map(_.gap).collect()
    val gaps = SievePipeline.rotateArray(gapsUnrotated, R)

    val newM = current.modulus * current.head
    val newTail = Array(current.head) ++ current.tailPrimes
    SieveStage(nextHV, newTail, newM, gaps.length, gaps)
  }

  test("S0→S1: pipeline matches pure") {
    val (pure, _) = SieveStage.base.nextStage()
    val s = runFullPipeline(SieveStage.base)
    assert(s.head === pure.head)
    assert(s.gaps === pure.gaps)
  }

  test("S1→S2: pipeline matches pure") {
    val (pS1, _) = SieveStage.base.nextStage()
    val (pS2, _) = pS1.nextStage()
    val sS1 = runFullPipeline(SieveStage.base)
    val sS2 = runFullPipeline(sS1)
    assert(sS2.head === pS2.head)
    assert(sS2.gaps === pS2.gaps)
  }

  test("S2→S3: pipeline matches pure") {
    val (pS1, _) = SieveStage.base.nextStage()
    val (pS2, _) = pS1.nextStage()
    val (pS3, _) = pS2.nextStage()
    val sS1 = runFullPipeline(SieveStage.base)
    val sS2 = runFullPipeline(sS1)
    val sS3 = runFullPipeline(sS2)
    assert(sS3.head === pS3.head)
    assert(sS3.gaps === pS3.gaps)
    assert(sS3.period === 8)
    assert(sS3.gaps.sum === 30L)
  }

  test("S0→S4: 5 stages all match pure") {
    var pStage = SieveStage.base
    var sStage = SieveStage.base
    for (_ <- 0 until 5) {
      val (ps, _) = pStage.nextStage()
      val ss = runFullPipeline(sStage)
      assert(ss.head === ps.head)
      assert(ss.gaps === ps.gaps)
      pStage = ps
      sStage = ss
    }
  }
}
