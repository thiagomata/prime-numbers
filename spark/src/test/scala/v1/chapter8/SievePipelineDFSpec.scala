package v1.chapter8

import org.apache.spark.sql.SparkSession
import org.scalatest.BeforeAndAfterAll
import org.scalatest.funsuite.AnyFunSuite

class SievePipelineDFSpec extends AnyFunSuite with BeforeAndAfterAll {

  lazy val spark: SparkSession = SparkSession.builder()
    .appName("SieveDFTests")
    .master("local[1]")
    .config("spark.ui.enabled", "false")
    .config("spark.driver.host", "127.0.0.1")
    .getOrCreate()

  override def afterAll(): Unit = {
    if (spark != null) spark.stop()
    super.afterAll()
  }

  private def residueGaps(residues: Array[Long], m: Long): Array[Long] = {
    val T = residues.length
    if (T <= 1) return Array(m)
    val g = new Array[Long](T)
    var i = 0
    while (i < T - 1) { g(i) = residues(i + 1) - residues(i); i += 1 }
    g(T - 1) = m - residues(T - 1) + residues(0)
    g
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

  private def runDF(current: SieveStage): SieveStage = {
    val h = current.head
    val m = current.modulus
    val residues = current.computeResidues()
    val T = residues.length
    val gaps = residueGaps(residues, m)
    val nextHV = current.head + current.gaps(0)
    val R = rotation(h, m, residues, nextHV)

    val expanded = SievePipelineDF.phase1Expand(spark, h, m, residues, gaps)
    val walked = SievePipelineDF.phase2Walk(expanded)
    val patched = SievePipelineDF.phase3Carry(walked, h, m, T, residues, gaps)
    val collected = SievePipelineDF.collectGaps(patched, R)

    val newTail = Array(current.head) ++ current.tailPrimes
    SieveStage(nextHV, newTail, m * h, collected.length, collected)
  }

  test("DF: S0→S1 matches pure") {
    val (pure, _) = SieveStage.base.nextStage()
    val s = runDF(SieveStage.base)
    assert(s.head === pure.head, s"head: ${s.head} vs ${pure.head}")
    assert(s.gaps === pure.gaps, s"gaps: ${s.gaps.mkString(",")} vs ${pure.gaps.mkString(",")}")
  }

  test("DF: S1→S2 matches pure") {
    val (pS1, _) = SieveStage.base.nextStage()
    val (pS2, _) = pS1.nextStage()
    val sS1 = runDF(SieveStage.base)
    val sS2 = runDF(sS1)
    assert(sS2.head === pS2.head)
    assert(sS2.gaps === pS2.gaps)
  }

  test("DF: S2→S3 matches pure") {
    val (pS1, _) = SieveStage.base.nextStage()
    val (pS2, _) = pS1.nextStage()
    val (pS3, _) = pS2.nextStage()
    val sS1 = runDF(SieveStage.base)
    val sS2 = runDF(sS1)
    val sS3 = runDF(sS2)
    assert(sS3.head === pS3.head)
    assert(sS3.gaps === pS3.gaps)
    assert(sS3.period === 8)
    assert(sS3.gaps.sum === 30L)
  }

  test("DF: S0→S4: 5 stages all match pure") {
    var pStage = SieveStage.base
    var sStage = SieveStage.base
    for (_ <- 0 until 5) {
      val (ps, _) = pStage.nextStage()
      val ss = runDF(sStage)
      assert(ss.head === ps.head)
      assert(ss.gaps === ps.gaps)
      pStage = ps
      sStage = ss
    }
  }

  // ─── File I/O tests ───

  test("writeRotatedCsv + readFirstValues: S3 values match pure") {
    val (pS1, _) = SieveStage.base.nextStage()
    val (pS2, _) = pS1.nextStage()
    val (pS3, _) = pS2.nextStage()

    val h = pS2.head
    val m = pS2.modulus
    val residues = pS2.computeResidues()
    val T = residues.length
    val gaps = residueGaps(residues, m)
    val nextHV = pS2.head + pS2.gaps(0)
    val R = rotation(h, m, residues, nextHV)
    val outDir = new java.io.File(System.getProperty("java.io.tmpdir"), "sieve-df-test-" + System.nanoTime())
    outDir.mkdirs()

    try {
      val expanded = SievePipelineDF.phase1Expand(spark, h, m, residues, gaps)
      val walked = SievePipelineDF.phase2Walk(expanded)
      val patched = SievePipelineDF.phase3Carry(walked, h, m, T, residues, gaps)
      val info = SievePipelineDF.writeRotatedCsv(patched, R, outDir.getAbsolutePath, 1, h, nextHV, m, Array(h) ++ pS2.tailPrimes)

      // Request all values that we have gaps for (period = number of gaps)
      val expected = pS3.firstNValues(info.period)
      val values = SievePipelineDF.readFirstValues(info.path, info.nextHeadValue, info.period, info.rotationIndex)

      assert(values.length === expected.length, s"value count: ${values.length} vs ${expected.length}")
      assert(values === expected, s"values: ${values.mkString(",")} vs ${expected.mkString(",")}")
    } finally {
      outDir.listFiles().foreach { f =>
        if (f.isDirectory) f.listFiles().foreach(_.delete())
        f.delete()
      }
    }
  }

  test("countTwoGaps: S3 has 3 two-gaps") {
    val (pS1, _) = SieveStage.base.nextStage()
    val (pS2, _) = pS1.nextStage()

    val h = pS2.head
    val m = pS2.modulus
    val residues = pS2.computeResidues()
    val T = residues.length
    val gaps = residueGaps(residues, m)
    val nextHV = pS2.head + pS2.gaps(0)
    val R = rotation(h, m, residues, nextHV)
    val outDir = new java.io.File(System.getProperty("java.io.tmpdir"), "sieve-df-test-" + System.nanoTime())
    outDir.mkdirs()

    try {
      val expanded = SievePipelineDF.phase1Expand(spark, h, m, residues, gaps)
      val walked = SievePipelineDF.phase2Walk(expanded)
      val patched = SievePipelineDF.phase3Carry(walked, h, m, T, residues, gaps)
      val info = SievePipelineDF.writeRotatedCsv(patched, R, outDir.getAbsolutePath, 1, h, nextHV, m, Array(h) ++ pS2.tailPrimes)

      val twoCount = SievePipelineDF.countTwoGaps(info.path)
      assert(twoCount === 3, s"S3 should have 3 two-gaps, got $twoCount")
    } finally {
      outDir.listFiles().foreach { f =>
        if (f.isDirectory) f.listFiles().foreach(_.delete())
        f.delete()
      }
    }
  }

  test("readFirstValues: single gap file returns correct values") {
    val tmpDir = new java.io.File(System.getProperty("java.io.tmpdir"), "sieve-df-test-" + System.nanoTime())
    tmpDir.mkdirs()
    val tmpFile = new java.io.File(tmpDir, "part-00000.csv.gz")
    val pw = new java.io.PrintWriter(new java.util.zip.GZIPOutputStream(new java.io.FileOutputStream(tmpFile)))
    try {
      pw.println("gidx,gap,origin")
      pw.println("0,1,new")
    } finally pw.close()

    try {
      val values = SievePipelineDF.readFirstValues(tmpDir.getAbsolutePath, 2L, 2)
      assert(values === Array(2L, 3L), s"got ${values.mkString(",")}")
    } finally {
      tmpFile.delete(); tmpDir.delete()
    }
  }

  // ─── compressAround2 tests ───

  test("compressAround2: empty output not created") {
    val outDir = tempDir()
    try {
      val tmpFile = new java.io.File(outDir, "out.csv.gz")
      // No part files in dir — nothing to compress
      SievePipelineDF.compressAround2(outDir.getAbsolutePath, tmpFile.getAbsolutePath)
      // No part files → no header written, file should not exist
    } finally { deleteAll(outDir) }
  }

  test("compressAround2: S3 compresses correctly") {
    val outDir = tempDir()
    try {
      val (pS1, _) = SieveStage.base.nextStage()
      val (pS2, _) = pS1.nextStage()
      val h = pS2.head; val m = pS2.modulus
      val residues = pS2.computeResidues()
      val T = residues.length
      val gaps = residueGaps(residues, m)
      val nextHV = pS2.head + pS2.gaps(0)
      val R = rotation(h, m, residues, nextHV)

      val expanded = SievePipelineDF.phase1Expand(spark, h, m, residues, gaps)
      val walked = SievePipelineDF.phase2Walk(expanded)
      val patched = SievePipelineDF.phase3Carry(walked, h, m, T, residues, gaps)
      val info = SievePipelineDF.writeRotatedCsv(patched, R, outDir.getAbsolutePath, 1, h, nextHV, m, Array(h) ++ pS2.tailPrimes)

      val outFile = new java.io.File(outDir, "compressed.csv.gz")
      SievePipelineDF.compressAround2(info.path, outFile.getAbsolutePath)

      // Read back and verify
      val is = new java.util.zip.GZIPInputStream(new java.io.FileInputStream(outFile))
      val reader = new java.io.BufferedReader(new java.io.InputStreamReader(is))
      reader.readLine() // skip header
      val lines = scala.collection.mutable.ArrayBuffer[(Long, Int)]()
      var line = reader.readLine()
      while (line != null) {
        val parts = line.split(",")
        lines += ((parts(1).toLong, parts(2).toInt))
        line = reader.readLine()
      }
      reader.close()

      // S3 gaps [6,4,2,4,2,4,6,2] → [10,2,4,2,10,2]
      assert(lines.length === 6, s"expected 6 compressed gaps, got ${lines.length}")
      assert(lines(0) === ((10L, 2)), s"first: ${lines(0)}")
      assert(lines(1) === ((2L, 1)), "second should be 2")
      assert(lines(2) === ((4L, 1)), "third should be 4")
      assert(lines(3) === ((2L, 1)), "fourth should be 2")
      assert(lines(4) === ((10L, 2)), s"fifth: ${lines(4)}")
      assert(lines(5) === ((2L, 1)), "sixth should be 2")
    } finally { deleteAll(outDir) }
  }

  // ─── mergeCount tests ───

  test("gaps CSV includes mergeCount column") {
    val outDir = tempDir()
    try {
      val (pS1, _) = SieveStage.base.nextStage()
      val h = pS1.head; val m = pS1.modulus
      val residues = pS1.computeResidues()
      val gaps = residueGaps(residues, m)
      val nextHV = pS1.head + pS1.gaps(0)
      val R = rotation(h, m, residues, nextHV)

      val expanded = SievePipelineDF.phase1Expand(spark, h, m, residues, gaps)
      val walked = SievePipelineDF.phase2Walk(expanded)
      val patched = SievePipelineDF.phase3Carry(walked, h, m, residues.length, residues, gaps)
      val info = SievePipelineDF.writeRotatedCsv(patched, R, outDir.getAbsolutePath, 1, h, nextHV, m, Array(h))

      // Read first part file header — should include mergeCount
      val part = new java.io.File(info.path).listFiles().find(_.getName.startsWith("part-")).get
      val is = new java.util.zip.GZIPInputStream(new java.io.FileInputStream(part))
      val reader = new java.io.BufferedReader(new java.io.InputStreamReader(is))
      val header = reader.readLine()
      reader.close()
      assert(header.contains("mergeCount"), s"header missing mergeCount: $header")
    } finally { deleteAll(outDir) }
  }

  test("S3 gaps have correct mergeCount") {
    val outDir = tempDir()
    try {
      val (pS1, _) = SieveStage.base.nextStage()
      val (pS2, _) = pS1.nextStage()
      val h = pS2.head; val m = pS2.modulus
      val residues = pS2.computeResidues()
      val gaps = residueGaps(residues, m)
      val nextHV = pS2.head + pS2.gaps(0)
      val R = rotation(h, m, residues, nextHV)

      val expanded = SievePipelineDF.phase1Expand(spark, h, m, residues, gaps)
      val walked = SievePipelineDF.phase2Walk(expanded)
      val patched = SievePipelineDF.phase3Carry(walked, h, m, residues.length, residues, gaps)
      val info = SievePipelineDF.writeRotatedCsv(patched, R, outDir.getAbsolutePath, 1, h, nextHV, m, Array(h) ++ pS2.tailPrimes)

      // Read all part files, collect (gap, origin, mergeCount)
      val parts = new java.io.File(info.path).listFiles().filter(_.getName.startsWith("part-")).sortBy(_.getName)
      val rows = scala.collection.mutable.ArrayBuffer[(Long, String, Int)]()
      for (part <- parts) {
        val is = new java.util.zip.GZIPInputStream(new java.io.FileInputStream(part))
        val reader = new java.io.BufferedReader(new java.io.InputStreamReader(is))
        reader.readLine() // skip header
        var line = reader.readLine()
        while (line != null) {
          val p = line.split(",")
          rows += ((p(1).toLong, p(2), p(3).toInt))
          line = reader.readLine()
        }
        reader.close()
      }

      assert(rows.length === 8, s"expected 8 gaps, got ${rows.length}")
      // Merges at positions 0 and 6
      assert(rows(0) === ((6L, "merge", 1)), s"row 0: ${rows(0)}")
      assert(rows(6) === ((6L, "merge", 1)), s"row 6: ${rows(6)}")
      // Copies have mergeCount=0
      assert(rows(1)._3 === 0, s"row 1 mergeCount: ${rows(1)._3}")
      assert(rows(2)._3 === 0, s"row 2 mergeCount: ${rows(2)._3}")
      assert(rows(3)._3 === 0, s"row 3 mergeCount: ${rows(3)._3}")
      assert(rows(4)._3 === 0, s"row 4 mergeCount: ${rows(4)._3}")
      assert(rows(5)._3 === 0, s"row 5 mergeCount: ${rows(5)._3}")
      assert(rows(7)._3 === 0, s"row 7 mergeCount: ${rows(7)._3}")
    } finally { deleteAll(outDir) }
  }

  private def tempDir(): java.io.File = {
    val d = new java.io.File(System.getProperty("java.io.tmpdir"), "sieve-df-test-" + System.nanoTime())
    d.mkdirs(); d
  }

  private def deleteAll(f: java.io.File): Unit = {
    if (f.isDirectory) f.listFiles().foreach(deleteAll)
    f.delete()
  }
}
