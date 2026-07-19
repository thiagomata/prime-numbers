package v1.chapter8

/**
 * Block processing functions — standalone, serializable.
 * Separated from SievePipeline to avoid serialization issues with Spark closures.
 */
object BlockProcessing {

  case class GapEntry(blockIdx: Int, localIdx: Int, gap: Long, origin: String) extends Serializable

  case class BlockMetadata(
    blockIndex: Int,
    firstFiltered: Boolean,
    lastFiltered: Boolean,
    tailAccumGap: Long,
    tailAccumCount: Int
  ) extends Serializable

  def processBlock(
    k: Long,
    residues: Array[Long],
    residueGaps: Array[Long],
    h: Long,
    m: Long,
    T: Int
  ): Iterator[GapEntry] = {
    var pos = 0
    var localIdx = 0
    var accumGap = 0L
    var accumCount = 0

    def advanceToNext(): Unit = {
      while (pos < T) {
        val gapOut = residueGaps(pos)
        val nextI = (pos + 1) % T
        val nextK = if (nextI == 0) k + 1 else k
        val nextVal = residues(nextI) + nextK * m
        val nextFiltered = (nextVal % h == 0)

        if (nextFiltered) {
          accumGap += gapOut
          accumCount += 1
          pos += 1
        } else {
          return
        }
      }
    }

    advanceToNext()

    new Iterator[GapEntry] {
      override def hasNext: Boolean = pos < T

      override def next(): GapEntry = {
        val gapOut = residueGaps(pos)
        val gap = if (accumCount > 0) accumGap + gapOut else gapOut
        val origin = if (accumCount > 0) "merge" else "copy"
        val entry = GapEntry(k.toInt, localIdx, gap, origin)
        localIdx += 1
        accumGap = 0L
        accumCount = 0
        pos += 1
        advanceToNext()
        entry
      }
    }
  }

  def blockMeta(
    k: Long,
    residues: Array[Long],
    residueGaps: Array[Long],
    h: Long,
    m: Long,
    T: Int
  ): BlockMetadata = {
    var accumGap = 0L
    var accumCount = 0
    for (i <- 0 until T) {
      val gapOut = residueGaps(i)
      val nextI = (i + 1) % T
      val nextK = if (nextI == 0) k + 1 else k
      val nextVal = residues(nextI) + nextK * m
      val nextFiltered = (nextVal % h == 0)
      if (nextFiltered) { accumGap += gapOut; accumCount += 1 }
      else { accumGap = 0L; accumCount = 0 }
    }
    val firstVal = residues(0) + k * m
    val lastVal = residues(T - 1) + k * m
    BlockMetadata(k.toInt, firstVal % h == 0, lastVal % h == 0, accumGap, accumCount)
  }
}
