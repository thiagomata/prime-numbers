package v1.chapter8

case class SieveStage(
  head: Long,
  tailPrimes: Array[Long],
  modulus: Long,
  period: Int,
  gaps: Array[Long]
) extends Serializable {

  def firstNValues(n: Int): Array[Long] = {
    val result = new Array[Long](n)
    if (n == 0) return result
    result(0) = head
    var acc = head
    var gi = 0
    var i = 1
    while (i < n) {
      acc += gaps(gi)
      result(i) = acc
      gi = (gi + 1) % period
      i += 1
    }
    result
  }

  def nextStage(): (SieveStage, Array[GapLineage]) = {
    val h = head
    val m = modulus
    val newModulus = m * h

    // 1. Residues: values in [0, m) coprime to all tail primes
    val residues = computeResidues()

    // 2. Expand: for each k in [0, h), for each r in residues, emit r + k*m
    val numResidues = residues.length
    val totalExpanded = h.toInt * numResidues
    val expanded = new Array[Long](totalExpanded)
    var k = 0
    while (k < h.toInt) {
      var j = 0
      while (j < numResidues) {
        expanded(k * numResidues + j) = residues(j) + k.toLong * m
        j += 1
      }
      k += 1
    }

    // 3. Sort ascending
    java.util.Arrays.sort(expanded)

    // 4. Filter: remove values divisible by head
    val filtered = new Array[Long](totalExpanded)
    var filteredCount = 0
    var i = 0
    while (i < totalExpanded) {
      if (expanded(i) % h != 0) {
        filtered(filteredCount) = expanded(i)
        filteredCount += 1
      }
      i += 1
    }
    val survivors = java.util.Arrays.copyOf(filtered, filteredCount)

    // 5. Compute gaps from sorted survivors
    val newGaps = if (survivors.length <= 1) {
      Array(newModulus)
    } else {
      val result = new Array[Long](survivors.length)
      var gi = 0
      while (gi < survivors.length - 1) {
        result(gi) = survivors(gi + 1) - survivors(gi)
        gi += 1
      }
      result(survivors.length - 1) = newModulus - survivors.last + survivors.head
      result
    }

    // 6. Rotate: next head is head + gaps(0) from current stage
    //    Find that value in survivors and rotate gaps so it's at position 0
    val nextHeadValue = head + gaps(0)
    val rotationIndex = {
      var idx = 0
      while (idx < survivors.length && survivors(idx) != nextHeadValue) idx += 1
      idx
    }

    val rotatedGaps = if (rotationIndex == 0) newGaps else {
      val r = new Array[Long](newGaps.length)
      var gi = 0
      while (gi < newGaps.length) {
        r(gi) = newGaps((gi + rotationIndex) % newGaps.length)
        gi += 1
      }
      r
    }

    // 7. Lineage: for each new gap, count how many old gaps it spans
    //    trackLineage returns lineage already rotated to match rotatedGaps
    val lineage = trackLineage(survivors, newGaps, rotationIndex, newModulus)

    val newPeriod = rotatedGaps.length
    val newTailPrimes = Array(head) ++ tailPrimes

    (SieveStage(nextHeadValue, newTailPrimes, newModulus, newPeriod, rotatedGaps), lineage)
  }

  /**
   * Track lineage for each new gap.
   *
   * The expanded sorted values are the residue representatives in [0, h*m).
   * Each old gap (repeated h times) spans two consecutive expanded values
   * within the same "copy" k.
   *
   * After filtering, some expanded values are removed. For each new gap
   * (between two consecutive survivors), count how many old gaps were
   * between them in the expanded list.
   *
   * - mergeCount == 1 means the gap survived unchanged (copy)
   * - mergeCount > 1 means multiple old gaps were merged
   */
  private def trackLineage(
    survivors: Array[Long],
    newGaps: Array[Long],
    rotationIndex: Int,
    newModulus: Long
  ): Array[GapLineage] = {
    val h = head
    val m = modulus
    val n = survivors.length

    // Rebuild the expanded sorted list
    val residues = computeResidues()
    val numResidues = residues.length
    val totalExpanded = h.toInt * numResidues
    val expanded = new Array[Long](totalExpanded)
    var k = 0
    while (k < h.toInt) {
      var j = 0
      while (j < numResidues) {
        expanded(k * numResidues + j) = residues(j) + k.toLong * m
        j += 1
      }
      k += 1
    }
    java.util.Arrays.sort(expanded)

    // Compute lineage in natural gap order:
    //   gap i connects survivor[i] to survivor[(i+1) % n]
    //   gap n-1 is the wrap-around: survivor[n-1] to survivor[0] + newModulus
    val naturalLineage = new Array[GapLineage](n)
    var gapIdx = 0
    while (gapIdx < n) {
      val curVal = survivors(gapIdx)
      val nextVal = survivors((gapIdx + 1) % n)
      val isWrap = (gapIdx == n - 1)

      var betweenCount = 0
      var i = 0
      while (i < totalExpanded) {
        val ev = expanded(i)
        if (isWrap) {
          // Wrap: count values in (curVal, newModulus) and [0, nextVal)
          if (ev > curVal || ev < nextVal) betweenCount += 1
        } else {
          if (ev > curVal && ev < nextVal) betweenCount += 1
        }
        i += 1
      }

      val mergeCount = betweenCount + 1
      val origin = if (mergeCount == 1) "copy" else "merge"

      naturalLineage(gapIdx) = GapLineage(
        index = gapIdx,
        gap = newGaps(gapIdx),
        origin = origin,
        age = 1,
        mergeCount = mergeCount,
        mergeAncestors = Array.empty,
        ancestorValues = Array.empty
      )
      gapIdx += 1
    }

    // Rotate lineage to match rotated gaps
    if (rotationIndex == 0) naturalLineage else {
      val rotated = new Array[GapLineage](n)
      var gi = 0
      while (gi < n) {
        val src = naturalLineage((gi + rotationIndex) % n)
        rotated(gi) = src.copy(index = gi)
        gi += 1
      }
      rotated
    }
  }

  def computeResidues(): Array[Long] = {
    val m = modulus
    val buf = new scala.collection.mutable.ArrayBuffer[Long]()
    var r = 0L
    while (r < m) {
      if (SieveStage.isCoprime(r, tailPrimes)) buf += r
      r += 1
    }
    buf.toArray
  }

  override def toString: String =
    s"SieveStage(head=$head, period=$period, modulus=$modulus, gaps=[${gaps.mkString(",")}])"
}

object SieveStage {

  def base: SieveStage =
    SieveStage(head = 2L, tailPrimes = Array.empty, modulus = 1L, period = 1, gaps = Array(1L))

  def isCoprime(v: Long, primes: Array[Long]): Boolean = {
    var i = 0
    while (i < primes.length) {
      if (primes(i) != 0 && v % primes(i) == 0) return false
      i += 1
    }
    true
  }
}
