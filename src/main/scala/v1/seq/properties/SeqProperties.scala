package v1.seq.properties

import stainless.lang.{BigInt, *}
import verification.Helper.assert
//import verification.Helper.check
import stainless.proof.check
import v1.cycle.Cycle
import verification.Helper
import verification.Helper.equality

object SeqProperties {
  def firstValuesMatchPrev(seq: v1.seq.Seq, pos: BigInt): Boolean = {
    require(pos >= 0)
    require(seq.previous.size > pos)
    seq.previous(pos) == seq(pos)
  }.holds

  def firstValuesMatchFirstPosInLoop(seq: v1.seq.Seq, pos: BigInt): Boolean = {
    require(pos == seq.previous.size)
    if (seq.previous.isEmpty) {
      seq(pos) == seq.loop(0)
    } else {
      seq(pos) == seq.previous(seq.previous.size - 1) + seq.loop(0)
    }
  }.holds

  def nextValuesMatchLoop(seq: v1.seq.Seq, pos: BigInt): Boolean = {
    require(pos >= seq.previous.size)

    val loopPosition = pos - seq.previous.size + 1
    seq(pos + 1) == seq(pos) + seq.loop(loopPosition)
  }.holds

  def prevValuesMatchLoop(seq: v1.seq.Seq, pos: BigInt): Boolean = {
    require(pos >= seq.previous.size)
    require(pos > 0)

    val loopPosition = pos - seq.previous.size
    seq(pos - 1) == seq(pos) - seq.loop(loopPosition)
  }.holds

  /**
   * The diff between the seq of in the positions (from and to)
   * of some Seq that have positions bigger than the previous list size
   * is the sum of the loop values for the positions in the interval
   * less the previous list size.
   *
   * assuming (from >= seq.previous.size)
   * assuming (to >= from)
   *
   * cycle(to) - cycle(from) =
   *    cycle.loop(to - cycle.previous.length ) +
   *    cycle.loop(to - cycle.previous.length - 1 ) +
   *    cycle.loop(to - cycle.previous.length - 2 ) +
   *    ... +
   *    cycle.loop(to - cycle.previous.length - from + 1 )
   *
   * @param from BigInt the key of the beginning of the interval
   * @param to BigInt the key of the end of the interval
   * @param seq Seq the seq
   * @return true if the property holds
   */
  def seqPosMatchSeqLoop(from: BigInt, to: BigInt, seq: v1.seq.Seq): Boolean = {
    require(from >= seq.previous.size)
    require(to >= from)
    decreases(to)

    if (from == to) {
      assert(compareTwoSeqPos(from, to, seq) == compareTwoSeqLoop(from, to, seq))
      assert(compareTwoSeqPos(from,  to, seq) == compareTwoSeqLoop(from, to, seq))
      assert(seq(to) - seq(from) == BigInt(0))
    } else {
      val loopPosition = to - seq.previous.size
      val diff = seq.loop(loopPosition)
      assert(seqPosMatchSeqLoop(from, to - 1, seq))
      assert(compareTwoSeqPos(from,   to - 1, seq) == compareTwoSeqLoop(from, to - 1, seq))
      assert(compareTwoSeqPos(from,   to, seq) == diff + compareTwoSeqPos(from,  to - 1, seq))
      assert(compareTwoSeqLoop(from,  to, seq) == diff + compareTwoSeqLoop(from, to - 1, seq))
    }
    assert(compareTwoSeqPos(from, to, seq) == compareTwoSeqLoop(from, to, seq))

    equality(
      compareTwoSeqPos(from, to, seq),
      compareTwoSeqLoop(from, to, seq),
      seq(to) - seq(from),
      sumAllCycleValues(from - seq.previous.size, to - seq.previous.size, seq.loop),
     )

  }.holds

    def compareTwoSeqPos(from: BigInt, to: BigInt, seq: v1.seq.Seq): BigInt = {
    require(from >= seq.previous.size)
    require(to >= from)
    decreases(to)
    if (from == to) {
      BigInt(0)
    } else {
      assert(prevValuesMatchLoop(seq, to))
      val loopPosition = to - seq.previous.size
      assert(seq(to - 1) == seq(to) - seq.loop(loopPosition))
      val diff = seq.loop(loopPosition)
      assert(seq(to - 1) == seq(to) - diff)
      assert(seq(to - 1) + diff == seq(to))
      assert(diff == seq(to) - seq(to - 1))
      seq(to) - seq(to - 1) + compareTwoSeqPos(from, to - 1, seq)
    }
  }

  def compareTwoSeqLoop(from: BigInt, to: BigInt, seq: v1.seq.Seq): BigInt = {
    require(from >= seq.previous.size)
    require(to >= from)
    decreases(to)
    if (from == to) {
      BigInt(0)
    } else {
      val loopPosition = to - seq.previous.size
      val diff = seq.loop(loopPosition)
      diff + compareTwoSeqLoop(from, to - 1, seq)
    }
  }

  def sumAllCycleValues(from: BigInt, to: BigInt, cycle: Cycle): BigInt = {
    require(from >= 0)
    require(to >= 0)
    require(to >= from)
    decreases(to)

    if (from == to) {
      BigInt(0)
    } else {
      cycle(to) + sumAllCycleValues(from, to - 1, cycle)
    }
  }
}