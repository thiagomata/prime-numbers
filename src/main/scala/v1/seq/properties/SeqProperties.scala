package v1.seq.properties

import v1.Calc
import stainless.lang.{BigInt, *}
import stainless.proof.check

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

    seq(pos + 1) == seq(pos) + seq.loop(Calc.mod(loopPosition, seq.loop.size))
  }.holds

  def prevValuesMatchLoop(seq: v1.seq.Seq, pos: BigInt): Boolean = {
    require(pos >= seq.previous.size)
    require(pos > 0)
    val loopPosition = pos - seq.previous.size
    seq(pos - 1) == seq(pos) - seq.loop(Calc.mod(loopPosition, seq.loop.size))
  }.holds

  def sumValuesMatchLoop(seq: v1.seq.Seq, pos: BigInt): Boolean = {
    require(pos >= seq.previous.size)
    val loopPosition = pos - seq.previous.size + 1
    seq(pos + 1) == seq(pos) + seq.loop(Calc.mod(loopPosition, seq.loop.size))
  }.holds

  def sumAllLoopValues(seq: v1.seq.Seq): BigInt = {
    sumAllListValues(0, seq.loop.size - 1, seq.loop)
  }

  def seqPosMatchSeqLoop(from: BigInt, to: BigInt, seq: v1.seq.Seq): Boolean = {
    require(from >= seq.previous.size)
    require(to >= from)
    decreases(to)
    if (from == to) {
      assert(compareTwoSeqPos(from, to, seq) == compareTwoSeqLoop(from, to, seq))
      check(compareTwoSeqPos(from,  to, seq) == compareTwoSeqLoop(from, to, seq))
    } else {
      val loopPosition = to - seq.previous.size
      val diff = seq.loop(Calc.mod(loopPosition, seq.loop.size))
      check(seqPosMatchSeqLoop(from, to - 1, seq))
      check(compareTwoSeqPos(from,   to - 1, seq) == compareTwoSeqLoop(from, to - 1, seq))
      check(compareTwoSeqPos(from,   to, seq) == diff + compareTwoSeqPos(from,  to - 1, seq))
      check(compareTwoSeqLoop(from,  to, seq) == diff + compareTwoSeqLoop(from, to - 1, seq))
    }
    compareTwoSeqPos(from, to, seq) == compareTwoSeqLoop(from, to, seq)
  }.holds

    def compareTwoSeqPos(from: BigInt, to: BigInt, seq: v1.seq.Seq): BigInt = {
    require(from >= seq.previous.size)
    require(to >= from)
    decreases(to)
    if (from == to) {
      BigInt(0)
    } else {
      check(prevValuesMatchLoop(seq, to))
      val loopPosition = to - seq.previous.size
      check(seq(to - 1) == seq(to) - seq.loop(Calc.mod(loopPosition, seq.loop.size)))
      val diff = seq.loop(Calc.mod(loopPosition, seq.loop.size))
      check(seq(to - 1) == seq(to) - diff)
      check(seq(to - 1) + diff == seq(to))
      diff + compareTwoSeqPos(from, to - 1, seq)
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
      val diff = seq.loop(Calc.mod(loopPosition, seq.loop.size))
      diff + compareTwoSeqLoop(from, to - 1, seq)
    }
  }

  def sumAllListValues(from: BigInt, to: BigInt, list: stainless.collection.List[BigInt]): BigInt = {
    require(from >= 0)
    require(to >= 0)
    require(to >= from)
    require(to < list.size)
    decreases(to)
    if (from == to) {
      list.apply(to)
    } else {
      list.apply(to) + sumAllListValues(from, to - 1, list)
    }
  }

//  def addAllLoopValuesp(seq: v1.seq.Seq, pos: BigInt): Boolean = {
//    require(pos >= (seq.previous.size + seq.loop.size))
//    (BigInt(0) to seq.loop.size).forall(
//      prev => {
//        val futureValue = seq.previous.size + seq.loop.size - prev
//        AdditionAndMultiplication.APlusMultipleTimesBSameMod(a=)
//        prevValuesMatchLoop(seq, )
//      }
//    )
//  }
}