package v1.seq.properties

import v1.Calc

object SeqProperties {
  def firstValuesMatchPrev(seq: v1.seq.Seq, pos: BigInt): Boolean = {
    require(pos >= 0)
    require(seq.previous.size > pos)
    seq.previous(pos) == seq(pos)
  }

  def firstValuesMatchFirstPosInLoop(seq: v1.seq.Seq, pos: BigInt): Boolean = {
    require(pos == seq.previous.size)
    if (seq.previous.isEmpty) {
      seq(pos) == seq.loop(0)
    } else {
      seq(pos) == seq.previous(seq.previous.size - 1) + seq.loop(0)
    }
  }

  def nextValuesMatchLoop(seq: v1.seq.Seq, pos: BigInt): Boolean = {
    require(pos >= seq.previous.size)
    val loopPosition = pos - seq.previous.size + 1
    seq(pos + 1) == seq(pos) + seq.loop(Calc.mod(loopPosition, seq.loop.size))
  }

  def prevValuesMatchLoop(seq: v1.seq.Seq, pos: BigInt): Boolean = {
    require(pos >= seq.previous.size)
    require(pos > 0)
    val loopPosition = pos - seq.previous.size
    seq(pos - 1) == seq(pos) - seq.loop(Calc.mod(loopPosition, seq.loop.size))
  }
}