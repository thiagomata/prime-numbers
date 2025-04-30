package v1.seq.properties

import org.scalatest.flatspec.FlatSpec
import org.scalatest.matchers.should.Matchers
import v1.cycle.Cycle
import v1.seq.Seq
import v1.tests.ArrayUtils.createList

class SeqPropertiesTest extends FlatSpec with Matchers {

  val testSequences: List[Seq] = List.apply(
    Seq(
      previous=createList(Array(BigInt(0),BigInt(1),BigInt(2))),
      loop=Cycle(createList(Array(BigInt(1)))),
    ),
    Seq(
      previous=createList(Array(BigInt(10),BigInt(20))),
      loop=Cycle(createList(Array(BigInt(100),BigInt(1000)))),
      ),
    Seq(
      previous=createList(Array(BigInt(1))),
      loop=Cycle(createList(Array(BigInt(2)))),
    ),
    Seq(
      previous=createList(Array(BigInt(1))),
      loop=Cycle(createList(Array(BigInt(0)))),
    ),
    Seq(
      previous=createList(Array(BigInt(0))),
      loop=Cycle(createList(Array(BigInt(0)))),
    ),
    Seq(
      previous=createList(Array(BigInt(1))),
      loop=Cycle(createList(Array(BigInt(1)))),
    ),
    Seq(
      stainless.collection.List.apply[BigInt](),
      loop=Cycle(createList(Array(BigInt(1)))),
    ),
  )

  "Seq.first values match previous" should "match" in {
    assert(testSequences.forall(
      testSeq => {
        val values = 0 until testSeq.previous.size.toInt
        values.forall( v => SeqProperties.firstValuesMatchPrev(testSeq, v) )
      })
    )
  }

  "first Values Match First Pos In Loop" should "match" in {
    assert(testSequences.forall(
      testSeq => {
        val prevSize = testSeq.previous.size
        SeqProperties.firstValuesMatchFirstPosInLoop(testSeq, prevSize)
      })
    )
  }

  "prev value in the loop" should "match" in {
    assert(testSequences.forall(
      testSeq => {
        val prevSize = testSeq.previous.size
        val bottomTest = if (prevSize == 0) then BigInt(1) else prevSize
        val upperTest = testSeq.loop.size * 2
        val range = bottomTest to (upperTest + bottomTest)
        range.forall(
          value => {
            SeqProperties.prevValuesMatchLoop(testSeq, value)
          }
        )
      })
    )
  }

  "next value in the loop" should "match" in {
    assert(testSequences.forall(
      testSeq => {
        val prevSize = testSeq.previous.size
        val bottomTest = if (prevSize == 0) then BigInt(1) else prevSize
        val upperTest = testSeq.loop.size * 2
        val range = bottomTest to (upperTest + bottomTest)
        range.forall(
          value => {
            SeqProperties.nextValuesMatchLoop(testSeq, value)
          }
        )
      })
    )
  }

  "seqPosMatchSeqLoop" should "hold" in {
    assert(testSequences.forall(
      testSeq => {
        SeqProperties.seqPosMatchSeqLoop(
          testSeq.previous.size,
          testSeq.previous.size + testSeq.loop.size,
          testSeq
        )
      })
    )
  }
}
