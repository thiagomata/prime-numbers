package v1.div.properties

import org.scalatest.flatspec.FlatSpec
import org.scalatest.matchers.should.Matchers

class AdditionAndMultiplicationTest extends FlatSpec with Matchers {

  "APlusBSameModPlusDiv" should "hold for any values" in {
    assert(AdditionAndMultiplication.APlusBSameModPlusDiv(BigInt(10), BigInt(20)))
    assert(AdditionAndMultiplication.APlusBSameModPlusDiv(BigInt(10), BigInt(2)))
    assert(AdditionAndMultiplication.APlusBSameModPlusDiv(BigInt(10), BigInt(1)))
  }

  "ALessBSameModDecreaseDiv" should "hold for any values" in {
    assert(AdditionAndMultiplication.ALessBSameModDecreaseDiv(BigInt(10), BigInt(20)))
    assert(AdditionAndMultiplication.ALessBSameModDecreaseDiv(BigInt(10), BigInt(-2)))
    assert(AdditionAndMultiplication.ALessBSameModDecreaseDiv(BigInt(-10), BigInt(1)))
  }

  "ATimesBSameMod" should "hold for any values" in {
    assert(AdditionAndMultiplication.ATimesBSameMod(BigInt(10), BigInt(20), BigInt(0)))
    assert(AdditionAndMultiplication.ATimesBSameMod(BigInt(10), BigInt(20), BigInt(1)))
    assert(AdditionAndMultiplication.ATimesBSameMod(BigInt(10), BigInt(2), BigInt(2)))
    assert(AdditionAndMultiplication.ATimesBSameMod(BigInt(10), BigInt(1), BigInt(10)))
    assert(AdditionAndMultiplication.ATimesBSameMod(BigInt(10), BigInt(20), BigInt(-1)))
    assert(AdditionAndMultiplication.ATimesBSameMod(BigInt(10), BigInt(2), BigInt(-2)))
    assert(AdditionAndMultiplication.ATimesBSameMod(BigInt(10), BigInt(1), BigInt(-10)))
  }

  "APlusMultipleTimesBSameMod" should "hold for any values" in {
    assert(AdditionAndMultiplication.APlusMultipleTimesBSameMod(BigInt(10), BigInt(20), BigInt(0)))
    assert(AdditionAndMultiplication.APlusMultipleTimesBSameMod(BigInt(10), BigInt(20), BigInt(1)))
    assert(AdditionAndMultiplication.APlusMultipleTimesBSameMod(BigInt(10), BigInt(2), BigInt(2)))
    assert(AdditionAndMultiplication.APlusMultipleTimesBSameMod(BigInt(10), BigInt(1), BigInt(10)))
  }

  "ALessMultipleTimesBSameMod" should "hold for any values" in {
    assert(AdditionAndMultiplication.ALessMultipleTimesBSameMod(BigInt(10), BigInt(20), BigInt(0)))
    assert(AdditionAndMultiplication.ALessMultipleTimesBSameMod(BigInt(10), BigInt(20), BigInt(1)))
    assert(AdditionAndMultiplication.ALessMultipleTimesBSameMod(BigInt(10), BigInt(2), BigInt(2)))
    assert(AdditionAndMultiplication.ALessMultipleTimesBSameMod(BigInt(10), BigInt(1), BigInt(10)))
  }

  "MoreDivLessMod" should "hold for any values" in {
    assert(AdditionAndMultiplication.MoreDivLessMod(10,2,5,0))
    assert(AdditionAndMultiplication.MoreDivLessMod(11,2,5,1))
    assert(AdditionAndMultiplication.MoreDivLessMod(0,2,0,0))
    assert(AdditionAndMultiplication.MoreDivLessMod(10,1,10,0))
    assert(AdditionAndMultiplication.MoreDivLessMod(11,-2,-5,1))
    assert(AdditionAndMultiplication.MoreDivLessMod(11,-3,5,26))
  }

  "LessDivMoreMod" should "hold for any values" in {
    assert(AdditionAndMultiplication.LessDivMoreMod(10,2,5,0))
    assert(AdditionAndMultiplication.LessDivMoreMod(11,2,5,1))
    assert(AdditionAndMultiplication.LessDivMoreMod(0,2,0,0))
    assert(AdditionAndMultiplication.LessDivMoreMod(10,1,10,0))
    assert(AdditionAndMultiplication.LessDivMoreMod(11,-2,-5,1))
    assert(AdditionAndMultiplication.LessDivMoreMod(11,-3,5,26))
  }

  "MoreDivLessModManyTimes" should "hold for any values" in {
    assert(AdditionAndMultiplication.MoreDivLessModManyTimes(10,2,5,0,1))
    assert(AdditionAndMultiplication.MoreDivLessModManyTimes(10,2,5,0,10))
    assert(AdditionAndMultiplication.MoreDivLessModManyTimes(11,2,5,1,1))
    assert(AdditionAndMultiplication.MoreDivLessModManyTimes(11,2,5,1,10))
    assert(AdditionAndMultiplication.MoreDivLessModManyTimes(0,2,0,0,1))
    assert(AdditionAndMultiplication.MoreDivLessModManyTimes(0,2,0,0,10))
    assert(AdditionAndMultiplication.MoreDivLessModManyTimes(10,1,10,0,1))
    assert(AdditionAndMultiplication.MoreDivLessModManyTimes(10,1,10,0,10))
  }

  "LessDivMoreModManyTimes" should "hold for any values" in {
    assert(AdditionAndMultiplication.LessDivMoreModManyTimes(10,2,5,0,1))
    assert(AdditionAndMultiplication.LessDivMoreModManyTimes(10,2,5,0,10))
    assert(AdditionAndMultiplication.LessDivMoreModManyTimes(11,2,5,1,1))
    assert(AdditionAndMultiplication.LessDivMoreModManyTimes(11,2,5,1,10))
    assert(AdditionAndMultiplication.LessDivMoreModManyTimes(0,2,0,0,1))
    assert(AdditionAndMultiplication.LessDivMoreModManyTimes(0,2,0,0,10))
    assert(AdditionAndMultiplication.LessDivMoreModManyTimes(10,1,10,0,1))
    assert(AdditionAndMultiplication.LessDivMoreModManyTimes(10,1,10,0,10))
  }
}
