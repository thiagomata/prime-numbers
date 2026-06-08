package v1.cycle.gap

import org.scalatest.flatspec.*
import org.scalatest.matchers.should.*
import stainless.collection.List

class GapCycleTest extends FlatSpec with Matchers {

  "GapCycle" should "construct from a single positive value" in {
    val gc = GapCycle.apply(List(BigInt(2)))
    gc.size should be(BigInt(1))
    gc.sum should be(BigInt(2))
  }

  it should "access gap at position 0" in {
    val gc = GapCycle.apply(List(BigInt(2)))
    gc.gap(0) should be(BigInt(2))
  }

  it should "access cumulative sum at position 0" in {
    val gc = GapCycle.apply(List(BigInt(2)))
    gc.cumulativeSum(0) should be(BigInt(2))
  }

  it should "wrap around for positions beyond size" in {
    val gc = GapCycle.apply(List(BigInt(4), BigInt(2)))
    gc.gap(0) should be(BigInt(4))
    gc.gap(1) should be(BigInt(2))
    gc.gap(2) should be(BigInt(4))
    gc.gap(3) should be(BigInt(2))
  }

  it should "compute cumulative sum for S_2 gaps" in {
    val gc = GapCycle.apply(List(BigInt(4), BigInt(2)))
    gc.cumulativeSum(0) should be(BigInt(4))
    gc.cumulativeSum(1) should be(BigInt(6))
    gc.cumulativeSum(2) should be(BigInt(10))
    gc.cumulativeSum(3) should be(BigInt(12))
  }

  it should "compute sum for S_2 gaps" in {
    val gc = GapCycle.apply(List(BigInt(4), BigInt(2)))
    gc.sum should be(BigInt(6))
  }

  it should "handle S_3 gaps" in {
    val gaps = List(BigInt(6), BigInt(4), BigInt(2), BigInt(4), BigInt(2), BigInt(4), BigInt(6), BigInt(2))
    val gc = GapCycle.apply(gaps)
    gc.size should be(BigInt(8))
    gc.sum should be(BigInt(30))
    gc.cumulativeSum(0) should be(BigInt(6))
    gc.cumulativeSum(7) should be(BigInt(30))
  }
}
