package verification

import org.scalatest.flatspec.FlatSpec
import org.scalatest.matchers.should.Matchers

class HelperTest extends FlatSpec with Matchers {

  "equals with two terms" should "be true only with equals values" in {
    Helper.equals(1, 1) should be(true)
    Helper.equals(2, 2) should be(true)
    Helper.equals(1, 2) should be(false)
    Helper.equals(2, 1) should be(false)
    Helper.equals(1, 2) should be(false)
  }

  "equals with three terms" should "be true only with equals values" in {
    Helper.equals(1, 1, 1) should be(true)
    Helper.equals(2, 2, 2) should be(true)
    Helper.equals(2, 1, 1) should be(false)
    Helper.equals(1, 2, 1) should be(false)
    Helper.equals(1, 1, 2) should be(false)
    Helper.equals(1, 2, 3) should be(false)
  }

  "equals with four terms" should "be true only with equals values" in {
    Helper.equals(1, 1, 1, 1) should be(true)
    Helper.equals(2, 2, 2, 2) should be(true)
    Helper.equals(2, 1, 1, 1) should be(false)
    Helper.equals(1, 2, 1, 1) should be(false)
    Helper.equals(1, 1, 2, 1) should be(false)
    Helper.equals(1, 1, 1, 2) should be(false)
    Helper.equals(1, 2, 3, 4) should be(false)
  }

  "equals with five terms" should "be true only with equals values" in {
    Helper.equals(1, 1, 1, 1, 1) should be(true)
    Helper.equals(2, 2, 2, 2, 2) should be(true)
    Helper.equals(2, 1, 1, 1, 1) should be(false)
    Helper.equals(1, 2, 1, 1, 1) should be(false)
    Helper.equals(1, 1, 2, 1, 1) should be(false)
    Helper.equals(1, 1, 1, 2, 1) should be(false)
    Helper.equals(1, 1, 1, 1, 2) should be(false)
    Helper.equals(1, 2, 3, 4, 5) should be(false)
  }

  "equals with six terms" should "be true only with equals values" in {
    Helper.equals(1, 1, 1, 1, 1, 1) should be(true)
    Helper.equals(2, 2, 2, 2, 2, 2) should be(true)
    Helper.equals(2, 1, 1, 1, 1, 1) should be(false)
    Helper.equals(1, 2, 1, 1, 1, 1) should be(false)
    Helper.equals(1, 1, 2, 1, 1, 1) should be(false)
    Helper.equals(1, 1, 1, 2, 1, 1) should be(false)
    Helper.equals(1, 1, 1, 1, 2, 1) should be(false)
    Helper.equals(1, 1, 1, 1, 1, 2) should be(false)
    Helper.equals(1, 2, 3, 4, 5, 6) should be(false)
  }

  "equals with seven terms" should "be true only with equals values" in {
    Helper.equals(1, 1, 1, 1, 1, 1, 1) should be(true)
    Helper.equals(2, 2, 2, 2, 2, 2, 2) should be(true)
    Helper.equals(2, 1, 1, 1, 1, 1, 1) should be(false)
    Helper.equals(1, 2, 1, 1, 1, 1, 1) should be(false)
    Helper.equals(1, 1, 2, 1, 1, 1, 1) should be(false)
    Helper.equals(1, 1, 1, 2, 1, 1, 1) should be(false)
    Helper.equals(1, 1, 1, 1, 2, 1, 1) should be(false)
    Helper.equals(1, 1, 1, 1, 1, 2, 1) should be(false)
    Helper.equals(1, 1, 1, 1, 1, 1, 2) should be(false)
    Helper.equals(1, 2, 3, 4, 5, 6, 7) should be(false)
  }

  "equals with eight terms" should "be true only with equals values" in {
    Helper.equals(1, 1, 1, 1, 1, 1, 1, 1) should be(true)
    Helper.equals(2, 2, 2, 2, 2, 2, 2, 2) should be(true)
    Helper.equals(2, 1, 1, 1, 1, 1, 1, 1) should be(false)
    Helper.equals(1, 2, 1, 1, 1, 1, 1, 1) should be(false)
    Helper.equals(1, 1, 2, 1, 1, 1, 1, 1) should be(false)
    Helper.equals(1, 1, 1, 2, 1, 1, 1, 1) should be(false)
    Helper.equals(1, 1, 1, 1, 2, 1, 1, 1) should be(false)
    Helper.equals(1, 1, 1, 1, 1, 2, 1, 1) should be(false)
    Helper.equals(1, 1, 1, 1, 1, 1, 2, 1) should be(false)
    Helper.equals(1, 1, 1, 1, 1, 1, 1, 2) should be(false)
    Helper.equals(1, 2, 3, 4, 5, 6, 7, 8) should be(false)
  }

  "equals with nine terms" should "be true only with equals values" in {
    Helper.equals(1, 1, 1, 1, 1, 1, 1, 1, 1) should be(true)
    Helper.equals(2, 2, 2, 2, 2, 2, 2, 2, 2) should be(true)
    Helper.equals(2, 1, 1, 1, 1, 1, 1, 1, 1) should be(false)
    Helper.equals(1, 2, 1, 1, 1, 1, 1, 1, 1) should be(false)
    Helper.equals(1, 1, 2, 1, 1, 1, 1, 1, 1) should be(false)
    Helper.equals(1, 1, 1, 2, 1, 1, 1, 1, 1) should be(false)
    Helper.equals(1, 1, 1, 1, 2, 1, 1, 1, 1) should be(false)
    Helper.equals(1, 1, 1, 1, 1, 2, 1, 1, 1) should be(false)
    Helper.equals(1, 1, 1, 1, 1, 1, 2, 1, 1) should be(false)
    Helper.equals(1, 1, 1, 1, 1, 1, 1, 2, 1) should be(false)
    Helper.equals(1, 1, 1, 1, 1, 1, 1, 1, 2) should be(false)
    Helper.equals(1, 2, 3, 4, 5, 6, 7, 8, 9) should be(false)
  }
}
