package verification

import org.scalatest.flatspec.FlatSpec
import org.scalatest.matchers.should.Matchers

class HelperTest extends FlatSpec with Matchers {

  "equality with two terms" should "be true only with equal values" in {
    Helper.equality(1, 1) should be(true)
    Helper.equality(2, 2) should be(true)
    Helper.equality(1, 2) should be(false)
    Helper.equality(2, 1) should be(false)
    Helper.equality(1, 2) should be(false)
  }

  "equality with three terms" should "be true only with equal values" in {
    Helper.equality(1, 1, 1) should be(true)
    Helper.equality(2, 2, 2) should be(true)
    Helper.equality(2, 1, 1) should be(false)
    Helper.equality(1, 2, 1) should be(false)
    Helper.equality(1, 1, 2) should be(false)
    Helper.equality(1, 2, 3) should be(false)
  }

  "equality with four terms" should "be true only with equal values" in {
    Helper.equality(1, 1, 1, 1) should be(true)
    Helper.equality(2, 2, 2, 2) should be(true)
    Helper.equality(2, 1, 1, 1) should be(false)
    Helper.equality(1, 2, 1, 1) should be(false)
    Helper.equality(1, 1, 2, 1) should be(false)
    Helper.equality(1, 1, 1, 2) should be(false)
    Helper.equality(1, 2, 3, 4) should be(false)
  }

  "equality with five terms" should "be true only with equal values" in {
    Helper.equality(1, 1, 1, 1, 1) should be(true)
    Helper.equality(2, 2, 2, 2, 2) should be(true)
    Helper.equality(2, 1, 1, 1, 1) should be(false)
    Helper.equality(1, 2, 1, 1, 1) should be(false)
    Helper.equality(1, 1, 2, 1, 1) should be(false)
    Helper.equality(1, 1, 1, 2, 1) should be(false)
    Helper.equality(1, 1, 1, 1, 2) should be(false)
    Helper.equality(1, 2, 3, 4, 5) should be(false)
  }

  "equality with six terms" should "be true only with equal values" in {
    Helper.equality(1, 1, 1, 1, 1, 1) should be(true)
    Helper.equality(2, 2, 2, 2, 2, 2) should be(true)
    Helper.equality(2, 1, 1, 1, 1, 1) should be(false)
    Helper.equality(1, 2, 1, 1, 1, 1) should be(false)
    Helper.equality(1, 1, 2, 1, 1, 1) should be(false)
    Helper.equality(1, 1, 1, 2, 1, 1) should be(false)
    Helper.equality(1, 1, 1, 1, 2, 1) should be(false)
    Helper.equality(1, 1, 1, 1, 1, 2) should be(false)
    Helper.equality(1, 2, 3, 4, 5, 6) should be(false)
  }

  "equality with seven terms" should "be true only with equal values" in {
    Helper.equality(1, 1, 1, 1, 1, 1, 1) should be(true)
    Helper.equality(2, 2, 2, 2, 2, 2, 2) should be(true)
    Helper.equality(2, 1, 1, 1, 1, 1, 1) should be(false)
    Helper.equality(1, 2, 1, 1, 1, 1, 1) should be(false)
    Helper.equality(1, 1, 2, 1, 1, 1, 1) should be(false)
    Helper.equality(1, 1, 1, 2, 1, 1, 1) should be(false)
    Helper.equality(1, 1, 1, 1, 2, 1, 1) should be(false)
    Helper.equality(1, 1, 1, 1, 1, 2, 1) should be(false)
    Helper.equality(1, 1, 1, 1, 1, 1, 2) should be(false)
    Helper.equality(1, 2, 3, 4, 5, 6, 7) should be(false)
  }

  "equality with eight terms" should "be true only with equal values" in {
    Helper.equality(1, 1, 1, 1, 1, 1, 1, 1) should be(true)
    Helper.equality(2, 2, 2, 2, 2, 2, 2, 2) should be(true)
    Helper.equality(2, 1, 1, 1, 1, 1, 1, 1) should be(false)
    Helper.equality(1, 2, 1, 1, 1, 1, 1, 1) should be(false)
    Helper.equality(1, 1, 2, 1, 1, 1, 1, 1) should be(false)
    Helper.equality(1, 1, 1, 2, 1, 1, 1, 1) should be(false)
    Helper.equality(1, 1, 1, 1, 2, 1, 1, 1) should be(false)
    Helper.equality(1, 1, 1, 1, 1, 2, 1, 1) should be(false)
    Helper.equality(1, 1, 1, 1, 1, 1, 2, 1) should be(false)
    Helper.equality(1, 1, 1, 1, 1, 1, 1, 2) should be(false)
    Helper.equality(1, 2, 3, 4, 5, 6, 7, 8) should be(false)
  }

  "equality with nine terms" should "be true only with equal values" in {
    Helper.equality(1, 1, 1, 1, 1, 1, 1, 1, 1) should be(true)
    Helper.equality(2, 2, 2, 2, 2, 2, 2, 2, 2) should be(true)
    Helper.equality(2, 1, 1, 1, 1, 1, 1, 1, 1) should be(false)
    Helper.equality(1, 2, 1, 1, 1, 1, 1, 1, 1) should be(false)
    Helper.equality(1, 1, 2, 1, 1, 1, 1, 1, 1) should be(false)
    Helper.equality(1, 1, 1, 2, 1, 1, 1, 1, 1) should be(false)
    Helper.equality(1, 1, 1, 1, 2, 1, 1, 1, 1) should be(false)
    Helper.equality(1, 1, 1, 1, 1, 2, 1, 1, 1) should be(false)
    Helper.equality(1, 1, 1, 1, 1, 1, 2, 1, 1) should be(false)
    Helper.equality(1, 1, 1, 1, 1, 1, 1, 2, 1) should be(false)
    Helper.equality(1, 1, 1, 1, 1, 1, 1, 1, 2) should be(false)
    Helper.equality(1, 2, 3, 4, 5, 6, 7, 8, 9) should be(false)
  }
}
