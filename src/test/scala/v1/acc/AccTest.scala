package v1.acc

import org.scalatest.flatspec.*
import org.scalatest.matchers.should.*
import v1.tests.ArrayUtils.{createList, createListFromInt}

import scala.BigInt

class AccTest extends FlatSpec with Matchers {

  "Acc" should "holds for any list" in {
    val list = createListFromInt(Array(1, 10, 100))
    val acc = Acc(list)
    assert(acc.acc == createListFromInt(Array(1, 11, 111)))
    assert(acc(0) == 1)
    assert(acc(1) == 11)
    assert(acc(2) == 111)

    val list2 = createListFromInt(Array(1, 20, 300))
    val acc2 = Acc(list2)
    assert(Acc(list2).acc == createListFromInt(Array(1, 21, 321)))
    assert(acc2(0) == 1)
    assert(acc2(1) == 21)
    assert(acc2(2) == 321)
  }

}