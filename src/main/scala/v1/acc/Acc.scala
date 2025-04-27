package v1.acc

import stainless.collection.List
import stainless.lang.decreases
import stainless.lang.*
import stainless.proof.check

case class Acc(list: List[BigInt], init: BigInt = 0) {

  def apply(position: BigInt): BigInt = {
    require(list.nonEmpty)
    require(position >= 0)
    require(position < list.size)
    if ( position == 0 ) {
      this.head
    } else {
      Acc(list.tail, this.head).apply(position - 1)
    }
  }

  def acc: List[BigInt] = {
    decreases(list.size)
    if (list.isEmpty) {
      list
    } else {
      List(this.head) ++ Acc(list.tail, this.head).acc
    }
  }

  def last: BigInt = {
    require(list.nonEmpty)
    acc.last
  }

  def head: BigInt = {
    require(list.nonEmpty)
    list.head + init
  }

  def tail: List[BigInt] = {
    require(list.nonEmpty)
    Acc(list.tail, this.head).acc
  }

  def isEmpty: Boolean = list.isEmpty

  def nonEmpty: Boolean = list.nonEmpty

  def size: BigInt = list.size

  def accDifferenceEqualsTailHead: Boolean = {
    require(list.size > 1)
    check(tail.head == Acc(list.tail, this.head).head)
    check(tail.head == list.tail.head + this.head)
    check(this.tail.head - this.head ==  list.tail.head + this.head - this.head)
    check(acc(1) == this.tail.head)
    check(apply(1) == this.tail.head)
    check(acc(0) == this.head)
    check(apply(1) == this.tail.head)
    check(list(1) == list.tail.head)

    check(apply(0)  == acc(0))
    check(apply(1)  == acc(1))

    apply(1) - apply(0) == list(1) &&
      acc(1) - acc(0)   == list(1)
  }.holds

  /**
   * Lemma: The difference between two consecutive accumulated values in Acc
   * equals the corresponding value from the original list.
   *
   * That is:
   * acc(position + 1) - acc(position) == list(position + 1)
   *
   * Holds for all valid `position` where 0 <= position < list.size - 1.
   */
  def accDiffMatchesList(position: BigInt): Boolean = {
    require(list.size > 1)
    require(position >= 0 && position < list.size - 1)
    decreases(position)

    if (position == 0) {
      // Base case
      check(accDifferenceEqualsTailHead)
      check(apply(0) == acc(0))
      check(apply(1) == acc(1))
      check(
        acc(position + 1) - acc(position) == list(position + 1) &&
        acc(position) == apply(position)
      )
    } else {
      check(position > 0 )
      check(position < list.size - 1)
      check(position - 1 < list.size )

      // Inductive step
      val next = Acc(list.tail, this.head)
      check(next.size == this.size - 1)
      check(this.tail == next.acc)
      check(next.accDiffMatchesList(position - 1))

      // link this values and next values
      check(apply(position)     == next.apply(position - 1))
      check(apply(position + 1) == next.apply(position))

      check(apply(position) == acc(position))
      check(apply(position + 1) == acc(position + 1))
    }
    acc(position + 1) - acc(position) == list(position + 1) &&
      acc(position + 1) == apply(position + 1) &&
      acc(position) == apply(position)
  }.holds

  /**
   * Lemma: The `apply(position)` method returns the same value as the value at
   * index `position` in the accumulated list `acc`.
   *
   * That is:
   * apply(position) == acc(position)
   *
   * Holds for all valid `position` in the bounds of the list.
   */
  def accApplyConsistent(position: BigInt): Boolean = {
    require(list.nonEmpty)
    require(position >= 0 && position < list.size)
    decreases(position)

    if (position == 0) {
      // Base case: directly compare head
      check(apply(0) == head)
      check(acc(0) == head)
//      check(list.size == acc.size)
      acc(position) == apply(position)
    } else {
      check(position > 0 )
      check(position < list.size)
      check(position - 1 < list.size - 1)

      val next = Acc(list.tail, this.head)
      check(next.size == this.size - 1)
      check(this.tail == next.acc)

      check(apply(position) == next.apply(position - 1))
        check(acc == List(this.head) ++ next.acc)
      val accList = List(this.head) ++ next.acc
//      val accTail = accList.tail
//      check(acc == accList)
//      check(accTail == next.acc)
//      check(accList(position) == accTail(position - 1))
//      check(acc(position)   == acc.tail(position - 1))
//      check(acc(position)   == next.acc(position - 1))
//      check(next.accApplyConsistent(position - 1))
//      check(next.acc(position - 1) == next.apply(position - 1))
//      check(acc(position) == apply(position))
    }
    true
//    acc(position) == apply(position)
  }.holds

}