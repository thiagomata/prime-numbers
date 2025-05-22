package v1.list.integral

import stainless.collection.List
import stainless.lang.*

case class Integral(list: List[BigInt], init: BigInt = 0) {

  /**
   * The integral of the list is defined as
   *    - the first element is the first element of the list plus the initial value
   *    - the rest of the elements are the sum of the previous element and the current element
   *
   * in other words:
   *
   * apply(0) = list(0) + init
   * apply(n) = apply(n - 1) + list(n)
   *
   * @param position BigInt the position of the element in the list
   * @return BigInt the element at the given position
   */
  def apply(position: BigInt): BigInt = {
    require(list.nonEmpty)
    require(position >= 0 && position < list.size)
    if ( position == 0 ) this.head else Integral(list.tail, this.head).apply(position - 1)
  }

  /**
   * The accumulated list is defined as
   *    - the first element is the first element of the list plus the initial value
   *    - the rest of the elements are the sum of the previous element and the current element
   *
   * in other words:
   *
   * acc(0) = list(0) + init
   * acc(n) = acc(n - 1) + list(n)
   *
   * @return List[BigInt] the accumulated list
   */
  def acc: List[BigInt] = {
    decreases(list.size)
    if (list.isEmpty) list else List(this.head) ++ Integral(list.tail, this.head).acc
  }

  /**
   * The last element of the accumulated list is defined as
   * the sum of all elements in the list plus the initial value
   *
   * in other words:
   *
   * last = init + sum(list)
   *
   * @return BigInt the last element of the accumulated list
   */
  def last: BigInt = {
    require(list.nonEmpty)
    acc.last
  }

  /**
   * The first element of the accumulated list is defined as
   * the first element of the list plus the initial value
   *
   * in other words:
   *
   * head = list(0) + init
   *
   * @return BigInt the first element of the accumulated list
   */
  def head: BigInt = {
    require(list.nonEmpty)
    list.head + init
  }

  /**
   * The tail of the accumulated list is defined as
   * the accumulated list without the first element
   *
   * in other words:
   *
   * tail = acc.tail
   *
   * @return List[BigInt] the tail of the accumulated list
   */
  def tail: List[BigInt] = {
    require(list.nonEmpty)
    Integral(list.tail, this.head).acc
  }

  /**
   * is empty returns true if the list is empty
   */
  def isEmpty: Boolean = list.isEmpty

  /**
   * non empty returns true if the list is not empty
   */
  def nonEmpty: Boolean = list.nonEmpty

  /**
   * size returns the size of the list
   */
  def size: BigInt = list.size
}