package v1.chapter3.list.properties

import stainless.collection.List
import stainless.lang.{decreases, BooleanDecorations}
import v1.chapter1.verification.Helper.assert
import v1.chapter3.list.{ListBoundUtils, ListUtils}

/**
 * Rotation theory for flat `List[BigInt]`.
 *
 * Rotation is a pure cyclic permutation: `rotateAt(list, index) = back ++ front`
 * where `(front, back) = splitAt(list, index)`. No head, no index-0, no cycle
 * concept appears anywhere in this object — rotation treats the list as an
 * unrooted bag of elements that may be re-viewed from any position. Every
 * lemma here states a permutation invariant: same elements, same lower bound,
 * same upper bound, same sum, same size, same product.
 *
 * The head-aware counterpart (a value list whose head changes by `+ apply(0)`)
 * is a distinct operation modeled by `ShiftedList`, deliberately kept separate
 * so the head concept never leaks into rotation.
 */
object RotationProperties {

  /**
   * Append-contains, left side: `(left ++ right).contains(x)` whenever
   * `left.contains(x)`.
   *
   * This is the missing mirror of the (ch6-private) `assertAppendContainsRight`
   * direction. Together the two give bidirectional `++`-contains, which is what
   * makes rotation a same-elements permutation.
   */
  def assertAppendContainsLeft(
    left: List[BigInt],
    right: List[BigInt],
    x: BigInt
  ): Boolean = {
    require(left.contains(x))
    decreases(left.size)
    if (left.isEmpty) {
      (left ++ right).contains(x)
    } else if (left.head == x) {
      (left ++ right).contains(x)
    } else {
      assert(left.tail.contains(x))
      assert(assertAppendContainsLeft(left.tail, right, x))
      (left ++ right).contains(x)
    }
  }.holds

  /**
   * Append-contains, right side: `(left ++ right).contains(x)` whenever
   * `right.contains(x)`. Mirrors the ch6-private lemma, placed here in ch3 so
   * the rotation theory is self-contained at the list layer.
   */
  def assertAppendContainsRight(
    left: List[BigInt],
    right: List[BigInt],
    x: BigInt
  ): Boolean = {
    require(right.contains(x))
    decreases(left.size)
    if (left.isEmpty) {
      (left ++ right).contains(x)
    } else {
      assert(assertAppendContainsRight(left.tail, right, x))
      (left ++ right).contains(x)
    }
  }.holds

  /**
   * Decomposition: if `(left ++ right).contains(x)`, then `x` is in `left` or
   * in `right`. This is the converse of the two append-contains lemmas above
   * and is what the rotation same-elements proof needs to split membership in
   * `front ++ back` into membership in one of the halves.
   *
   * Note: the disjunctive postcondition can be hard for the solver to consume
   * at call sites; prefer `assertAppendContainsSwap` for rotation proofs.
   */
  def assertAppendContainsDecompose(
    left: List[BigInt],
    right: List[BigInt],
    x: BigInt
  ): Boolean = {
    require((left ++ right).contains(x))
    decreases(left.size)
    if (left.isEmpty) {
      right.contains(x)
    } else if (left.head == x) {
      left.contains(x) || right.contains(x)
    } else {
      assert((left.tail ++ right).contains(x))
      assert(assertAppendContainsDecompose(left.tail, right, x))
      left.contains(x) || right.contains(x)
    }
  }.holds

  /**
   * Append order is irrelevant for `contains`: `(left ++ right).contains(x)`
   * iff `(right ++ left).contains(x)`. This is the clean, non-disjunctive fact
   * the rotation same-elements proof needs: `rotateAt(list, index) = back ++ front`
   * contains `x` exactly when `front ++ back = list` does, because append order
   * does not affect membership.
   */
  def assertAppendContainsSwap(
    left: List[BigInt],
    right: List[BigInt],
    x: BigInt
  ): Boolean = {
    decreases(left.size)
    if (left.isEmpty) {
      assert(right.contains(x) == (left ++ right).contains(x))
      (left ++ right).contains(x) == (right ++ left).contains(x)
    } else if (left.head == x) {
      ((left ++ right).contains(x)) == ((right ++ left).contains(x))
    } else {
      assert(assertAppendContainsSwap(left.tail, right, x))
      (left ++ right).contains(x) == (right ++ left).contains(x)
    }
  }.holds

  /**
   * Rotation preserves the element multiset: for any `x`,
   * `rotateAt(list, index).contains(x) == list.contains(x)`.
   *
   * `rotateAt(list, index) = back ++ front` where `(front, back) = splitAt`.
   * Since `list = front ++ back` (keystone recombination) and append order does
   * not affect membership (`assertAppendContainsSwap`), the rotated list and the
   * original contain exactly the same elements.
   *
   * Stated as two directional implications (`...Forward`, `...Backward`) rather
   * than a bare biconditional, because Stainless handles each direction more
   * reliably than the equality (LEARNINGS §1.3).
   */
  def assertRotateContainsForward(
    list: List[BigInt],
    index: BigInt,
    x: BigInt
  ): Boolean = {
    require(index >= 0)
    require(list.contains(x))
    decreases(index)
    if (list.isEmpty || index == BigInt(0)) {
      ListUtils.rotateAt(list, index).contains(x)
    } else if (index >= list.size) {
      assert(assertRotateContainsForward(list, index - list.size, x))
      ListUtils.rotateAt(list, index).contains(x)
    } else {
      val (front, back) = ListUtils.splitAt(list, index)
      assert(ListUtilsProperties.assertSplitAtRecombines(list, index))
      assert(front ++ back == list)
      // `list = front ++ back` contains `x`; swapping append order,
      // `back ++ front = rotateAt(list, index)` contains `x` too.
      assert(assertAppendContainsSwap(front, back, x))
      ListUtils.rotateAt(list, index).contains(x)
    }
  }.holds

  /**
   * Converse direction: `list.contains(x)` whenever
   * `rotateAt(list, index).contains(x)`. Same structure, swapping the roles
   * of `front` and `back` via `assertAppendContainsSwap`.
   */
  def assertRotateContainsBackward(
    list: List[BigInt],
    index: BigInt,
    x: BigInt
  ): Boolean = {
    require(index >= 0)
    require(ListUtils.rotateAt(list, index).contains(x))
    decreases(index)
    if (list.isEmpty || index == BigInt(0)) {
      list.contains(x)
    } else if (index >= list.size) {
      assert(assertRotateContainsBackward(list, index - list.size, x))
      list.contains(x)
    } else {
      val (front, back) = ListUtils.splitAt(list, index)
      assert(ListUtilsProperties.assertSplitAtRecombines(list, index))
      assert(front ++ back == list)
      // `rotateAt = back ++ front` contains `x`; swapping append order,
      // `front ++ back = list` contains `x` too.
      assert(assertAppendContainsSwap(back, front, x))
      list.contains(x)
    }
  }.holds

  /**
   * Rotation preserves size: `rotateAt(list, index).size == list.size`.
   *
   * Follows from `splitAt` recombination (`front ++ back == list`) and the
   * commutativity of addition over the two halves: `back ++ front` and
   * `front ++ back` have the same total size because each half's size is
   * unchanged and addition commutes.
   */
  def assertRotateSameSize(
    list: List[BigInt],
    index: BigInt
  ): Boolean = {
    require(index >= 0)
    decreases(index)
    if (list.isEmpty || index == BigInt(0)) {
      ListUtils.rotateAt(list, index).size == list.size
    } else if (index >= list.size) {
      assert(assertRotateSameSize(list, index - list.size))
      ListUtils.rotateAt(list, index).size == list.size
    } else {
      val (front, back) = ListUtils.splitAt(list, index)
      assert(ListUtilsProperties.assertSplitAtRecombines(list, index))
      assert(front ++ back == list)
      ListUtils.rotateAt(list, index).size == list.size
    }
  }.holds

  /**
   * Rotation preserves the sum: `sum(rotateAt(list, index)) == sum(list)`.
   *
   * `rotateAt = back ++ front`, and `list = front ++ back`. Sum over `++` is
   * additive and commutative (`ListUtils.listCombine` + `listSwap`), so the
   * two orders give the same total.
   */
  def assertRotateSameSum(
    list: List[BigInt],
    index: BigInt
  ): Boolean = {
    require(index >= 0)
    decreases(index)
    if (list.isEmpty || index == BigInt(0)) {
      ListUtils.sum(ListUtils.rotateAt(list, index)) == ListUtils.sum(list)
    } else if (index >= list.size) {
      assert(assertRotateSameSum(list, index - list.size))
      ListUtils.sum(ListUtils.rotateAt(list, index)) == ListUtils.sum(list)
    } else {
      val (front, back) = ListUtils.splitAt(list, index)
      assert(ListUtilsProperties.assertSplitAtRecombines(list, index))
      assert(front ++ back == list)
      // Explicit substitution chain: rotateAt = back ++ front, list = front ++ back.
      // sum is additive over ++ (listCombine) and commutative across ++ (listSwap),
      // so both orders share the same total.
      assert(ListUtils.listCombine(back, front))
      assert(ListUtils.sum(back ++ front) == ListUtils.sum(back) + ListUtils.sum(front))
      assert(ListUtils.listCombine(front, back))
      assert(ListUtils.sum(front ++ back) == ListUtils.sum(front) + ListUtils.sum(back))
      ListUtils.sum(ListUtils.rotateAt(list, index)) == ListUtils.sum(list)
    }
  }.holds

  /**
   * Rotation preserves the strict lower bound:
   * `allGreaterThan(list, value)` ⟹ `allGreaterThan(rotateAt(list, index), value)`.
   *
   * Already proven (mirrored from the ch6 lemma); restated here in ch3 next to
   * the other rotation invariants so the permutation theory is self-contained.
   */
  def assertRotateSameLowerBound(
    list: List[BigInt],
    index: BigInt,
    value: BigInt
  ): Boolean = {
    require(index >= 0)
    require(ListBoundUtils.allGreaterThan(list, value))
    decreases(index)
    if (list.isEmpty || index == BigInt(0)) {
      ListBoundUtils.allGreaterThan(ListUtils.rotateAt(list, index), value)
    } else if (index >= list.size) {
      assert(assertRotateSameLowerBound(list, index - list.size, value))
      ListBoundUtils.allGreaterThan(ListUtils.rotateAt(list, index), value)
    } else {
      val (front, back) = ListUtils.splitAt(list, index)
      assert(ListUtilsProperties.assertSplitAtRecombines(list, index))
      assert(front ++ back == list)
      assert(ListBoundUtils.assertSplitAtPreservesAllGreaterThan(list, index, value))
      assert(ListBoundUtils.allGreaterThan(front, value))
      assert(ListBoundUtils.allGreaterThan(back, value))
      assert(ListBoundUtils.assertAppendGreaterThan(back, front, value))
      ListBoundUtils.allGreaterThan(ListUtils.rotateAt(list, index), value)
    }
  }.holds

  /**
   * Rotation preserves the strict upper bound:
   * `allLessThan(list, bound)` ⟹ `allLessThan(rotateAt(list, index), bound)`.
   *
   * Mirror of `assertRotateSameLowerBound` using `assertAppendLessThan`.
   * Requires the (forthcoming) `assertSplitAtPreservesAllLessThan`; until then
   * it is left as a stated-but-not-yet-verified companion.
   */
  def assertRotateSameUpperBound(
    list: List[BigInt],
    index: BigInt,
    bound: BigInt
  ): Boolean = {
    require(index >= 0)
    require(ListBoundUtils.allLessThan(list, bound))
    decreases(index)
    if (list.isEmpty || index == BigInt(0)) {
      ListBoundUtils.allLessThan(ListUtils.rotateAt(list, index), bound)
    } else if (index >= list.size) {
      assert(assertRotateSameUpperBound(list, index - list.size, bound))
      ListBoundUtils.allLessThan(ListUtils.rotateAt(list, index), bound)
    } else {
      val (front, back) = ListUtils.splitAt(list, index)
      assert(ListUtilsProperties.assertSplitAtRecombines(list, index))
      assert(front ++ back == list)
      assert(ListBoundUtils.assertSplitAtPreservesAllLessThan(list, index, bound))
      assert(ListBoundUtils.allLessThan(front, bound))
      assert(ListBoundUtils.allLessThan(back, bound))
      assert(ListBoundUtils.assertAppendLessThan(back, front, bound))
      ListBoundUtils.allLessThan(ListUtils.rotateAt(list, index), bound)
    }
  }.holds

  /**
   * Rotation-by-one index access: for `k + 1 < size`,
   * `rotateAt(list, 1)(k) == list(k + 1)`.
   *
   * Because `rotateAt(list, 1) = back ++ front` where
   * `(front, back) = splitAt(list, 1)`, `back == list.tail`, and
   * `front == List(list.head)`. For `k < back.size`, the element at
   * index `k` comes from `back`, which is `list.tail`, giving `list(k + 1)`.
   */
  def assertRotatedAtIndexPlusOne(
    list: List[BigInt],
    k: BigInt
  ): Boolean = {
    require(list.nonEmpty)
    require(k >= 0)
    require(k + 1 < list.size)
    decreases(k)

    val (front, back) = ListUtils.splitAt(list, BigInt(1))
    val rotated = back ++ front

    assert(ListUtilsProperties.assertSplitAtRecombines(list, BigInt(1)))
    assert(front ++ back == list)

    assert(ListUtilsProperties.assertSplitAtOne(list))
    assert(front == List(list.head))
    assert(back == list.tail)

    if (k == BigInt(0)) {
      rotated.apply(k) == list.apply(k + 1)
    } else {
      assert(k < back.size)
      assert(ListUtilsProperties.assertAppendApplyLeft(back, front, k))
      assert(rotated.apply(k) == back.apply(k))
      assert(ListUtilsProperties.accessTailShiftRight(list, k))
      assert(list.tail(k) == list(k + 1))
      rotated.apply(k) == list.apply(k + 1)
    }
  }.holds
}
