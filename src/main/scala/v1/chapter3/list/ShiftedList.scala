package v1.chapter3.list

import stainless.collection.List
import stainless.lang.{decreases, BooleanDecorations}
import stainless.lang.BigInt
import v1.chapter1.verification.Helper.assert
import v1.chapter3.list.properties.RotationProperties

/**
 * A value sequence viewed one position later, with a new head.
 *
 * `ShiftedList` is the head-aware counterpart to rotation. Unlike
 * `RotationProperties` (which re-indexes a flat list with NO head change and
 * NO value change), a shifted sequence advances the head by the first gap:
 *
 *   newHead == oldHead + gaps.head
 *
 * and re-indexes the integral so that
 *
 *   shifted.apply(i) == original.apply(i + 1)
 *
 * The two operations are deliberately separate types/objects so the head
 * concept never leaks into the head-free rotation theory.
 *
 * This is pure list arithmetic — no primes, no coprimality. It captures the
 * structural fact that "advancing one sieve stage" is a head shift plus a
 * re-index, which is what makes the next stage's gap cycle a one-step
 * rotation of the current one (the gap-translation law below).
 *
 * @param head    the new head value (`oldHead + gaps.head`)
 * @param gaps    the gap list (UNCHANGED by shifting — only the viewing head moves)
 */
case class ShiftedList(
  head: BigInt,
  gaps: List[BigInt]
) {
  require(gaps.nonEmpty)

  /** Number of positions in one period (same as the original — shift preserves period). */
  def size: BigInt = gaps.size

  /**
   * The value at position `position`, defined as the head plus the cumulative
   * sum of the first `position` gaps. This mirrors `CycleIntegral.apply`:
   *
   *   apply(0) = head
   *   apply(n) = apply(n - 1) + gaps(n - 1)
   *
   * so that consecutive differences reproduce the gap list:
   *   apply(i + 1) - apply(i) = gaps(i)
   */
  def apply(position: BigInt): BigInt = {
    require(position >= 0)
    require(position < size)
    decreases(position)
    if (position == BigInt(0)) {
      head
    } else {
      apply(position - 1) + gaps(position - 1)
    }
  }

  /**
   * Adjacent-gap identity: `apply(i + 1) - apply(i) == gaps(i)`.
   *
   * This is the direct consequence of the integral definition above and is the
   * load-bearing fact for the gap-translation law: the shifted sequence's
   * adjacent differences ARE the gap list.
   */
  def assertAdjacentDifferenceEqualsGap(position: BigInt): Boolean = {
    require(position >= 0)
    require(position + 1 < size)
    decreases(position)
    assert(apply(position + 1) == apply(position) + gaps(position))
    apply(position + 1) - apply(position) == gaps(position)
  }.holds

  /**
   * Period preservation: a shifted sequence has the same number of positions
   * as the original. Trivial from `size == gaps.size` (the gap list is
   * unchanged by shifting).
   */
  def assertSamePeriod(otherSize: BigInt): Boolean = {
    require(otherSize == gaps.size)
    size == otherSize
  }.holds
}

object ShiftedList {

  /**
   * Constructs the shifted view of an original sequence `(origHead, gaps)`:
   * the new head is `origHead + gaps.head`, and the gap list is rotated by one
   * position so that `shifted.apply(i) == original.apply(i + 1)`.
   */
  def shift(origHead: BigInt, gaps: List[BigInt]): ShiftedList = {
    require(gaps.nonEmpty)
    ShiftedList(origHead + gaps.head, ListUtils.rotateAt(gaps, BigInt(1)))
  }

  /**
   * Gap-translation law: shifting a sequence translates its adjacent-gap
   * sequence by one index. Concretely, if `shifted = shift(origHead, gaps)`
   * and `orig = ShiftedList(origHead, gaps)` (the original, un-shifted view),
   * then:
   *
   *   shifted.apply(i + 1) - shifted.apply(i) == orig.apply(i + 2) - orig.apply(i + 1)
   *
   * i.e. the shifted sequence's adjacent gap at `i` equals the original's
   * adjacent gap at `i + 1`. Both sides equal `gaps(i + 1)` because shifting
   * leaves the gap list unchanged and only moves the head — the adjacent-
   * difference law (`apply(k+1) - apply(k) == gaps(k)`) holds for both views.
   */
  /**
   * Gap-translation law: shifting a sequence translates its adjacent-gap
   * sequence by one index. Concretely, if `shifted = shift(origHead, gaps)`
   * and `orig = ShiftedList(origHead, gaps)` (the original, un-shifted view),
   * then:
   *
   *   shifted.apply(i + 1) - shifted.apply(i) == orig.apply(i + 2) - orig.apply(i + 1)
   *
   * Both sides equal `gaps(i + 1)`: the shifted adjacent difference at index
   * `i` uses `shifted.gaps(i)` = `gaps(i+1)` (rotation by one), while the
   * original adjacent difference at index `i+1` uses `gaps(i+1)` directly.
   */
  def assertGapTranslation(
    origHead: BigInt,
    gaps: List[BigInt],
    i: BigInt
  ): Boolean = {
    require(gaps.nonEmpty)
    require(i >= 0)
    require(i + 2 < gaps.size)
    val shifted = shift(origHead, gaps)
    val orig = ShiftedList(origHead, gaps)
    assert(shifted.assertAdjacentDifferenceEqualsGap(i))
    assert(orig.assertAdjacentDifferenceEqualsGap(i + 1))
    assert(RotationProperties.assertRotatedAtIndexPlusOne(gaps, i))
    assert(shifted.gaps(i) == gaps(i + 1))
    assert(shifted.apply(i + 1) - shifted.apply(i) == gaps(i + 1))
    shifted.apply(i + 1) - shifted.apply(i) ==
      orig.apply(i + 2) - orig.apply(i + 1)
  }.holds

  /**
   * Positional-shift law: `shifted.apply(i) == orig.apply(i + 1)`.
   *
   * The shifted sequence at index `i` equals the original at index `i + 1`,
   * because the shifted head is `origHead + gaps.head = orig.apply(1)` and the
   * cumulative-gap structure is rotated by one. Proved by induction on `i`,
   * using the adjacent-difference law to step both sides forward by one gap.
   */
  def assertShiftedApplyIsOriginalPlusOne(
    origHead: BigInt,
    gaps: List[BigInt],
    i: BigInt
  ): Boolean = {
    require(gaps.nonEmpty)
    require(i >= 0)
    require(i + 1 < gaps.size)
    decreases(i)
    val shifted = shift(origHead, gaps)
    val orig = ShiftedList(origHead, gaps)
    if (i == BigInt(0)) {
      assert(shifted.head == origHead + gaps.head)
      assert(orig.apply(BigInt(1)) == origHead + gaps.head)
      shifted.apply(i) == orig.apply(i + 1)
    } else {
      assert(assertShiftedApplyIsOriginalPlusOne(origHead, gaps, i - 1))
      assert(shifted.apply(i - 1) == orig.apply(i))
      assert(shifted.assertAdjacentDifferenceEqualsGap(i - 1))
      assert(orig.assertAdjacentDifferenceEqualsGap(i))
      assert(RotationProperties.assertRotatedAtIndexPlusOne(gaps, i - 1))
      assert(shifted.gaps(i - 1) == gaps(i))
      shifted.apply(i) == orig.apply(i + 1)
    }
  }.holds
}
