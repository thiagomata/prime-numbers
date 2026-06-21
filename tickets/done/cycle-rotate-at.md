# ModCycle rotateAt Verification

## Status: COMPLETE

## Goal
Uncomment and verify `ModCycle.rotateAt(index: BigInt): ModCycle` and its helper `collectRotated`.

## What rotateAt needs
- `collectRotated` returns list with `res.size == count` and `CycleUtils.checkPositiveOrZero(res)`
- `rotateAt` calls `ModCycle(rotated)` which requires `rotated.nonEmpty` and `checkPositiveOrZero(rotated)`

## What we already have
- ✅ `cycleValuePositiveOrZero` — proves `apply(pos) >= 0`
- ✅ `checkPositiveOrZeroAtIndex` — proves `values(idx) >= 0`

## What's still needed (hypotheses)
- `checkPositiveOrZero` preserved under list construction (if `v >= 0` and `checkPositiveOrZero(tail)` then `checkPositiveOrZero(v :: tail)`)
- May need `checkPositiveOrZero(List(v))` for single element (special case)
- May need `checkPositiveOrZero` unfolding lemma (head ≥ 0, tail preserves)

## Risks
- `checkPositiveOrZero` is `@tailrec` — may need lemmas for construction direction
- collectRotated calls `apply(start + 1)` which may need preconditions for `start + 1`

## What was added

### CycleUtils
- `checkPositiveOrZeroCons(head, tail)` lemma: `head >= 0 && checkPositiveOrZero(tail) ⇒ checkPositiveOrZero(head :: tail)` — the "construction" direction

### ModCycle
- `collectRotated(start, count)` — uncommented and verified. Uses `values(Calc.mod(start, size))` directly (not `apply`) to avoid indirection. `.ensuring(res => res.size == count && checkPositiveOrZero(res))`
- `rotateAt(index)` — uncommented and verified. `index == 0` returns `this`; otherwise builds rotated list via `collectRotated` and constructs new `ModCycle`.

### Total: 3624 → 3647

## Lessons
- `checkPositiveOrZero` being `@tailrec` needed a "construction" lemma (`checkPositiveOrZeroCons`) — the "deconstruction" direction (unfolding) was already implicitly supported
- Adding `.ensuring` without internal guidance timed out; adding internal `assert` calls to the lemma first solved it
- `allValuesExistInList` assertions were skipped (not needed for current functionality)
