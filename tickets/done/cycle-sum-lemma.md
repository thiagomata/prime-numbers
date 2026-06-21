# Ticket: Prove `sum(calculateGaps(sorted, modulus)) == modulus`

**Created:** 2026-06-07
**Status:** In progress
**Depends on:** next-level-requirements.md (Step 3)

---

## Goal

Prove the telescoping sum lemma for `calculateGaps`. This is the foundational pipeline-dependent lemma needed for R10 (`newCycle.sum() == product(newPrimes)`).

## Current State

- 3761 valid, 0 invalid — green
- `SieveUtils.calculateGaps` exists and verifies in isolation
- `ListUtilsProperties.listCombine` exists (sum of append)
- `ListUtilsProperties.assertLastEqualsLastPosition` exists (confirms `.last` works)
- `SieveSequenceNextLevel.nextGaps` calls `calculateGaps(sorted, modulus * head)`

## Expected State

- `assertSumPairwiseGaps(list)` — `.holds`, proves `sum(pairwiseGaps(list)) == list.last - list.head`
- `assertCalculateGapsSum(sorted, modulus)` — `.holds`, proves `sum(calculateGaps(sorted, modulus)) == modulus`

## Proof Strategy

Telescoping sum:

```
calculateGaps(sorted, M) = pairwiseGaps(sorted) ++ [M - sorted.last + sorted.head]

sum(pairwiseGaps(sorted)) = sorted.last - sorted.head    [lemma 1]

sum(calculateGaps) = (sorted.last - sorted.head) + (M - sorted.last + sorted.head) = M
```

### Lemma 1: `assertSumPairwiseGaps`

Structural induction on `list`:
- `list.size == 1`: `pairwiseGaps` returns `[]`, sum = 0, `list.last - list.head = 0` ✓
- `list.size == 2`: `pairwiseGaps` returns `[list(1) - list(0)]`, sum = `list(1) - list(0)` = `list.last - list.head` ✓
- `list.size > 2`: `pairwiseGaps(list)` = `(list(1)-list.head) :: pairwiseGaps(list.tail)`. By induction on `list.tail`: `sum(pairwiseGaps(list.tail)) = list.tail.last - list.tail.head = list.last - list(1)`. Total = `(list(1)-list.head) + (list.last-list(1)) = list.last - list.head` ✓

### Lemma 2: `assertCalculateGapsSum`

- If `sorted.size == 1`: `calculateGaps` returns `[modulus]`, sum = modulus ✓
- If `sorted.size > 1`:
  - `assertSumPairwiseGaps(sorted)` → `sum(pairwiseGaps) = sorted.last - sorted.head`
  - `listCombine(pairwiseGaps, [wrapGap])` → `sum(pairwiseGaps ++ [wrapGap]) = sum(pairwiseGaps) + wrapGap`
  - `calculateGaps = pairwiseGaps ++ [wrapGap]`, where `wrapGap = modulus - sorted.last + sorted.head`
  - Therefore `sum(calculateGaps) = (sorted.last - sorted.head) + (modulus - sorted.last + sorted.head) = modulus`

## Alternatives Considered

1. **Direct recursive proof without sub-lemmas** — tried, but `calculateGaps` uses `++` (append) which Stainless can't unfold through `sum` without a `sumAppend` lemma.
2. **Track-first-element accumulator** — base case can't know about wrap gap without first element reference.
3. **Writing own `listLast`** — unnecessary, Stainless `List.last` exists and is used in `calculateGaps` already.
4. **Writing own `assertSumAppend`** — unnecessary, `ListUtilsProperties.listCombine` already exists.

## Risks

- `assertSumPairwiseGaps` recursion on `list.tail` when `list.size > 2` — Stainless should handle this since it's structural recursion on `list.size`.
- `list.last` in inductive hypothesis: needs `list.tail.nonEmpty`. Since we're in the `list.size > 2` branch, `list.tail.size > 1` ≥ 1, so it's non-empty. ✓

## Validation

- `just verify` passes after each lemma
- `assertCalculateGapsSum` is `.holds` in `SieveUtils`
