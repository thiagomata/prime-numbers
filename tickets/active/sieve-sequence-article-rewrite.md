# Sieve Sequence Article Rewrite

**Status:** Active
**Created:** 2026-06-28
**Owner:** `articles/sieve-sequence.md`
**Related proof ticket:** [`sieve-sequence-proof.md`](sieve-sequence-proof.md)
**Related epic:** [`../sieve-sequence-epic.md`](../sieve-sequence-epic.md)

## Goal

Rewrite `articles/sieve-sequence.md` so it matches `PROOF_GUIDE.md` and the
finished article style used by `integral-cycle.md`, `modulo.md`, `list.md`,
`cycle.md`, and `integral.md`.

The rewrite must be publication-oriented, source-backed, and honest about the
current proof boundary:

- Spec and Canonical current-stage equivalence are verified.
- The canonical next cycle built from `spec.next` is verified.
- The concrete survival walk used by `CycleSieveSequence.next()` is **not**
  verified to emit `spec.next` gaps yet.

## Current Problems in `articles/sieve-sequence.md`

1. **Section order is broken.** The current Conclusion appears before Section 9,
   so the article reads as if it concludes before introducing next-stage
   survivor composition.
2. **Claims overreach the current code.** The article currently says the
   survivor-based sequence and all three sequences produce identical values at
   every position. That is too strong if read as certifying
   `nextGapsWalk(cycle)` or `cycle.next()`.
3. **Some Scala snippets are illustrative, not current source.** Sections for
   distinct primes, filter preservation, and head primality contain simplified
   placeholder-style functions that do not match the current verified function
   names or paths.
4. **The structure does not consistently follow PROOF_GUIDE.** Several
   properties do not have all three forms:
   - English overview above the math;
   - step-by-step `math` proof with labels;
   - Stainless verification reference to the real source.
5. **No properties index.** Finished articles provide a table mapping each
   property to its statement and verifier. This article should do the same.
6. **Mixed scope.** The article combines:
   - foundation properties;
   - Spec linear-scan properties;
   - Canonical Spec/Cycle equivalence;
   - next-stage canonical construction;
   - open survival-walk correctness.

   These should be separated so the reader can tell what is verified and what
   remains open.

## Comparison With Existing Articles

The rewrite should match the shape and tone of the finished articles in
`articles/`, not invent a new format. The strongest structural references are:

- `articles/integral-cycle.md`: best overall template for a layered article
  that depends on earlier foundations, introduces several related definitions,
  separates core verified properties from draft/open extensions, and ends with
  Scala code plus verification-log appendices.
- `articles/cycle.md`: best template for equivalence between representations.
  Its structure is useful for presenting Spec, Canonical, and Cycle as related
  views while keeping each theorem source-backed.
- `articles/list.md`: best template for a large property catalog. Its
  properties index and appendix organization are useful because
  `sieve-sequence.md` will cite many small lemmas.
- `articles/gap-dynamics.md`: best template for open proof boundaries. Its
  "Boundary Index" and explicit status key should guide the survival-walk
  section, because that theorem is not verified yet.
- `articles/modulo.md`: important mathematical foundation, but older article
  structure. Use it for conceptual dependency and references, not as the main
  layout template because it does not follow the newer properties-index style.

### Shared House Style To Preserve

Finished articles generally use this order:

1. Title and author metadata.
2. Abstract with honest scope.
3. Properties Index, or Boundary Index for open/frontier material.
4. Introduction explaining motivation and the zero-prior-knowledge foundation.
5. Preliminaries and definitions before property proofs.
6. Numbered property sections.
7. For each property:
   - English overview above the formula;
   - `math` block with step-by-step labels;
   - Stainless verifier reference to the exact source object/function.
8. Limitations or open problems before the conclusion when relevant.
9. Conclusion after all proof sections.
10. References.
11. Appendix A for Scala verification code.
12. Appendix B for verification-log output where useful.

The current `sieve-sequence.md` violates that house style in two important
ways: it places the conclusion before later proof material, and it mixes
verified claims with open survivor-walk claims without a clear status boundary.

### Target Article Skeleton

The rewrite should follow this concrete skeleton:

1. Title, author metadata, and abstract.
2. Properties Index with status for every listed property.
3. Introduction.
4. Preliminaries and notation.
5. Definitions: Spec, Canonical, Cycle, and active filter tail.
6. Spec sequence verified properties.
7. Spec gap-cycle reconstruction.
8. Canonical current-stage equivalence.
9. Canonical next-stage equivalence.
10. Survivor bridge facts.
11. Open Problem: survival-walk correctness.
12. Limitations and future work.
13. Conclusion.
14. References.
15. Appendix A: Scala verification code.
16. Appendix B: latest verification-log summary.

### Formatting Rules For The Rewrite

- Use `integral-cycle.md` as the primary layout model.
- Use `gap-dynamics.md` only for explicit open-boundary language.
- Do not put long proof bodies inline when an appendix reference is clearer.
- Do not include illustrative Scala snippets unless they are clearly marked as
  draft or pseudocode.
- Every verified row in the Properties Index must link to a current source
  function that exists under `src/main/scala/`.
- Every open row must say `[Open]` or `[Draft — verification pending]`, not
  merely omit the verifier.
- Prefer source-backed prose over broad narrative claims. In particular, do not
  claim that `CycleSieveSequence.next()` is verified to match `spec.next` until
  the survival-walk theorem is actually proved.

## Recommended Article Structure

### Abstract

State the exact verified scope:

- `SpecSieveSequence` is the linear-scan specification.
- `SpecDerivedCycleSieve` reconstructs the same stream from Spec-certified gaps.
- `SpecDerivedCycleSieve(spec.next, nextPeriod)` matches `spec.next`.
- The concrete walk-backed `CycleSieveSequence.next()` remains open pending
  survival-walk correctness.

Do **not** claim full walk-backed next-stage equivalence.

### Properties Index

Add a table like the finished articles:

| # | Property | Statement | Verifier |
|---|---|---|---|
| 3.1 | Spec soundness | `spec(k)` passes tail-prime filters | `SpecSieveSequence.apply` postcondition / alias lemma |
| 3.2 | Spec completeness | every accepted `n >= head` has an index | `SpecSieveSequence.indexOfAccepted` |
| 3.3 | Spec monotonicity | `i < j => spec(i) < spec(j)` | `assertApplyMonotonic` / strict alias |
| 4.1 | Gap positivity | `gap(k) > 0` | `assertGapPositive` |
| 4.2 | Gap periodicity | `gap(k+p) == gap(k)` | `assertGapPeriodic` |
| 4.3 | Gap list reconstruction | `CycleIntegral(head, specGapCycle)(k-1) == spec(k)` | `assertSpecGapCycleIntegralMatchesApply` |
| 5.1 | Canonical current apply | `canonical.cycle(k) == spec(k)` | `SpecDerivedCycleSieve.assertApplyMatches` |
| 5.2 | Canonical next head | `cycle(1) == spec.next.head.value` | `assertNextHeadMatches` |
| 5.3 | Canonical next cycle | `SpecDerivedCycleSieve(spec.next,...).cycle(k) == spec.next(k)` | `assertNextCycleApplyMatchesSpecNext` |
| 6.1 | Survivor position bridge | `spec.next(k)` occurs at a current-cycle survivor position | `assertSurvivorPositionMatchesSpecNext` |
| 6.2 | Survivor gap bridge | adjacent survivor gap equals adjacent `spec.next` gap | `assertSurvivorGapEqualsSpecNextGap` |
| 7.1 | Open walk theorem | `nextGapsWalk(cycle) == spec.next.gapList(...)` | **Open** |

Only include rows that are source-backed after checking current function names.

### 1. Introduction

Introduce the three representations:

1. Spec: simple linear scan over natural numbers, filtering by tail primes only.
2. Canonical: constructed from Spec's verified gaps and prime values.
3. Cycle: optimized gap-cycle representation and survival walk.

Explain why the article uses Canonical as the bridge and why raw Cycle
correctness is not assumed by constructor invariants alone.

### 2. Definitions

Define:

```math
\begin{aligned}
\text{head} &= \text{primes.head} \\
\text{filterPrimes} &= \text{primes.tail} \\
\text{accepts}(n) &\iff n \ge head \land
  \forall p \in filterPrimes,\ n \bmod p \ne 0
\end{aligned}
```

Be explicit that the head prime is **not** in the active filter list for the
current Spec stage; it becomes a filter only in `spec.next`.

### 3. Spec Sequence Properties

Each property must have English, math, and source-backed Stainless reference.

Recommended sections:

- Soundness: every `spec(k)` passes `filterPrimes`.
- Completeness: every accepted `n >= head` is generated by some index.
- Monotonicity/injectivity: generated values are ordered and unique.

### 4. Spec Gap-Cycle Construction

Document the verified gap-list machinery:

- `gapList(from, count)`
- `assertGapListPositive`
- `assertGapPeriodic`
- `specGapCycle(period)`
- `assertSpecGapCycleIntegralMatchesApply`

This is the mathematical bridge from linear scan to cycle integral.

### 5. Canonical Current-Stage Equivalence

Document:

```math
SpecDerivedCycleSieve(spec, period).cycle(k) = spec(k)
```

Use current source references:

- `assertHeadMatches`
- `assertPrimesMatch`
- `assertGapCycleMatches`
- `assertApplyMatches`

### 6. Canonical Next-Stage Construction

Document what is verified today:

```math
SpecDerivedCycleSieve(spec.next, nextPeriod).cycle(k) = spec.next(k)
```

This is the verified "correct next cycle exists" theorem.

Do **not** describe it as proof that `cycle.next()` computes that cycle.

### 7. Survivor Bridges

Document the per-value and per-gap survivor facts:

```math
\begin{aligned}
pos_k &= spec.indexOfAccepted(spec.next(k)) \\
cycle(pos_k) &= spec.next(k) \\
spec.next(k+1)-spec.next(k)
  &= cycle(pos_{k+1}) - cycle(pos_k)
\end{aligned}
```

Then explain the proof boundary:

- These bridge facts show where `spec.next` values appear in the current cycle.
- They do not yet prove the concrete `collectGaps` recursion emits exactly those
  values in order.

### 8. Open Problem: Survival Walk Correctness

This section should be explicit and useful, not hidden:

```math
SieveSequenceNextLevel.nextGapsWalk(cycle)
  \stackrel{?}{=} spec.next.gapList(0,nextPeriod)
```

Describe the planned invariant from `sieve-sequence-proof.md`:

- `gaps.reverse == spec.next.gapList(0, emitted)`
- `lastSurvivor == spec.next(emitted)`
- skipped values are rejected by `spec.next`
- emitted values are the next accepted values

Mark it as **Open — Stainless verification pending**.

### 9. Conclusion

Summarize only what the article proves:

- Spec linear scan is the source of truth.
- Spec gaps reconstruct the Spec stream.
- Canonical current stage matches Spec.
- Canonical next stage built from `spec.next` matches `spec.next`.
- The concrete survival walk is the remaining proof gap.

## Source Audit Checklist

Before editing the article, check these current source names and paths:

- `src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala`
- `src/main/scala/v1/chapter6/seq/sieve/SpecDerivedCycleSieve.scala`
- `src/main/scala/v1/chapter6/seq/sieve/CycleSieveSequence.scala`
- `src/main/scala/v1/chapter6/seq/sieve/SieveSequenceNextLevel.scala`
- `src/main/scala/v1/chapter6/seq/sieve/properties/SieveSequenceProperties.scala`
- `src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralOnesProperties.scala`
- `src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala`
- `OBJECTS.md`, especially the `SpecSieveSequence` and `SpecDerivedCycleSieve`
  sections

## Editing Plan

1. Preserve any current user edits in `articles/sieve-sequence.md`; read the
   file before patching.
2. Replace placeholder Scala snippets with either:
   - exact source-backed code from the verified function; or
   - a source reference plus "full code in Appendix" if the function is long.
3. Move the conclusion to the end.
4. Add the Properties Index.
5. Rewrite the overclaiming Section 9.3 as:
   - verified canonical next-stage equivalence;
   - verified survivor bridge facts;
   - open survival-walk theorem.
6. Add an "Open Problem" section for Leg 4 survival-walk correctness.
7. Check all links and anchors.

## Validation

Markdown-only article edits do not require `just verify`, but before finalizing:

- Check `verify.log` for the latest green run.
- Run `rg` for every function name cited in the article.
- Confirm each property has English, math, and Stainless/source reference.
- Confirm the abstract, introduction, and conclusion do not claim the open
  survival-walk theorem as verified.
- Confirm no article section references stale filenames such as
  `canonical-next-strategy.md` or `spec-canonical-cycle-design.md`.

## Progress Log

### 2026-06-28 article first pass

Updated `articles/sieve-sequence.md` toward the target structure:

- Rewrote the abstract to state the verified scope honestly:
  - Spec linear-scan foundation;
  - Canonical current-stage equivalence;
  - conditional canonical next-stage equivalence;
  - open survival-walk list theorem.
- Added a Properties Index near the top, matching the finished article style.
- Replaced stale "distinct primes", "filter preserves primes", and
  "head is prime" sections with source-backed Spec and Canonical sections:
  - Spec soundness via `SpecSieveSequence.apply` postcondition;
  - Spec completeness via `SpecSieveSequence.indexOfAccepted`;
  - Spec strict progress via `SpecSieveSequence.applyStrictlyIncreases`;
  - gap positivity and gap-cycle reconstruction;
  - canonical current-stage apply equality;
  - conditional canonical next-stage identity.
- Converted the old premature conclusion into a "Current Verification Boundary"
  section.
- Rewrote the survivor section so it documents verified bridge facts without
  claiming that `CycleSieveSequence.next()` is fully equivalent to `spec.next`.
- Added an explicit open theorem:

  ```math
  \text{SieveSequenceNextLevel.nextGapsWalk}(\text{cycle})
    \stackrel{?}{=}
    \text{spec.next.gapList}(0,nextPeriod)
  ```

- Added Appendix A as a verifier catalog and Appendix B as the latest checked
  `verify.log` summary.

Validation performed:

- Searched the article for removed overclaims and stale verifier names:
  `full next-stage`, `all three sequences`, `Three-Sequence`,
  `assertCycleIntegralOfOnesStrictMonotonic`, `filterPreservesPrimes`,
  `filteredContainsAllPrimes`, and stale head-prime article claims.
- Confirmed no matches remained.
- Checked the latest `verify.log` instead of rerunning verification because the
  work was markdown-only:
  `total: 10495 valid: 10495 invalid: 0 unknown: 0 time: 34.38`.

Remaining cleanup:

- The article is now structurally much closer to `integral-cycle.md`, but a
  later editorial pass should still smooth Sections 3 and 4 so the older unit
  cycle material flows more naturally into the Spec sequence story.
- Consider adding a short dependency map diagram like `integral-cycle.md`.
- Consider replacing long inline Scala snippets in Section 9 with shorter
  signatures plus Appendix references if the article feels too code-heavy.
