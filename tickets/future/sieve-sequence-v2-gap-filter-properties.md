# Sieve Sequence V2 Gap Filtering Properties

**Status:** Active
**Created:** 2026-07-14
**Owner:** `articles/chapter6/sieve-sequence-v2.md`
**Related ticket:** [`m-interval-density-and-sieve-sequence-v2.md`](../active/m-interval-density-and-sieve-sequence-v2.md)

## Goal

Add a reader-facing subsection to `articles/chapter6/sieve-sequence-v2.md`
explaining the important gap properties used by the next-stage filtering step.
The section should focus on sieve-sequence properties, not implementation
mechanics.

## Current State

Section 7.1 currently explains the pipeline as:

1. residues from the current cycle,
2. expansion into a longer finite window,
3. filtering by the current head,
4. gaps from consecutive filtered survivors,
5. rotation.

The article now states that expansion has different internals but emits the
same values and gaps before filtering. It does not yet explain the key gap
properties of filtering itself.

## Expected State

Add a new subsection near Section 7, likely between the pipeline and pipeline
correctness theorem, tentatively titled:

`Gap Behavior Under Filtering`

The section should explain:

1. Filtering does not invent arbitrary gaps.
2. If two consecutive expanded values both survive, the old gap is copied.
3. If one or more expanded values are removed between two survivors, the new
   gap is the sum of the skipped old gaps.
4. Filtering can reduce the number of gaps, but it does not reduce the total
   span of the full window because skipped distances are merged into survivor
   gaps.
5. The endpoint anchors matter:
   - the relevant head/first survivor is not filtered out;
   - the period endpoint `head + M` is not filtered out.
6. Once the copy/merge behavior is properly presented, the article can use it
   to motivate finite gap-value analysis. For example: if a stage's gap cycle
   has no gap of value `2`, and later filtering can only copy existing gaps or
   merge adjacent gaps into larger values, then later stages cannot reintroduce
   a gap of value `2`; this would rule out twin-prime candidate pairs after
   that stage's head.

The wording must avoid the ambiguous claim that the "head is never filtered
out" unless the article first disambiguates which head is meant. In the
current-head filter step, the old current head `h` is divisible by `h`, so the
article must state the anchor precisely.

## Source Evidence To Review

- `GapProperties.assertRepeatedGapsPreservesIntegral`
  - `src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala`
  - Repeating gap cycles preserves emitted values.
- `GapProperties.assertMergedGapPositive`
  - Merged survivor gaps remain positive.
- `GapProperties.assertFilteredSumEqualsOriginalSum`
  - Filtering one full period preserves the total gap span:
    `survivors.last - survivors.head == ci.sum`.
- `SpecSieveSequence.assertConsecutiveAcceptedByNextPreservesGap`
  - Consecutive old values accepted by the next stage copy the old gap.
- `SpecSieveSequence.assertMergeGapEqualsOldGapSum`
  - Skipped old values merge into the sum of old gaps.
- `SieveUtils.assertCalculateGapsSum`
  - Calculated cyclic gaps sum to the modulus.

## Proposed Math Shape

Copied gap:

```math
\begin{aligned}
e_i,\ e_{i+1} \text{ survive}
  \quad &\Longrightarrow \quad
  f_{j+1} - f_j = e_{i+1} - e_i
  = g_{i \,\text{mod}\, T}
\end{aligned}
```

Merged gap:

```math
\begin{aligned}
e_i,\ e_m \text{ survive and } e_{i+1},\dots,e_{m-1} \text{ are removed}
  \quad &\Longrightarrow \quad
  f_{j+1} - f_j
  = e_m - e_i
  = \sum_{r=i}^{m-1} g_{r \,\text{mod}\, T}
\end{aligned}
```

Span preservation:

```math
\begin{aligned}
\sum G_{\text{filtered-window}}
  &= \text{last survivor} - \text{first survivor} \\
  &= \text{window endpoint} - \text{window start}
\end{aligned}
```

The exact endpoint notation must be chosen carefully after confirming whether
the subsection is describing the same-head filter window, the next-stage window,
or the rotated next-cycle view.

## Risks And Assumptions

- Do not overclaim that `h` survives filtering by `h`; that is false if `h` is
  the old current head and the filter is `mod(v, h) != 0`.
- The phrase "head is never filtered out" must be rewritten with precise
  notation before publication.
- Distinguish verified properties from article-level corollaries. If the article
  presents a corollary not directly verified as a public `.holds` function, mark
  it as a consequence of the listed verified lemmas.
- Avoid reintroducing sort/ordered-survivor pipeline language.

## Validation Plan

1. Re-read the source lemmas listed above and confirm their exact preconditions.
2. Identify the correct endpoint anchors for the article's notation.
3. Draft the subsection with English, math, and source references.
4. Run `git diff --check` for markdown formatting.
5. No Stainless verification is required for markdown-only article edits.

## Learning Log

| Date | Progress | Notes |
|------|----------|-------|
| 2026-07-14 | Created ticket from article discussion. | User identified two missing anchors for the future gap-filtering section: the relevant head/first survivor is not filtered out, and `head + M` is not filtered out. |
| 2026-07-14 | Moved the gap-2/twin-prime-candidate example out of the article body and into this ticket until the gap-copy/gap-merge properties are properly introduced. | The conclusion should not rely on properties not yet presented in the article. |
