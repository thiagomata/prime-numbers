# Sieve Sequence V2 Salvage Before V1 Removal

**Created:** 2026-07-14
**Status:** Planning
**Owner:** `articles/chapter6/sieve-sequence-v2.md`
**Source being retired:** `articles/chapter6/sieve-sequence.md`

## Goal

Before removing or deprecating `articles/chapter6/sieve-sequence.md`, salvage
the small amount of useful editorial and proof-boundary material that should
remain available in `articles/chapter6/sieve-sequence-v2.md`.

The expected result is not a merge of v1 into v2. V2 should remain the
canonical article because it has the cleaner full-period framing, the
same-head survivor-count boundary, and a more honest abstract. This ticket is
only for preserving useful v1 material that would otherwise disappear.

## Current State

`articles/chapter6/sieve-sequence-v2.md` is the stronger canonical article:

- It defines the sieve stage as a finite object with head, tail filters,
  period, and gap cycle.
- It uses the corrected exact full-period framing around the current `M`
  interval and the expanded same-head survivor count.
- It states the current proof boundary as Bertrand plus the packaging boundary
  that the verified same-head count is supplied to the cycle-level
  construction rather than propagated through the full next-spec/cycle wrapper.

`articles/chapter6/sieve-sequence.md` should not be kept as publication text in
its current form:

- Its abstract contains placeholder debris (`Hello World`, `$x = 1^2$`).
- Its top-level framing overclaims a fully verified three-way equivalence.
- Some proof-boundary language appears stale relative to the current v2
  theorem surface.

However, v1 still contains a few useful explanatory blocks and audit tables
that should be mined before it is removed.

## Similar Tickets and Prior Work

- [`m-interval-density-and-sieve-sequence-v2.md`](m-interval-density-and-sieve-sequence-v2.md)
  - Current v2 repair/proof planning ticket.
  - Establishes that v2 should stay focused on exact full-period `M`-interval
    counting and avoid vague density language.
- [`sieve-sequence-article-rewrite.md`](sieve-sequence-article-rewrite.md)
  - Older rewrite guidance for `articles/chapter6/sieve-sequence.md`.
  - Records that the concrete survival walk / `CycleSieveSequence.next()` must
    remain a visible open boundary unless proved.
- [`sieve-sequence-proof.md`](sieve-sequence-proof.md)
  - Tracks the survival-walk producer theorem.
  - Useful for checking whether the walk caveat is still current before adding
    it to v2.

## Salvage Items

### 1. Preserve the Walk-Status Caveat

V1 explicitly warns that the constructive path and the concrete walk are not
the same proof object:

> The constructive path (`nextWithGapCycle`) is fully verified — `Spec.next = Canonical.next = Cycle.next` for all positions.

> The walk (`CycleSieveSequence.next()`) uses `nextGapsWalk`, an unverified internal implementation with zero callers in the codebase.

And later:

> This theorem remains open. Until it is proved, this article must not claim that `CycleSieveSequence.next()` itself is fully equivalent to `spec.next`.

V2 should gain a short "Implementation Boundary" or "Concrete Walk Boundary"
paragraph in Section 7, or near the end of Section 6.2, preserving this
distinction.

Before editing v2, re-check the current source and `tickets/active/sieve-sequence-proof.md`.
If the walk theorem has since been proved, update the statement accordingly
instead of copying the old caveat.

### 2. Add a Verified Lemma Inventory Appendix

V1 has a useful final table mapping article claims to source handles:

> The following table lists the key verified lemmas discussed in the body of the article.

The v1 table should not be copied verbatim. Some names, source paths, and
claims may be stale. Instead, create a fresh v2 appendix:

```text
Appendix A: Verified Lemma Inventory
```

Suggested columns:

| Role | Statement | Source |
|------|-----------|--------|
| Linear scan soundness | emitted values pass tail filters | `SpecSieveSequence::apply` |
| Linear scan completeness | accepted values have an index | `SpecSieveSequence::indexOfAccepted` |
| Strict monotonicity | `apply(k + 1) > apply(k)` | `SpecSieveSequence::applyStrictlyIncreases` |
| Gap positivity | adjacent gaps are positive | `SpecSieveSequence::assertGapPositive` |
| Current period boundary | `h + M` is accepted | `SpecSieveSequence::assertHeadPlusTailPrimorialAccepted` |
| Same-head count | expanded survivors count is `T * (h - 1)` | `SpecSieveSequence::assertSameHeadExtendedFilterCount` |
| Current-stage reconstruction | cycle integral reconstructs scan | verify current source name |
| Next-stage conditional bridge | constructed next cycle matches next spec under supplied period boundary | verify current source name |
| Concrete survival walk | walk-backed gap producer matches spec next gaps | `[Open]` unless source proves it |

Validation rule: every `[Verified]` row must link to a real current source
function that exists under `src/main/scala/`. If a row cannot be source-backed,
mark it `[Open]` or remove it.

### 3. Preserve the Modulo Dependency Mini-Catalog

V1's modulo dependency section is more explanatory than v2's compact
dependency list. It names the arithmetic moves used by the proof:

> Modular shift invariance by multiplier — adding a multiple of the divisor preserves the remainder.

> Modular shift from zero — when `a` is divisible by `b`, the remainder of `a + c` is just the remainder of `c`.

> Unit-step increment law — incrementing a value whose remainder is not `b - 1` increases the remainder by exactly one.

V2 should add a compact paragraph or table under Section 2.2 that lists only
the dependency laws actually used by v2. Do not reintroduce v1's long
preliminaries wholesale.

### 4. Keep the "Head Is Not an Active Filter" Explanation

V1 makes a reader-friendly point that should survive:

> The head itself is not part of the active filter.

It gives the useful example:

> For `[5, 3, 2]`, the active filters are `[3, 2]`, so `25` is accepted even though it is a multiple of the head `5`.

V2 already implies this through the stage definition and examples, but a
single explicit sentence in Section 3.1 or Section 4.1 would prevent a common
misreading:

```text
At stage S_k, the head h is not yet an active filter; it becomes a filter only
in S_{k+1}. Thus the current stage may still emit multiples of h, and the next
stage construction removes them.
```

### 5. Do Not Preserve V1's Old Abstract or Overclaiming

Do not carry over v1's abstract, introduction, or conclusion language that
claims an unconditional or fully internalized three-way equivalence.

Examples of v1 language to avoid:

> This article presents the fully verified three-way equivalence between the Spec (`SpecSieveSequence`), the Canonical bridge (`SpecDerivedSieveSequence`), and the Cycle (`CycleSieveSequence`) at both the current and next stages.

> This article presents the fully verified three-way equivalence Spec = Canonical = Cycle for both current and next stages.

V2's current abstract is better because it states the supplied next-period
boundary and the remaining packaging boundary explicitly.

### 6. Do Not Reintroduce Stale Euclid-Boundary Claims Without Audit

V1 has a section framing an "Euclid's lemma extended" prerequisite. Do not
copy that section into v2 without a fresh source audit. Current v2 focuses on
Bertrand and same-head-count propagation; older article-review notes warned
that sieve-sequence proof issues often involve stale proof names and boundary
drift.

If Euclid/product-coprimality needs to be mentioned in v2, first verify the
current proof surface in `PrimeUtils`, `BezoutUtils`, `AllPrimesSoFarList`, and
the chapter6 source files, then state the boundary using current function
names.

## Expected V2 Changes

1. Add a short concrete-walk boundary note.
2. Add or prepare a verified lemma inventory appendix.
3. Expand the dependency section with a compact modulo-law table.
4. Add one explicit sentence explaining that the current head is not an active
   filter until the next stage.
5. Leave v2's abstract and proof-boundary framing intact except for small
   clarifications.
6. Do not reference tickets from the article body.

## Validation

Markdown-only edits do not require Stainless verification.

Before closing this ticket:

- Confirm every new source reference in v2 exists under `src/main/scala/`.
- Confirm no article text references this ticket or any other internal ticket.
- Confirm v2 still satisfies the three-representation rule for any newly added
  property section.
- Confirm v2 does not claim `CycleSieveSequence.next()` / `nextGapsWalk`
  correctness unless a current verified lemma proves it.
- Confirm the old v1 quotes above have been converted into polished article
  prose, not copied as archival commentary.

## Learning Log

- 2026-07-14: Initial ticket created from a v1/v2 editorial comparison. V2
  should remain canonical, but v1 has useful material to salvage around the
  concrete-walk caveat, proof inventory, modulo dependency explanation, and
  the "head is not an active filter" reader warning.
