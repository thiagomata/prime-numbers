# Relaxed Almost-Prime — promotion from draft to chapter-6 article

**Created:** 2026-09-14
**Branch:** `feature/draft-to-article`
**Depends on:** review-draft-relaxed-almost-prime-sieve-sequence.md (house-style
review, 2026-09-01, complete); CONVERSION_GUIDE; the survival-frontiers
promotion this same branch (pattern-C fix precedent).

## Goal

Promote `articles/draft/draft-relaxed-almost-prime-sieve-sequence.md`
(*Relaxed Almost-Prime Production in Sieve Sequences*, 893 lines) to a
published chapter-6 article + arXiv package, positioned between
`sieve-sequence.md` and `gap-dynamics.md`, with `gap-dynamics.md` §11.1
gaining a real citation for its currently-uncited claim about the
modulo-3 character refutation.

## Strategy

Unlike `draft-sieve-foundation.md` (retired) and
`exercise-local-safe-window-capacity.md` (moved to notes/), this draft is a
genuine promotion candidate: 893 lines (in range with the smallest published
chapters), five real theorems (an implication, two exact algebraic
reductions, an exact bilinear decomposition, and a refutation), correctly
scoped against real external literature (Chen, Halberstam-Richert,
Iwaniec-Kowalski, Friedlander-Iwaniec), with an explicit Claim Boundary
section. Different genre from the Stainless-verified chapters (pure
analytic number theory, verification explicitly pending throughout) --
acceptable per the `survival-frontiers` precedent already on this branch.

Chapter placement: the draft's only real prerequisite is `sieve-sequence.md`
(chapter 6) -- it never cites `gap-dynamics.md`. `gap-dynamics.md` §11
independently states this draft's headline refutation result in prose only,
with a self-referential (non-)citation. Since `gap-dynamics.md` is not
externally published (no arXiv ID anywhere in its package or article),
reordering is cheap. Chosen structure (owner decision 2026-09-14): add this
as chapter 6's third article, positioned in README.md's reading order
between `sieve-sequence.md` and `gap-dynamics.md`, so `gap-dynamics.md`
§11.1 cites it as a normal same-chapter, earlier-listed sibling -- no
renumbering of `gap-dynamics`, `sieve-sequence`, or `survival-frontiers`,
and neither already-built arXiv package is touched.

Phase 1 -- markdown fixes in draft/ (per the 2026-09-01 review + this
session's independent verification):
1. Pattern C: reword the 18 "is maintained in [properties/.../candidates/]"
   citations (same fix already applied to survival-frontiers this branch).
2. De-duplicate the scope restatement in Theorems 1-4 (bold statement +
   near-identical "We prove this for..." paragraph immediately after).
3. Add `\blacksquare` alongside every `[Q.E.D.]`, matching house style.
4. Fix the §4 (Theorem 2) gap: the theorem statement quantifies over every
   $m\ge1$, but $\rho(m)$ is only defined for the $\gcd(m,W)=1$ branch. Add
   the convention $\rho(m)=E_m=0$ when $\gcd(m,W)>1$, immediately after the
   vanishing case (per the review's 2026-09-01 Source-Check Adjudication).

Phase 2 -- promotion:
5. Move to `articles/chapter6/<name>.md` (name TBD, candidate:
   `relaxed-almost-prime.md`).
6. Update `README.md`'s chapter-6 listing to insert it between
   `sieve-sequence.md` and `gap-dynamics.md`.
7. Add a citation from `gap-dynamics.md` §11.1 to the new article, closing
   its currently-dangling self-referential claim.
8. Build the arXiv package (`articles/arxiv/<name>/`) per CONVERSION_GUIDE,
   `just arxiv-pdf`, `just arxiv-parity`, zero-warning gate.

## Current State

Phase 1 complete (all 4 markdown fixes applied and verified). Phase 2
markdown steps 5-7 complete: moved to `articles/chapter6/relaxed-almost-prime.md`,
front matter aligned to house style (Proof status/full name/ORCID),
README.md's chapter-6 listing updated with a new summary section between
`sieve-sequence.md` and `gap-dynamics.md`, and `gap-dynamics.md` §11.1 (both
the `.md` and its already-published arXiv `.tex` section) now cites the new
article for its previously-uncited claim -- rebuilt and re-verified
`just arxiv-parity gap-dynamics` PASS after the edit. Step 8 (build the new
article's own arXiv LaTeX package) not started -- this is the large
remaining chunk of work, comparable in scope to the survival-frontiers
conversion earlier this branch.

## Open Concerns

- Exact chapter-6 filename not yet finalized.
- Should `articles/notes/review-draft-relaxed-almost-prime-sieve-sequence.md`
  be kept as-is (precedent: survival-frontiers' review file was kept after
  its promotion, not deleted -- promotion is not retirement).

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-09-14 | Independently verified (not just trusted the 2026-09-01 review): 18 pattern-C citations, 0 `\blacksquare` uses, the §4 $\rho(m)$ gap still present, and confirmed via grep that no published chapter article overlaps this draft's content (euclid-theorem.md hits were false positives on `p_2` list notation). Found gap-dynamics.md §11.1 states this draft's Theorem 5 conclusion in prose, word-for-word matching in substance ("correlate perfectly with the full relaxed survivor count" = "the ratio to the survivor count is exactly 1"), with zero supporting citation. | Confirmed real promotion value beyond the mechanical fixes: this draft is the missing proof for an existing published claim. |
| 2026-09-14 | Owner decision on chapter placement, after confirming no `arXiv:`/`arxiv.org` marker exists anywhere for gap-dynamics (not externally published, so reordering is cheap): third chapter-6 article, not a renumbered earlier chapter. | Strategy section updated; proceeding without touching gap-dynamics/sieve-sequence/survival-frontiers chapter numbers. |
