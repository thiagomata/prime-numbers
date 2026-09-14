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
`just arxiv-parity gap-dynamics` PASS after the edit.

Step 8 complete: built `articles/arxiv/relaxed-almost-prime/` (main.tex,
13 section files, references.bib with 10 entries -- 6 internal
cross-references + 4 external literature -- unified into one bibliography
per the survival-frontiers precedent, no figures needed). Also fixed a
leftover self-referential "this draft" wording (4 instances) in the
promoted markdown, found while converting. `just arxiv-pdf
relaxed-almost-prime` zero-warning (13 pages); `just arxiv-parity
relaxed-almost-prime` full PASS. Two real parity mismatches surfaced and
fixed during conversion: the Appendix A heading needed the "Appendix A:"
prefix dropped from the `.tex` `\section{}` title (matches gap-dynamics's
precedent for colon-style Appendix headings -- survival-frontiers uses the
period-style form instead, which doesn't need this); and Section 3's
heading (`Prime-Plus-$P_2$`) was renamed in both the md and tex to the
plain-English synonym the article already uses in its own prose
("prime-plus-almost-prime production"), sidestepping a genuine conflict
between hyperref's PDF-string bare-underscore restriction and the parity
checker's exact-match title normalization. Full-suite regression
(`just arxiv-pdf` / `just arxiv-parity`, all 10 packages) confirmed clean;
reverted the other 9 packages' incidentally-rebuilt output PDFs (identical
byte sizes, timestamp-only churn) to keep the diff scoped.

Promotion complete end to end. Nothing committed yet.

## Open Concerns

- RESOLVED: filename is `relaxed-almost-prime.md`.
- RESOLVED: `articles/notes/review-draft-relaxed-almost-prime-sieve-sequence.md`
  kept as-is, unchanged -- matches the survival-frontiers precedent
  (promotion is not retirement; only retired drafts' reviews get deleted).
  Its filename still says "draft" but that's a historical record of what
  was reviewed at the time, not a live claim about the current article.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-09-14 | Independently verified (not just trusted the 2026-09-01 review): 18 pattern-C citations, 0 `\blacksquare` uses, the §4 $\rho(m)$ gap still present, and confirmed via grep that no published chapter article overlaps this draft's content (euclid-theorem.md hits were false positives on `p_2` list notation). Found gap-dynamics.md §11.1 states this draft's Theorem 5 conclusion in prose, word-for-word matching in substance ("correlate perfectly with the full relaxed survivor count" = "the ratio to the survivor count is exactly 1"), with zero supporting citation. | Confirmed real promotion value beyond the mechanical fixes: this draft is the missing proof for an existing published claim. |
| 2026-09-14 | Owner decision on chapter placement, after confirming no `arXiv:`/`arxiv.org` marker exists anywhere for gap-dynamics (not externally published, so reordering is cheap): third chapter-6 article, not a renumbered earlier chapter. | Strategy section updated; proceeding without touching gap-dynamics/sieve-sequence/survival-frontiers chapter numbers. |
| 2026-09-14 | Owner flagged that "Pending" (Appendix A table's Stainless-status column) implies a commitment/roadmap to eventually verify -- the project makes no such promise. Checked: "Pending" as a table status word appears nowhere else in the published corpus (gap-dynamics/survival-frontiers use descriptive phrases, never a bare workflow word); the adjacent `candidates/README.md` taxonomy that Candidate #25 (row 1) belongs to uses "PROOF OPEN" instead. A real tracking ticket exists (`add-draft-scala-three-representations-2026-08-03.md`) but its own text hedges that the analytic-heavy results are "expected to remain documented obstacles" -- not actually expected to get done. Broadened the fix beyond the table on the owner's correction ("we never promise that we will verify"): also reworded the front-matter proof-status line, §1.1's "tracked as separate future work," and §4's "A future verification should prove..." (all implied an anticipated/committed event), leaving purely descriptive phrasing throughout ("not yet Stainless-verified", "Not yet verified", "Proving it would require..."). | Applied to both the `.md` and every corresponding `.tex` section; rebuilt, `just arxiv-parity relaxed-almost-prime` still full PASS; full 10-package regression clean. |
