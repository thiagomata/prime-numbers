# Evaluate Draft Review Claims — 2026-08-15

## START HERE

Audit every scientific-quality claim in
`articles/draft/review-draft-articles-2026-08-15.md` against the current
repository, then append concise evidence-backed dispositions in that same
review document. Do not edit any other file under `articles/`.

## Goal

Determine which review claims are correct and worth acting on, which need
qualification, and which should be rejected. The work is complete when every
substantive claim has a documented disposition and supporting repository
evidence in the review document itself, with all six reviewed drafts left
unchanged.

## Strategy

Treat the review as hypotheses rather than authority. Inventory its numbered
and cross-cutting claims, then verify each against the exact current article,
linked Scala `.holds` implementations, `OBJECTS.md`, durable learnings,
empirical scripts/data, and relevant prior tickets. Use dispositions such as
`Accept`, `Accept with qualification`, `Defer`, and `Reject`, separating
scientific correctness from optional editorial preference. Append replies to
the review document only after the evidence pass is complete.

## Current State

- The review document and ticket discipline have been located and inspected.
- A repository-wide search found several related article-review and
  claim-boundary tickets.
- The review's cross-cutting and per-draft issues have been inventoried and
  checked against the six current drafts, linked Scala sources, empirical data,
  project guidance, and relevant prior work.
- Independent fact-checks covered drafts 1--5 and the current dirty-worktree
  version of draft 6. Several review statements are stale or overstate
  editorial preferences as scientific defects.
- A deeper audit of draft 3 found material provenance and mathematical errors
  that the review itself missed: the historical data ends at `p=991` with
  `p_next=997`, the runner used the closed interval `[p,p^2]`, and §4.3 uses
  the wrong density denominator.
- The complete response and disposition matrix has been appended to
  `articles/draft/review-draft-articles-2026-08-15.md`.
- Every cross-cutting claim and numbered issue has an `Accept`, `Accept with
  qualification`, or `Reject` disposition, plus a worth/priority judgment.
- The response adds the urgent draft-3 corrections missed by the original
  review and replaces its priority order accordingly.
- Scope, claim coverage, local links, and trailing whitespace checks passed.
- No reviewed draft was edited; the pre-existing dirty draft-6 state remains
  untouched.

## Related Work

- [`address-aug-2026-reviewer-notes-2026-08-03.md`](address-aug-2026-reviewer-notes-2026-08-03.md)
  establishes the precedent of verifying reviewer assertions before accepting
  narrowly scoped Markdown corrections.
- [`update-final-program-articles-2026-08-03.md`](update-final-program-articles-2026-08-03.md)
  records the claim matrices and evidence boundaries behind two of the drafts.
- [`draft-mixed-adversarial-random-companion-2026-08-11.md`](draft-mixed-adversarial-random-companion-2026-08-11.md)
  records the premise and status audits behind the companion-model draft.
- [`draft-sieve-foundation-bridge-2026-07-22.md`](draft-sieve-foundation-bridge-2026-07-22.md)
  records the scope and source mapping behind the foundation draft.
- [`local-safe-window-capacity-exercise.md`](local-safe-window-capacity-exercise.md)
  records the pedagogical purpose and validation boundary of the exercise.

## Alternatives Considered

- Accept all reviewer recommendations wholesale: rejected because descriptive
  review text is not ground truth and some recommendations may be stylistic,
  stale, or outside the drafts' intended purpose.
- Reply only to disputed claims: rejected because silence would make accepted
  claims ambiguous and leave no complete decision record.
- Edit the six drafts while auditing: rejected because the user explicitly
  requested no article changes yet and because evidence review must precede
  documentation changes.

## Assumptions and Hypotheses

- Assumption: “claims” includes cross-cutting findings and per-article numbered
  issues/improvements, but not purely descriptive summaries or strengths unless
  they contain a factual assertion relevant to disposition.
- Assumption: “worth” means worth adopting as a future revision, judged by
  correctness, scientific value, intended genre, cost, and duplication.
- Hypothesis: some literature and theorem-numbering recommendations are valid
  for research-paper drafts but excessive for exercises or superseded records.
- Hypothesis: several alleged omissions are already addressed in current text
  or intentionally excluded by scope/status and will need qualification rather
  than unconditional acceptance.

## Validation Plan

1. Parse the review into a complete claim inventory.
2. Read all six target drafts and their source links.
3. Search relevant `.holds` lemmas and read their bodies before judging formal
   verification claims.
4. Cross-check `OBJECTS.md`, `LEARNINGS.md`, empirical artifacts, and related
   tickets for provenance and known boundaries.
5. Add one response section to the review document, mapping every substantive
   claim to a disposition, rationale, and evidence.
6. Verify `git diff -- articles/draft/` shows only the review document changed;
   run Markdown link/fence/whitespace checks scoped to that file. No Scala or
   Python runtime gates apply because no executable instructions or code will
   change.

## What is Learned

- The review covers six documents of intentionally different genres: verified
  bridge, exercise, superseded empirical record, superseded mathematical
  exploration, analytic-sieve draft, and probabilistic companion-model draft.
- Prior tickets contain load-bearing provenance for the recent analytic and
  companion drafts and must be checked rather than relying on the review alone.
- Draft 1 §§4--5 are substantively duplicate, but the alleged §6 quantifier
  mismatch is false: both the displayed statement and Scala theorem quantify
  one prime `q` contained in an otherwise unrestricted list.
- Draft 2's `2*R(p,q)` argument is already correct. The review's proposed
  both-endpoints-removed edge case does not invalidate the upper bound and is
  not the ambiguity claimed.
- Draft 3's recorded 166 observations run from `p=3` through `p=991`; the final
  row's `p_next=997` was mistakenly promoted to the measured `p`. Its printed
  regression coefficients do not reproduce from the extant CSV, and its
  §4.3 product is `G_2/phi(M)`, not the per-integer density `G_2/M` used
  correctly in §4.6.
- Draft 4 already defines a 2-gap as consecutive accepted values, and §11
  explicitly describes the local-capacity and cluster claims as conditional.
  A status table could improve scanning, but the current prose is not
  mathematically misleading.
- Draft 5 needs external positioning, but calling its modulo-3 character
  obstruction simply an instance of the classical parity barrier is too
  strong. The article's weight is project-specific rather than “precisely” a
  standard lower-bound-sieve sequence.
- Draft 6 already states the blind empty-window bound as a premise in the body,
  appendix, and limitations. The useful remaining change is to define that
  premise once near the notation, not to portray it as unstated. Confidence
  intervals are inappropriate for its exhaustive deterministic datasets
  without a sampling model; optional trend/spread summaries are descriptive.
- Draft 6's scripts are deterministic, so seed metadata is irrelevant. Most
  generated SVGs already embed commit metadata; only uniformity of that
  metadata is a minor cleanup.
- The original bibliography-first priority is not defensible after the data
  audit. Draft 3's false terminal head, interval convention, density
  normalization, and regression provenance affect factual truth and take
  priority over citations or layout.

## Failed Paths

- Treating the review's draft-3 count discrepancy as a footnote-level indexing
  issue failed because the current CSV shows a deeper provenance error: the
  article relabels a `p=991, p_next=997` row as `p=997`. Retry only if a distinct
  archived dataset containing an actual `p=997` measurement is produced.
- Treating draft 6's empty-window inequality as unstated failed because the
  current working-tree draft names it repeatedly as the blind-placement
  premise and explicitly limits expectation-only arguments. Reopen only if a
  theorem is found that uses the inequality without inheriting that premise.

## Open Concerns

- External-literature judgments may require current primary-source checking;
  repository evidence alone can establish missing citations but not always the
  review's precise characterization of classical results.
- The review is long, so the final response format must remain complete without
  becoming a second full article.
- Replies must not introduce ticket references into publishable article text;
  this review document is itself under `articles/draft/`, so final prose should
  cite repository sources directly and avoid pointing readers to internal
  tickets.
- The current draft-6 file has unrelated user-owned modifications. Every final
  comparison must use the working-tree version, and validation must distinguish
  those pre-existing changes from this task's sole review-document edit.
- Exact external bibliography choices need source-specific vetting. Cramér and
  Gallagher are relevant context but should not be used to classify the
  companion as simply a Cramér model; the parity-barrier label for draft 5 also
  requires qualification.

## Next Action

Wait for explicit user direction before editing any of the six reviewed
articles. If revisions are requested, begin with draft 3's factual record and
apply one scoped Markdown correction per validation cycle.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-08-15 | The request requires a full evidence audit but forbids changes to the six reviewed drafts. | Created this ticket with a review-only scope and explicit article-preservation gate. |
| 2026-08-15 | The review mixes valid improvements, optional editorial preferences, stale diagnoses, and several incorrect claims; draft 3 has more serious data/provenance defects than the review identified. | Completed repository, source, data, guidance, and external-literature checks; preserved the corrected findings before drafting replies. |
| 2026-08-15 | A complete response can preserve useful reviewer suggestions while retracting false diagnoses and elevating missed factual errors. | Appended the full disposition matrix and revised priorities to the review document; passed scope, coverage, link, and whitespace checks without editing any reviewed draft. |
