# Detailed Side Versions for the Last Two Articles

## Goal

Create a branch from `master` and add side-by-side detailed versions of the two
latest chapter articles, without replacing the current articles. The new
versions should keep the mathematical content honest while expanding advanced
steps into slower, more explicit explanations.

Extended goal as of the follow-up request: improve the canonical
`articles/chapter6/sieve-sequence.md` and
`articles/chapter7/survival-frontiers.md` so their explanations of tests,
proofs, development, and proof boundaries follow the clearer pattern of earlier
articles. Keep the claims unchanged; improve exposition, evidence mapping,
reader checkpoints, and step-by-step derivations.

## Strategy

Work from `master` on a new `codex/` branch. Identify the two latest chapter
articles as `articles/chapter6/sieve-sequence.md` and
`articles/chapter7/survival-frontiers.md`, then create alternative Markdown
files next to them with a clear detailed-edition name. Preserve the original
articles unchanged. Because this is a Markdown-only side edition, runtime
verification is not required unless executable instructions or synced arXiv
editions are changed. The side editions will avoid claiming replacement status
and will not cite tickets or internal working notes.

For the canonical article clarity pass, borrow patterns from the earlier
articles:

- top-level scope/proof-spine bullets;
- short "what this proves" prose before each dense formula chain;
- labeled math derivations with fewer skipped algebraic steps;
- stable source-evidence paragraphs for verified claims;
- explicit distinction between verified source, mathematical-only reasoning,
  empirical context, and open work;
- short reader checkpoints after dense threshold or transition sections.

Because both canonical Markdown articles have arXiv packages, any canonical
Markdown content changes must be reflected in the corresponding LaTeX sections
before the unit of work is complete, or any remaining drift must be called out
explicitly in Open Concerns / Next Action.

## Current State

Initial repo inspection found the current branch at
`codex/translate-articles-pt-br`, with no short-status changes shown by
`git status --short --branch`. The repository has a local `master` branch. The
article list shows the latest chapter articles as chapter 6
`sieve-sequence.md` and chapter 7 `survival-frontiers.md`.

The work branch has been created from local `master`. Two side-version files
have been added:

- `articles/chapter6/sieve-sequence-detailed.md`
- `articles/chapter7/survival-frontiers-detailed.md`

Lightweight Markdown validation is complete: both new files have balanced fenced
code/math blocks, and grep found no internal ticket references in the article
files. The working tree contains only the two new detailed articles and this
ticket file.

Follow-up canonical clarity work has started. Earlier articles were sampled for
style patterns, especially `chapter5/euclid-theorem.md`, which uses a clear
scope list, staged proof strategy, short prose before math, labeled derivations,
and source-evidence paragraphs.

Canonical clarity pass completed for the first targeted layer:

- `articles/chapter6/sieve-sequence.md` now has a four-layer source-evidence
  proof spine and a reader bridge before the dense current-head transition
  section.
- `articles/chapter7/survival-frontiers.md` now has a four-level evidence map,
  a calculation-spine guide for the relative-hazard section, and an explicit
  definition of `\asymp` / constant-factor asymptotic comparison.
- Matching LaTeX changes were applied under both arXiv packages.
- `just arxiv-pdf sieve-sequence` and `just arxiv-pdf survival-frontiers` exited
  0 and rebuilt PDFs.
- `just arxiv-parity sieve-sequence` passed with one URL warning for the raw
  GitHub SVG already represented differently in the TeX package; summary PASS.
- `just arxiv-parity survival-frontiers` passed cleanly.

## What is Learned

- Existing related tickets include:
  - `tickets/active/sieve-sequence-arxiv-latex-2026-09-07.md`
  - `tickets/active/sieve-sequence-proof.md`
  - `tickets/active/sieve-sequence-property-catalog.md`
  - `tickets/active/survival-frontiers-article-review-2026-09-13.md`
  - `tickets/active/survival-frontiers-promotion-2026-09-13.md`
- The requested work is a side-version drafting task, not a change to the
  canonical article text.
- Because the original articles have arXiv packages, changing the originals
  would trigger arXiv sync. Creating separate side editions avoids desyncing the
  published Markdown/LaTeX pairs.
- The chapter 6 detailed guide should treat `l_T = h + M` as the canonical
  endpoint. For the `h = 5`, `M = 6` example, `T = 2`, values are
  `l_0 = 5`, `l_1 = 7`, `l_2 = 11`, and the gap cycle is `[2, 4]`.
- Earlier article pattern to reuse: "This article verifies" or equivalent
  proof-spine bullets near the top; "The proof proceeds in stages"; each
  property gets intuition, displayed derivation, and source-evidence paragraph.
- The survival-frontiers article cannot use "verified" in the Stainless sense
  for its companion asymptotics. It should instead use a separate evidence map:
  exact model identities, conditional mathematical derivations, empirical
  context, and pending Stainless verification.
- The `\asymp` symbol should be defined in the article notation because it is
  used heavily and is easy to misread as exact equality. It now means
  two-sided constant-factor comparison for all sufficiently large `Q`.
- Classical analytic-number-theory steps should be cited locally, not only once
  globally. Chapter 7 §4.3 now points the Taylor, prime harmonic, and PNT by
  partial summation steps to Hardy and Wright before using them.
- The local-citation principle was broadened beyond the user's example:
  Chapter 7 now also adds nearby citations for absolute-share mixture inputs,
  exact-quota prime-head summation and Borel-Cantelli/Kochen-Stone use,
  Mertens-type product estimates in biased quotas, and appendix proof-record
  prime-sum/Taylor clusters.
- The survival-frontiers PDF had a float-only page around page 35 after the
  citation/layout edits. The Section 8 arXiv figures 5 and 6 were adjusted as
  layout-only TeX changes (`[!htb]`, `0.82\textwidth`) so the charts share a
  page with surrounding text instead of stranding one image on a mostly blank
  page.
- Chapter 7 Section 8 still had dense prose blocks that combined setup,
  measurement, interpretation, and caveat in single paragraphs. The Markdown
  and TeX sources now split those ideas into shorter paragraphs, and the TeX
  transfer-theorem checklist is a real `itemize` list.
- The arXiv Introduction had collapsed several Markdown paragraphs and lists
  into page-sized TeX prose blocks. It now uses explicit paragraph breaks,
  `enumerate` for the three survival scales, and `itemize` for the article's
  contribution list.
- The two Introduction heatmaps were still vulnerable to floating together as
  an image plate. The arXiv source now renders them as in-place centered image
  blocks, each attached to its own explanatory paragraph and caption.
- Chapter 7's early hazard math now follows the clearer earlier-article
  pattern: each dense display is framed by what it is proving or defining, then
  followed by a short interpretation of what was proved and what boundary still
  applies.
- `AGENTS.md` now has an explicit `no-image-only-pages` article layout rule for
  arXiv PDFs. Page 13 of `survival-frontiers.pdf` was fixed by resizing and
  anchoring the head-threshold chart so the page also contains the regime
  formulas and explanatory text.

## Failed Paths

- None yet.

## Open Concerns

- Confirm after switching branches that `master` contains the same article
  locations and language state expected by the request.
- The phrase "last two articles" is interpreted by chapter order, not filesystem
  modification time. If `master` differs, re-check before editing.
- The parity check for `sieve-sequence` reports one URL warning for
  `charts/hit-miss-matrices.svg`; summary is PASS and the PDF is fresh. This is
  not caused by the clarity text edits but should be kept in mind for a future
  URL-parity cleanup.

## Next Action

The Chapter 7 arXiv PDF rebuild and parity check are green after the
Introduction image-placement fix, Introduction paragraph/list split, and
Section 8 paragraph split. The first hazard sections also have before/after
math-block framing in both Markdown and TeX. The no-image-only-pages rule and
page 13 fix are also complete. Final response can summarize the files and
validation.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-10-03 | Latest chapter article paths appear to be chapter 6 `sieve-sequence.md` and chapter 7 `survival-frontiers.md`; related article tickets already exist. | Created this ticket before branch creation and edits. |
| 2026-10-03 | Local `master` exists and is one commit ahead of `origin/master`; the requested branch was created from that local `master`. | Added two side-version detailed guides without editing the canonical articles. |
| 2026-10-06 | "Beginner" could read as critical of the reader, while "detailed" describes the article style. | Renamed the two side-version files to `*-detailed.md` and changed public-facing wording to "detailed companion version." |
| 2026-10-03 | The first draft of the `h = 5` period example was too loose about the canonical endpoint. | Rewrote it to show `l_2 = h + M = 11` and gap cycle `[2, 4]`. |
| 2026-10-03 | The new files have balanced fenced blocks and do not reference tickets. | Completed lightweight Markdown validation; runtime gates are not applicable. |
| 2026-10-03 | User identified a real clarity/style drift in the two latest canonical articles compared with earlier articles. | Extended this ticket from side versions to a canonical clarity pass with arXiv sync awareness. |
| 2026-10-03 | Earlier article style pattern is scope/proof spine, intuition before formulas, source-evidence paragraph, and explicit proof boundary. | Added those patterns to the two canonical articles and synced matching arXiv sections. |
| 2026-10-03 | Both affected arXiv packages rebuild and pass parity after the edits. | Ran `just arxiv-pdf` and `just arxiv-parity` for `sieve-sequence` and `survival-frontiers`. |
| 2026-10-03 | External classical proof inputs should be cited near the derivations that use them. A parallel validation run can race PDF freshness checks. | Added local Hardy--Wright citation prose in chapter 7 §4.3, rebuilt `survival-frontiers`, reran parity after the PDF build, and got PASS. |
| 2026-10-03 | The user's cited formula was an example of a broader issue: bracket labels invoking external classical results need nearby bibliographic support. | Added local citation prose across the remaining Chapter 7 clusters and reran `just arxiv-pdf survival-frontiers` plus `just arxiv-parity survival-frontiers`; both passed. |
| 2026-10-03 | Rendered survival-frontiers page 35 had only a centered figure and excessive whitespace; page 34 had the same float-only pattern. | Reduced and constrained Section 8 Figures 5 and 6 in the arXiv TeX, rebuilt the PDF, visually inspected pages 34-35, and reran parity PASS. |
| 2026-10-03 | Section 8 remained too paragraph-heavy after the citation and chart work. | Split the long Markdown and TeX paragraphs into smaller conceptual blocks and converted the TeX transfer checklist into `itemize`; PDF validation is next. |
| 2026-10-03 | The Survival Frontiers Introduction PDF source had collapsed Markdown lists into inline prose, causing the opening pages to read as large uninterrupted blocks. | Converted the survival-scale list to `enumerate`, the contribution list to `itemize`, added paragraph breaks, fixed one overfull bullet, rebuilt the PDF, visually inspected pages 1-2, and reran parity PASS. |
| 2026-10-03 | The Introduction heatmaps still formed an image-heavy plate when left as floats. | Converted the two intro heatmaps from floating `figure` environments to in-place centered image blocks with fixed-width captions, rebuilt the PDF, inspected pages 2-3, and reran parity PASS. |
| 2026-10-03 | The canonical survival-frontiers math blocks were still missing the earlier articles' direct "what this block proves" / "what this proves afterward" rhythm. | Added concise proof-frame prose around §3.2-§3.4 hazard, normalization, mixture, and fixed-factor calculations; synced TeX, rebuilt PDF, and reran parity PASS. |
| 2026-10-03 | Page 13 still had a single image, so the layout issue needed to become a durable article rule rather than an ad hoc fix. | Added `no-image-only-pages` to `AGENTS.md`, converted the head-threshold chart to a smaller in-place block, inspected page 13, rebuilt the PDF, and reran parity PASS. |
