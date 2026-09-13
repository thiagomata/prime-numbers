# Survival Frontiers — promotion from draft to chapter article

**Created:** 2026-09-13
**Branch:** `feature/draft-to-article`
**Depends on:** survival-frontiers-article-review-2026-09-13 (deep audit,
complete); review-draft-articles-2026-08-15 (notes/); arxiv-sync rule;
CONVERSION_GUIDE

## Goal

Promote `articles/draft/draft-adversariality-phase-transition-2-gap-companions.md`
(*Survival Frontiers in Balanced 2-Gap Companion Processes*, 3087 lines) to
a published chapter article with PDF: `articles/chapter7/survival-frontiers.md`
+ `articles/arxiv/survival-frontiers/` package, zero-warning build, parity PASS.

## Strategy

Phase 1 — markdown editing pass in draft/ (one commit each):
1. Front matter: full author name, ORCID, license `../LICENSE`, status date.
2. ~~Coverage-audit requirement: cite the six proved `companions/properties/`
   lemmas by path~~ REVERSED per owner (pattern C: never cite internal notes
   as authority from an article).
3. Internal §N references -> anchored Markdown links (~32, review pattern D).
4. Abstract: attach spatial premise to the square-window claim (item 6.6).
5. Optional: kappa/w consolidation (6.2) — decide later.

Phase 2 — conversion per CONVERSION_GUIDE: move md to chapter7/, build the
arXiv package section by section, `just arxiv-pdf`, `just arxiv-parity`,
.parity-skip for the four master-pinned figure URLs + verify.log quirks.

## Current State

Phase 1 complete (md lives at `articles/chapter7/survival-frontiers.md`).
Phase 2 complete: `articles/arxiv/survival-frontiers/` package built,
`just arxiv-pdf survival-frontiers` zero-warning, `just arxiv-parity
survival-frontiers` full PASS (0 warnings), README.md added (was missing
relative to every other arxiv package), `.parity-skip` holds the 9
master-pinned chart SVG URLs replaced by embedded PDF figures. Full-suite
regression run (`just arxiv-pdf` / `just arxiv-parity` with no article arg)
confirms the other 8 packages are unaffected.

## Open Concerns

- Chapter number 7 is free (chapters 2-6 published).
- File name `survival-frontiers` proposed; confirm at conversion time.
  RESOLVED: package built under this name, parity PASS.
- Appendix A mirrors body proofs — LaTeX edition page count will grow;
  acceptable (proof-record surface, review 6.2 disposition).
- The kappa/w consolidation item (Strategy 1.5) was left undecided in Phase
  1 and never revisited; still open if the owner wants it before publication.

## Next Action

Goal is met: md promoted, arXiv package built, zero-warning, parity PASS.
Nothing is queued to run. Remaining choices are the owner's: whether to
commit/push this work (not done — no commit made per no-unrequested-commits),
whether to resolve the kappa/w consolidation item above, and whether to move
this ticket out of `tickets/active/`.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-09-13 | Owner directive: articles must be self-contained. Generalized into the no-ticket-references rule (AGENTS.md): never cite internal working materials as authority; permitted links are published siblings, verified sources, provenance, external literature. Audit of the draft confirms compliance — only data/candidates CSVs (datasets, not research notes) matched the internal-ish paths. | Rule generalized; Phase 1 self-containment checkpoint PASS. |
| 2026-09-13 | The 2026-09-01 coverage-audit item "cite the companions/properties records by path" is REVERSED: adding those links reintroduced pattern C (internal notes cited as mathematical authority), which the repo ranked as its most severe finding and which the gap-dynamics de-drafting just purged. The article's own appendix proofs are the authority; the companion records stay working notes. | Record-citation sentences removed from A.1-A.4, A.6, and 5.1; zero companions/properties links remain. |
| 2026-09-13 | Pattern D (bare §N refs) was ALREADY satisfied — 35/35 in-file refs linked during the post-audit revision. The only bare §s were inside cross-article link labels ("[Gap Dynamics §5.2](url)"), where plain text is correct. A regex sweep without a link-text exclusion corrupted 4 of them into nested links (partial §5 match of §5.2). | Repaired all 4 on retry; verified working tree identical to HEAD; lesson: exclude `\[...\]\(...\)` spans before any ref rewriting, and never rewrite what link labels intentionally contain. |
| 2026-09-13 | First `just arxiv-pdf` pass failed the zero-warning gate: one mismatched-column `aligned` block (extra alignment point widened a row) and four `longtable`s (one unbounded `lll`, three `p{}` tables whose widths, or missing `\raggedright` on one column, exceeded textwidth once tabcolsep overhead is counted). | Collapsed the mismatched row into the house LHS/RHS/tag shape; resized/added `\raggedright\arraybackslash` on every `p{}` column consistent with the article's own established table pattern. Zero-warning build achieved; all 4 fixed tables visually verified via ghostscript render (no clipping/overflow). |
| 2026-09-13 | `just arxiv-parity` failed 2 real checks the build log can't see: (1) `sections/00-abstract.tex` used `\section{Abstract}` instead of the house `\begin{abstract}...\end{abstract}` (only package among 9 doing this), permanently failing the headings bidirectional check; (2) the shared `dangling-a` tripwire (`python/tools/arxiv_parity.py`) false-positived on 5 legitimate "A **term**" / "A \textbf{term}" sentence-starts — its continuation-allowed character class didn't include `\textbf{`/`\emph{`/`**`, only bare `[A-Za-z{]`. Also: README.md was missing (every other of the 8 packages has one), and the bibliography's bare `doi = {...}` field renders no visible/clickable DOI under `\bibliographystyle{plain}` (confirmed visually) — sieve-sequence's convention of `note = {\url{https://doi.org/...}}` was the fix, not a parity-skip workaround. | Fixed abstract env; extended `DANGLING_ARTICLE` regex (with a same-line vs blank-line distinction preserving the existing surgery-leftover test) + added test coverage in `python/tests/test_arxiv_parity.py` (30/30 pass); added README.md from the gap-dynamics template; added `note` fields with `\url{}` DOIs to `references.bib`; added `.parity-skip` for the 9 chart-SVG URLs replaced by embedded PDF figures (parallel to gap-dynamics' 3-entry skip file). Full parity PASS, 0 warnings. Full-suite `just arxiv-pdf`/`just arxiv-parity` regression (all 8 other packages) confirmed unaffected; reverted the other packages' incidentally-rebuilt output PDFs (byte-identical content, only embedded-timestamp churn) to keep the diff scoped. |
