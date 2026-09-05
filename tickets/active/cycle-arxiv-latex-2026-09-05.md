# cycle arXiv LaTeX package + release

**Created:** 2026-09-05
**Updated:** 2026-09-06
**Status:** Complete — package green and arXiv-ready; author-requested
conclusion tag alignment applied after the first release commit; release
commit and tag `cycle-article-v1.0.0` re-cut at the final state (push
pending)
**Branch:** `feature/article/cycle`
**Depends on:** none (follow-on to the completed `list-arxiv-latex` /
`list-arxiv-release-v1` and `modulo-arxiv-latex` / `modulo-arxiv-release-v1`
pairs; same conversion method and release flow)

## START HERE

Convert `articles/chapter4/cycle.md` (*Formal Verification of Cyclic Lists*)
into an arXiv LaTeX package at `articles/arxiv/cycle/`, following
`articles/arxiv/CONVERSION_GUIDE.md`. Scope (author-approved, two-stage in
one session):

- **Stage 1 — LaTeX:** convert all 8 section files, one logical unit per
  compile cycle, `blob/master/` links, zero-warning gate, parity audit,
  clean-room archive.
- **Stage 2 — Release:** `just verify-ch 4`, force-add the pinned log, cut
  tag `cycle-article-v1.0.0`, scripted link re-pin, Appendix B
  reproducibility statement, rebuild + clean-room verify, commit, push
  branch + tag (mirrors `list-arxiv-release-v1-2026-09-04.md` exactly).

## Related Tickets

- `list-arxiv-latex-2026-09-04.md`, `list-arxiv-release-v1-2026-09-04.md`
  — most recent successful pair; same two-stage flow, same tag-pinning.
- `modulo-arxiv-latex-2026-09-02.md`, `modulo-arxiv-release-v1-2026-09-03.md`
  (archived) — original conversion; parity-audit row-level lesson.
- `list-cite-modulo-doi-2026-09-05.md` (future) — DOI citation follow-up
  pattern once companion articles get arXiv DOIs.

## Survey (baseline numbers for parity)

- Source: `articles/chapter4/cycle.md`, 1333 lines, clean tree.
- Sections: 8 numbered (Intro+Related work, Preliminaries, Cycle
  Definitions 3.1–3.3, Cycle Equivalence 4.1–4.2, Cycle Properties
  5.1–5.12, Conclusion, Future Work) + References + Appendix A (10 Scala
  excerpts) + Appendix B (verification log).
- 67 math blocks, 14 scala blocks (3 inline main-text + 10 appendix + 1
  inline in 5.6), 20 unique GitHub links, 5 bib entries.
- One Mermaid classDiagram in §3 (no prior precedent — resolved by
  rendering to PNG via `npx @mermaid-js/mermaid-cli`, see below).

## Section file plan

```text
00-abstract  01-introduction (+related work)  02-preliminaries
03-cycle-definitions (3.1–3.3, incl. class figure)  04-cycle-equivalence (4.1–4.2)
05-cycle-properties (5.1–5.12, grown in groups)
06-conclusion (+future work)  07-appendix (A.1–A.10 + B)
```

## Conventions (from CONVERSION_GUIDE.md + list/modulo learnings)

- Frozen Markdown edition; `\operatorname` normalization (applied
  functions only; bare field names stay `\text{}`); 𝕊/𝕃/ℕ/ℤ →
  `\mathbb{...}`; `\therefore` chains; `\quad \blacksquare\ \text{[Q.E.D.]}`;
- plain `\input` assembly (already in main.tex, matches list end state);
  `microtype`; lstlisting `style=scala` on every excerpt;
- **Alignment house style:** premise+equation → flush-left leading `&`;
  single-row + tag → `\quad` hug (never `&&` on single row); multi-row
  tags → `&&` column; **Conclusion recap blocks → independent
  `equation*` per identity with inline tag** (list's shared-`aligned`
  column-width blowup); **grep-sweep at the end for multi-row `aligned`
  with zero `&`** (list found 18 latent right-shifted rows);
- long `MemCycleProperties::...` links paragraph (§5.9) → scoped
  `{\raggedright ... \par}` + `\allowbreak`;
- **`\#` only in `\href` display text, never the URL argument** — catch
  by URL-set diff, invisible in the log (list caught 2 broken links);
- compile after every unit; zero-warning gate: `Warning|Error|Overfull|
  Underfull|undefined|Missing`; ghostscript render with `-%02d` page
  patterns (poppler absent);
- parity audit row-level: math blocks AND quantifier/premise rows within
  blocks (modulo's author caught 2 dropped rows); URL-set diff;
  byte-identical scala excerpts; `\blacksquare` count;
- bib ready up front (5 entries, brace-protected titles) — `\cite`
  directly, no `[N]` placeholder stage;
- **Release stage:** `just verify-ch 4` local only (no Docker paragraph —
  list dropped it); force-add pinned log (gitignored otherwise, §23.4);
  `git rev-parse <tag>^{commit}` check before pushing (§23.5); one tag
  per package; never move a pushed tag.

## Goal

Produce a faithful, warning-free LaTeX edition of
`articles/chapter4/cycle.md`, visually verify its compiled PDF and clean-room
arXiv source archive, then complete the approved release flow with a pinned
Chapter 4 verification log and tag `cycle-article-v1.0.0`.

## Strategy

Follow the proven `list` conversion and release sequence. Treat the Markdown as
the frozen source edition, convert one logical unit per compile-and-visual-check
cycle, and finish with mechanical parity checks and a clean-room archive build.
Only after the LaTeX package is complete and green will the release stage run
Chapter 4 verification and replace moving `blob/master/` links with tag-pinned
links.

## Current State

- Branch `feature/article/cycle` active. Third session on this ticket: the
  scaffolding agent died pre-conversion; the conversion agent completed all
  content and pinning, then died at the post-pinning underfull fix; the
  current session re-verified every claim against the tree before resuming.
- `main.tex` (89 lines) assembled with plain `\input` — metadata,
  Scala listing style, license block match list/modulo shape.
- `references.bib` — 5 entries (mata2026lists, mata2026integral,
  mata2026modulo, leanmathlibrotate, hamana2017cyclic), ready.
- No section file remains a placeholder stub. Appendix A.1--A.10 is fully
  converted; Sections 0--5, Conclusion, and Future Work are fully converted,
  including Cycle Definitions, its source excerpts and class diagram and both
  Cycle Equivalence proof subsections. Appendix B is also complete with fresh
  Chapter 4 verification totals.
- Link pinning is DONE: exactly 53 `blob/master/` URLs replaced with
  `blob/cycle-article-v1.0.0/` (50 in main.tex + sections, 3 in
  references.bib); zero moving links remain anywhere in the package, and
  Appendix B already identifies the immutable tag.
- **Conclusion tag alignment (author request, post-release-commit):** the
  four tagged recap groups were converted from `gathered` with inline
  `\quad \text{[Tag]}` to `aligned` with `&&\text{[Tag]}` columns, so the
  tags align vertically within each group (the definitions block and the
  single-row Three-Way Equivalence line are unchanged — single-row `&&`
  is the documented floating-tag antipattern). Gates green: zero-warning
  rebuild, math parity preserved at exactly 6 displays, conclusion recap
  fits on one page (page 16; References moved to page 17), archive
  regenerated and clean-room verified (text and all 22 raster pages
  identical to the tracked PDF).
- **Underfull regression RESOLVED:** one preamble line was added to
  `main.tex` after `\usepackage{hyperref}` — `\Urlmuskip=0mu plus 1mu\relax`
  — allowing justified bibliography lines containing the long pinned URLs
  to stretch. No content or link target changed. The rebuilt 22-page PDF
  passes the zero-warning gate (final `main.log` has zero
  Warning/Error/Overfull/Underfull/undefined/Missing) and the bibliography
  page (page 16, all five entries) was visually inspected: URLs break
  cleanly with normal spacing. The earlier xurl fallback was not needed.
- Per-unit conversion history (exact parity and visual review for every
  section batch) is preserved in the Learning Log below.
- A fresh `just verify-ch 4` run completed successfully with 2,995 valid,
  0 invalid, and 0 unknown verification conditions. Verified against the log
  itself (2026-09-05 21:27): `total: 2995 valid: 2995 (2990 from cache,
  5 trivial) invalid: 0 unknown: 0`, covering
  `src/main/scala/v1/chapter4/` sources — the log is related to the
  described tests and matches Appendix B's totals exactly.
- Full-package parity is green: 67/67 math blocks, 14/14 Q.E.D. markers,
  14/14 byte-identical Scala excerpts, 5/5 bibliography entries cited, and
  one rendered class diagram. The three-heading count delta is fully
  explained by the document title, abstract environment, and generated
  References heading.
- Added the package `README.md` matching the list/modulo contract.
- `output/arxiv-cycle-source.tar.gz` regenerated from the green sources
  (fresh `main.bbl`, 2026-09-06 00:39) per the README recipe, and
  clean-room verified: extracted to a fresh temp directory, compiled from
  INSIDE it — exit 0, 22 pages, zero final-log issues — with extracted
  text and all 22 rasterized pages identical to the tracked PDF.
- `figures/cycle-classes.png` rendered (2508×2088, scale 4, white bg)
  from `figures/cycle-classes.mmd` via `npx -y @mermaid-js/mermaid-cli`
  (mermaid export approach chosen by the author; verified visually —
  three class boxes + two relations). `main.tex` includes
  `\usepackage{graphicx}` for the figure.
- Stray dead-agent artifacts at repo root: `sections/` (8 empty files)
  and `references.bib` (empty). Author will delete them (`rm -r sections
  references.bib` at repo root) — `rm` is blocked for agents.

## What is Learned

- Full trap digest compiled from list/modulo tickets +
  CONVERSION_GUIDE.md + LEARNINGS.md §14/§23 — see Conventions above;
  every pitfall is to be applied proactively (list converted a 2.3x
  larger article with most units compiling clean on the first or second
  try after reading the full source up front).
- Mermaid → PNG via `npx -y @mermaid-js/mermaid-cli -i in.mmd -o
  out.png -s 4 -b white` works without a global install (downloads once);
  output verified by visual inspection.
- `just arxiv-pdf cycle` recipe exists; `latexmk` + `gs` available;
  poppler absent (use `gs -sDEVICE=png16m` / `txtwrite`).
- With a persistent latexmk scratch directory, the console can show transient
  first-pass BibTeX/citation warnings from stale auxiliary state even when the
  final pass is clean. The zero-warning gate is the final `main.log`, not an
  earlier pass printed in the combined console output.
- A Markdown math fence containing both an `aligned` definition and a trailing
  quantifier can remain one LaTeX display without bad alignment by wrapping the
  inner `aligned` and quantifier row in `gathered`.
- Inline code-style mathematical summaries can be normalized to math notation
  when PDFLaTeX cannot faithfully render a Unicode operator; using `\cdot`
  preserves the source's multiplication dot instead of substituting `*`.
- The Markdown conclusion's statement that "all properties" were formally
  verified conflicts with Subsections 5.10--5.12, which explicitly identify
  the residue transfers as article-level corollaries rather than separate
  Stainless lemmas. The LaTeX conclusion must preserve the results while
  stating this verification boundary accurately.
- The zero-warning gate is per-change, not per-section: the "mechanical"
  53-link pinning changed bibliography line breaking and broke the gate.
  Tree evidence (final `main.log`, PDF timestamp) is ground truth over
  ticket prose; the ticket's clean-log claim described the pre-pinning
  build (TICKET_DISCIPLINE §6).
- Underfull hboxes from long `\url`s in a BibTeX-generated `.bbl` are a
  packaging defect, not a content defect. Standard cures, in minimality
  order: `\Urlmuskip=0mu plus 1mu\relax` (uses the already-loaded
  url/hyperref machinery) or `\usepackage{xurl}` (standard package, breaks
  URLs anywhere; verified available in the local TeX Live 2025 and
  arXiv-safe).

## Failed Paths

(ticket-specific failures first, then the inherited do-not-retry list:)
- **Treating the 53-link pinning as a gate-free mechanical change:** the
  replacement itself was exact, but the longer pinned URLs changed
  bibliography line breaking, producing three underfull boxes and a 22-page
  reflow on the next rebuild. Reason: `\url` in the generated `main.bbl`
  could no longer fill justified lines. Verdict flip: nothing to flip — the
  pinning stands and must not be reverted; the lesson is that the
  zero-warning gate re-runs after every change, including scripted
  replacements.
- A broad ticket-normalization patch failed before changing any file because
  its context accidentally included a line from the modulo ticket. Retry only
  from freshly read cycle-ticket context; no new ingredient is otherwise
  required.
- Compiling the empty scaffold as a baseline cannot meet the zero-warning gate:
  unconditional bibliography assembly with no citation commands produces a
  BibTeX error and an empty-`thebibliography` warning. Retry only after the
  citation-bearing Introduction exists; that corrected path is now green.
- Splitting Section 2's slice-definition fence and its trailing quantifier into
  two `equation*` displays rendered cleanly but failed the mechanical block
  parity gate (13 versus 12). Use one `gathered` display; retrying that way
  restored 12-to-12 parity.
- Section 4's first build overflowed both long
  `RecursiveCycleMatchesModCycle` link labels and emitted PDF-bookmark warnings
  for math in subsection titles. Scoped ragged-right breakpoints and
  `\texorpdfstring` fixed the same file. A subsequent visual/parity pass caught
  a shortened proof annotation; restoring its exact wording in a compact
  `\substack` kept the final build green.
- The first 5.7--5.9 build had two overfull paragraphs: the long
  `RecursiveCycle::cycleValueBiggerThan` link and the paragraph containing
  `MemCycle.checkMod(d)`. Scoped `\raggedright` around only those paragraphs
  preserved their content and restored the zero-warning/overflow gate.
- The first visual-review lookup for PDF pages 10--12 used filenames
  `page-10.png` through `page-12.png`, but Ghostscript renumbered the selected
  range from `page-01.png`. No artifact was affected; listing the render
  directory and inspecting `page-01.png` through `page-03.png` completed the
  review. Use Ghostscript's sequential output names for future page ranges.
- The first Appendix A byte-comparison command counted the first five Scala
  fences in the whole article, so it compared earlier main-text examples
  against A.1--A.5 and produced an irrelevant diff. Scoping the Markdown
  extractor after `## Appendix A` produced an empty diff; use that scope for
  all appendix byte audits.
- The first A.6--A.10 insertion patch matched the file's first
  `\end{lstlisting}`, placing A.6 immediately after A.1. This was caught before
  compilation. The first generated move patch then failed safely because its
  context collapsed the blank line before A.2. A second move built from exact
  line-array boundaries restored A.1--A.10 source order; use a unique trailing
  anchor or explicit file-end context for future append operations.
- The first attempt to update the ticket from "first three" to "first six"
  properties accidentally supplied identical old and new text, producing a
  no-op. A one-word same-target retry corrected the state; verify ticket
  wording with `rg` after status edits.
- Row-by-row overfull patching inside a shared `aligned` — restructure
  instead (list).
- Docker reproduction in Appendix B — cite local run only (list).
- Direct `stainless` invocation outside `just verify-ch` — Dotty crash
  (list release).
- The first clean-room command invoked `latexmk` with an absolute `main.tex`
  path while remaining in the repository root. TeX resolved relative inputs
  against that working directory and produced a one-page shell. Re-running
  from inside the extracted archive directory produced the complete clean
  document; clean-room checks must change directory before compilation.

## Open Concerns

- `logs/verify-ch-4-v1-chapter4-_.log` is gitignored; without `git add -f`
  the tag-pinned Appendix B link 404s (LEARNINGS §23.4).
- Stray root `sections/` and `references.bib` still await author deletion;
  commit staging must be scoped to exclude them.
- Push of branch + tag: author has not yet said who executes it.

## Next Action

Commit the conclusion tag-alignment change (scoped: `06-conclusion.tex`,
the regenerated `output/` artifacts, this ticket, the guide note), delete
and re-create the never-pushed tag `cycle-article-v1.0.0` at the new
commit, verify with `git rev-parse`, then push branch + tag. The author
reviews the package and performs the actual arXiv submission themselves.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-09-05 | Ticket re-founded after previous agent died post-scaffold. Read cycle.md end-to-end (1333 lines), both prior conversion tickets, the release tickets, CONVERSION_GUIDE.md, and LEARNINGS.md §14/§23. Author approved two-stage scope (LaTeX then release) and mermaid-as-rendered-image for the §3 class diagram. | Render the diagram, then convert unit 1 (abstract + introduction). |
| 2026-09-05 | Rendered `cycle-classes.png` (scale 4, white background) from the extracted mermaid via `npx -y @mermaid-js/mermaid-cli`; verified visually. Stray root artifacts identified for author deletion. | Update main.tex with `graphicx` when unit 3 (definitions) lands; start unit 1. |
| 2026-09-05 | Reconciled the ticket against the current tree. Its live-state sections were already present; only Goal and Strategy were missing. One overly broad patch failed safely because it contained stale context copied from the modulo ticket. | Establish the existing skeleton's LaTeX baseline, then convert unit 1. |
| 2026-09-05 | The empty scaffold exposed an unavoidable empty-bibliography warning, so the red-cascade retry converted only the citation-bearing Introduction and Related work. The final two-page build has zero log issues; both pages render cleanly apart from the intentionally untouched abstract placeholder. | Convert only the abstract, rebuild, and inspect page 1. |
| 2026-09-05 | Converted the abstract faithfully. The two-page build remains free of final-log issues, and page 1 renders cleanly with the placeholder removed. | Convert Section 2, Preliminaries. |
| 2026-09-05 | Converted all of Section 2. The first draft was visually clean but split one Markdown math fence into two displays; a same-file correction used `gathered` and restored exact 12-to-12 block parity. The four-page build has zero final-log issues, and all affected pages were visually inspected. | Convert Section 3 and wire in the existing class-diagram PNG. |
| 2026-09-05 | Added explicit `graphicx` support and converted all of Section 3. The seven-page build is clean; parity is 3 math/3 listings/1 image, and visual review confirms the class diagram and source excerpts render correctly. | Convert Section 4, Cycle Equivalence. |
| 2026-09-05 | Converted all of Section 4. The first build exposed bookmark warnings and two long-link overflows; a same-file correction fixed both. Final review restored one proof annotation that had been shortened for layout. The eight-page build is clean, math parity is 4-to-4, and all Section 4 pages were inspected. | Grow Section 5 in property groups, beginning with 5.1--5.3. |
| 2026-09-05 | Converted the Section 5 overview and Subsections 5.1--5.3. The ten-page build is clean, math parity is exactly 10-to-10, and all three affected pages were visually inspected. A one-line fidelity correction replaced an interim asterisk with the source's multiplication dot and remained green. | Add Subsections 5.4--5.6, including the repeated-cycle Scala excerpt. |
| 2026-09-05 | Converted Subsections 5.4--5.6. The twelve-page build is clean, parity is exactly 9-to-9 math displays and 1-to-1 Scala listing, and pages 10--12 were visually inspected. The first inspection lookup used original page numbers although Ghostscript emitted a sequence starting at 01; listing the directory resolved it without changing the artifact. | Add Subsections 5.7--5.9. |
| 2026-09-05 | Converted Subsections 5.7--5.9. The first build exposed two paragraph overflows; scoped ragged-right formatting fixed only those sites. The final fourteen-page build is clean, parity is exactly 10-to-10 math displays with no Scala listings, and pages 12--14 were visually inspected. | Add Subsections 5.10--5.12, completing Section 5. |
| 2026-09-05 | Converted Subsections 5.10--5.12, completing all twelve Cycle Properties. The sixteen-page build is clean, parity is exactly 12-to-12 math displays with no Scala listings, and pages 14--16 were visually inspected. The text preserves that these transfers are article-level corollaries of verified base-list facts rather than separate Stainless lemmas. | Convert Conclusion and Future Work. |
| 2026-09-05 | Converted Conclusion and Future Work. The seventeen-page build is clean, parity is exactly 6-to-6 math displays, and pages 15--17 were visually inspected. The Markdown's overbroad "all properties" sentence was corrected so the conclusion agrees with the body's explicit Stainless/corollary boundary. | Convert Appendix A verification excerpts, beginning with A.1--A.5. |
| 2026-09-05 | Converted Appendix A.1--A.5. The nineteen-page build is clean, five Markdown Scala fences match five LaTeX listings byte-for-byte, and pages 17--19 were visually inspected. The first diff was incorrectly scoped to the article's earliest fences; an Appendix-A-scoped extraction returned no differences. | Convert Appendix A.6--A.10. |
| 2026-09-05 | Converted Appendix A.6--A.10 and restored the initially misplaced block to source order before compiling. The twenty-one-page build is clean, all ten Appendix A listings are byte-identical to the Markdown fences, and pages 19--21 were visually inspected. | Run Chapter 4 verification and complete Appendix B. |
| 2026-09-05 | Fresh `just verify-ch 4` completed with 2,995 valid, 0 invalid, and 0 unknown conditions. Added Appendix B with the command, toolchain, totals, and current chapter-log link; the twenty-one-page PDF remains clean and page 21 was visually inspected. | Run global parity and clean-room archive checks, then pin links during release. |
| 2026-09-05 | Full parity audit passed (67 math blocks, 14 Q.E.D. markers, 14 byte-identical Scala excerpts, five cited bibliography entries, one diagram). Added the missing package README and image-aware archive recipe. The first clean-room invocation ran from the wrong working directory and produced a one-page shell; the same-target retry from inside the extracted archive produced all 21 pages with zero issues and identical text/raster output. | Pin links, rebuild, commit, tag, and push the approved release. |
| 2026-09-05 | Release pinning unit completed: exactly 53 links pinned to `cycle-article-v1.0.0` (50 tex + 3 bib), Appendix B identifies the tag, archive rebuilt with pinned sources. Its post-build FAILED the gate: three underfull boxes in the generated bibliography and a 22-page reflow. The conversion agent died at this fix step. | Fix bibliography URL line-breaking, then re-gate. |
| 2026-09-06 | Handoff re-verification (third session): all content, parity, pinning, and fresh-verify claims confirmed against the tree; the Chapter 4 log's totals (2995 valid / 0 invalid / 0 unknown, chapter4 sources) match Appendix B; the ticket's clean-log claim was found stale (pre-pinning build); the on-disk archive is current-with-red-state (53 pinned links inside). Ticket corrected to the real state. | Resume at the underfull fix. |
| 2026-09-06 | Applied the minimal URL-breaking fix: `\Urlmuskip=0mu plus 1mu\relax` after hyperref in `main.tex` (one line, no content/link change). Rebuild green: 22 pages, zero Warning/Error/Overfull/Underfull/undefined/Missing in the final log; bibliography page 16 visually verified (all five entries, URLs wrap cleanly). The xurl fallback was not needed. | Regenerate the archive and clean-room verify. |
| 2026-09-06 | Regenerated `arxiv-cycle-source.tar.gz` per the README recipe with the fresh `main.bbl`; clean-room compile from inside the extracted directory: exit 0, 22 pages, zero log issues; extracted text and all 22 rasterized pages identical to the tracked PDF. Package is arXiv-ready. | Run the release sequence (force-add log, commit, tag, push). |
| 2026-09-06 | Promoted the pinning-underfull lesson to `CONVERSION_GUIDE.md` §4 (pinned URLs lengthen `.bbl` entries; gate re-runs after scripted replacements; `\Urlmuskip` cure). Staged the release per the list convention: verify log force-added (gitignored), package with tracked `output/` artifacts, both ticket files, root strays excluded; commit + annotated tag `cycle-article-v1.0.0` ("cycle article v1.0.0: arXiv-ready manuscript, links pinned, verification reproduced (2995/2995/0/0)"), tag commit verified with `git rev-parse`. | Push branch + tag; author reviews and submits to arXiv. |
| 2026-09-06 | Author requested aligned conclusion tags. Converted the four recap groups from `gathered` + inline `\quad` tags to `aligned` + `&&\text{[Tag]}` columns (definitions block and single-row equivalence line unchanged). Gates green: zero-warning rebuild, 6/6 display parity, recap on one page, References moved 16→17; archive regenerated, clean-room text/raster identical. Follow-up commit will land and the unpushed tag will be re-cut at the final commit (safe per §23.5 — never pushed). | Commit the alignment change, re-point `cycle-article-v1.0.0`, then push. |
