# Gap-Dynamics arXiv LaTeX Conversion — Finish Sections 04-15

## Goal

Complete the in-progress LaTeX conversion of
`articles/chapter6/gap-dynamics.md` (2,284 lines, 12 sections + references +
3 appendices) into `articles/arxiv/gap-dynamics/`, then rebuild the full PDF
and source tarball, add the missing package README, commit unit-by-unit on
`feature/article/gap-dynamics` (synced with master), PR, merge, and attach
the complete PDF + tarball to release v3.0.0 (updating notes to eight
articles).

## Strategy

Follow the unit-by-unit conversion precedent (integral-cycle ticket:
"convert unit NN" commits). Convert each MD section to its
`sections/NN-*.tex` file as pre-declared by main.tex's `\IfFileExists`
skeleton. Follow `articles/arxiv/CONVERSION_GUIDE.md` conventions and the
style already established by the 4 existing converted sections
(00-abstract, 01-introduction, 02-preliminaries,
03-complete-period-two-gap-properties).

## Current State

- 2026-09-12 (post-completion audit): all 16 section files exist; PDF is
  35 pages (not the 3-page stub). A full MD-vs-PDF parity audit found the
  conversion faithful — see Learning Log 2026-09-12 entries. The App B
  malformed-table header was fixed in MD + TeX and the PDF rebuilt;
  the only remaining known divergence is the author-block
  https://thiagomata.com/ addition (accepted).
- Branch `feature/article/gap-dynamics` synced with master (merge commit,
  unpushed). Working tree on the branch.
- Existing converted: 00, 01, 02, 03 (PDF stub: 3 pages).
- Remaining units (main.tex order):
  - 04-local-certification.tex (MD §4, lines 640-936)
  - 05-weighted-harmful-excess-survival.tex (MD §5, lines 937-1070)
  - 06-why-capacity-envelope-exhausted.tex (MD §6, lines 1071-1219)
  - 07-exact-filter-seven-localization.tex (MD §7, lines 1220-1341)
  - 08-open-estimates.tex (MD §8, lines 1342-1451)
  - 09-copy-block-harmful-excess.tex (MD §9, lines 1452-1606)
  - 10-routes-classified.tex (MD §10, lines 1607-1676)
  - 11-almost-prime-program.tex (MD §11, lines 1677-1729)
  - 12-conclusion.tex (MD §12, lines 1730-1805)
  - References (MD lines 1806-1810; bib has 1 entry)
  - 13-appendix-a-evidence-status.tex (MD lines 1811-1836)
  - 14-appendix-b-research-map.tex (MD lines 1837-1919)
  - 15-appendix-c-proofs.tex (MD lines 1920-2284)
- references.bib: only mata2026sievesequence (master link, level 4 — correct).
- pdfauthor already correct (Thiago Henrique Ramos da Mata).
- Package README.md: missing (all other 7 packages have one).
- Source tarball: not built yet.

## What is Learned

- main.tex uses `\IfFileExists` guards, so partial builds silently skip
  missing sections — the 248 KB PDF stub only contains Intro + Preliminaries.
- Conversion style template: the 4 existing sections + CONVERSION_GUIDE.md.
- The other agent's MD is still evolving (its WIP edits committed on
  feature/tickets); conversion targets the CURRENT merged MD on this branch.

## Failed Paths

(none yet)

## Open Concerns

- MD §4 includes an unnumbered heading "Local Harmful-Excess Notation"
  between 4.4 and §5 — must map to a subsection in 04-local-certification.tex.
- Section 3's existing conversion used \texorpdfstring for inline code in
  headings — follow that pattern.
- Release v3.0.0 currently says "seven articles" — must update notes after
  attaching the eighth.
- The other agent's untracked file
  properties/sieve-sequence/pre-final-filter-twin-semiprime-decomposition.md
  is in the working tree — DO NOT commit it with the gap-dynamics work.

## Next Action

1. [DONE 2026-09-12] Parity audit + App B header fix (see Learning Log).
2. App B redesign (user-approved): reshape table to
   `Property | Why it is outside this article | Proof status` —
   per-row reason derived from research line + disposition; proof status
   pulled from each linked record's own `**Status:**` line (all 72 records
   resolved; conditions named at the granularity the records assert:
   53 unconditional-proved flavored, 19 conditional flavored, 4 partly
   proved/open parts, 1 under external verification). Intro rewritten to
   state the blanket rationale + status vocabulary. Mirror in TeX
   (longtable widths), rebuild PDF, validate parity.
3. Push, PR, merge, attach to v3.0.0 (unchanged).

## Learning Log

| Date | Entry |
|---|---|
| 2026-09-12 | Ticket created. Discovered package was 25% converted (4/16 section files); PDF is a 3-page stub. Plan: finish conversion unit-by-unit. |
| 2026-09-12 | Parity audit (MD `articles/chapter6/gap-dynamics.md` vs `output/pdf/gap-dynamics.pdf`, 35 pp, via PyMuPDF text extraction): PASS. Structure: all 12 sections + subsections (2.1-2.2, 3.1-3.6, 4.1-4.4 + unnumbered "Local Harmful-Excess Notation" and "Scala Verification Foundation..." subsections, 5.1-5.2, 6.1-6.7, 8.1-8.2, 10.1, 11.1) + Appendices A/B/C (C.1-C.6) + References present in same order. Equations: 130 MD ```math blocks vs 134 TeX `equation*` envs — delta fully explained by block splits in §3 (30→33) and §4 (19→20); normalized bodies identical. Prose: ~930 TeX prose lines checked against squashed PDF text; 0 real mismatches (initial misses were all extraction artifacts: subscript reordering, hyphenation, links rendered as hyperlinks not URL text). Tables: App A 3 rows match; App B 72 data rows match with same hrefs. Figures: 3, same order/captions (SVG→PDF). Scala listing verbatim. Two intentional divergences: (1) author block adds https://thiagomata.com/ (absent from MD); (2) App B table: MD header declares 4 cols ("...Investigation chain | Article treatment") but all 72 rows have 3 cells — malformed MD; TeX resolved to 3 cols (Property/Canonical note/Article treatment), effectively renaming col 3. Suggest fixing the MD table header (or accepting the TeX resolution as canonical). |
| 2026-09-12 | App B header FIXED. Root cause: MD header had a data-less "Canonical note" column; project vocabulary (articles/review/reviewer-notes-aug-2026.md) defines a property's record file as its "canonical note", and that phrase in the table is cell-3 CONTENT ("Canonical note only; no full article section"), so cell 2 is the investigation chain. Fix: MD header 4-col → 3-col `| Property | Investigation chain | Article treatment |` + matching one-word TeX header change + PDF rebuild. Superseded same day by redesign v2 below. |
| 2026-09-12 | App B redesign v2 (user feedback: the 54-fold repeated "not in this article" cell is boilerplate). Final shape — TWO tables: Table 1 "properties left out of this article" (54 rows: Property / Investigation line / Proof status; the blanket reason stated once in the lead-in), Table 2 "properties connected to this article" (18 rows: Property / Connection to this article / Proof status; 6 Appendix-C-supported + 9 collectively-summarized + 3 almost-prime-draft). Proof statuses sourced from each record's own `**Status:**` line (verified: 53 unconditional-proved flavored, 19 conditional families named, 4 partly-proved with open remainder, 1 under external verification). MD + TeX regenerated from one script; PDF rebuilt (36 pp). Build-gate failures hit and fixed: (a) MD table separator row emitted as single-cell `|---|` (fixed to 3-col); (b) TeX generator passed raw MD link `[Name](url)` into `\href` display text → 146 overfull boxes (strip to bare name); (c) r-string `\\raggedright` + missing `\textwidth` units → "Illegal unit of measure" fatal; (d) `[which]` indexing returned one column so `' & '.join` split `\href` per character → "Extra alignment tab" fatal. Final log: 0 Overfull / 0 Underfull / 0 Warning / 0 errors; MD↔PDF parity probes pass (headers, both lead-ins, open-claim row, conditional rows, Appendix-C rows, Bertrand/PNT row, draft rows, no `](http` leak). Remaining known divergence: author-block https://thiagomata.com/ (accepted). |
