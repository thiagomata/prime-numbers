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
2. [DONE 2026-09-13] App B redesign v2 (two tables + proof statuses).
3. [DONE 2026-09-13] De-drafting pass (see Learning Log 2026-09-13).
4. Push, PR, merge, attach to v3.0.0 (unchanged).

## Learning Log

| Date | Entry |
|---|---|
| 2026-09-12 | Ticket created. Discovered package was 25% converted (4/16 section files); PDF is a 3-page stub. Plan: finish conversion unit-by-unit. |
| 2026-09-12 | Parity audit (MD `articles/chapter6/gap-dynamics.md` vs `output/pdf/gap-dynamics.pdf`, 35 pp, via PyMuPDF text extraction): PASS. Structure: all 12 sections + subsections (2.1-2.2, 3.1-3.6, 4.1-4.4 + unnumbered "Local Harmful-Excess Notation" and "Scala Verification Foundation..." subsections, 5.1-5.2, 6.1-6.7, 8.1-8.2, 10.1, 11.1) + Appendices A/B/C (C.1-C.6) + References present in same order. Equations: 130 MD ```math blocks vs 134 TeX `equation*` envs — delta fully explained by block splits in §3 (30→33) and §4 (19→20); normalized bodies identical. Prose: ~930 TeX prose lines checked against squashed PDF text; 0 real mismatches (initial misses were all extraction artifacts: subscript reordering, hyphenation, links rendered as hyperlinks not URL text). Tables: App A 3 rows match; App B 72 data rows match with same hrefs. Figures: 3, same order/captions (SVG→PDF). Scala listing verbatim. Two intentional divergences: (1) author block adds https://thiagomata.com/ (absent from MD); (2) App B table: MD header declares 4 cols ("...Investigation chain | Article treatment") but all 72 rows have 3 cells — malformed MD; TeX resolved to 3 cols (Property/Canonical note/Article treatment), effectively renaming col 3. Suggest fixing the MD table header (or accepting the TeX resolution as canonical). |
| 2026-09-12 | App B header FIXED. Root cause: MD header had a data-less "Canonical note" column; project vocabulary (articles/notes/reviewer-notes-aug-2026.md) defines a property's record file as its "canonical note", and that phrase in the table is cell-3 CONTENT ("Canonical note only; no full article section"), so cell 2 is the investigation chain. Fix: MD header 4-col → 3-col `| Property | Investigation chain | Article treatment |` + matching one-word TeX header change + PDF rebuild. Superseded same day by redesign v2 below. |
| 2026-09-12 | App B redesign v2 (user feedback: the 54-fold repeated "not in this article" cell is boilerplate). Final shape — TWO tables: Table 1 "properties left out of this article" (54 rows: Property / Investigation line / Proof status; the blanket reason stated once in the lead-in), Table 2 "properties connected to this article" (18 rows: Property / Connection to this article / Proof status; 6 Appendix-C-supported + 9 collectively-summarized + 3 almost-prime-draft). Proof statuses sourced from each record's own `**Status:**` line (verified: 53 unconditional-proved flavored, 19 conditional families named, 4 partly-proved with open remainder, 1 under external verification). MD + TeX regenerated from one script; PDF rebuilt (36 pp). Build-gate failures hit and fixed: (a) MD table separator row emitted as single-cell `|---|` (fixed to 3-col); (b) TeX generator passed raw MD link `[Name](url)` into `\href` display text → 146 overfull boxes (strip to bare name); (c) r-string `\\raggedright` + missing `\textwidth` units → "Illegal unit of measure" fatal; (d) `[which]` indexing returned one column so `' & '.join` split `\href` per character → "Extra alignment tab" fatal. Final log: 0 Overfull / 0 Underfull / 0 Warning / 0 errors; MD↔PDF parity probes pass (headers, both lead-ins, open-claim row, conditional rows, Appendix-C rows, Bertrand/PNT row, draft rows, no `](http` leak). Remaining known divergence: author-block https://thiagomata.com/ (accepted). |
| 2026-09-13 | De-drafting pass EXECUTED (user: article mixed proved spine with drafted material; move notes to a new draft; non-verification is the default, so drop "not yet Stainless-verified" disclaimers, keep positive verification claims). MD rebuilt from HEAD (98d3a8d7 — overnight user commit already contained the two-table redesign) after a first transform over-matched and mangled formatting; lesson: anchor transforms on blank-line-separated blocks with whitespace-flexible markers, never per-line regex, never rewrite paragraphs without droppers. Results: 16 pointer/disclaimer sites cut with kept sentences preserved; header note, §2.2, App A label/closing, App C intro/notation reworded; §11 draft link → "developed separately"; Appendix B removed. 130 math blocks and all headings intact. TeX mirrored (main.tex proof-status + section-14 unhooked, file kept on disk per never-destroy; 02-05, 06, 07, 08, 09, 11, 13, 15). Package README layout note + tarball refreshed. New draft `articles/draft/draft-gap-dynamics-research-notes.md` receives all moved material. Gates: PDF 36→31 pp, log 0 Overfull/0 Underfull/0 Warning/0 errors; probes pass (no pointers, no `.holds` disclaimers, no research map/Deep-Dive; positive Scala + companion verification kept; all 19 headings; legit §11 open-Type-I sentence kept). |
| 2026-09-13 | Structural (article-ness) review, user-prompted. Verdict: article-shaped — §1 states the organizing principle (complete-period vs square-window); §4/§7/§8/§10/§11 open with explicit backward/forward hand-offs; §6 is a 7-step narrative chain ending in a verdict; §12 recaps. Three defects found and fixed in MD+TeX: (1) §8 intro still said conclusion readable "without external files" and referenced the removed "wider research map" — reworded to "readable on its own" + "exist beyond the article's scope"; (2) §5 was the only main section with no opening bridge — added one (count/certify → signed harmful excess → 5.1 conservation → 5.2 terminal inequality); (3) intro's 16-item property list claimed "dependency order" but lists §6 before its input §5 — claim dropped, list kept (defensible theorem-before-lemma ordering). PDF rebuilt: 31 pp, log 0/0/0/0, probes pass. |

## PR #35 review round (2026-09-13, evening)

- Owner's manual PR review found stray sentence-final "A"s in the built
  PDF. Diagnosis: the de-drafting pass removed "A supplementary
  research/model record is ..." sentences from the TEX sections but left
  the leading article behind — 14 instances across 6 section files
  (03: x5, 04: x4, 05/07/09: x1, 08: x2). The Markdown side was clean in
  every corresponding spot, so this was a tex-only desync invisible to
  the parity content checks. All 14 removed; PDF rebuilt green
  (17:12, zero-warning gate); PDF text layer verified clean.
- `sections/14-appendix-b-research-map.tex` DELETED (owner decision in
  the PR review: "Why are we keeping a MOVED OUT element?"; the
  never-destroy hold is released by that decision). Content remains in
  `articles/draft/draft-gap-dynamics-research-notes.md` (moved same day to
  `articles/notes/gap-dynamics-research-notes.md`); the README
  package listing entry was removed with the file.
- Record correction: the earlier commit message said "source tarball
  refreshed", which overstated it — the committed tarball's main.tex
  predates the ORCID line (verified by extraction). Refresh remains a
  release-time step per the ORCID ticket.
- The parity tool gained a dangling-a tripwire (FAIL-level) from this
  defect class; `just arxiv-parity` is 8/8 PASS after the fixes.
- Standing practice from the owner (2026-09-13): no git history
  rewriting, ever — plain add/commit/push, fix-forward only. The
  research-map deletion landing in the tool commit (0470006f) was
  accepted as-is and disclosed in the next commit message instead of
  being relocated.
