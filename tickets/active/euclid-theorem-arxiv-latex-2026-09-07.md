# euclid-theorem arXiv LaTeX package

**Created:** 2026-09-07
**Status:** Complete — all sections converted; compile green (11 pages,
zero warnings); parity checked; PDF built
**Branch:** `feature/article/euclid-theorem`
**Depends on:** none (follow-on to the completed `list` / `modulo` /
`integral-cycle` conversions; same method, same house style)

## START HERE

Convert `articles/chapter5/euclid-theorem.md` (*Formal Verification of
Euclid's Theorem on the Infinitude of Primes*, 763 lines) into an arXiv
LaTeX package at `articles/arxiv/euclid-theorem/`, following
`articles/arxiv/CONVERSION_GUIDE.md`.

Section plan (order mirrors the Markdown numbering exactly):

- 00-abstract
- 01-introduction (§1)
- 02-preliminaries (§2, 2.1-2.2)
- 03-proof-strategy (§3, 3.1-3.4 — the four-stage Euclid construction)
- 04-supporting-lemmas (§4, 4.1-4.4)
- 05-verification-status (§5)
- 06-related-work (§6)
- 07-conclusion (§7 Conclusion + §8 Future Work)
- 08-appendix (Appendix A.1-A.3 Scala excerpts + Appendix B verification log)

## Current State

- references.bib: 8 entries (Hamza/Stainless, modulo-viXra, list, integral,
  cycle, integral-cycle, Euclid's Elements, Mathlib infinitude-of-primes).
  Three (integral, cycle, integral-cycle) are cited in the Markdown's
  reference list but never inline-cited in the body text; forced into the
  bibliography via `\nocite` to preserve link parity with the source.
- All 9 section files converted; full document compiles green at 11 pages
  with zero warnings/errors/overfull/underfull boxes.
- Mechanical parity: URL set matches (16 unique links each side, modulo
  the author-block GitHub link living in `main.tex` and the Hamza citation
  URL that's a project-wide bib convention, not a Markdown link);
  identifier counts (`isPrime`, `findSmallestDivisor`, `isCoprime`,
  `primorial`, `\forall`, `\therefore`, `\blacksquare`) all match between
  Markdown and `.tex` sources; math block count is 26 in the Markdown vs
  28 in the `.tex` (the +2 is from splitting two shared-column-blowup
  blocks per the guide's escape hatch, not new content).

## Learning Log

- Two shared-column blowup cases (guide §3): the §3.4 main-theorem block
  and the §4.1 corollary block each had one row whose column-1 content was
  far longer than its neighbors, forcing every row's shared column wide
  and producing overfull hboxes. Fixed by splitting the final
  `\therefore`/tagged conclusion row out into its own `equation*` (inline
  `\quad [Tag]` instead of an `&&` column), matching the "recap list of
  independent one-line identities" escape hatch.
- One row in §4.1 had zero leading `&` (`\operatorname{isPrime}(q)\land
  q\notin P`, only a trailing `&&\text{[tag]}`), so its entire content
  became column 1 — same blowup mechanism from a different cause. Fixed
  by inserting a leading `&` at a natural conjunction boundary
  (`\operatorname{isPrime}(q) &\land q\notin P`), a layout-only change.
- One row in §4.2 (`Composite Smallest Prime Divisor`) was a single very
  long conjunction chain overflowing the line by 103pt; fixed with the
  guide's continuation-row pattern (`\\` + `&\qquad` before the last
  conjunct), content unchanged.
- Three paragraphs mixing prose with several long `\texttt` identifiers
  (source-link sentences ending in "This corollary/property/lemma is
  verified in ...") needed the `{\raggedright ... \par}` wrap from the
  guide; `microtype` alone did not fix them.
- The generated `main.bbl` itself produced an Underfull hbox from a long
  `chapter4/...md` GitHub URL with no good break point. Since `.bbl` is
  generated and not hand-editable, wrapped the `\bibliography{references}`
  call itself in `{\raggedright ... \par}` rather than editing the
  auto-generated file — fixes the same underlying justification issue at
  its call site.
- The Markdown's own `\text{Calc.mod}` vs `\text{mod}` inconsistency
  (three occurrences use the qualified name, all others use bare `mod`)
  looks like a source typo but was preserved verbatim per the "faithful
  conversion" ground rule rather than normalized away.
- The "primorial" identifier count mismatch found during parity checking
  (45 lowercase in Markdown vs 42 in `.tex`) traced to a single instance:
  a Markdown anchor slug (`#31-stage-1-primorial-plus-one-modulo-...`)
  contains the substring as URL-fragment text, not article content; the
  guide's anchor-to-"Section~N.M"-text conversion correctly drops it.
