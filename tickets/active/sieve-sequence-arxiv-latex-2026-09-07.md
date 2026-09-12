# sieve-sequence arXiv LaTeX package

**Created:** 2026-09-07
**Status:** Complete — all sections converted; compile green (15 pages,
zero warnings); parity checked; PDF built
**Branch:** `feature/article/sieve-sequence`
**Depends on:** none (follow-on to the completed `list` / `modulo` /
`integral-cycle` / `euclid-theorem` conversions; same method, same house
style)

## START HERE

Convert `articles/chapter6/sieve-sequence.md` (*Formal Verification of
Sieve Sequence Stages and Their Transitions*, 945 lines) into an arXiv
LaTeX package at `articles/arxiv/sieve-sequence/`, following
`articles/arxiv/CONVERSION_GUIDE.md`.

Section plan (order mirrors the Markdown numbering exactly):

- 00-abstract
- 01-introduction (§1)
- 02-preliminaries (§2, 2.1-2.4 — includes the hit/miss-matrices figure)
- 03-linear-stage-semantics (§3, 3.1-3.2)
- 04-period-and-cycle-reconstruction (§4, 4.1-4.3)
- 05-installing-current-head-as-filter (§5, 5.1-5.4, incl. 5.2.1-5.2.3
  with three inline Scala excerpts)
- 06-next-stage (§6, 6.1-6.4)
- 07-exact-proof-boundary (§7)
- 08-open-proof-work (§8)
- 09-conclusion (§9)
- no separate Appendix — this article's code excerpts live inline in §5.2

## Current State

- references.bib: 9 entries (modulo, list, cycle, integral-cycle, Hardy
  & Wright, Pritchard, Stainless verification-conditions docs, Hamza/
  Stainless, Ramanujan/Bertrand). All 9 are inline-cited in the body (no
  `\nocite` needed, unlike `euclid-theorem`).
- All 10 section files converted; full document compiles green at 15
  pages with zero warnings/errors/overfull/underfull boxes.
- One embedded figure: `charts/hit-miss-matrices.svg` (referenced by
  GitHub-raw URL in the Markdown) converted once to vector
  `figures/hit-miss-matrices.pdf` via `cairosvg` and wired in with
  `\includegraphics` — first article in this series with a real figure.
- Mechanical parity: URL sets match except the raw-SVG URL (correctly
  replaced by the embedded figure) and the two boilerplate links every
  package's `main.tex` carries (license, author homepage); math-block
  count 28 in Markdown vs 29 in `.tex` (the +1 is one shared-column-
  blowup split, not new content); Scala-block count matches exactly (3);
  identifier counts for the three §5.2 lemma names, `SpecSieveSequence`,
  `\forall`, `\blacksquare`, and `\pmod` all match exactly between
  Markdown and `.tex` sources.

## Learning Log

- The Markdown writes strict inequalities with the MathJax-style `\gt` /
  `\lt` macros (GitHub's math renderer aliases these to `>` / `<`; plain
  LaTeX has no such macros and fails with "Undefined control sequence").
  Defined both as trivial `\newcommand` aliases in `main.tex`'s preamble
  instead of hunting down all 25 occurrences — a pure syntax shim, not a
  content change. Worth checking for in any sibling article before
  assuming its math blocks will compile unmodified (`gap-dynamics`, same
  chapter, is a likely candidate).
- This was the first article in the series with an embedded image
  (`![...](https://raw.githubusercontent.com/.../hit-miss-matrices.svg)`).
  pdfLaTeX cannot include raw SVG. Found the source SVG already checked
  into the repo at `charts/hit-miss-matrices.svg` (not the path the
  Markdown's URL implies) and converted it once to a vector PDF with
  `cairosvg` (`pip install` needed a venv — Homebrew Python blocks
  unmanaged global installs). `qlmanage -t` (macOS Quick Look) was tried
  first but silently center-crops non-square SVGs to the requested `-s`
  size, truncating the figure without any error — cairosvg with an
  explicit `scale=` was the correct fix, verified by rendering the PDF
  back to PNG before trusting it.
- Two more shared-column-blowup cases beyond the pattern already
  documented in the `euclid-theorem` ticket: in §6.2 a 4-row `aligned`
  had one very long final row (long premise + long tag with
  `\blacksquare`); split that row out into its own un-aligned
  `equation*` with an inline `\quad [Tag]`, same escape hatch as before.
- Several "This property is verified in ⟨long qualified Scala
  identifier⟩" sentences needed the `{\raggedright ... \par}` wrap
  proactively (not just reactively after a build failure) once the
  pattern was recognized from the `euclid-theorem` conversion — cut the
  number of fix-rebuild cycles significantly.
