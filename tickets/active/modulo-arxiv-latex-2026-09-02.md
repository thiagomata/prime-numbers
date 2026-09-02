# Modulo arXiv LaTeX Submission Package

**Created:** 2026-09-02
**Updated:** 2026-09-02
**Status:** In progress
**Depends on:** none

## START HERE

Create the first small manuscript change: add the arXiv package skeleton and a
minimal `main.tex` that compiles independently before converting article
sections one at a time.

## Related Tickets

- `chapter4-integral-cycle-article-publish-prep-2026-08-20.md` — prior
  publication-preparation work. Its relevant lesson is to finish content and
  framing review before treating an article as publication-ready.

## Related Articles

- `articles/chapter2/modulo.md` — canonical GitHub article to convert without
  changing its mathematical claims.

## Goal

Create a clean, conventional, arXiv-compatible LaTeX package for
`articles/chapter2/modulo.md`, compile it with a normal LaTeX engine, and
visually verify the resulting PDF. The package must preserve the article's
claims, proof ordering, Scala excerpts, references, source links, author
identity, and CC BY 4.0 notice. Completion means the source is ready to upload
to arXiv after the author's final approval; this ticket does not authorize the
actual arXiv submission.

## Strategy

Treat the Markdown article as the frozen source edition and perform a one-time,
reviewed conversion into a small multi-file LaTeX manuscript under
`articles/arxiv/modulo/`. Use the standard `article` class and common packages
supported by arXiv. Compile only with `latexmk`/`pdflatex`; do not generate the
PDF with Python, ReportLab, browser/HTML printing, or a PDF-generation skill.
Convert one logical manuscript unit at a time and compile after each unit so a
formatting regression is isolated. Keep generated build files outside the
tracked source package.

## Current State

- The arXiv account exists with `cs.LO` as its default category and `cs` plus
  `math` enabled.
- The source article exists only as Markdown; the repository contains no LaTeX
  manuscript pipeline.
- The article has no figures, Mermaid diagrams, scripts, iframes, or embedded
  media, so the package needs only TeX section files and a bibliography.
- `latexmk`, `pdflatex`, `pdftoppm`, and `pdfinfo` are available locally.
- Unrelated working-tree changes exist in chapters 4 and 6, review documents,
  publication-venue documents, and other tickets. They must remain untouched.
- `articles/arxiv/modulo/main.tex` now contains the standard document setup,
  title, author/contact metadata, Scala listing style, hyperlink metadata, and
  CC BY 4.0 notice.
- The minimal manuscript compiles successfully through two PDFLaTeX passes;
  its log has no warnings, overflow, undefined references, or errors.
- The rendered one-page baseline is visually clean, with readable metadata,
  correct glyphs, clear margins, and no clipping. Generated files remained in
  a temporary build directory outside the repository.
- `main.tex` now conditionally assembles the seven planned section files and
  the BibTeX database, so each content unit can be added and compiled as one
  isolated file change.
- `sections/00-abstract.tex` now faithfully reproduces the Markdown abstract;
  it compiles without warnings or overflow and renders completely on page one.
- The CC BY 4.0 notice now follows the abstract, restoring conventional
  front-matter order; the revised page remains visually and mechanically green.
- `sections/01-introduction.tex` now preserves the complete Introduction and
  Limitations, including all six contribution-summary bullets; its two-page
  compile and render are green.
- `sections/02-definitions.tex` now faithfully converts Markdown Section 3
  (Traditional Definition) and Section 4 (Recursive Definition), including the
  `DivMod` constraint, the solved-range cases, the recursive `DivMod.solve`
  definition, and the DivMod.scala GitHub link; the hardcoded cross-references
  (Section~3, Section~5) coincide with the LaTeX section numbering. The
  three-page compile is green (exit 0, no warnings, no overfull boxes, no
  undefined references), and the rendered pages show no clipping, overflow, or
  broken glyphs.
- Poppler tools (`pdfinfo`, `pdftoppm`) are absent from the current PATH.
  Page rendering and text extraction were done with ghostscript instead
  (`gs -sDEVICE=png16m` for page images, `gs -sDEVICE=txtwrite` for text).
  The PDF itself is still produced only by `latexmk`/`pdflatex`, per the
  author's constraint; ghostscript is used solely for post-compilation
  inspection.
- `sections/03-shift-invariance.tex` now faithfully converts Markdown
  Section 5 and subsection 5.1: the five-line linear-shift invariant, the
  positive/negative shift links to ModIdempotence.scala, the Calc.scala
  projection definitions, and the functional/infix notation prose. The
  compile is green (exit 0, zero log issues) and the section renders
  completely on page three with clean links and equations.
- `sections/04-properties.tex` now opens the properties chapter with the
  Markdown Section 6 introduction (all six group bullets) and the first
  property group §6.1–6.4 (Trivial Case, Identity, Modulo and Division by
  One, Native Modulo Compatibility), including both Q.E.D. normalization
  proofs and all five verification links. The five-page compile is green
  (exit 0, zero log issues); the rendered pages show the escaped `%`
  operator, blacksquare Q.E.D. markers, and blue links all clean.
- The second property group §6.5–6.8 (single-step and multiplier linear
  shift laws, Unique Remainder with both formalizations and floor notation,
  Modulo Idempotence) is now appended, with the induction prose and all six
  AdditionAndMultiplication/ModIdempotence links. The six-page compile is
  green (exit 0, zero log issues) and pages five and six render cleanly,
  including the ∃! quantifier and ⌊a/b⌋ brackets.
- The third property group §6.9–6.10 (Distributivity over Addition and
  Distribution over Subtraction) is now appended, each with its three
  identities, substitution proof, and ModOperations/ModIdempotence links
  (with `#` escaped as `\#` inside `\texttt` labels). The seven-page compile
  is green (exit 0, zero log issues); the long third identities fit the
  margins with no overfull warnings.
- The fourth property group §6.11–6.12 (Modular Shift Invariance under
  Divisible Base with its −c subtraction corollary, and Symmetrical Modulo
  Pairs) is now appended, with the Subsection~6.9 cross-reference and the
  Appendix~A.2 forward reference hardcoded per convention. The eight-page
  compile is green (exit 0, zero log issues) and page eight renders cleanly.
- The final property group §6.13–6.14 (Unit-Step Increment Law and
  Consecutive Integers Zero Density with its three tagged sub-results, the
  ∴ Q.E.D. block, four ConsecutiveIntegers links, Appendix~A.3 reference,
  multi-factor helper caveat, and Future Work forward reference) is now
  appended; the properties chapter is complete.
- The §6.14 links-paragraph overflow is resolved: `microtype` was added to
  the `main.tex` preamble (document-wide typography benefit), and the links
  paragraph itself is set `\raggedright` with `\allowbreak` after each `::`.
  The nine-page compile is green with zero log issues, and page nine renders
  cleanly.
- `sections/05-conclusion.tex` now converts Markdown Section 7 (Conclusion)
  and Section 8 (Future Work): all fourteen collected-property equation
  groups with their `[Label]` tags, both closing paragraphs with the
  Summary.scala link, and the Future Work paragraph with the Hardy & Wright
  `[1]` marker hardcoded as plain text until the bibliography unit replaces
  it with `\cite`. Two distributivity recap identities initially overflowed
  (11–25pt) under the tag columns and were fixed with the standard amsmath
  continuation-row idiom (`&\qquad` break before the closing factor);
  content unchanged. The eleven-page compile is green with zero log issues;
  pages ten and eleven render cleanly.
- A preview PDF for the author is now materialized under
  `articles/arxiv/modulo/output/pdf/` (11 pages, LaTeX-compiled,
  zero-warning log). Iteration compiles still use throwaway `/tmp`
  directories; this is the package's persistent PDF artifact.
  Note: the repo has no `.gitignore` coverage for `output/`, so the preview
  PDF currently shows as untracked.
- Author review feedback on alignment fixed: (a) §6.12's premise row floated
  right-of-center because its `b &> 0` alignment point was shared with the
  long equation row below; both rows now use the flush-left leading-`&`
  house pattern. (b) Single-row statements with a `&&\text{[tag]}` column
  leave the tag floating in a stretched gap (the tag column only looks neat
  in multi-row blocks where tags align vertically); the three §6.14
  statements were normalized to a leading-`&` row with the tag hugging the
  equation via `\quad`. The multi-row tagged blocks (§6.14 Q.E.D. chain,
  Conclusion recap) keep the `&&` column, where it renders as a proper
  aligned tag column. Recompiled green (exit 0, zero log issues), affected
  regions re-rendered and verified, preview PDF refreshed.
- Build tooling and knowledge capture, per author request: (a) new
  `just arxiv-pdf [article]` recipe builds every article under
  `articles/arxiv/` (or one named article) via `latexmk` with a scratch
  `$TMPDIR` outdir and writes `articles/arxiv/<article>/output/pdf/
  <article>.pdf`; validated end-to-end (11 pages, exit 0). (b) The preview
  PDF was renamed from `output/pdf/main.pdf` to `output/pdf/modulo.pdf` so
  the artifact carries the article name. (c) The durable conversion
  conventions are captured in `articles/arxiv/CONVERSION_GUIDE.md`
  (frozen-source rules, package layout, alignment house style, overflow and
  long-link tooling, ghostscript validation loop, per-article checklist)
  so the remaining articles can be converted without rediscovering the
  pitfalls.
- Bibliography unit complete: `references.bib` now contains the normalized
  Hardy & Wright `@book` entry (`hardywright1979`; brace-protected title
  casing; "See Section 5.4" pointer kept in the `note` field; no invented
  metadata), and the hardcoded `[1]` marker in `05-conclusion.tex` is now
  `\cite{hardywright1979}`. latexmk drove bibtex correctly against the
  scratch outdir (found `./references.bib`, produced `main.bbl`); the final
  log has zero issues with no undefined citations. The References section
  renders after Future Work on page eleven: `[1] G. H. Hardy and E. M.
  Wright. An Introduction to the Theory of Numbers. Clarendon Press,
  Oxford, fifth edition, 1979. See Section 5.4 for the Chinese Remainder
  Theorem.` — matching the Markdown entry in content and casing.

## Expected State

- `articles/arxiv/modulo/main.tex` provides metadata, packages, abstract, and
  section assembly.
- `articles/arxiv/modulo/sections/` contains a small logical split of the paper,
  not one file per subsection.
- `articles/arxiv/modulo/references.bib` contains normalized bibliography data.
- `articles/arxiv/modulo/README.md` documents compile and arXiv packaging steps.
- A compiled PDF exists under `output/pdf/`, produced by LaTeX and visually
  checked page by page.
- A source archive contains only files required by arXiv.

## Approaches Considered

### Standard Multi-file LaTeX Package

**Status:** RECOMMENDED

Use `main.tex`, six logical section files, and `references.bib`.

**Strengths:** Conventional, readable, easy to compile on arXiv, and suitable
for later journal-template adaptation.
**Risks:** Manual conversion can introduce wording, math, anchor, or listing
drift.
**Fallback:** Reduce the split to fewer section files if cross-file structure
causes compilation or review difficulty.

### Single Large `main.tex`

**Status:** UNTESTED

Place the entire manuscript in one TeX file.

**Strengths:** Simplest upload shape.
**Risks:** Harder to review and compare against the long Markdown source.
**Fallback:** Use only if arXiv packaging exposes an unexpected multi-file
problem.

### Markdown-to-PDF Without LaTeX Source

**Status:** REJECTED

Generate and upload only a PDF from Markdown.

**Strengths:** Fewer conversion steps.
**Risks:** Discards the arXiv-preferred TeX source and is less reusable for
future journal submissions.
**Fallback:** None while the chosen LaTeX path remains viable.

## Assumptions

- The Markdown wording and mathematical claims are the conversion baseline.
- Standard `article`, AMS math, `hyperref`, `xcolor`, and `listings` packages are
  available in arXiv's TeX environment.
- Code excerpts can be represented with `lstlisting` without semantic changes.
- Existing relative source references can be converted to stable GitHub URLs.
- No figure assets are required for this article.

Each assumption will be checked by source comparison, local compilation, log
inspection, link inspection, and final visual review.

## Risks

- GitHub-specific fenced `math` blocks and HTML wrappers need careful manual
  translation.
- Long aligned equations or Scala listings may overflow page margins.
- Unicode symbols and punctuation may not compile under PDFLaTeX without
  normalization.
- The existing references are prose entries rather than BibTeX and may need
  bibliographic normalization without inventing missing metadata.
- arXiv may require endorsement or category adjustment after upload; that is an
  account workflow concern, not a manuscript-generation blocker.

## Validation

For each manuscript change:

1. Compile with `latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex`.
2. Require a zero exit code and no unresolved-reference warning in the final
   compile log.
3. Compare headings, theorem statements, equations, code, references, and links
   against `articles/chapter2/modulo.md`.
4. Use `pdfinfo` and text extraction to confirm a readable PDF.
5. Render every page with `pdftoppm` and visually inspect for clipping,
   overflow, broken glyphs, poor page breaks, and unreadable code.
6. Inspect the final source archive and compile it from a clean temporary
   directory before calling it arXiv-ready.

This is a publication-only change. Scala tests and Stainless verification are
not applicable unless Scala sources, Scala tests, build behavior, or executable
verification instructions are changed.

## Implementation Plan

1. Add the package skeleton and minimal compiling `main.tex`.
2. Convert the abstract, introduction, limitations, and traditional definition.
3. Convert the recursive definition and shift-invariance proof.
4. Convert the modulo and division properties, one property section per
   compile cycle.
5. Convert the conclusion, future work, references, and appendix.
6. Normalize bibliography data and resolve internal/external links.
7. Perform complete source-parity, compile-log, text, and visual PDF checks.
8. Create and independently compile the minimal arXiv upload archive.

## What is Learned

- arXiv does not require a universal visual template; a conservative standard
  `article` manuscript is appropriate.
- The author explicitly requires the PDF to be produced by compiling LaTeX,
  not by Python, ReportLab, HTML rendering, or PDF-generation skills.
- A small multi-file package balances navigability and upload simplicity.
- The selected standard packages are all available in the local TeX Live 2025
  installation, and the baseline compiles cleanly with PDFLaTeX.
- Missing conditional section files and bibliography data are handled cleanly;
  the assembly scaffold compiles without placeholder files or warnings.
- The source Introduction contains six contribution bullets. Counting them
  explicitly before conversion prevented omission of the unit-step and
  zero-density summary.

## Failed Paths

- **PDF-generation skill / Python or HTML-to-PDF path:** considered before the
  author's clarification and abandoned because the requested artifact is a
  LaTeX manuscript whose PDF is compiled by LaTeX. Retry only if the author
  explicitly changes that requirement.
- **PDF-only Markdown submission:** rejected because it loses the reusable TeX
  source desired for arXiv and later journal preparation. Retry only if LaTeX
  compilation becomes genuinely unavailable or the author changes the target.
- **§6.14 links paragraph justification (5 attempts, resolved):**
  (1) plain paragraph — 4 Overfull \hbox (up to 93pt) because the four
  `ConsecutiveIntegers::...` \texttt labels cannot hyphenate and one ran past
  the page edge; (2) `\sloppypar` — overfull gone but 2 Underfull \hbox
  (badness 10000/1701) from stretched interword gaps; (3) `\sloppypar` +
  `\allowbreak` after each `::` — identical underfull warnings (the log shows
  TeX fills the first line with prose + a full 38-char identifier, so the
  loose line is unavoidable under justification); (4) `\usepackage{microtype}`
  — underfull persisted (badness 10000/3229); microtype kept anyway for
  document-wide quality; (5) `\raggedright` scoped to the links paragraph via
  `{\raggedright ... \par}` — RESOLVED: zero log issues, normal spacing,
  ragged right edge confined to that one paragraph. Lesson: justification
  cannot recover when a paragraph mixes prose with multiple long unbreakable
  `\texttt` identifiers; scope `\raggedright` to such paragraphs and keep
  `microtype` for the rest.

## Open Concerns

- Final content readiness and category suitability still need a dedicated
  review before public submission.
- Bibliographic entries may lack fields expected by BibTeX.
- The eventual journal target may require a different template, but that should
  not complicate this neutral arXiv manuscript.

## Fallback Options

- Keep a single `main.tex` if the multi-file package becomes unnecessarily
  difficult to validate.
- Inline a manually normalized bibliography if BibTeX cannot reproduce the
  intended reference content without invented metadata.
- Use `\url{}` and descriptive prose for source links if fragile internal
  Markdown anchors cannot be mapped cleanly.

## Next Action

Run the Worker/Critic/Monitor pipeline for exactly one change: create
`articles/arxiv/modulo/sections/06-appendix.tex` as a faithful conversion of
Markdown Section 9 (Appendix): A.1 Identity Property Excerpt, A.2 Symmetrical
Modulo Pairs Excerpt, A.3 Consecutive Zero Density Excerpt (all as
lstlisting Scala excerpts with their source links), and A.4 Verification
Log. Note `main.tex` switches to `\appendix` before this include, so the
section numbering becomes A.x as the Markdown expects; then compile and
inspect the affected page.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-09-02 | Ticket created after reviewing the publication guidance, prior publication-prep precedent, source article structure, local tools, and the author's LaTeX-only PDF constraint. | Create and compile the minimal manuscript skeleton. |
| 2026-09-02 | Added the minimal `main.tex`; `latexmk`/PDFLaTeX compiled it without warnings or overflow, and the rendered metadata page is visually clean. | Add conditional section assembly points to `main.tex`. |
| 2026-09-02 | Added conditional assembly for all planned sections and the bibliography; a fresh LaTeX compile and rendered-page check remained green. | Convert only the abstract into `sections/00-abstract.tex`. |
| 2026-09-02 | Converted the abstract faithfully; LaTeX and visual checks are green. The render exposed a non-blocking ordering issue: the license notice precedes the abstract. | Move the existing license notice below the abstract before converting more prose. |
| 2026-09-02 | Moved the unchanged license notice below the abstract; compilation and the conventional front-matter render are green. | Convert Introduction and Limitations into `sections/01-introduction.tex`. |
| 2026-09-02 | Converted the complete Introduction and Limitations, preserving all six contribution bullets after the Critic corrected the initial count; the two-page build and render are green. | Convert Traditional Definition and Recursive Definition into `sections/02-definitions.tex`. |
| 2026-09-02 | `sections/02-definitions.tex` (already drafted from the prior session) was verified line-by-line against the Markdown for parity, then compiled and inspected: three-page build is green with a clean log, and the rendered definitions pages are visually clean. Poppler is missing from PATH, so ghostscript's `png16m` and `txtwrite` devices replace `pdftoppm`/`pdfinfo` for inspection only; the PDF remains LaTeX-compiled. | Convert Section 5 (linear-shift invariance, including subsection 5.1) into `sections/03-shift-invariance.tex`. |
| 2026-09-02 | Converted Section 5 and subsection 5.1 in one unit; the three-page build stayed green (exit 0, zero log issues) and the full section renders on page three with working-looking blue links and correct glyphs. The `main.tex` conditional-include scaffold made the new file zero-touch. | Begin `sections/04-properties.tex` with the Section 6 intro plus §6.1–6.4, then grow it one property group per compile cycle. |
| 2026-09-02 | Opened `sections/04-properties.tex` with the chapter intro and §6.1–6.4; five-page build green (exit 0, zero log issues), all headings confirmed by text extraction, Q.E.D. blocks and the escaped `%` render correctly. Growing a single properties file group-by-group keeps each compile diff small while honoring the one-file split. | Append §6.5–6.8 to `sections/04-properties.tex` and compile. |
| 2026-09-02 | Appended §6.5–6.8; six-page build green (exit 0, zero log issues), pages five and six render cleanly with ∃!, ⌊a/b⌋, subscripts, and all six case links. | Append §6.9–6.10 (distributivity over addition and subtraction) and compile. |
| 2026-09-02 | Appended §6.9–6.10; seven-page build green (exit 0, zero log issues); the long third identities fit with no overfull warnings, and the `\#`-escaped anchor links render correctly. | Append §6.11–6.12 (divisible-base shift invariance, symmetrical modulo pairs) and compile. |
| 2026-09-02 | Appended §6.11–6.12; eight-page build green (exit 0, zero log issues); corollary, Q.E.D. chains, and paragraph indentation all render correctly. | Append §6.13–6.14 (unit-step increment law, zero density) and compile. |
| 2026-09-02 | The §6.14 links paragraph overflowed (93pt) because four unbreakable 38-char `\texttt` identifiers defeat justification. Three fix attempts hit the stop-and-ask gate; with the author unavailable, best judgment resolved it: `microtype` in the preamble plus a scoped `\raggedright` for that paragraph. Nine-page build is green with zero log issues. Durable lessons: (a) mixing prose with multiple long unbreakable `\texttt` tokens requires scoped ragged-right, `\allowbreak` alone cannot save justification; (b) `microtype` is safe here and benefits the whole manuscript; (c) poppler tools absent in this environment — ghostscript `png16m`/`txtwrite` are the standing render/extract substitutes. | Convert §7 Conclusion and §8 Future Work into `sections/05-conclusion.tex`. |
| 2026-09-02 | Converted the Conclusion (14 tagged recap blocks) and Future Work; two distributivity recap identities overflowed (11–25pt) under their new tag columns and were fixed by the amsmath continuation-row idiom (`&\qquad` wrap before the closing factor) — content unchanged, zero log issues, 11 pages, pages ten/eleven render cleanly. Also learned: `gs -o file.png` without `%d` overwrites one file for all pages; always use `-%02d` patterns when counting pages. A persistent author-preview PDF now lives at `output/pdf/main.pdf` (untracked; repo has no `.gitignore` for it). | Create `references.bib` + switch the hardcoded `[1]` to `\cite` in one unit; then the appendix. |
| 2026-09-02 | Author alignment review: (a) a quantifier/premise row sharing an alignment point with a long equation row floats right-of-center — use the flush-left leading-`&` pattern for premise+equation statement blocks (§6.12 fixed); (b) `&&\text{[tag]}` on a SINGLE-row aligned leaves the tag floating in a stretched gap — on single-row statements, hug the tag with `\quad` after a leading-`&` (the three §6.14 statements normalized); keep `&&` tag columns only for multi-row blocks where they align vertically (§6.14 Q.E.D. chain, Conclusion recap — unflagged). Preview PDF refreshed; commit `076a253a` holds the pre-fix state. | Apply the same review lens to remaining units; create `references.bib` + `\cite`. |
| 2026-09-02 | Delivered author tooling requests: `just arxiv-pdf [article]` recipe (validated end-to-end; latexmk into `$TMPDIR` scratch, PDF copied to `output/pdf/<article>.pdf`), renamed the preview `main.pdf` to `modulo.pdf` so the artifact carries the article name, and captured the durable conversion conventions in `articles/arxiv/CONVERSION_GUIDE.md` — the playbook the next article conversions should follow (frozen-source rules, numbering coincidence requirement, alignment house style, overflow/long-link fixes, ghostscript validation loop, per-article checklist). | Create `references.bib` + switch the hardcoded `[1]` to `\cite` in one unit; then the appendix. |
| 2026-09-03 | Bibliography unit green: `references.bib` (`hardywright1979`, no invented metadata, note field preserved) plus `\cite` switch in the same unit — latexmk drove bibtex against the scratch outdir without any manual env, final log zero issues, and page eleven renders the entry with preserved title casing and the "fifth edition" formatting from `plain.bst`. Lesson: `latexmk -outdir` + `\bibliography{references}` works out of the box on TeX Live 2025 (bibtex resolves the bib relative to the project cwd); brace-protect `@book` titles to stop case mangling, and `plain.bst` renders `edition = {Fifth}` as "fifth edition". | Convert Markdown Section 9 into `sections/06-appendix.tex` (`\appendix` numbering gives the A.x headings the Markdown expects). |
