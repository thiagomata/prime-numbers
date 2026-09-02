# Converting Markdown Articles to arXiv LaTeX Packages

This guide captures the working conventions from the first Markdown-to-LaTeX
conversion (`modulo`) so the remaining articles can be converted the same
way without rediscovering the pitfalls. It is a practical manual, not a
style debate: every rule below earned its place by breaking a build or
surviving an author review.

## 1. Ground Rules

- The Markdown article is the frozen source edition. The conversion is
  faithful: same claims, same proof ordering, same code excerpts, same
  links, same author identity and license. Wording may be adjusted only for
  Markdown-specific markup (HTML wrappers, anchor syntax).
- Allowed markup normalizations (never content changes):
  - `\text{div}` / `\text{mod}` / `\text{DivMod}` / `\text{...solve}` /
    `\text{sign}` become `\operatorname{...}`.
  - `|x|` becomes `\lvert x\rvert`.
  - `%` as an operator becomes `\mathbin{\%}` (escaped percent).
  - `\forall \text{ } a` spacing hacks become `\forall\, a`.
  - GitHub anchor links become hardcoded references by section name or
    number ("Section~5", "Subsections~6.1--6.4", "Appendix~A.2").
- The `three-representations` rule carries over: English prose, math block,
  and the verified-source link must all survive the conversion. GitHub
  ```` ```math ```` fenced blocks become `\begin{equation*}\begin{aligned}
  ...\end{aligned}\end{equation*}`.

## 2. Package Layout

```text
articles/arxiv/<article>/
  main.tex                 document setup, metadata, assembly
  sections/00-abstract.tex sections/01-introduction.tex ...
  references.bib           bibliography (when the article has references)
  output/pdf/<article>.pdf built by `just arxiv-pdf` (untracked)
```

- Keep the LaTeX section order identical to the Markdown section numbering.
  The conversion hardcodes cross-references ("Section~5"), so section N of
  the Markdown must become the Nth `\section` of the manuscript. Verify the
  coincidence before converting prose that references sections.
- `main.tex` assembles sections with `\IfFileExists{sections/NN-...tex}`
  guards. This lets a partially converted article compile cleanly at every
  step — add one section file at a time and the package stays green.
- Bibliography caveat: do not use `\cite` until `references.bib` exists;
  a missing bib file produces undefined-citation warnings. Convert the
  citation markers to plain `[1]` text first and switch to `\cite` in the
  same unit that adds the `.bib` file.

## 3. Math and Alignment House Style

These are the rules the author's visual review enforced:

- **Premise + equation blocks** (a constraint row above an equation): use
  the flush-left leading-`&` pattern. Never let a short premise row share
  an alignment point with a long equation row — the premise will float far
  right of center and look disconnected.

  ```latex
  \begin{equation*}
  \begin{aligned}
  & b > 0,\quad 0 < k < b \\
  & k \operatorname{mod} b + (b - k) \operatorname{mod} b = b
  \end{aligned}
  \end{equation*}
  ```

- **Single-row statements with a label** (for example `[existsZero]`): hug
  the label to the equation with `\quad` after a leading-`&`. A trailing
  `&&\text{[label]}` column on a single-row `aligned` leaves the label
  floating in a stretched gap.

- **Multi-row recaps with per-row labels**: the `&&\text{[Label]}` column
  is right there — it only looks good when there are multiple rows, because
  the labels align into a vertical column. Use it for conclusion recaps and
  multi-line statements, not for one-liners.

- **Q.E.D. proofs inside equations** end with
  `\quad \blacksquare\ \text{[Q.E.D.]}` (requires `amssymb`). Derivation
  chains use `\therefore`.

- **Long identities that overflow**: wrap with a continuation row at a
  natural factor boundary, content unchanged:

  ```latex
  ( a + c) \operatorname{mod} b
    &= (a \operatorname{mod} b) + (c \operatorname{mod} b)
       - b \cdot (((a \operatorname{mod} b) \\
    &\qquad + (c \operatorname{mod} b)) \operatorname{div} b)
  ```

## 4. Links and Code

- Copy link URLs verbatim from the Markdown. Labels use `\texttt{...}`.
- A literal `#` is fine inside the URL argument of `\href`, but must be
  escaped as `\#` inside the display-text argument
  (`\href{...scala\#anchor}{\texttt{File.scala\#anchor}}`).
- Paragraphs mixing prose with several long `\texttt` identifiers defeat
  justification. After exhausting `\sloppypar` and `\allowbreak`, the
  working fix is a scoped ragged-right block plus breakpoints:

  ```latex
  {\raggedright
  These properties are verified in
  \href{...}{\texttt{ConsecutiveIntegers::\allowbreak nonzeroAfterZero}},
  ...
  \par}
  ```

  `microtype` belongs in the preamble regardless; it helps the whole
  document but does not fix such paragraphs alone.
- Scala excerpts use the `scala` lstlisting style defined in `main.tex`.
  Always write `\begin{lstlisting}[style=scala]` — passing only
  `language=Scala` skips the style entirely (no small font, no frame, no
  `breaklines`), and long code lines then overflow. The style uses
  `columns=fixed` with `keepspaces=true` on purpose: it preserves the
  source's internal alignment spaces exactly and keeps `breaklines`
  functional (`columns=fullflexible` silently disables breaking).

## 5. Build and Validation Loop

- Build: `just arxiv-pdf` (all articles) or `just arxiv-pdf modulo` (one).
  The recipe runs `latexmk -g -pdf -interaction=nonstopmode -halt-on-error`
  with a scratch `--outdir` under `$TMPDIR` (kept outside the repository)
  and copies the result to `output/pdf/<article>.pdf`. The `-g` (go) flag
  matters: latexmk tracks only files it actually input, and the assembly
  guards probe section files with `\IfFileExists` — without `-g`, a newly
  added section file is silently missed and the stale PDF is recopied.
- During conversion, compile after every logical unit (one section file or
  one property group per cycle) so regressions stay isolated. Require exit
  code 0 and a log grep free of `Warning`, `Error`, `Overfull`, `Underfull`,
  `undefined`, and `Missing`. Never keep editing while a compile is red —
  revert the failing unit or fix it alone.
- Visual check: ghostscript renders pages when poppler (`pdftoppm`,
  `pdfinfo`) is unavailable:

  ```bash
  gs -q -dNOPAUSE -dBATCH -sDEVICE=png16m -r150 -o build/page-%02d.png main.pdf
  gs -q -dNOPAUSE -dBATCH -sDEVICE=txtwrite -o build/main.txt main.pdf
  ```

  Inspect every page for clipping, overflow, broken glyphs, and bad breaks;
  use the text layer to confirm headings and labels survived. Always use a
  `-%02d` filename pattern — without `%d`, ghostscript overwrites one file
  for all pages.
- Mechanical parity check: every heading, equation, label, and link in the
  Markdown must be findable in the `.tex` sources or the extracted text.

## 6. Conversion Checklist for the Next Article

1. Read the Markdown end to end; count sections, subsections, contribution
   bullets, equations, and links before converting anything.
2. Copy the `modulo` package shape: `main.tex` with updated metadata and
   the `\IfFileExists` assembly points; adjust the planned section files.
3. Convert one logical unit per compile cycle: front matter and abstract,
   then introduction/limitations, then definitions, then properties in
   groups of three or four subsections, then conclusion, references, and
   appendix.
4. Apply the alignment house style of Section 3 as you write, not as a
   cleanup pass.
5. After each unit: build, grep the log, render, inspect the affected
   pages, then record progress in the ticket.
6. Finish with a full source-parity pass, a clean `just arxiv-pdf` build,
   a page-by-page visual review, and finally the arXiv upload archive.
