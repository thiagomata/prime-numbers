# arXiv LaTeX — integral article

**Created:** 2026-09-06
**Branch:** `feature/article/integral`
**Status:** Conversion complete — package arXiv-ready, awaiting author review
  and the release step (tag pinning)

## Goal

Convert `articles/chapter4/integral.md` into an arXiv LaTeX package
at `articles/arxiv/integral/`, release with tag `integral-article-v1.0.0`,
then merge so `feature/article/cycle` can follow.

## Strategy

Same as the completed list/modulo/cycle conversions, per
`articles/arxiv/CONVERSION_GUIDE.md` (now including the cycle-branch
additions, ported verbatim):

- Markdown source = frozen edition; standard `article` class;
  `just arxiv-pdf integral` (latexmk/pdflatex, `-g`, scratch outdir).
- One unit per compile cycle; exit 0 and log grep free of `Warning`,
  `Error`, `Overfull`, `Underfull`, `undefined`, `Missing` per unit.
- Plain `\input` assembly (modulo's `\IfFileExists` guards not needed in a
  one-session conversion — all section files scaffolded empty up front so
  every unit build stays green).
- Links `blob/master/...` during conversion (list-package precedent);
  tag-pinning to `integral-article-v1.0.0` happens in the release step,
  then the zero-warning gate is re-run (pinned URLs are longer — see guide
  `\Urlmuskip` lesson, already in preamble from the start).
- Release evidence: Chapter 4 verify log is committed on
  `feature/article/cycle` (commit `6951fbfb`,
  `logs/verify-ch-4-v1-chapter4-_.log`) and will be retrieved via
  `git show` at release time; no fresh Stainless run needed (same tree,
  same 2995/0/0 totals).

Section split (9 files, mirroring the Markdown's sequential numbering,
which coincides with LaTeX auto-numbering — verified section-for-section):

```text
00-abstract.tex            Abstract
01-introduction.tex        1 + Related work (unnumbered subsection*)
02-preliminaries.tex       2
03-definition.tex          3 (3.1-3.2, first Scala excerpt)
04-core-properties.tex     4 (4.1-4.6, Scala excerpts in 4.5 and 4.6)
05-consistency-lemmas.tex  5 (5.1-5.5, Scala excerpt in 5.1)
06-limitations.tex         6
07-conclusion.tex          7 Conclusion + 8 Future Work
08-appendix.tex            Appendix A (A.1-A.8; A.6 is a pointer note)
                           + Appendix B (log pointer)
```

Source inventory (verified by read-through): 929 lines, 43 `math` blocks,
11 Scala blocks, 9 numbered sections, 2 references
([1] list article → `mata2026lists`, [2] Rocq stdlib Lists with the
`rocq-prover.org/doc/V8.20.0/...` URL copied verbatim), cross-reference
anchors → "Section~N" hardcoded references, `\mathbb{Z}` present,
`|L|` → `\lvert L\rvert`, applied `\text{sum/head/tail/last/acc}`
→ `\operatorname{...}`.

## Current State

- Pre-conversion content decisions all closed (see
  `tickets/future/integral-pre-conversion-fixes-2026-09-06.md`):
  fixes 2 + 3 + 5 applied (fix 2 with positive framing), 1 and 4 rejected.
- `CONVERSION_GUIDE.md`: cycle-branch additions (+15 lines) ported
  verbatim — identical change on both branches, so the later cycle merge
  stays clean.
- Package scaffolded: `main.tex` (metadata, `scala` listing style,
  `\Urlmuskip` preamble, plain `\input` for all 9 section files,
  bibliography before `\appendix`), `README.md`, `references.bib`
  (2 entries: `mata2026lists` — same entry as the cycle package but with
  the master URL; `rocqliststdlib` with the md's V8.20.0 URL),
  9 empty section files.
- House author block confirmed against list + cycle `main.tex`:
  includes `thiagomata.com` URL even though the md header omits it.
- ALL 9 section files converted, each unit built green (exit 0, zero
  `Warning`/`Error`/`Overfull`/`Underfull`/`undefined`/`Missing`) before
  the next. Final build: 17 pages, `output/pdf/integral.pdf`.
- Mechanical parity audit (all pass):
  - Q.E.D. markers 11=11, `\blacksquare` 10=10, `\therefore` 11=11
    (after removing one spurious `\therefore` display I had added in the
    §4.2 inductive step — md order is implication → aligned → ∴ → Q.E.D.).
  - Scala: 11=11 blocks, byte-identical (242 lines total, plain diff).
  - Math: 43 md fences = 44 `equation*` displays; +1 fully explained by
    the §3.1 zero-`&` 2-row block split into two displays (guide rule).
    Per-section: §3 3→4, §4 19→19, §5 19→19, Conclusion 2→2.
  - Quantifier/tag rows: all 8 distinct `\forall`-shaped rows matched
    md↔tex one by one.
  - URL sets: identical; tex-only additions are the two house `main.tex`
    links (creativecommons.org license, thiagomata.com author block),
    same as list/cycle.
- Visual review: all 17 pages rendered (ghostscript `png16m` + `txtwrite`)
  and inspected — no clipping, overflow, broken glyphs, or bad breaks;
  lone-`\therefore` displays and the A.6 pointer note render correctly.
- arXiv archive `output/arxiv-integral-source.tar.gz` built (main.tex,
  9 section files, references.bib, main.bbl) and clean-room compiled in a
  fresh temp dir: exit 0, zero log issues, PDF reproduces (338778 vs
  338786 bytes — PDF timestamp metadata only).

## What is Learned

- The cycle package's `references.bib` is the canonical cross-article
  citation pattern: `@misc{mata2026<integral|lists|modulo>}` with
  `\url{...blob/<ref>/articles/...}`. Cycle pins its URLs to
  `cycle-article-v1.0.0`; a pre-release package uses `blob/master/` and
  pins at release (list precedent).
- Cycle's guide additions: `\Urlmuskip=0mu plus 1mu\relax` after
  `hyperref`; recap blocks with similar-width rows keep the
  `aligned` + `&&\text{[Tag]}` pattern (integral's Conclusion recap is
  exactly that shape; the md's two recap fences map 1:1 to two displays).

## Failed Paths

(none yet)

## Open Concerns

- §4.2's proof has a Markdown `​```math` fence containing only
  `\therefore` (and §5.2/§5.5 have small "connector" fences like
  `& & \therefore \\` inside blocks). Faithful conversion keeps each
  fence as its own display; a lone `\therefore` display is unusual in
  LaTeX but matches the frozen edition — verify it renders cleanly.
- §4.1's proof uses `L_e` as empty-list notation and
  `I \ne L_e` — kept verbatim (content, not markup).
- Chapter 4 verify log retrieval from `feature/article/cycle` at release
  time (see Strategy); the log file is NOT on this branch's working tree.
- Root strays `sections/` and `references.bib` were deleted by the author
  (2026-09-06) — do not confuse them with the package's own files.

## Next Action

Author reviews `output/pdf/integral.pdf`. Then the release step
(follow-on): pin links to `integral-article-v1.0.0`, retrieve the Chapter 4
verify log from `feature/article/cycle` (`git show 6951fbfb`), re-run the
zero-warning gate after pinning (guide `\Urlmuskip` lesson), rebuild the
archive + clean-room compile, and tag.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-09-06 | Content decisions closed (fixes 2+3+5 applied; 1, 4 rejected). Cycle package studied via `git show` (no checkout): bib pattern, author block, plain `\input`, guide +15 lines. | Port guide additions; scaffold package; convert unit-by-unit with a build per unit. |
| 2026-09-06 | All 9 units converted green on first or second build; the proactive guide rules (zero-`&` splits, flush-left leading-`&`, `\operatorname` for applied names, raggedright verification sentences) prevented every historically-known failure mode. The md's lone-`\therefore` fences convert cleanly to one-display `equation*`s. | Mechanical parity audit after the last unit. |
| 2026-09-06 | Parity audit caught one real defect the compile log could not: an extra `\therefore` display I had inserted in §4.2's inductive step (marker counts 11 vs 12) — the md's order there is implication → aligned → ∴ → Q.E.D., with no ∴ after the implication. Removed; 11=11. The URL-set diff and Scala byte-diff were clean on first pass (unlike the `list` conversion, where the URL diff caught a `\#` bug). | Visual review, archive, clean-room compile. |
| 2026-09-06 | Clean-room compile of the archive reproduces the tracked 17-page PDF (8-byte size delta = PDF timestamp metadata only). Package is arXiv-ready. | Ticket complete pending author review; release step pins links. |
