# list arXiv LaTeX Submission Package

**Created:** 2026-09-04
**Updated:** 2026-09-04
**Status:** arXiv-ready — awaiting author review and submission (submission
itself is out of this ticket's scope)
**Depends on:** none (follow-on to the completed `modulo-arxiv-latex-2026-09-02.md`
/ `modulo-arxiv-release-v1-2026-09-03.md` pair, same conversion method)

## START HERE

Do for `articles/chapter3/list.md` what was done for the modulo article:
convert it into a clean, conventional arXiv LaTeX package under
`articles/arxiv/list/`, compile with `latexmk`/`pdflatex`, and visually
verify the resulting PDF. Follow `articles/arxiv/CONVERSION_GUIDE.md`
throughout — it already encodes every pitfall hit during the modulo
conversion (alignment house style, `style=scala` requirement, long-link
paragraph fix, parity-audit method, build tooling).

## Related Tickets

- `modulo-arxiv-latex-2026-09-02.md`, `modulo-arxiv-release-v1-2026-09-03.md`
  — the prior conversion this one reuses conventions and tooling from.

## Related Articles

- `articles/chapter3/list.md` — canonical GitHub article to convert without
  changing its mathematical claims. 2087 lines, 91 headings, 99 `math`
  blocks — roughly 2.3x the size of `modulo.md` (887 lines, 48 blocks).

## Goal

Produce `articles/arxiv/list/` (main.tex, sections/, references.bib,
README.md), a compiled `output/pdf/list.pdf`, and an arXiv upload archive,
preserving the article's claims, proof ordering, Scala excerpts,
references, author identity, and CC BY 4.0 notice.

## Strategy

Same as modulo: one-time reviewed conversion, standard `article` class,
compile only with `latexmk`/`pdflatex`. Section split (14 files, matching
`main.tex`'s `\input` order — LaTeX `\section`/`\subsection` auto-numbering
was checked to coincide with the Markdown's own baked-in numeric heading
prefixes, section-for-section, since both are a plain sequential count with
no gaps):

00-abstract, 01-introduction (+ Related work), 02-definitions (2.1-2.9),
03-index-access (3.1-3.3), 04-slice (4.1-4.4), 05-sum (5.1-5.5),
06-product (6.1-6.5), 07-product-divisibility (7.1-7.3),
08-bound-order (8.1-8.7), 09-equivalence (9.1), 10-shifted-list (10.1-10.3,
inline Scala excerpts), 11-rotation (11.1-11.2, inline Scala excerpts),
12-conclusion (Conclusion + Future Work), 13-limitations (14.1-14.5),
14-appendix (Appendix A.1-A.24 + Appendix B).

Markup normalizations applied per the guide, plus one new one this article
needs: the Markdown's literal Unicode blackboard-bold letters ($\mathbb{L}$
for the list set, $\mathbb{S}$ for the element domain) become `\mathbb{L}`
/ `\mathbb{S}`, the same treatment modulo already established for
$\mathbb{Z}$/$\mathbb{N}$. `\text{head}`/`\text{tail}`/`\text{sum}`/
`\text{product}`/`\text{last}`/`\text{slice}`/`\text{shift}`/
`\text{rotateAt}`/`\text{splitAt}`/etc. become `\operatorname{...}` per the
guide's existing rule.

References: reuse `hamza2019systemfr` verbatim from modulo's `references.bib`
(same source, cited by both articles). Three new entries: Wikipedia's
"Formal verification" article, the Rocq standard library list docs, and the
Lean mathlib list-rotation docs — all `@misc` with no invented metadata.

## Current State

- Branch `feature/article-list` created from `master`.
- Ticket created; full Markdown source read end-to-end (2087 lines, 91
  headings, 99 `math` blocks, appendix with 24 Scala excerpts covering
  A.1-A.24, plus Appendix B log pointer).
- Package scaffolded: `main.tex` (metadata, Scala listing style, plain
  `\input` assembly for all 14 planned section files — using plain
  `\input` from the start rather than `\IfFileExists`, since this
  conversion is being written and compiled within one continuous session
  rather than across many incremental days; the modulo release ticket
  already established plain `\input` as the intended end state), `README.md`,
  `references.bib` (4 entries as above).
- All 14 section files converted and compiled incrementally, each unit
  green (exit 0, zero log issues) before moving to the next: abstract +
  introduction/related-work, definitions (2.1-2.9), index/access (3.1-3.3)
  + slice (4.1-4.4), sum (5.1-5.5) + product (6.1-6.5), product
  divisibility (7.1-7.3) + bound/order (8.1-8.7), equivalence (9.1) +
  shifted-list (10.1-10.3, with inline Scala excerpts) + rotation
  (11.1-11.2, with inline Scala excerpts), conclusion + future work +
  limitations (14.1-14.5), and finally references (`\cite` switched in
  directly, no placeholder-`[N]` stage needed since `references.bib` was
  created up front) + Appendix A (A.1-A.24, all 24 Scala excerpts) +
  Appendix B. Final build: 33 pages, exit 0, zero log issues.
- Full mechanical parity audit against `articles/chapter3/list.md`:
  `\blacksquare`/Q.E.D. markers 17=17 exact; unique GitHub URL sets
  identical after a fix (below); all 29 Scala code fences byte-identical
  to their `lstlisting` counterparts except one blank line's trailing
  whitespace (semantically inert, left as-is); heading count 90 (MD) vs
  87 (`\section`+`\subsection`) fully explained by three by-design
  non-1:1 mappings (Abstract isn't a `\section`; `\subsection*{Related
  work}` isn't numbered so a naive grep undercounts it; References has no
  manual `\section{}` because `\bibliography` auto-generates the
  heading) — not a real gap. Math-block count differs (99 `\`\`\`math` +
  4 `$$` = 103 in MD vs 112 `equation*` in TeX) because several
  Conclusion recap blocks were deliberately split into more, narrower
  `equation*` environments to fix an alignment-overflow bug (see Learning
  Log) — content-preserving, not a parity bug.
- Bug caught by the URL-set diff, not by the compile log: two `\href`
  calls in `02-definitions.tex` had `\#` escaped *inside the URL
  argument* (`ListUtils.scala\#slice`), which silently produces a broken
  link (a literal backslash in the target) while still compiling clean.
  Fixed to a literal `#` in the URL argument, per `CONVERSION_GUIDE.md`'s
  existing (but easy to misapply) rule; documented the concrete failure
  mode there since the build log gives zero signal for it.
- arXiv upload archive `output/arxiv-list-source.tar.gz` built (main.tex,
  14 section files, references.bib, generated main.bbl) and clean-room
  compiled in a fresh temp directory: exit 0, 33 pages, byte-identical
  PDF size (409733 bytes) to the tracked build, zero log issues.
- `CONVERSION_GUIDE.md` updated with three durable lessons from this
  conversion (see its own changelog / diff): the shared-column-width
  blowup in `aligned` environments (this ticket's only real debugging
  detour), the bare-variable-vs-function-application rule for when
  `\text{name}` should become `\operatorname{name}`, and the `\#`-in-URL
  pitfall above.

## What is Learned

- `amsmath`'s `aligned` environment shares column widths across **every**
  row it contains, computed once for the whole environment. Packing one
  genuinely wide row (long premise + long conclusion + a `[Tag]`) into
  the same `aligned` as several short ones forces every row's shared
  column wider. This produced a confusing debugging loop in the
  Conclusion section: fixing one row's overfull-hbox by adding a
  `\\`-continuation made a *different*, previously-fine row's reported
  overfull-pt grow instead of shrink on the next compile, because the
  shared column had just gotten wider still. The fix that actually
  worked: stop sharing alignment across rows with very different natural
  widths — give each recap identity its own `equation*` (only using an
  internal `aligned` when that one statement needs its own line break)
  and inline the `[Tag]` with `\quad \text{[Tag]}` instead of an `&&`
  column. Full detail now lives in `CONVERSION_GUIDE.md` §3.
- A parity audit that only checks the compile log misses real defects: a
  `\#` escaped inside an `\href` URL argument (vs. correctly escaped only
  in the display-text argument) compiles perfectly cleanly while quietly
  producing a broken hyperlink target. Diffing the unique URL sets
  between the Markdown source and the `.tex` files caught this
  immediately; a log-only or even a full visual page-by-page review would
  not have (an underlined blue link looks identical whether or not its
  target is broken).
- Converting a ~2.3x-larger article than the prior `modulo` conversion,
  in one continuous session with the full Markdown source read up front,
  let most units compile clean on the first or second try — the
  remaining CONVERSION_GUIDE.md pitfalls (style=scala, raggedright for
  long-link paragraphs, long-identity continuation rows) were applied
  proactively rather than rediscovered.

## Failed Paths

- **Shared-`aligned`-column overflow fixes applied row-by-row (several
  attempts before recognizing the pattern):** repeatedly inserting a
  `\\`-continuation into whichever single row the log flagged as overfull
  made the *reported* overfull amount on other rows grow across
  successive recompiles, because every row in that `aligned` shares
  column widths. Resolved by restructuring the affected blocks (the
  Conclusion section's product-divisibility, bound/order, and
  shifted-list/rotation recap blocks) into independent `equation*`
  environments instead of one shared `aligned`. Retry the "keep patching
  the row the log names" approach only for warnings inside a single,
  otherwise-uniform `aligned` block where all rows are naturally similar
  width.

## Open Concerns

- One Scala listing (`A.6 assertAppendToSlice`) differs from the
  Markdown source by trailing whitespace on one blank line only —
  invisible in both the Markdown and the rendered PDF, left uncorrected
  as not worth another edit/compile/verify cycle. Flag only if the author
  wants literal byte-for-byte parity including invisible whitespace.
- Same two open items as the modulo ticket, not addressed here either:
  dedicated content-readiness/category review before public submission,
  and journal-template adaptation if a journal target is chosen.
- GitHub source links point at `blob/master/...`, not an immutable tag —
  matching this ticket's own scope (mirrors modulo's own
  `modulo-arxiv-latex` ticket, which also used `blob/master/` and left
  tag-pinning to a separate release ticket). If a tagged release is
  wanted for `list` the way `modulo-article-v1.0.0` was cut for modulo,
  that is a follow-on ticket, not part of this one.

## Next Action

None in this ticket — all Expected State items are satisfied and
validated. The author reviews the package (`output/pdf/list.pdf`,
archive `output/arxiv-list-source.tar.gz`) and performs the actual arXiv
submission themselves, or requests a release ticket (mirroring
`modulo-arxiv-release-v1-2026-09-03.md`) if a tagged, pinned release is
wanted first.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-09-04 | Ticket created from the user's request to repeat the modulo arXiv conversion for `list.md`. Read the full source, sized it against modulo (2.3x), and scaffolded the package using plain `\input` since the whole conversion happens in one session. | Convert front matter, then work through each property section in the planned order, compiling and log-checking after each unit. |
| 2026-09-04 | All 14 section files converted in one pass, informed by CONVERSION_GUIDE.md's existing pitfalls (style=scala, raggedright+allowbreak for long-link paragraphs, operatorname for function names) applied proactively. Two new normalizations needed: literal Unicode 𝕃/𝕊 → `\mathbb{L}`/`\mathbb{S}` (same treatment as modulo's ℤ/ℕ), and a bare-vs-applied distinction for when `\text{name}` becomes `\operatorname{name}`. | Compile after every 1-2 section files; fix overfull boxes as they appear. |
| 2026-09-04 | Hit a real debugging detour in the Conclusion section: `aligned` shares column widths across all its rows, so patching one overfull row grew a different row's overflow on recompile. Root-caused it and restructured the affected recap blocks into independent `equation*` per identity instead of one shared `aligned`; all warnings resolved to zero. | Apply the same "don't share `aligned` across very different row widths" rule proactively for the rest of the appendix (none needed it — the appendix's per-lemma blocks are already narrow, one-off statements). |
| 2026-09-04 | Full mechanical parity audit: Q.E.D. markers exact (17=17), Scala code byte-identical (29/29 excerpts, one inert whitespace exception), heading-count and math-block-count deltas both fully explained (not gaps). The URL-set diff caught a real bug the compile log couldn't: `\#` escaped inside an `\href` URL argument (not just its display text) silently breaks the link while compiling clean. Fixed, and added to CONVERSION_GUIDE.md since the failure mode is invisible without an explicit URL diff. | Build the arXiv upload archive and clean-room compile it. |
| 2026-09-04 | Clean-room compile of the extracted `output/arxiv-list-source.tar.gz` reproduced the tracked 33-page, 409733-byte PDF exactly, exit 0, zero log issues. Captured all three new durable lessons (shared-`aligned` columns, bare-vs-applied `\operatorname`, `\#`-in-URL) in `CONVERSION_GUIDE.md` for the next article conversion. | Ticket complete; submission (or a release ticket mirroring modulo's) is the author's action. |
| 2026-09-04 | Author caught a visual bug in §10.3 Gap Translation: a short premise-style line and a long equation line were both inside one `aligned`, but only the equation line had a leading `&`; with zero `&` on the premise row, `aligned` right-justified it under the equation's column width instead of centering it, so it sat visibly off to the right. Root cause is distinct from the earlier shared-column-width bug (that one needs `&` on every row; this one is about `aligned` not centering a zero-`&` row independently at all) — both now documented in `CONVERSION_GUIDE.md`. Fixed §10.3, then grep-swept every section file for the same shape (a multi-row `aligned` where no row contains `&`) and found 18 more live instances across §5-§8, all with the exact same latent bug, just less visually dramatic where the two rows happened to be closer in length. Converted all of them (plus §9.1, already fixed) to sequences of independent `equation*` blocks, which is the pattern already used successfully elsewhere in the document (§4's "Goal:" statements). One incidental cleanup: a leftover `\quad` indent in §8.5 that only made sense inside the old shared block was removed now that the line centers on its own. | Rebuild, recompile (zero log issues), rebuild the upload archive, clean-room verify, and visually re-check every affected page. |
| 2026-09-04 | Full rebuild after the sweep: exit 0, zero log issues, clean-room compile of the regenerated archive also exit 0 zero issues. Visually re-inspected §5.1, §6.1-6.2, §7.1, §8.5-8.7, §9.1, and §10.3 — every previously-crooked line now centers correctly, and the blocks that legitimately use `&` (e.g. §8.7's "All Less Than Family") were untouched by the sweep, confirming the grep-based detector (rows split on `\\`, flagged only when zero of them contain `&`) didn't produce false positives. | Ticket complete; same next action as before. |
| 2026-09-04 | Author flagged a second problem in §7.1 before the previous commit landed: earlier overflow-driven splitting (from the very first conversion pass) had over-fragmented the Head Divides Product and Inserted Element Divides Product proofs into many tiny `\qquad`-continuation lines that no longer needed to be split — most of it read fine as compact one-line-per-step statements once isolated (confirmed against the working precedent in §6.1's nearly-identical proof shape). Rebuilt both proofs from the compact form and let the compiler identify the one row per proof that genuinely still overflowed (§7.1's `mod`-wrapped equality; §7.3's Product-Pull-Out tag and its final `mod e` step), rather than guessing. Splitting a wide row that shares an `aligned` with an already-compact `&&`-tagged row re-triggered the shared-column-width bug (one attempt made the overfull grow from 40pt to 174pt) — the fix that actually held was giving each logical proof step its OWN `equation*` (no `aligned` needed for one-line steps; a local flush-left `aligned` only for the one step that itself needed an internal `\\`-break), never mixing a compact tagged row and a wrapped row in the same `aligned`. | Rebuild (zero log issues, 34 pages now vs. 33 — expected from the extra `equation*` blocks), rebuild the archive, clean-room verify, and visually confirm both proofs read as coherent step sequences. |
| 2026-09-04 | Final rebuild and clean-room compile after the §7.1/§7.3 restructuring: exit 0, zero log issues, archive reproduces the tracked PDF. Visually confirmed both proofs now read as clean, independently-centered step sequences matching the rest of the document's house style. | Ticket complete. |
