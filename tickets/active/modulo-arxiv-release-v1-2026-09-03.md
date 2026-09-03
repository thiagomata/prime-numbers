# modulo arXiv Release v1.0.0

**Created:** 2026-09-03
**Updated:** 2026-09-03
**Status:** In progress
**Depends on:** `modulo-arxiv-latex-2026-09-02.md` (manuscript is arXiv-ready;
this ticket covers the team's pre-submission recommendations and the tagged
release flow)

## START HERE

Implement the team's review (priority: reproducibility statement + Stainless
citation), switch all GitHub links to an immutable tag, and produce the
release: branch `codex/release-modulo-arxiv-v1`, tag `modulo-article-v1.0.0`,
rebuilt arXiv archive.

## Related Tickets

- `modulo-arxiv-latex-2026-09-02.md` — the manuscript ticket this release
  builds on.

## Goal

Address the team review, then publish the verified state as an immutable
tagged release whose links the article can reference permanently.

## Team Recommendations (opinion comments, author-prioritized)

1. Reproducibility statement (PRIORITY): A.4 currently links the generic
   `logs/verify.log` (contains an unrelated Chapter 6 run). Replace with a
   tag-pinned Chapter 2 result recording Stainless version, bundled Scala
   version, command `just verify-ch 2`, valid/invalid/unknown totals, and
   the final commit reference. NOTE: a raw commit hash cannot be embedded in
   the commit it identifies; the immutable tag name is the self-consistent
   pin.
2. Stainless citation (PRIORITY): add the framework and preferably
   *System FR* to `references.bib`, cite where Stainless is introduced.
3. Define $\mathbb{N}=\{0,1,2,\ldots\}$ explicitly (several results include
   zero).
4. "Distributivity" wording — team says "consider"; author marked all
   comments as opinion, not gospel. DEFERRED: renaming §6.9/§6.10 and the
   `[Distributivity, *]` recap tags diverges from the frozen Markdown
   edition's own labels; needs a conscious author decision, not a silent
   release edit. Recorded as an open question.
5. Replace `\IfFileExists` wrappers with plain `\input` in `main.tex`
   (upload can't silently drop sections). Conversion is complete, so the
   scaffold's partial-compile convenience is no longer needed.

## Release Flow (team thread)

1. Branch `codex/release-modulo-arxiv-v1`.
2. Run `just verify-ch 2`; record Stainless version and totals (verify
   numbers ourselves — do not trust quoted values).
3. Update every GitHub source/log link from `blob/master/` to
   `blob/modulo-article-v1.0.0/`.
4. Recompile and inspect the PDF.
5. Commit everything; create tag `modulo-article-v1.0.0`; push branch+tag.
6. Confirm links resolve on GitHub; rebuild the arXiv source archive.

## Current State

- Manuscript arXiv-ready per the base ticket (13 pages, parity audited).
- Team review received; no changes made yet.
- The quoted verification totals (Stainless 0.9.8.8, Scala 3.3.3,
  1,374 valid) are UNVERIFIED claims until the run reproduces them.

## What is Learned

- (empty — fill as work proceeds)

## Failed Paths

- (empty)

## Open Concerns

- Item 4 (distributivity wording) deferred pending author decision; it
  changes headings/labels that mirror the frozen Markdown edition.
- The Markdown article `articles/chapter2/modulo.md` is NOT updated with
  the ℕ sentence or reproducibility statement; the LaTeX manuscript is the
  submission artifact and may diverge via sanctioned editorial additions.
  The Markdown should be synced by the author separately if desired.

## Next Action

Create the release branch, kick off `just verify-ch 2` in the background,
and gather the exact Stainless citation metadata while it runs.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-09-03 | Ticket created from team review; verification numbers must be reproduced locally before entering the manuscript. | Branch, verify, edit, tag, push, rebuild archive. |
