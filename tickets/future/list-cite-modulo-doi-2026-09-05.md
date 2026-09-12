# Update list article with modulo arXiv DOI

**Created:** 2026-09-05
**Status:** Waiting — blocked on the modulo arXiv DOI being issued
**Type:** Follow-up (reference update, no math changes)

## Trigger

Once the modulo article (*Division and Modulo from Recursive
Normalization*) is submitted to arXiv and receives its DOI.

## What to update

The list article references the modulo article as a "companion article"
in exactly two places:

1. **LaTeX** — `articles/arxiv/list/sections/07-product-divisibility.tex`
   (Section 7, Product Divisibility Properties, first paragraph): the
   companion article is a prose `\href` pointing at
   `blob/list-article-v1.0.0/articles/chapter2/modulo.md` (the Markdown
   file inside the list tag's tree — functional but not a formal
   citation).
   - Add the modulo paper to `articles/arxiv/list/references.bib`
     (e.g. `@misc{mata2026modulo, author = {Mata, Thiago Henrique},
     title = {Division and Modulo from Recursive Normalization}, ...}`
     with the arXiv ID/DOI in the note or doi field — only real
     metadata, nothing invented).
   - Replace the `\href` with `companion article~\cite{mata2026modulo}`
     (optionally keeping the arXiv URL).
2. **Markdown** — `articles/chapter3/list.md` (line ~879): the companion
   link points at `blob/master/articles/chapter2/modulo.md` — a moving
   target inconsistent with the tag-pinning scheme. Update it to the
   arXiv abs/DOI URL.

## Sequencing recommendation

If the **list** article has not been submitted to arXiv yet: submit
**modulo first**, wait for its DOI, fold this update in, and then submit
list — its first submission then already cites the companion properly
(no post-publication revision).

If list is already published on arXiv: this becomes
`list-article-v1.0.1` (patch — reference update only), with the reproducibility
statement unchanged (no Scala sources touched) and links re-pinned per
the versioning rules (never move the old tag).

## Validation

- LaTeX: rebuild via `just arxiv-pdf list`; zero log issues; References
  section shows the new entry; no undefined citations (`references.bib`
  and the `\cite` land in the same commit).
- Markdown: link resolves; no other content changes.

## Related

- `list-arxiv-release-v1-2026-09-04.md` and
  `list-arxiv-latex-2026-09-04.md` (active) — the list article packages.
- `modulo-arxiv-release-v1-2026-09-03.md` (archived) — modulo release.
