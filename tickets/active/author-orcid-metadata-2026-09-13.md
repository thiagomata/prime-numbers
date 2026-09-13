# Author ORCID metadata

**Created:** 2026-09-13
**Status:** Complete — all editions updated, all PDFs rebuilt green, full parity PASS
**Depends on:** `arxiv-sync` rule, `arxiv-pdf` zero-warning gate, `arxiv-parity`

## Goal

Record the author's ORCID (https://orcid.org/0009-0002-7366-939X) in the
author identity block of every article edition (Markdown source + arXiv
LaTeX package), keeping both editions in sync per rule `arxiv-sync`.

## What was done

- 8 Markdown articles: `**ORCID:** [0009-0002-7366-939X](https://orcid.org/0009-0002-7366-939X)`
  inserted directly after the `**Email:**` line of the author header
  (modulo, list, cycle, integral-cycle, integral, euclid-theorem,
  gap-dynamics, sieve-sequence).
- 8 arXiv packages: `\small ORCID: \href{https://orcid.org/0009-0002-7366-939X}{0009-0002-7366-939X}\\`
  inserted after the email line of the `\author{}` block in main.tex.
- All 8 PDFs rebuilt via `just arxiv-pdf` (exit 0, zero-warning log gate
  passed for every package).
- `just arxiv-parity`: all 8 packages PASS (same benign warnings as
  before, none new — the ORCID url is present on both sides).
- Title-page render verified in the integral-cycle PDF text layer.

## Open Concerns / Next Action

- The `output/arxiv-*-source.tar.gz` upload archives embed the previous
  main.tex and are now stale; they are refreshed per-package at release
  time (no just recipe exists for tarballs). Refresh before any arXiv
  upload.
- gap-dynamics main.tex carries this change on top of its ticket's
  uncommitted de-drafting work — will be committed together with it.
