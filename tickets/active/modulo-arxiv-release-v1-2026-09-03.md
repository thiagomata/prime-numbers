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
- Local `just verify-ch 2` run REPRODUCED the quoted totals: total 1374,
  valid 1374 (1364 from cache, 10 trivial), invalid 0, unknown 0
  (33.2s). Stainless 0.9.8.8 confirmed from install dir; bundled Scala
  3.3.3 confirmed from log line 1 ("Compiling with standard Scala 3.3.3
  compiler front end"). Chapter log file: `logs/verify-ch-2-v1-chapter2-_.log`.
- Stainless citation added from the official references page: Hamza,
  Voirol, Kuncak — *System FR: Formalized Foundations for the Stainless
  Verifier*, OOPSLA 2019 (no DOI listed; official PDF URL used as note).
- Content edits applied: A.4 reproducibility statement (tag-pinned log
  link), intro `\cite{hamza2019systemfr}` (Hardy & Wright auto-renumbers
  to [2]), ℕ = {0,1,2,...} sentence in §4, `main.tex` plain `\input`
  (IfFileExists guards removed), all section links pinned to
  `blob/modulo-article-v1.0.0/`. 14-page build green; archive clean-room
  compile green (14 pages).
- Author approved Docker addition (Option A): implemented `--docker` flag
  in `scripts/verify-ch.sh` (same chapter scoping/focus inside the
  compose service, `--vc-cache=false` cold cache, logs get a `-docker`
  suffix); `verify-ch` recipe is now variadic (`just verify-ch 2
  --docker`); README's stale `just verify-docker` section rewritten (the
  recipe had been removed from the justfile while the README still
  advertised it). Docker (OrbStack) daemon started; chapter-2 Docker run
  in progress — first run builds the image.
- Docker run DOCKER REPRODUCED THE TOTALS: cold cache (`--vc-cache=false`,
  0 from cache) in the container (arm64; native z3 JNI unavailable in the
  container so Stainless fell back to its bundled cvc5) reported
  `total: 1374 valid: 1374 (0 from cache, 10 trivial) invalid: 0
  unknown: 0` in 309.56s. Two instructive failures fixed en route:
  (1) the release zip extracts FLAT into /opt/stainless, so the binary is
  on PATH directly (a `stainless-dotty-standalone-0.9.8.8/stainless`
  subpath fails with exit 127); (2) native z3 needs the x86-64 JNI jar —
  on arm64 containers Stainless warns and falls back to cvc5 (documented
  here, not in the paper). A.4 gained the containerized-reproduction
  sentence linking both pinned logs; both chapter-2 logs are force-added
  to git (`logs/*.log` is gitignored, so links would 404 otherwise).

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
