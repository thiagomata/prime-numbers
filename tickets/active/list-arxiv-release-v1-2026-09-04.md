# list arXiv Release v1.0.0

**Created:** 2026-09-04
**Updated:** 2026-09-04
**Status:** Complete — tag `list-article-v1.0.0` cut and pushed
**Depends on:** `list-arxiv-latex-2026-09-04.md` (manuscript is arXiv-ready;
this ticket cuts the tagged, verified release — mirrors
`modulo-arxiv-release-v1-2026-09-03.md`)

## START HERE

Nothing left to do. Verification, link pinning, tag, and push are done.
See Learning Log for the full story, including the Docker detour.

## Related Tickets

- `list-arxiv-latex-2026-09-04.md` — the manuscript conversion this
  release builds on.
- `modulo-arxiv-release-v1-2026-09-03.md` — the release this one mirrors
  (same `just verify-ch <n>` flow, same tag-pinning approach).

## Goal

Publish `list-article-v1.0.0`: an immutable tag whose commit has every
GitHub link in `articles/arxiv/list/` pointing at itself, backed by a
reproduced verification log.

## Verification

`just verify-ch 3` (list.md = `src/main/scala/v1/chapter3/list/`):
`total: 1602 valid: 1602 invalid: 0 unknown: 0` (30.47s). Stainless
0.9.8.8, Scala 3.3.3. Log: `logs/verify-ch-3-v1-chapter3-_.log`
(force-added; gitignored otherwise).

Docker cold-cache reproduction was attempted and dropped from the article
— see Open Concerns / Learning Log. The manuscript's Appendix B cites
only the local run.

## Link Pinning

All 101 `blob/master/` links across `main.tex` and 11 section files
replaced with `blob/list-article-v1.0.0/` (scripted replace, count
verified). Includes the `modulo.md` cross-reference in §7, pinned to the
`list` tag itself rather than `modulo-article-v1.0.0` — one tag per
package, simpler rule. Author's GitHub profile link (bare `\url`, no
`blob/`) left unpinned, matching modulo's convention.

## Current State

Done. PDF and archive rebuilt and clean-room compiled clean after every
change. Tag pushed.

## What is Learned

- Docker verification for chapter 3 hits two genuine solver timeouts
  (`ListProduct.productPullOutElement`, `ListProduct.productConcatLemma`)
  under `cvc5` (no native Z3 on arm64) — confirmed real, not "almost
  there": doubling the timeout (300s → 600s) changed nothing, both hit
  the wall at exactly 600.1s. Both proofs are valid outside Docker.
- Attempts to reproduce this with a direct local `stainless` invocation
  (bypassing `just verify-ch`) crashed on an unrelated Dotty compiler
  exception three times in a row — an environment quirk in invoking the
  binary standalone, not a solver issue. Left uninvestigated; use
  `just verify-ch` for any future local reproduction.

## Failed Paths

- **Docker reproduction in the article's Appendix B**: written once with
  "reports identical totals" (wrong — not yet run), corrected to the
  honest 1,600/0/2 result with an explanation once the run finished, then
  dropped from the article entirely per author decision — Docker
  verification isn't part of this article's story, and the known
  limitation belongs in project docs, not the paper. Retry only if the
  Z3-in-Docker gap gets fixed and someone wants the containerized
  reproduction back in.
- **Raising the Docker timeout as the fix**: tested directly (300s and
  600s), no change — both VCs hit the wall exactly both times. Don't
  retry this without also changing the solver.

## Open Concerns

- The Docker/cvc5 timeout is real and documented as a known issue in the
  main `README.md`'s Docker section (not in the article). No fix
  implemented; the two candidates (get the container to use a working Z3,
  or add explicit intermediate `assert`s to the two lemmas) are noted
  there but untested.

## Next Action

None — ticket complete.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-09-04 | Local `just verify-ch 3` reproduced 1602/1602/0/0. Pinned all 101 `blob/master` links to `list-article-v1.0.0` via scripted replace. Rewrote Appendix B with the reproducibility statement (initially including a Docker paragraph). | Run Docker cold-cache reproduction before trusting the "identical totals" claim. |
| 2026-09-04 | Docker run (851.79s) came back 1600/0/2, not identical — two `ListProduct` postconditions time out under the container's `cvc5` fallback (no native Z3 on arm64). Corrected Appendix B to report the real numbers with an explanation rather than the wrong "identical" claim. | Author asked whether raising the timeout would fix it. |
| 2026-09-04 | Tested directly: doubled the timeout (300s→600s) on just the two failing functions. No change — both still time out, hitting the wall at exactly 600.1s both times. Separately, three attempts to get a clean cold local read on which solver handles these VCs crashed on an unrelated Dotty exception when invoking `stainless` directly (outside `just verify-ch`) — left uninvestigated. | Reported findings; author decided to drop Docker from the article and note it as a known issue in the README instead. |
| 2026-09-04 | Removed the Docker paragraph from Appendix B (article now cites only the local run). Added a concise known-issue note to `README.md`'s Docker section — softened after review to avoid asserting an untested fix as certain ("looks like the fix, but that's untested"). Rebuilt PDF/archive, clean-room verified. Force-added the local verify log (gitignored `logs/`), committed, tagged `list-article-v1.0.0`, pushed branch + tag. | Ticket complete. |
