# GitHub Markdown Rendering Audit

**Created:** 2026-09-25
**Status:** Active

## START HERE

Micro-goal: record reader-visible Markdown rendering defects found by opening
the chapter articles in GitHub Preview, then use this record to drive a focused
cleanup PR without disturbing unrelated worktree changes.

## Goal

Audit the canonical chapter articles file by file in GitHub's rendered Preview
and capture raw LaTeX, broken math, malformed headings, tables, links, diagrams,
and other defects that interrupt reading.

## Strategy

1. Inspect each `articles/chapter*/` Markdown file in GitHub Preview.
2. Record only defects visible in the rendered page, with file and section.
3. Fix issues in small, reviewable groups, preserving the article's math and
   Markdown conventions.
4. Re-open the changed pages in GitHub Preview and verify the rendered result.

## Current State

- COMPLETE. All ten chapter articles were re-audited in the browser at branch
  head `ad23485a` and render clean: zero visible raw-dollar fragments, zero
  raw backslash commands, zero `Missing \end{aligned}` errors, with math
  nodes rendering on every page.
- Fixes applied on this branch (in addition to the original `cycle.md` group):
  `integral-cycle.md` (paren-adjacent delimiters, nested `$` in `\text`),
  `euclid-theorem.md` (`\(...\)` marker), `gap-dynamics.md` (hyphen-adjacent
  and `$):` adjacencies), `relaxed-almost-prime.md` (hyphen-adjacent),
  `survival-frontiers.md` (hyphen-adjacent), `cycle.md` (malformed fences).
- Most `8dd94a8` findings were already fixed on master by PRs #60/#62; the
  branch merges master, so `modulo.md` §6.12/§6.13 `Missing \end{aligned}`
  failures are resolved by the merged `\lt` fix.
- Guidelines updated: PROOF_GUIDE "GitHub Math Rendering Rules (Verified in
  the Rendered Page)" (8 rules + verification protocol) and LEARNINGS 14.12a.
- arXiv editions: the Markdown fixes are GitHub-rendering-only (delimiter
  placement, fence structure). The LaTeX editions render the same visible
  text natively (e.g. `size-$K$` is fine in LaTeX), so rendered content is
  identical in both editions and no `.tex` content change or PDF rebuild is
  required for parity.

## What Is Learned

- In this repository, a dollar sign is a strong rendering-risk signal even
  when GitHub accepts the source Markdown.
- Fenced `math` blocks render as visible mathematical symbols in GitHub Preview.
- Raw inline `$...$` can remain literal in prose and heading/permalink text.

## Failed Paths

- A single browser batch opening all ten long articles timed out during
  accessibility extraction; smaller batches are required.
- Source grep alone is insufficient evidence for a rendering verdict because
  dollar signs also occur in code fences and some dollar-delimited expressions
  render successfully. The browser is required to identify visible failures.

## Open Concerns

- Any article fix with a matching `articles/arxiv/<article>/` package must be
  synchronized with LaTeX and its PDF under the repository's arXiv rules.
- The current worktree contains unrelated user changes; they must not enter
  this PR.
- Most audit findings recorded at commit `8dd94a8` were already fixed on
  `master` by PRs #60/#62; the branch now merges master, so re-verification
  must run against the merged head, not the recorded findings.

## Next Action

None — audit complete and all reader-visible failures fixed and re-verified
in the browser at `ad23485a`. Ready for review/merge of PR #61.

## Learning Log

| Date | Observation | Decision |
|------|-------------|----------|
| 2026-09-25 | Chapter 4 `cycle.md` visibly exposes raw `$$` and inline LaTeX. | Track as a confirmed rendering defect and use it as the first cleanup target. |
| 2026-09-26 | Chapter 2 `modulo.md` shows two visible `Missing \\end{aligned}` failures in GitHub Preview. | Track flash-errors separately from successfully rendered dollar-delimited math. |
| 2026-09-26 | Chapter 4 `integral.md` exposes raw inline and display math throughout the body in GitHub Preview. | Record the page as a confirmed raw-dollar rendering failure; continue the browser audit before fixing. |
| 2026-09-26 | Chapter 5 `euclid-theorem.md` loses inline math in many rendered paragraphs and leaks `\\blacksquare`/`\\text{[Q.E.D.]}` in §4.4. | Record as a confirmed reader-visible math rendering failure; continue the browser audit. |
| 2026-09-26 | Chapter 6 `gap-dynamics.md` exposes raw dollar-delimited math across the page. | Record as a page-wide raw-dollar rendering failure. |
| 2026-09-26 | Chapter 6 `relaxed-almost-prime.md` loses inline math and visibly leaks `$P_2$` in list/table text. | Record both missing-math and raw-dollar defects; continue the browser audit. |
| 2026-09-26 | Chapter 6 `sieve-sequence.md` loses most inline mathematical content in definitions and theorem prose. | Record as a confirmed missing-inline-math failure. |
| 2026-09-26 | Chapter 7 `survival-frontiers.md` exposes raw inline and display math throughout the rendered page. | Record as a page-wide raw-dollar rendering failure. |
| 2026-09-26 | Re-audit at master HEAD shows most `8dd94a8` findings already fixed by PRs #60/#62 (`integral.md` fully clean). | Audit against merged head; do not fix stale findings. |
| 2026-09-26 | `integral-cycle.md` §5.2 leaked `($\\text{pos} \\lt ...$):` even after `<`→`\\lt`; the failure is the closing `$` immediately followed by `)`. | Remove the `(...)` wrapper around inline math followed by `:`; fixed and pushed. |
| 2026-09-26 | Hyphen-adjacent inline math (`filter-$7$`, `prime-plus-$P_2$`) leaks raw source in `gap-dynamics.md`. | Insert a space or reword; fixed and pushed. |
| 2026-09-26 | `\\(...\\)` QED marker in `euclid-theorem.md` §5 renders as literal text. | Replace with plain `[Q.E.D.]` text; GitHub renders only `$...$` and fenced math. |
| 2026-09-26 | GitHub math rendering is deferred (8–10s) and rendered math nodes embed hidden TeX annotations that false-positive raw-source regexes. | Browser checks must wait and filter to visible text; protocol recorded in PROOF_GUIDE and LEARNINGS 14.12a. |
| 2026-09-26 | First load of a blob page can fail to hydrate math entirely (0 `<math>` nodes, everything raw); a reload renders normally. | Treat 0-math-node results as hydration flakes: reload before diagnosing. |
| 2026-09-26 | `cycle.md` leaked stray `$` from math fences: trailing `\\\\` on the last line before the closing fence, and a `\\forall` line placed after `\\end{aligned}` inside the fence. | Fixed fence structure; recorded as PROOF_GUIDE rules 7–8. |
| 2026-09-26 | Hyphen-adjacent inline math also present in `relaxed-almost-prime.md` (`prime-plus-$P_2$`, `modulo-$3$`) and `survival-frontiers.md` (`size-$K$`, `size-$J_r$`). | Fixed by inserting a space; LaTeX editions keep the hyphen form since LaTeX renders it correctly — no tex drift. |
