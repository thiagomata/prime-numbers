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

- Chapter 2 `modulo.md`: inspected in GitHub Preview; no raw dollar syntax was
  observed in the rendered page.
- Chapter 3 `list.md`: inspected in GitHub Preview; no raw dollar syntax was
  observed in the rendered page.
- Chapter 4 `cycle.md`: confirmed defects remain in the rendered page:
  - standalone `$$` is visible in the introduction;
  - raw inline LaTeX appears in §5.7 Cycle Value Positivity;
  - raw inline LaTeX appears in §5.9 MemCycle-Level Restatement;
  - permalink labels expose raw `$i < n$` and `$i \\geq n$` fragments.
- Chapter 4 `integral-cycle.md`, Chapter 4 `integral.md`, Chapter 5, Chapter 6,
  and Chapter 7 remain to be inspected in the browser.

## What Is Learned

- In this repository, a dollar sign is a strong rendering-risk signal even
  when GitHub accepts the source Markdown.
- Fenced `math` blocks render as visible mathematical symbols in GitHub Preview.
- Raw inline `$...$` can remain literal in prose and heading/permalink text.

## Failed Paths

- A single browser batch opening all ten long articles timed out during
  accessibility extraction; smaller batches are required.
- Source grep alone is insufficient evidence for a rendering verdict because
  dollar signs also occur in code fences and arXiv README shell examples.

## Open Concerns

- Any article fix with a matching `articles/arxiv/<article>/` package must be
  synchronized with LaTeX and its PDF under the repository's arXiv rules.
- The current worktree contains unrelated user changes; they must not enter
  this PR.

## Next Action

Continue the GitHub Preview audit, then make one focused rendering cleanup
group and re-check the affected pages before expanding scope.

## Learning Log

| Date | Observation | Decision |
|------|-------------|----------|
| 2026-09-25 | Chapter 4 `cycle.md` visibly exposes raw `$$` and inline LaTeX. | Track as a confirmed rendering defect and use it as the first cleanup target. |
