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

- Chapter 2 `modulo.md`: inspected at commit `8dd94a8` in GitHub Preview.
  The abstract and most math blocks render, but two visible renderer failures
  occur: `Missing \\end{aligned}` in §6.12 and §6.13, followed by raw `$$` math
  source. The page also contains many dollar-delimited expressions in source;
  the browser confirms that some render while malformed blocks do not.
- Chapter 3 `list.md`: inspected in GitHub Preview; no raw dollar syntax was
  observed in the rendered page.
- Chapter 4 `cycle.md`: confirmed defects in the original rendered page:
  - standalone `$$` is visible in the introduction;
  - raw inline LaTeX appears in §5.7 Cycle Value Positivity;
  - raw inline LaTeX appears in §5.9 MemCycle-Level Restatement;
  - permalink labels expose raw `$i < n$` and `$i \\geq n$` fragments.
- The cleanup branch now removes the confirmed raw inline-prose failures and
  unsupported `\\operatorname` usage, and was re-opened in GitHub Preview.
- Chapter 4 `integral-cycle.md`, Chapter 4 `integral.md`, Chapter 5, Chapter 6,
  and Chapter 7 remain to be inspected in the browser.
- Chapter 4 `integral-cycle.md`: inspected at commit `8dd94a8`. GitHub renders
  many display-math blocks, but numerous inline expressions lose their math
  content entirely in the prose (for example the variables in §3.2, §4.1,
  and §5.1), and §5.2 visibly exposes raw `($\\text{pos} < \\text{period}(ci)$)`
  and `($\\text{pos} \\geq \\text{period}(ci)$)` fragments. This is a confirmed
  reader-visible rendering failure, not merely a source-dollar count.
- Chapter 4 `integral.md`: inspected at commit `8dd94a8`. The abstract renders,
  but the body visibly exposes extensive raw inline `$...$` and display `$$...$$`
  source beginning in §2 and continuing through §§3–5 and later. Confirmed
  examples include `$L = [x_0, x_1, \\dots, x_{n-1}] \\in \\mathbb{Z}^n$`, `$n$`,
  `$$I_0 = x_0 + init$$`, and raw math in the list bullets and section headings.
  No explicit `Missing \\end{aligned}` flash-error was observed in this pass;
  the visible defect is the raw math source itself.

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

## Next Action

Continue the GitHub Preview audit, then make one focused rendering cleanup
group and re-check the affected pages before expanding scope.

## Learning Log

| Date | Observation | Decision |
|------|-------------|----------|
| 2026-09-25 | Chapter 4 `cycle.md` visibly exposes raw `$$` and inline LaTeX. | Track as a confirmed rendering defect and use it as the first cleanup target. |
| 2026-09-26 | Chapter 2 `modulo.md` shows two visible `Missing \\end{aligned}` failures in GitHub Preview. | Track flash-errors separately from successfully rendered dollar-delimited math. |
| 2026-09-26 | Chapter 4 `integral.md` exposes raw inline and display math throughout the body in GitHub Preview. | Record the page as a confirmed raw-dollar rendering failure; continue the browser audit before fixing. |
