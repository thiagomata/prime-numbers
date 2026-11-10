# Properties GitHub Math Rendering Fixes

**Created:** 2026-11-09
**Status:** Closed — user verified the rendered pages clean on the branch (2026-11-10); merged via PR #65

## START HERE

Micro-goal: fix the GitHub math-rendering breakage across `properties/**/*.md`
(the reported "Extra open brace or missing close brace" class and the other
documented breakers), then open one PR.

## Goal

Make every ` ```math ` fence in `properties/` render correctly on GitHub blob
pages, using the fix patterns already browser-verified for the articles in
PRs #60/#61/#62, without changing mathematical content.

## Strategy

Three mechanical fixes, one commit per pattern (mirroring PR #60/#61
structure):

1. Replace bare `<` immediately followed by a letter with `\lt ` inside
   ` ```math ` fences only (64 files, 191 blocks). Root cause: GitHub's
   HTML-tag detection swallows `<letter...>` before the math renderer sees
   it, corrupting brace balance ("Extra open brace or missing close brace").
   Leave `<=`, `<\`, `<`+digit, `>`, prose, and backtick spans untouched
   (non-letter-adjacent `<` cannot start an HTML tag; `>` is verified safe).
2. Replace `\operatorname{X}` with `\text{X}` inside math fences
   (15 files, 28 uses) — GitHub rejects `\operatorname` ("macro not
   allowed"); `\text{...}` is the sanctioned Markdown form per
   `articles/arxiv/CONVERSION_GUIDE.md`.
3. Move content placed after `\end{aligned}` inside a fence onto the last
   aligned row (5 blocks in 3 files) — PROOF_GUIDE rule 8: a line after
   `\end{aligned}` breaks the block.

Validation: local KaTeX parse of every properties math fence (all must
pass), plus a script-verified diff audit proving no change outside the
intended transforms. Browser re-verification of the rendered pages is the
user's follow-up (browser pane unavailable in this session).

## Current State

- 2026-11-09: Research complete. Scan of all 101 property files found:
  191 blocks with `<`+letter in fences (64 files), 28 `\operatorname` uses
  (15 files), 5 blocks with content after `\end{aligned}` (3 files).
  Ruled out as false positives: `}` after `\end{aligned}` from `\boxed{`
  wrappers (6), `\\[6pt]` line-break spacing misread as `\[` (3), inline
  `$...$` in prose (1, renders fine, left alone).
- User confirmed the root cause is the `<`-as-HTML-tag issue (same as the
  articles before PR #60) and approved fixing all three breakers in one PR.
- 2026-11-09: All three fixes applied on branch
  `docs/properties-github-math-rendering`, one commit per pattern:
  - `801bf234` — 246 `<`+letter -> `\lt ` substitutions, 64 files.
  - `039bafe7` — 30 `\operatorname` -> `\text` substitutions, 15 files
    (one prose-backtick occurrence left alone: no math processing there).
  - `3a2b7bf3` — 5 post-`\end{aligned}` fragments moved onto the last
    aligned row, 3 files (4 changed).
- Validation gates all green: local KaTeX parses 1945/1945 properties
  fences before and after every step; round-trip audits prove prose is
  byte-identical and fences changed by exactly the intended substitution;
  rule-8 scanner reports zero remaining violations.
- 2026-11-10: User opened the example file on the PR branch in GitHub and
  confirmed the math renders clean — the rendered-page follow-up is
  satisfied. Ticket closed; moved to `tickets/archived/`.

## What Is Learned

- The properties tree follows the same fence style as the articles but was
  never included in the 2026-09-25 rendering audit, which covered only
  `articles/chapter*/`.
- The properties style keeps simple expressions in backticks (safe: no math
  processing) and LaTeX in ` ```math ` fences, so all breakage is inside
  fences.
- `\boxed{...}` renders fine on GitHub per the user's report (the errors
  track the `<`-containing blocks), and `\begin{aligned}` renders fine
  (proven by the articles), so neither is touched.

## Failed Paths

- Web search for independent `\boxed`-on-GitHub evidence: unavailable in
  this session (search cancelled).
- Browser verification of the rendered page: built-in browser tools not
  available in this session; cannot self-verify rendering. Mitigated by
  user confirmation of the root cause and the KaTeX + diff-audit gates.

## Open Concerns

- Rendered-page verification after the fix is a user follow-up: re-open
  `properties/sieve-sequence/incomplete-block-bessel-excludes-no-capacity.md`
  on the PR branch and confirm the math nodes render with no red errors.
- `<=` inside fences is left as-is (not letter-adjacent, cannot open an
  HTML tag, matches PR #60's verified rule). If any `<=`-only fence is ever
  observed failing, revisit.
- If a future audit finds `\boxed` or other constructs failing on GitHub,
  that is a separate ticket (would need rendered-page evidence).

## Next Action

1. ~~Create branch~~ done.
2. ~~Apply fix 1, validate, commit~~ done (`801bf234`).
3. ~~Apply fix 2, validate, commit~~ done (`039bafe7`).
4. ~~Apply fix 3, validate, commit~~ done (`3a2b7bf3`).
5. ~~Push branch, open PR against master~~ done (PR #65).
6. ~~User re-opens the example file in GitHub and confirms clean
   rendering~~ done (2026-11-10). Ticket closed.

## Learning Log

| Date | Observation | Decision |
|------|-------------|----------|
| 2026-11-09 | User reports "Extra open brace or missing close brace" on `incomplete-block-bessel-excludes-no-capacity.md`. | Same error class PR #60 fixed in articles: bare `<`+letter inside math fences. |
| 2026-11-09 | Scan: 191 `<`+letter blocks across 64 property files; 28 `\operatorname`; 5 post-`\end{aligned}` blocks; boxed-aligned and `\\[6pt]` hits are false positives. | Scope the PR to the three documented breakers; user approved. |
| 2026-11-09 | Browser pane and web search unavailable in this session. | Rely on KaTeX parse gate + mechanical diff audit + user's rendered-page confirmation; record rendered verification as user follow-up. |
| 2026-11-09 | Baseline KaTeX run: all 1945 properties fences parse — the tree is valid TeX; every failure is GitHub-side pre-processing/macro restriction. | Gate for this PR is "1945/1945 parse after each step", which held at every step. |
| 2026-11-09 | The `\lt` sweep: `<\cdots`, `<=`, `<`+digit untouched by design; `\boxed` untouched (user confirmed `<` is the breaker). | Kept the substitution strictly to `<`+letter, matching PR #60's verified rule. |
| 2026-11-10 | User verified the example page renders clean on the PR branch. | Close the ticket; rendered-page follow-up satisfied. |

## Related Tickets

- `tickets/active/github-markdown-rendering-audit-2026-09-25.md` — the
  articles rendering audit whose browser-verified rules (PROOF_GUIDE
  "GitHub Math Rendering Rules") this PR applies to `properties/`.
- `tickets/active/markdown-cleanup-audit-2026-07-23.md` — earlier markdown
  cleanup audit.
