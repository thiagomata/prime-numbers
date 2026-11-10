# Repo-Wide GitHub Math Rendering Sweep

**Created:** 2026-11-10
**Status:** Active

## START HERE

Micro-goal: fix the remaining GitHub math-rendering breakage outside
`properties/` (34 files), correct PROOF_GUIDE rule 8 against new evidence,
and open one PR.

## Goal

Bring every other markdown tree in the repository (articles, candidates,
companions, empirical, tickets, root files) to the same rendered-clean
state `properties/` reached in PR #65, and narrow PROOF_GUIDE rule 8 to
match the evidence.

## Strategy

1. Fix the one genuine KaTeX error first: `#` inside
   `\text{candidate #14's}` in
   `empirical/sieve-sequence/capacity-density-candidates.md` (escape as
   `\#`). This restores a 0-failure KaTeX baseline across the repo.
2. `\lt` sweep: bare `<`+letter -> `\lt ` inside ```math fences across the
   33 affected tracked files (91 blocks), same transform and audit as
   PR #65 commit `801bf234`.
3. `\operatorname{X}` -> `\text{X}` sweep (10 blocks, 8 files), same as
   PR #65 commit `039bafe7`.
4. Correct PROOF_GUIDE rule 8: after-`\end{aligned}` content is verified
   safe (evidence below); the blanket prohibition is wrong.

Validation: local KaTeX over every math fence in the repo (except
vendored `python/.venv`, `target/`, caches): 0 failures required after
each step; round-trip audits for the scripted sweeps; sweep restricted to
tracked files so untracked user work cannot be touched.

## Current State

- 2026-11-10: Check complete. 34 files carry the two proven breakers
  (91 `<`+letter blocks, 10 `\operatorname` blocks):
  `articles/chapter7/survival-frontiers-detailed.md` (11 lt; added by
  PR #63 after the #61 audit; no arXiv package), `candidates/` (28
  files), `companions/` (3), `empirical/sieve-sequence/capacity-density-candidates.md`
  (4 lt + the `#` KaTeX error), `tickets/active/` (2), root
  `VOCABULARY.md` (3).
- User approved: fix all + rule-8 correction in one PR.

## What Is Learned

- **PROOF_GUIDE rule 8 is over-broad.** Ten
  `\qquad[\text{Q.E.D.}]`-after-`\end{aligned}` blocks were present in
  `articles/chapter7/survival-frontiers.md` at commit `ad23485a`, where
  the PR #61 audit browser-verified the page renders clean (zero raw
  leaks). So after-`\end{aligned}` content does not break GitHub
  rendering. The cycle.md failure that motivated rule 8 co-occurred with
  the trailing-`\\` defect (rule 7) in the same fence; the causal
  attribution was never isolated. Consequence: PR #65's fix 3 (5 blocks)
  was harmless but unnecessary, and the 16 remaining after-end blocks
  (`survival-frontiers.md` x10, companions x6) need no fix.
- A `#` inside `\text{...}` in a math fence is a hard KaTeX error
  ("Expected 'EOF', got '#'") and breaks on GitHub too; escape as `\#`.
- The PR #63 detailed side-editions were added after the rendering audit
  and reintroduced the bare-`<` pattern in
  `survival-frontiers-detailed.md`; future article additions need the
  rendering rules applied at authoring time.
- Trees confirmed clean: articles chapters 2-6 (fixes held),
  `articles/notes`, `presentations/`, `tasks/`, `docs/`, `charts/`,
  `spark/`, `python/*.md`, `companion` models except the three listed.

## Failed Paths

- None yet on this ticket. (Prior-session constraints — browser pane and
  web search unavailable — carry over; rendered-page verification is
  again the user's follow-up.)

## Open Concerns

- `survival-frontiers-detailed.md` has no arXiv package of its own; must
  confirm its content is not folded into `articles/arxiv/survival-frontiers/`
  before editing (if it is, the arxiv-sync rule applies and the change
  must also land in `.tex` + rebuilt PDF).
- Rendered-page spot check after the sweep is the user's follow-up
  (suggest the detailed article and one candidates file).

## Next Action

1. Create branch `docs/repo-wide-github-math-rendering`.
2. Commit ticket; verify detailed-article content is absent from the
   survival-frontiers tex package.
3. Fix the `#` KaTeX error; KaTeX gate to 0 failures repo-wide; commit.
4. `\lt` sweep over tracked files; round-trip audit + KaTeX gate; commit.
5. `\operatorname` sweep; audits + gate; commit.
6. PROOF_GUIDE rule-8 correction; commit.
7. Push, open PR, user verifies rendering, merge.

## Learning Log

| Date | Observation | Decision |
|------|-------------|----------|
| 2026-11-10 | Repo-wide scan (210 md files, 1695 non-properties fences): 34 files with the two proven breakers; 1 genuine KaTeX failure (`#` in `\text{}`); after-end blocks proven safe via ad23485a evidence. | User approved fix-all + rule-8 correction. |
| 2026-11-10 | survival-frontiers-detailed.md (PR #63) reintroduced bare `<` after the audit. | Include it in the sweep; note the process gap in What Is Learned. |

## Related Tickets

- `tickets/archived/properties-github-math-rendering-2026-11-09.md` — the
  properties sweep (PR #65) whose transforms are reused here.
- `tickets/active/github-markdown-rendering-audit-2026-09-25.md` — the
  PR #61 audit; its clean verdict at `ad23485a` is the evidence for the
  rule-8 correction.
