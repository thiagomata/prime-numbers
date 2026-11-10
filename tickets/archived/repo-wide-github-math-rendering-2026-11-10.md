# Repo-Wide GitHub Math Rendering Sweep

**Created:** 2026-11-10
**Status:** Closed — user verified the rendered pages clean on the branch (2026-11-10); merged via PR #66

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
- 2026-11-10: All fixes applied on branch
  `docs/repo-wide-github-math-rendering`:
  - `54456332` — `#` escaped as `\#` in the empirical fence; KaTeX
    baseline to 0 failures.
  - `068a1be4` — 115 `<`+letter -> `\lt ` substitutions in 32 tracked
    files.
  - `16eaa482` — 9 fence `\operatorname` -> `\text` substitutions in 6
    files, the starred `\operatorname*{arg\,min}` form in
    seven-layer-capacity-floor.md, and 4 inline `$...$` instances in
    tickets/future/sieve-property-landscape.md (same breaker, inline
    form; scope addition discovered during the sweep).
  - `89102311` — PROOF_GUIDE rule 8 corrected to match the evidence.
- Final verification: zero remaining `<`+letter or `\operatorname` in
  any tracked markdown math fence repo-wide; 3640 fences (properties +
  everything else) all parse under local KaTeX; confirmed the detailed
  edition's content is absent from articles/arxiv/survival-frontiers/
  (zero tex mentions), so no LaTeX sync applies.
- Left alone deliberately: `\operatorname` inside backtick code spans
  (companions/balanced-randomized-2-gap/model.md — code spans run no
  math processing) and prose mentions in guides/tickets that document
  the macro itself.
- 2026-11-10: User spot-checked the rendered pages on the branch
  (detailed article + candidates) and confirmed clean rendering.
  Remediation of the staging incident verified in the final net diff
  (37 intended files, no user files). Ticket closed; moved to
  `tickets/archived/`.

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

- **2026-11-10 staging error (PR #66, fixed same day):** the lt-sweep
  commit used `git add -A ':!tickets'`, which staged the untracked user
  file `candidates/twin-analysis-advancement-plan.md` (byte-identical,
  never modified, but exposed in the pushed PR) and simultaneously
  excluded the two `tickets/active` files the sweep had fixed. Root
  cause: sweeping over `git ls-files` (correct) but staging with a
  broad pathspec instead of the changed-file list. Remediation (user
  chose surgical fix): `git rm --cached` the file (returns to
  untracked), commit the two omitted fixes, push. Net PR diff verified
  correct (37 intended files, no user files). Lesson: stage exactly the
  files a scripted change wrote — derive the path list from the script's
  own output, never from `-A` with exclusions. The file's content
  remains visible in PR #66's intermediate commit `068a1be4` (user
  accepted this).
- Prior-session constraints — browser pane and web search unavailable —
  carry over; rendered-page verification is the user's follow-up.

## Open Concerns

- `survival-frontiers-detailed.md` has no arXiv package of its own; must
  confirm its content is not folded into `articles/arxiv/survival-frontiers/`
  before editing (if it is, the arxiv-sync rule applies and the change
  must also land in `.tex` + rebuilt PDF).
- Rendered-page spot check after the sweep is the user's follow-up
  (suggest the detailed article and one candidates file).

## Next Action

1. ~~Create branch~~ done.
2. ~~Ticket commit; arXiv-package check~~ done (detailed edition absent
   from the tex package).
3. ~~`#` fix; KaTeX gate to 0~~ done (`54456332`).
4. ~~`\lt` sweep~~ done (`068a1be4`).
5. ~~`\operatorname` sweep~~ done (`16eaa482`).
6. ~~PROOF_GUIDE rule-8 correction~~ done (`89102311`).
7. ~~Push, open PR, user verifies rendering, merge, close ticket~~ done
   (PR #66; user verified 2026-11-10; ticket closed).

## Learning Log

| Date | Observation | Decision |
|------|-------------|----------|
| 2026-11-10 | Repo-wide scan (210 md files, 1695 non-properties fences): 34 files with the two proven breakers; 1 genuine KaTeX failure (`#` in `\text{}`); after-end blocks proven safe via ad23485a evidence. | User approved fix-all + rule-8 correction. |
| 2026-11-10 | survival-frontiers-detailed.md (PR #63) reintroduced bare `<` after the audit. | Include it in the sweep; note the process gap in What Is Learned. |
| 2026-11-10 | The `\operatorname` sweep surfaced two forms the fence regex missed: the starred `\operatorname*{arg\,min}` and inline `$...$` math in tickets/future. | Fixed both with targeted edits; disclosed as scope additions. `\operatorname` inside backtick code spans left alone (no math processing). |
| 2026-11-10 | Final gate: 3640 fences repo-wide, 0 KaTeX failures, 0 remaining breakers in tracked fences. | Ready for PR. |
| 2026-11-10 | PR-content verification caught an accidentally staged untracked user file and two omitted tickets/active fixes (bad `git add -A ':!tickets'` pathspec). | Stop-and-ask; user chose surgical fix; remediated and re-verified net diff (37 files). Rule for next time: stage the script's changed-file list, not `-A`. |
| 2026-11-10 | User verified rendered pages clean on the branch. | Close the ticket; merge PR #66. |

## Related Tickets

- `tickets/archived/properties-github-math-rendering-2026-11-09.md` — the
  properties sweep (PR #65) whose transforms are reused here.
- `tickets/active/github-markdown-rendering-audit-2026-09-25.md` — the
  PR #61 audit; its clean verdict at `ad23485a` is the evidence for the
  rule-8 correction.
