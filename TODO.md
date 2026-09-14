# TODO

This file is a small current backlog only. Historical cleanup lists belong in
`docs/markdown-cleanup-manifest.md`; proof execution details belong in active
tickets.

## Documentation Cleanup

- [ ] Review the deletion candidates in `docs/markdown-cleanup-manifest.md`.
- [ ] Decide whether to remove `tickets/trash/` and `articles/deprecated/`.
- [ ] Triage `tickets/done/`: keep only the referenced anchor tickets or extract
  durable lessons into `LEARNINGS.md` / `OBJECTS.md` and remove the raw tickets.
- [ ] Collapse or archive `tasks/` after salvaging any still-current planning
  notes.

## Article Triage

- [x] `draft-sieve-foundation.md` deleted 2026-09-14: retired rather than
  folded in or kept — §§2-3 already published in `integral-cycle.md` §4.6,
  §§4-6 verified but consumed by nothing any article cites (see
  `articles/notes/README.md` "Superseded material (deleted 2026-09-14)").
- [x] `draft-sieve-gap-survival-math.md` deleted 2026-09-13 as superseded
  (content preserved in `articles/chapter6/gap-dynamics.md` and git history).
- [x] `draft-empirical-g-local-analysis.md` deleted 2026-09-13 as superseded
  (canonical `[q,q^2)` experiment replaced it; see git history).
- [x] `exercise-local-safe-window-capacity.md` moved 2026-09-14 to
  `articles/notes/` (pedagogical exercise, never headed for a chapter
  number); math converted to `math`/`$...$`, restated background replaced
  with links into `sieve-sequence.md` and `gap-dynamics.md` §4.3–4.4.
- [ ] Consider merging durable cautions from
  `articles/learnings/reviewer-notes-gap-dynamic.md` into
  `articles/learnings/learnings-capacity-argument.md`.

## Chapter 6 Reconciliation

- [ ] Reconcile stale Chapter 6 tickets with the current source tree before
  assuming any proof remains open.
- [ ] Audit `OBJECTS.md` Chapter 6 entries against current source. Several
  entries still describe old surfaces that are not present under
  `src/main/scala/v1/chapter6/`.
- [ ] Decide whether old tickets such as `tickets/active/sieve-sequence-proof.md`
  and `tickets/active/repeat-filter-rotate-cycle-path.md` should move to
  `tickets/done/`, `tickets/trash/`, or be rewritten as migration notes.
