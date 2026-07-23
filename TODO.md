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

- [ ] Decide whether `articles/draft/draft-sieve-foundation.md` should remain a
  draft bridge or be folded into `articles/chapter6/sieve-sequence.md`.
- [ ] Keep `articles/draft/draft-sieve-gap-survival-math.md` and
  `articles/draft/exercise-local-safe-window-capacity.md` clearly scoped as
  mathematical exploration until their claims have verified source references.
- [ ] Keep `articles/draft/draft-empirical-g-local-analysis.md` explicitly
  empirical / `@extern`, or merge only its limitations into
  `articles/chapter6/gap-dynamics.md`.
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
