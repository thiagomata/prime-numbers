# Markdown Cleanup Manifest

**Created:** 2026-07-23

This manifest classifies markdown files by cleanup action. It is intentionally
non-destructive: use it to review what can be reduced, merged, archived, or
deleted manually.

## Snapshot

- Curated source markdown found by `rg --files -g '*.md'`: 140 files, 47,356
  lines
- Markdown files reported by `git ls-files '*.md'`: 187 files
- Obvious historical bucket: `tickets/trash/`
- Completed ticket bucket: `tickets/done/` has 42 files and 8,842 lines
- Generated markdown outside the source tree also exists under `.metals/` and
  `target/`; those are build/tool artifacts and should not be treated as source
  documentation.

## Keep Canonical

These files define current project guidance, public entry points, or active
article surfaces:

- `README.md`
- `AGENTS.md`
- `CONTRIBUTING.md`
- `PROOF_GUIDE.md`
- `OBJECTS.md`
- `LEARNINGS.md`
- `TODO.md`
- `docs/architecture.md`
- `docs/proof-dependencies.md`
- `articles/chapter2/modulo.md`
- `articles/chapter3/list.md`
- `articles/chapter4/integral.md`
- `articles/chapter4/cycle.md`
- `articles/chapter4/integral-cycle.md`
- `articles/chapter5/euclid-theorem.md`
- `articles/chapter6/sieve-sequence.md`
- `articles/chapter6/gap-dynamics.md`
- `articles/learnings/learnings-capacity-argument.md`
- `properties/sieve-sequence/README.md`

## Delete Candidates After Owner Review

These files are already classified as historical by path or banner. They are
the strongest candidates for deletion from a lean working tree.

### Ticket Trash

All markdown files under:

- `tickets/trash/archived/`
- `tickets/trash/superseded/`

Rationale: `tickets/README.md` says stale tickets, superseded approaches, old
planning records, and article reviews live here and should not drive current
work.

### Deprecated Articles

- `articles/deprecated/deprecated-sieve-foundation.md`
- `articles/deprecated/deprecated-gap-persistence.md`
- `articles/deprecated/deprecated-generalized-gap-dynamic.md`
- `articles/deprecated/deprecated-twin-prime-persistence.md`
- `articles/deprecated/deprecated-sieve-sequence.md`

Rationale: each is explicitly marked deprecated. Several have stale superseding
links or stale source references. Current chapter-6 articles and learnings
articles should be the source of truth instead.

## Merge Or Rewrite Candidates

These may contain useful material, but they are not canonical as-is.

- `articles/draft/draft-sieve-foundation.md` -> merge useful bridge material
  into `articles/chapter6/sieve-sequence.md` or keep as a short draft.
- `articles/draft/draft-sieve-gap-survival-math.md` -> keep as math-only
  exploration until claims become verified or clearly scoped in
  `articles/chapter6/gap-dynamics.md`.
- `articles/draft/exercise-local-safe-window-capacity.md` -> either fold into
  the gap-dynamics learning material or keep as an exercise note.
- `articles/draft/draft-empirical-g-local-analysis.md` -> keep only if
  empirical exploration remains useful; otherwise merge the limitations into
  `articles/chapter6/gap-dynamics.md`.
- `articles/learnings/reviewer-notes-gap-dynamic.md` -> consider merging any
  durable cautionary points into `articles/learnings/learnings-capacity-argument.md`.

## Done Ticket Triage

`tickets/done/` is too large to keep as a default search target. Treat completed
tickets as a temporary evidence archive, not a permanent knowledge base.

Recommended policy:

- Keep a tiny index or summary of durable lessons.
- Move implementation-neutral lessons into `LEARNINGS.md`.
- Move verified object/function catalogs into `OBJECTS.md`.
- Delete or deep-archive the raw done tickets after the durable lessons have
  landed elsewhere.

If keeping a small done set, keep only the tickets still referenced by active
work or project guidance:

- `tickets/done/canonical-spec-to-cycle-alignment.md`
- `tickets/done/spec-same-head-filter-density.md`
- `tickets/done/scientific-review-articles-2026-07-17.md`
- `tickets/done/gap-dynamics-v2-research-update.md`
- `tickets/done/integral-cycle-examiner-review.md`
- `tickets/done/ticket-lifecycle-restructure-2026-06-21.md`
- `tickets/done/verify-timeout-root-cause.md`

Everything else under `tickets/done/` is a reasonable delete/deep-archive
candidate after owner review. The cleanup script exposes this as a separate
`--commands-with-done` mode so it cannot be selected by accident.

## Archive Or Collapse Candidates

These look like working notes rather than canonical docs.

- `tasks/twins.md`
- `tasks/1overp.md`
- `tasks/2s.md`
- `tasks/seq.md`
- `tasks/talk.md`
- `tasks/sieve-sequence-refactor-plan.md`
- `presentations/sieve-sequence-visualization/*.md`
- `PR.md`

Recommended handling: collapse still-useful notes into one current planning doc
or move the whole set to a clearly historical folder before any deletion.

## Keep For Now

These files are active tickets, blocked/future tickets, completed proof logs, or
current property catalog pages. They are noisy, but deleting them blindly risks
losing active proof context.

- `tickets/active/*.md`
- `tickets/blocked/*.md`
- `tickets/future/*.md`
- `tickets/sieve-sequence-epic.md`
- `properties/sieve-sequence/*.md`
- `properties/sieve-sequence/research/*.md`
- `src/main/scala/**/README.md`
- `spark/README.md`

## Suggested Cleanup Order

1. Remove or archive `tickets/trash/` after owner review.
2. Remove `articles/deprecated/` after confirming the current chapter articles
   and learnings files preserve any still-useful content.
3. Triage `tickets/done/`: either keep only the seven referenced anchor tickets
   listed above, or delete/deep-archive all done tickets after extracting lessons.
4. Merge or rewrite `articles/draft/` one file at a time.
5. Collapse `tasks/` into current tickets or `docs/architecture.md`.
6. Re-run link checks and `git diff --check`.

## Validation Notes

- Markdown-only cleanup does not require Stainless verification by AGENTS.md.
- Do run `git diff --check` after edits.
- If cleanup changes links in active articles, run a markdown link check before
  publishing.
