# Markdown Cleanup Audit

**Created:** 2026-07-23
**Status:** Active

## START HERE

Micro-goal: Inventory markdown files and produce a conservative cleanup manifest
that reduces stale, duplicate, and outdated documentation without deleting files
from the assistant side.

## Goal

Clean up old markdown documentation by identifying files to keep, merge, archive,
or manually delete.

## Current State

- The repository contains many markdown files across articles, tickets, tasks,
  docs, properties, presentations, and source README files.
- `tickets/trash/` already exists for superseded and archived tickets.
- `articles/deprecated/` and `articles/draft/` contain likely stale narrative
  material, but article cleanup must preserve verified-property provenance and
  not overclaim results.

## Expected State

- A reviewable markdown cleanup manifest lists each candidate action.
- Destructive deletion is left to the project owner, not performed by the
  assistant.
- Any generated helper script is dry-run first and cannot silently delete files.

## Similar Tickets

- `tickets/active/readme-article-link-cleanup-2026-07-22.md` cleaned stale
  article links from `README.md`.
- `tickets/done/ticket-lifecycle-restructure-2026-06-21.md` established active,
  blocked, done, future, and trash ticket lifecycle folders.
- `tickets/trash/archived/article-consolidation.md` proposed merging older draft
  articles into coherent current articles.

## Alternatives Considered

- Create a raw `rm` script: rejected because it bypasses the repository rule that
  forbids destructive cleanup through the assistant.
- Delete files immediately: rejected for the same reason and because markdown
  documents may contain proof history worth preserving.
- Move everything stale into one archive folder: safer than deletion, but still
  too broad without first classifying canonical vs. superseded content.

## Assumptions And Hypotheses

- Files already under `tickets/trash/` are historical and likely removable from
  a lean working tree after owner review.
- Files under `articles/deprecated/` are not active publications and are likely
  deletion or archive candidates after checking whether current chapter articles
  supersede them.
- Files under `articles/draft/` may contain useful material and should usually
  be merged or rewritten rather than deleted blindly.
- Root files such as `README.md`, `AGENTS.md`, `OBJECTS.md`, `LEARNINGS.md`,
  `PROOF_GUIDE.md`, `TODO.md`, and `CONTRIBUTING.md` are likely canonical.

## Validation

- Count all markdown files and line counts before and after classification.
- Search for stale markers such as `deprecated`, `superseded`, `outdated`,
  `trash`, `TODO`, and draft references.
- Validate helper scripts with dry-run output only.
- For markdown-only edits, Stainless verification is not required by AGENTS.md.

## Learning Log

- Initial scan found a lifecycle convention in `tickets/README.md`: active work
  lives under `tickets/active/`, stale planning records under `tickets/trash/`.
- Added `docs/markdown-cleanup-manifest.md` with keep, delete-candidate,
  merge/rewrite, archive/collapse, and keep-for-now categories.
- Added `scripts/markdown-cleanup-review.sh`, a non-destructive helper that
  prints markdown inventory by default and prints reviewable `git rm` commands
  with `--commands`.
- Validation passed:
  `bash scripts/markdown-cleanup-review.sh`,
  `bash scripts/markdown-cleanup-review.sh --commands`, and
  `git diff --check -- docs/markdown-cleanup-manifest.md scripts/markdown-cleanup-review.sh tickets/active/markdown-cleanup-audit-2026-07-23.md`.
- User flagged that `tickets/done/` is also too noisy. Counted 42 done tickets
  with 8,842 lines. Updated the manifest to treat done tickets as a separate
  triage tier and updated the helper with `--commands-with-done`, preserving
  seven referenced anchor tickets by default.
- Rewrote `TODO.md` from a stale mixed backlog into a compact current backlog.
  Removed references to nonexistent paths such as
  `articles/chapter6/sieve-sequence-v2.md`,
  `tickets/active/spec-same-head-filter-density.md`, and
  `tickets/active/next-gaps-size-closed-form.md`.
- User pointed out that there may be no open Chapter 6 proof left. Source audit
  found current `src/main/scala/v1/chapter6/` contains only the curated spec-side
  files, while several tickets and `OBJECTS.md` still describe old surfaces such
  as `CycleSieveSequence`, `SieveSequenceNextLevel`, `SpecDerivedSieveSequence`,
  and `SpecDerivedBySurvivors`. Updated `TODO.md` to frame the next action as
  Chapter 6 ticket/source reconciliation, not proof work.
