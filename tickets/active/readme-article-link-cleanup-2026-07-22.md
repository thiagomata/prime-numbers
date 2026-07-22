# README Article Link Cleanup

**Created:** 2026-07-22
**Status:** Completed

## Goal

Clean up stale article links in `README.md` so the project overview points only
to active, existing articles or source-backed properties.

## Current State

- Several README links still use old pre-chapter article paths.
- The Euclid section links to a draft path even though the active article is
  `articles/chapter5/euclid-theorem.md`.
- The sieve foundation section links to `articles/draft-sieve-foundation.md`,
  which does not exist in the current tree.

## Expected State

- Active article links point to current `articles/chapterN/...` paths.
- The sieve foundation section does not link to a nonexistent draft.
- Markdown-only validation passes with `git diff --check`.

## Similar Tickets

- `tickets/trash/archived/article-consolidation.md` recorded the original
  draft-to-active article consolidation.
- `tickets/done/scientific-review-articles-2026-07-17.md` previously noted
  stale draft/deprecated article references.

## Validation

- Search README for remaining draft/deprecated article links.
- Run `git diff --check`.

## Result

- Updated README article links to current `articles/chapterN/...` paths.
- Removed the nonexistent `articles/draft-sieve-foundation.md` link from the
  README and described those properties as source-backed but not currently
  covered by an active standalone article.
- `rg` found no remaining draft/deprecated article links in `README.md`.
- `git diff --check -- README.md tickets/active/readme-article-link-cleanup-2026-07-22.md`
  passed.
- Repo-wide `git diff --check` is still blocked by a pre-existing trailing
  whitespace line in `articles/chapter2/modulo.md`, which was not changed here.
