# Draft Sieve Foundation Bridge Article

**Created:** 2026-07-22
**Status:** Completed

## Goal

Create a new draft article for the sieve-foundation bridge while keeping the
old deprecated article retired.

## Current State

- `articles/deprecated/deprecated-sieve-foundation.md` remains retired.
- The source-backed foundation lemmas still exist in:
  - `CycleIntegralOnesProperties.scala`
  - `FilterPreservesPrimesProperties.scala`
- README now summarizes these properties but does not link to a draft.
- There is no active or draft replacement article for the bridge story.

## Expected State

- Add `articles/draft/draft-sieve-foundation.md`.
- Mark it clearly as a draft.
- Present the bridge role: candidate generation plus prime-preserving filtering.
- Keep proof boundaries explicit and point readers to the active chapter 6
  sieve-sequence article for full stage/transition semantics.
- Do not modify the retired article.

## Similar Tickets

- `tickets/active/readme-article-link-cleanup-2026-07-22.md`
- `tickets/active/readme-important-lemma-audit-2026-07-22.md`
- `tickets/trash/archived/article-consolidation.md`

## Validation

- Confirm the deprecated article is untouched.
- Run `git diff --check -- articles/draft/draft-sieve-foundation.md tickets/active/draft-sieve-foundation-bridge-2026-07-22.md`.

## Result

- Added `articles/draft/draft-sieve-foundation.md` as a new draft bridge
  article.
- Kept `articles/deprecated/deprecated-sieve-foundation.md` untouched.
- The draft covers unit-cycle candidate generation, strict increase, distinct
  primes not dividing each other, prime-preserving filtering, and list-level
  preservation after filtering.
- The draft states its boundary and points to the active chapter 6
  sieve-sequence article for full stage and transition semantics.
- `git diff --check -- articles/draft/draft-sieve-foundation.md tickets/active/draft-sieve-foundation-bridge-2026-07-22.md`
  passed.
