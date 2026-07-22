# README Important Lemma Audit

**Created:** 2026-07-22
**Status:** Completed

## Goal

Compare the README's proved-property overview against the current active
articles and `OBJECTS.md`, then add any missing headline properties that belong
in the README.

## Current State

- README covers the foundation articles through chapter 5.
- README includes a short source-backed sieve-foundation section.
- README does not summarize the active chapter 6 articles:
  `articles/chapter6/sieve-sequence.md` and
  `articles/chapter6/gap-dynamics.md`.
- The Euclid section states the main infinitude theorem but not the verified
  next-prime and primality-test consequences already documented in the active
  article.

## Expected State

- README includes only overview-level properties, not every helper lemma.
- Active chapter 6 article links are present.
- Missing chapter 5 consequences are mentioned without bloating the README.
- Markdown-only validation passes for touched files.

## Similar Tickets

- `tickets/done/scientific-review-articles-2026-07-17.md` noted active article
  scope and stale article references.
- `tickets/active/readme-article-link-cleanup-2026-07-22.md` cleaned stale
  README article links immediately before this audit.

## Validation

- Search README for active chapter article links.
- Search README for remaining stale draft/deprecated links.
- Run `git diff --check -- README.md tickets/active/readme-important-lemma-audit-2026-07-22.md`.

## Result

- Added the chapter 5 downstream consequences that are important for later
  sieve work: the Euclid prime exceeds the current complete prime-prefix head,
  and composite numbers have a smallest prime divisor bounded by sqrt(n).
- Added a README section for the active chapter 6 sieve-sequence article,
  including accepted-value completeness, strict increase, block-period shift,
  gap-cycle reconstruction, repeated-cycle invariance, exact expanded
  filtering, copy-or-merge, and conditional next-head primality.
- Added a README section for the active chapter 6 gap-dynamics article,
  including exact full-period 2-gap count, stable absence, two forbidden
  copy-index classes, finite-batch survival, and square-safe twin certificates.
- Kept the chapter 6 boundary explicit: these complete-period properties do
  not prove local square-window placement or prime-gap persistence.
- `rg` found the expected new active chapter 6 links and no stale draft or
  deprecated README links.
- `git diff --check -- README.md tickets/active/readme-important-lemma-audit-2026-07-22.md`
  passed.
