# articles/notes/ — home for never-promoted documents

**Created:** 2026-09-13
**Status:** In progress
**Depends on:** owner decision (PR #35 review session); never-destroy rule
released by owner for superseded material

## Goal

Give notes their own place so `articles/draft/` means "promotable
candidates" only. Contract of `articles/notes/`: useful reference
documents that must never be promoted to articles — no PDF, no arXiv
package, no parity gate.

## Disposition (owner-approved)

- MOVE draft/draft-gap-dynamics-research-notes.md -> notes/gap-dynamics-research-notes.md
- MOVE draft/review-draft-articles-2026-08-15.md -> notes/
- MERGE articles/review/ (7 surviving files) into notes/; README folded
- DELETE draft-empirical-g-local-analysis.md (superseded; convention
  abandoned; math content preserved in chapter6/gap-dynamics.md)
- DELETE draft-sieve-gap-survival-math.md (superseded; derivations
  preserved in gap-dynamics + research notes)
- DELETE their 2 dead reviews (review-draft-empirical-g-local,
  review-draft-sieve-gap-survival)
- Sweep ~30 inbound links (TODO.md, learnings, properties, candidates,
  docs manifest, exercise prerequisite, tickets)

## Current State

Executing. Validation: zero stale references to moved/deleted paths
after sweep; markdown-only change, no runtime gates.

## Next Action

Commit; then consider draft/ README stating promotable-only semantics.
