# Split SpecSieveSequence Assertion Families

**Created:** 2026-07-16
**Status:** Active
**Owner:** Refactor `chapter6b` spec assertions into focused property objects

## START HERE

Split the current `src/main/scala/v1/chapter6b/sieve/seq/spec/SpecSieveSequence.scala`
proof surface by responsibility:

- keep core stream semantics with `SpecSieveSequence`, preferably on the companion
  object side when they are object-level helpers;
- move period and gap-cycle reconstruction proofs to
  `SpecSieveSeqPeriodProperties`;
- move expanded same-head survivor count proofs to
  `SpecSieveSeqSurvivorCountProperties`;
- move next-stage filter and merge proofs to `SpecSieveSeqNextProperties`;
- move first-generated-head/prime proofs to `SpecSieveSeqHeadIsPrime`.

## Current State

`SpecSieveSequence.scala` is an untracked `chapter6b` file with the data model,
linear stream implementation, and several unrelated proof families in one class.
The latest `logs/verify.log` did not expose a `total:` summary during the initial
inspection, so establish a verification baseline before Scala edits.

## Expected State

The spec package follows the same broad style as `v1.chapter5.prime.Prime`:
the core object keeps its executable semantics close by, while theorem families
live in focused property objects. Public call sites should either call the new
property object directly or keep only thin compatibility wrappers if a staged
migration needs them.

## Similar Tickets And Context

- `tickets/active/chapter6b-curated-proof-spine.md` says `chapter6b` should be
  a curated proof spine, not a mechanical copy of old Chapter 6.
- `tickets/done/spec-same-head-filter-density.md` identifies the same-head
  count theorem as a spec-local proof lane.
- `tickets/active/repeat-filter-rotate-cycle-path.md` records the preference
  for context-specific property objects around cycle/next-stage proof surfaces.
- `tickets/blocked/prove-apply1-is-prime.md` is adjacent to the head-is-prime
  proof boundary.

## Risks And Assumptions

- Moving methods out of the class can break access to private helpers. Validate
  whether helpers should move with their theorem family, become companion-object
  helpers, or become package-private only where necessary.
- Existing article/source references may still point at
  `SpecSieveSequence::methodName`. Keep compatibility wrappers only when they
  materially reduce migration risk.
- There are two old/new package copies. This ticket targets the untracked
  `chapter6b` curated copy unless the user explicitly asks to refactor legacy
  `chapter6`.

## Validation Plan

1. Check latest verification log, then run a baseline `just verify` if no green
   summary is available.
2. Move one proof family at a time.
3. After each Scala change, run focused verification where possible.
4. Run one final `just verify` after the split.
5. Run `git diff --check`.

## Learning Log

| Date | Progress | Notes |
|------|----------|-------|
| 2026-07-16 | Ticket created. | User mapped the five proof families and asked for the split to follow the Chapter 5 `Prime` object/property style. |
| 2026-07-16 | Split implemented. | Added period, survivor-count, next-stage, and head-is-prime property objects. Kept compatibility wrappers in `SpecSieveSequence`; user asked to leave final verification to them. |
