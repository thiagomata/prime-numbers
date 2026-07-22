# Chapter 6b Curated Proof Spine

**Created:** 2026-07-15
**Status:** Active
**Owner:** Curate the useful Chapter 6 sieve-sequence proof surface into a new `chapter6b` area

## START HERE

Create a new `chapter6b` folder that contains only the parts of Chapter 6 that
are article-backed, proof-relevant, and worth preserving. Do not delete the old
Chapter 6 folder in this ticket. The old folder can be retired only after the new
area demonstrably contains everything needed.

## Goal

Turn the current mixed Chapter 6 sieve package into a curated proof spine:

- inspect active article source references and `Main.scala` usage,
- inspect active/future tickets that identify load-bearing lemmas,
- compare with Chapter 4's package organization,
- create a new `chapter6b` folder with a clearer module layout,
- copy or re-home only the selected proof surfaces,
- leave legacy/trash surfaces behind.

Only active articles under `articles/chapter6/` and `src/main/scala/v1/Main.scala`
are migration drivers. Deprecated articles, old tickets, and verified-but-unused
helpers can explain history but must not justify copying code into `chapter6b`.

## Current State

Chapter 6 currently mixes:

- semantic spec objects,
- concrete cycle objects,
- residue/expand/filter/sort/gap/rotate pipeline helpers,
- survivor/window proof experiments,
- bridge/equivalence wrappers,
- legacy raw-list helpers,
- empirical code that is already being moved elsewhere in the worktree.

The current package is verified, but hard to share and hard to explain. It
contains useful proof grains embedded in a large amount of historical scaffolding.

## Similar Tickets And Context

- `tickets/active/explain-sieve-sequence-architecture.md`
  - Documents the current mess and marks `SieveSequenceByPrimes` as legacy.
- `tickets/sieve-sequence-epic.md`
  - Defines the Spec / Canonical / Cycle story and records that `nextGapsWalk`
    direct proof attempts timed out.
- `tickets/active/m-interval-density-and-sieve-sequence-v2.md`
  - Records the user correction that period/count proofs should start from the
    spec, not from `nextSorted` / `nextFiltered` implementation machinery.
- `tickets/done/spec-same-head-filter-density.md`
  - Identifies the verified spec-local same-head count theorem and warns against
    reviving detached cycle/pipeline routes.
- `tickets/active/repeat-filter-rotate-cycle-path.md`
  - Tracks the newer repeat-filter-rotate lane and explicitly says some
    `SpecDerivedSieveSequence` surfaces should be split into context-specific
    property objects.
- `articles/chapter6/sieve-sequence.md`
  - Article source references identify the public proof surface that readers are
    being asked to trust.

## Expected State For This Ticket

- `chapter6b` exists with a README/migration map explaining what was preserved
  and what was intentionally left behind.
- The first curated source layout follows Chapter 4's style: core objects near
  the root and proof/property objects under focused `properties/` namespaces.
- No deletion of old Chapter 6 files.
- No behavior change to old Chapter 6.

## Validation Plan

- Check latest `logs/verify.log` before source moves.
- For markdown-only planning, run `git diff --check`.
- If Scala files are copied/edited into `chapter6b`, run `just verify` once
  after the move.

## Learning Log

| Date | Progress | Notes |
|------|----------|-------|
| 2026-07-15 | Ticket created. | User wants a curated `chapter6b` mined from article-backed proofs, not one-by-one beautification of the old package. |
| 2026-07-15 | Correction after initial copy attempt. | Do not mechanically copy Chapter 6 concrete objects. `chapter6b` should use real data classes only for real data and lemma/property objects for proof collections, following Chapter 4 style. Added `src/main/scala/v1/chapter6b/README.md` as the plan-first guide. |
| 2026-07-15 | Migration gate tightened. | Copy/rewrite only what is used by active Chapter 6 articles or `Main.scala`; ignore old ticket-only, deprecated, draft empirical, and unused verified surfaces. |
| 2026-07-15 | First real files created. | Added package READMEs, spec/bridge property namespace anchors, and `integral/SieveGapUtils.scala` with only the active gap article's current source-backed gap functions. Found that `collectGapsV2` is cited by the article but is not present in current `src/main/scala`, so it must not be copied from stale memory. |
| 2026-07-16 | Actual spec and bridge added. | Added `spec/SpecSieveSequence.scala`, `bridge/SpecDerivedSieveSequence.scala`, and curated `bridge/SpecDerivedSieveSequenceProperties.scala`. The property object contains the active article bridge lemmas from old `SpecDerivedCoreProperties` instead of copying that whole file. |
| 2026-07-16 | Actual survivor/equivalence bridges added. | Added `bridge/SpecDerivedBySurvivors.scala` for `assertCycleNextApplyEqualsSpecNext` and `bridge/SpecCycleSieveEquivalence.scala` for the active article's equivalence module reference. The survivor file is trimmed to the active next-stage bridge lane and does not import the repeated-cycle proof tail. |
| 2026-07-16 | Validation boundary recorded. | `git diff --check` passes. Direct `sbt compile` emitted class/tasty files for every new `chapter6b` Scala source, then continued into broad Stainless verification and was interrupted after unrelated old proof UNKNOWNs appeared in Chapter 4 / old Chapter 6 surfaces. Full verification was not completed in this pass. |
