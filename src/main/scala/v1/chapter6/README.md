# Chapter 6b Plan

`chapter6b` is a cleanup branch of the Chapter 6 proof surface, not a mechanical
copy of `chapter6`.

The goal is to preserve the useful proofs while avoiding the main Chapter 6
mistake: turning every proof context into a concrete object. Most proof surfaces
should be objects that collect lemmas over explicit arguments, not classes that
pretend to be new mathematical entities.

## Ground Rules

1. Do not introduce a concrete class unless it represents actual data.
2. Lemma collections should be `object ...Properties`, following the Chapter 4
   style.
3. A bridge proof should be named as a bridge, not as another sequence.
4. Active article references and `Main.scala` usage decide what belongs here.
5. Legacy experiments stay out unless an article or active ticket needs them.
6. The old Chapter 6 package remains untouched until `chapter6b` is complete.

## What Counts As A Real Data Type

These may remain classes or case classes because they describe data:

- a linear sieve stage, if it stores the current prime-prefix stage;
- a cycle-backed sieve stage, if it stores a prime-prefix stage and a gap cycle;
- small typed witnesses only when they carry irreducible invariants that cannot
  be expressed as lemma preconditions without making callers worse.

Everything else should start as a lemma object.

## What Should Become Lemma Objects

The old Chapter 6 names blur proof context with domain objects. In `chapter6b`,
the following should be treated as property namespaces unless proven otherwise:

- spec-to-cycle correspondence;
- current-stage period and gap reconstruction;
- same-head expanded survivor counting;
- next-stage filter nesting;
- repeat-filter-rotate transition checkpoints;
- survivor-to-next-stage alignment;
- residue-pipeline helper facts.

For example, instead of creating another `SpecDerived...` class, prefer:

```scala
object SpecCycleCorrespondenceProperties
object SameHeadFilterCountProperties
object RepeatFilterRotateProperties
object SurvivorAlignmentProperties
object SieveTransitionProperties
```

Each lemma should take the real data objects as explicit parameters.

## Migration Gate

Only copy or rewrite code that is actually used by one of these drivers:

- active articles under `articles/chapter6/`;
- the runnable entry point `src/main/scala/v1/Main.scala`.

Deprecated articles, old tickets, verified-but-unused helpers, and interesting
experiments are not migration drivers. They may explain history, but they do not
justify copying code into `chapter6b`.

## Article And Main Backed Surface

The current active Chapter 6 articles and `Main.scala` cite these proof areas:

- `SpecSieveSequence`: linear scan, accepted index, monotonicity, gap
  positivity, period, same-head survivor count, next-head facts;
- `SieveUtils`: gap calculation and pairwise/list helpers used by the gap
  dynamics article;
- `SieveSequenceNextLevel`: transition helper surface;
- `SpecCycleSieveEquivalence`: spec/cycle bridge facts;
- `SpecDerivedSieveSequence`: currently holds canonical-cycle and next-period
  bridge facts;
- `SpecDerivedBySurvivors`: currently holds survivor-to-next-stage bridge facts.
- `CycleSieveSequence`: used by `Main.scala` for the runnable equivalence demo.

`chapter6b` should not copy these names blindly. It should mine the cited lemmas
and place them into clearer modules.

Current explicit drivers:

| Driver | Old surface it uses | Migration classification |
|--------|---------------------|--------------------------|
| `Main.scala` | `SpecSieveSequence` | Real data model: linear stage. |
| `Main.scala` | `SpecDerivedSieveSequence` | Do not copy as a data model; mine into bridge/property objects unless a tiny witness is unavoidable. |
| `Main.scala` | `CycleSieveSequence` | Real data model: cycle-backed stage. |
| `articles/chapter6/sieve-sequence.md` | `SpecSieveSequence::*` | Spec properties and period/count lemmas. |
| `articles/chapter6/sieve-sequence.md` | `SpecDerivedSieveSequence::*` | Bridge properties; should move out of the concrete wrapper shape. |
| `articles/chapter6/sieve-sequence.md` | `SpecDerivedBySurvivors::*` | Survivor alignment properties; should be a property object. |
| `articles/chapter6/sieve-sequence.md` | `SieveSequenceNextLevel`, `SpecCycleSieveEquivalence` | Transition and correspondence property namespaces. |
| `articles/chapter6/gap-dynamics.md` | `SieveUtils::calculateGaps`, `pairwiseGaps`, `collectGapsV2` | Utility functions used by article text. |

## Current Shape

```text
v1.chapter6b.sieve.seq.spec
  SpecSieveSequence.scala
  SpecSieveSequenceProperties.scala
  README.md

v1.chapter6b.sieve.seq.integral
  SieveGapUtils.scala
  README.md

v1.chapter6b.sieve.seq.bridge
  SpecDerivedSieveSequence.scala
  SpecDerivedSieveSequenceProperties.scala
  SpecDerivedBySurvivors.scala
  SpecCycleSieveEquivalence.scala
  SpecCycleBridgeProperties.scala
  README.md
```

The `spec`, `integral`, and `bridge` folders were created as the initial guide
for the curated layout. New files should stay inside those roles unless an
active article or `Main.scala` forces a better boundary.

## Files Created So Far

- `sieve/seq/spec/SpecSieveSequenceProperties.scala`
  - placeholder namespace for spec-level lemmas cited by
    `articles/chapter6/sieve-sequence.md`;
  - intentionally not a new sequence class.
- `sieve/seq/spec/SpecSieveSequence.scala`
  - actual linear-scan sieve specification;
  - migrated because both `Main.scala` and `sieve-sequence.md` depend on it;
  - still imports the old `SieveUtils` until that utility surface is curated.
- `sieve/seq/integral/SieveGapUtils.scala`
  - first actual migrated implementation surface;
  - contains only `calculateGaps`, `pairwiseGaps`, and their size lemmas,
    because those are active gap-dynamics references.
- `sieve/seq/bridge/SpecCycleBridgeProperties.scala`
  - placeholder namespace for spec/cycle equivalence lemmas;
  - intentionally not another `SpecDerived...` concrete wrapper.
- `sieve/seq/bridge/SpecDerivedSieveSequence.scala`
  - actual canonical spec-derived cycle bridge used by `Main.scala` and the
    article;
  - concrete because it stores real bridge data: `spec`, `period`, `gapCycle`,
    `cycle`, and `integral`.
- `sieve/seq/bridge/SpecDerivedSieveSequenceProperties.scala`
  - actual article-facing bridge lemmas;
  - curated from the old `SpecDerivedCoreProperties`, not copied wholesale;
  - contains `assertApplyMatches`, `assertCyclePeriod`, and
    `assertNextCycleGapsMatchSpecNext`.
- `sieve/seq/bridge/SpecDerivedBySurvivors.scala`
  - actual value-level survivor bridge for the active article's
    `assertCycleNextApplyEqualsSpecNext` reference;
  - trimmed to the active next-stage bridge lane; the repeated-cycle proof tail
    stays out until an active driver needs it.
- `sieve/seq/bridge/SpecCycleSieveEquivalence.scala`
  - actual local equivalence lemma module cited by the active article;
  - currently depends on old Chapter 6 `CycleSieveSequence`,
    `SieveSequenceNextLevel`, and `SieveUtils` until those are curated.

`collectGapsV2` is cited by `articles/chapter6/gap-dynamics.md`, but it is not
present in current source under `src/main/scala`. It is therefore not copied.
That article reference should be repaired from current code before a migration
target is chosen.

## Validation Notes

- `git diff --check` passes for the new `chapter6b` files and ticket updates.
- Direct `sbt compile` emitted class/tasty files for every `chapter6b` Scala
  source under `target/scala-3.5.0/classes/v1/chapter6b`.
- The same direct `sbt compile` then continued into a broad Stainless
  verification run over old and new sources. It was interrupted after unrelated
  old proof surfaces reported UNKNOWN while the run was still processing:
  `chapter4/cycle/properties/CycleProperties.scala:171`,
  `chapter6/seq/sieve/SieveSequenceNextLevel.scala:399`, and
  `chapter4/cycle/integral/recursive/properties/GapProperties.scala:82`.
  This is not a completed full verification result for `chapter6b`.

## First Migration Pass

1. Build an inventory of all active-article-cited and `Main.scala`-used lemmas.
2. Classify each cited lemma as one of:
   - data definition,
   - spec property,
   - cycle property,
   - bridge property,
   - transition helper,
  - legacy/no-copy.
3. Create only the package structure, README files, and minimal namespace
   anchors needed to make the layout visible.
4. Move one proof family at a time, starting with the smallest article-backed
   family.
5. Verify after each non-markdown source move.

## Do Not Copy

Do not copy these into the curated proof spine:

- `SieveSequenceByPrimes`: raw-list scaffolding without the typed prime-prefix
  invariants;
- `CompletePrimePrefix`: superseded exploratory semantic object;
- empirical runners and CSV code;
- deprecated article-only surfaces;
- draft article-only empirical references unless the draft becomes active;
- old ticket-only surfaces;
- any class whose only purpose is to host lemmas.

## Current Correction

An initial mechanical copy of some Chapter 6 source files was started too early.
Treat that as scratch, not as the intended `chapter6b` design. The next step is
to replace that copy-first approach with the plan above: article-cited proof
families first, lemma namespaces by default, data classes only when they carry
real data.
