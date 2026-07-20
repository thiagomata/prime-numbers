# Bridge Package

This package is for proofs that connect the spec sequence to the cycle/integral
sequence.

Migrated bridge surface:

- `SpecDerivedSieveSequence::assertApplyMatches`
- `SpecDerivedSieveSequence::assertCyclePeriod`
- `SpecDerivedSieveSequence::nextPeriod`
- `SpecDerivedSieveSequence::assertNextCycleGapsMatchSpecNext`
- `SpecDerivedBySurvivors::assertCycleNextApplyEqualsSpecNext`
- `SpecCycleSieveEquivalence`

These are split across:

- `SpecDerivedSieveSequence.scala`
  - concrete canonical bridge data;
  - owns `nextPeriod`.
- `SpecDerivedSieveSequenceProperties.scala`
  - lemma collection;
  - owns `assertApplyMatches`, `assertCyclePeriod`, and
    `assertNextCycleGapsMatchSpecNext`.
- `SpecDerivedBySurvivors.scala`
  - value-level survivor bridge over a canonical derived cycle;
  - owns `assertCycleNextApplyEqualsSpecNext`;
  - deliberately excludes the repeated-cycle proof tail, which is a separate
    proof lane.
- `SpecCycleSieveEquivalence.scala`
  - local spec/cycle equivalence lemmas cited by the article;
  - still imports old Chapter 6 transition/cycle utilities until those modules
    are curated.

Still pending:

- narrowly selected `SieveSequenceNextLevel` lemmas, only when an active article
  cites the bridge they provide

This package should mostly contain `*Properties` objects. A concrete adapter is
allowed only if it stores real data needed by `Main.scala` or by a verified
proof boundary; otherwise, keep the bridge as lemmas over existing values.
