# Spec Sequence Package

This package is for the abstract sieve sequence: the ordered values accepted by
the current prime prefix and the lemmas that make that definition usable.

Files should enter this package only when they are cited by an active
`articles/chapter6/*.md` article or by `src/main/scala/v1/Main.scala`.

Current migration candidates:

Migrated in `SpecSieveSequence.scala`:

- `SpecSieveSequence::apply`
- `SpecSieveSequence::indexOfAccepted`
- `SpecSieveSequence::applyStrictlyIncreases`
- `SpecSieveSequence::assertGapPositive`
- `SpecSieveSequence::assertHeadPlusTailPrimorialAccepted`
- `SpecSieveSequence::period`
- `SpecSieveSequence::assertSameHeadExtendedFilterCount`
- `SpecSieveSequence::sameHeadSurvivorCount`
- `SpecSieveSequence::assertSpecGapCycleIntegralMatchesApply`
- `SpecSieveSequence::assertApplyOneEqualsNextPrime`
- `SpecSieveSequence::assertApplyOneIsPrimeIfBelowHeadSq`
- `SpecSieveSequence::assertSurvivorAcceptedByNext`

Do not add another concrete sequence class here just to host lemmas. If a method
does not need object state, it belongs in a `*Properties` object.
