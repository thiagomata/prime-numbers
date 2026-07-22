# Integral Sequence Package

This package is for the cycle/integral representation of a sieve state: gap
cycles, finite periods, and utilities that turn ordered survivors into gap
lists.

The first migrated implementation is `SieveGapUtils`, because
`articles/chapter6/gap-dynamics.md` currently cites `calculateGaps` and
`pairwiseGaps`.

`collectGapsV2` is named by the article but is not present in current source
under `src/main/scala`. It should not be recreated from memory. Either the
article reference should be corrected to the current `SieveSequenceNextLevel`
walk, or a fresh proof surface should be designed from the actual current code.

Do not put spec/cycle equivalence lemmas here. Cross-model claims belong in the
bridge package.
