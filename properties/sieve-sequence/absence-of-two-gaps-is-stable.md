# Absence of 2-Gaps Is Stable Under Later Filtering

**Status:** Mathematically proved from copy-or-merge gap behavior. Stainless
verification of the complete packaged statement is not claimed here.

## Meaning

Filtering can preserve an old gap or merge consecutive old gaps, but it cannot
invent a smaller positive gap. Consequently, once a post-2 stage has no
2-gaps, no later stage can recreate one.

## Setup

Assume the filter `2` has already been installed. Every accepted value is odd,
so every gap between consecutive accepted values is a positive even integer.

During a later filter step, consider two consecutive surviving values. Either:

1. they were already consecutive before filtering, so their new gap copies one
   old gap; or
2. one or more intermediate accepted values were removed, so their new gap is
   the sum of two or more consecutive old gaps.

## Property

If the old cyclic gap sequence contains no gap of value `2`, then the new cyclic
gap sequence also contains no gap of value `2`.

## Proof

Since all old gaps are positive and even, absence of `2` means every old gap is
at least `4`.

- A copied gap is therefore at least `4`.
- A merged gap is a sum of at least two positive old gaps, so it is at least
  `8` under the no-2 hypothesis.

Neither operation can produce a gap of value `2`. Applying the same argument
inductively proves absence at every later stage.

## Consequence

Global 2-gap extinction would be permanent. Therefore any proof of persistent
or infinite 2-gap behavior must ensure that the construction never reaches a
post-2 stage whose complete cycle has zero 2-gaps.

The exact global count property supplies that guarantee for the canonical
complete-period sieve: its finite product is positive at every odd stage.

## Limitation

This property concerns absence in the complete cyclic gap population. A stage
may have many global 2-gaps while a particular safe window contains none. The
stability theorem does not bridge that global-to-local distinction.
