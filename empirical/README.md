# Empirical Research

This directory records finite computations, measured regularities, stress
tests, and conjectural scales. Its contents are evidence about mathematical
claims, not proofs of their unbounded or universal forms.

## Classification Boundary

- `properties/` contains only statements proved at their full stated scope by
  deduction, algebra, structural argument, or a valid counterexample to a
  universal claim.
- `candidates/` contains unproved general hypotheses whose truth would advance
  the research.
- `empirical/` contains exact finite observations and conjectures suggested by
  those observations.
- `data/` contains the raw machine-readable outputs consumed by empirical
  notes.

A computation can prove a statement about the finite cases it exhaustively
checked. It cannot establish an extrapolation to all stages unless a separate
mathematical argument proves that extrapolation.

## Required Contents

Every empirical note must state:

1. the exact finite domain measured;
2. the program and data used;
3. the tests or independent checks that passed;
4. the observed result;
5. the general claim the result does **not** prove;
6. a falsifier or next measurement when one is known.

Do not describe a measured trend as a theorem, property, established input, or
verified universal fact. Use terms such as “observed,” “measured,”
“empirically reinforced,” and “not mathematically proved.”

## Sieve-Sequence Evidence

- [Hereditary Shot-Spacing Evidence](sieve-sequence/hereditary-shot-spacing.md)
  records the finite wheel tables, fixed-window lineage measurements,
  recurrence counterexamples, and square-root discrepancy observations related
  to candidate #14.
- [Capacity-Density Candidate Evidence](sieve-sequence/capacity-density-candidates.md)
  records the 53-head, 1,837-layer lower-envelope and redundant close-pair
  measurements for candidates #17 and #18.
