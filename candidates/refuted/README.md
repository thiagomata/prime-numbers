# Refuted Candidate Statements

This folder records research statements that are now known to be false by an
explicit valid counterexample.

Its purpose is narrower than the main `candidates/` folder:

- `candidates/` keeps live hypotheses, partial mechanisms, and notes whose main
  statement may still be true.
- `candidates/refuted/` keeps exact statements that should not be retried in
  the same universal form unless some definition changes.
- Tickets keep failed proof attempts, exploratory dead ends, and strategies
  abandoned for process reasons. A failed path is not automatically a refuted
  mathematical statement.

## Admission Rule

Add a note here only when all three conditions hold:

1. the statement is written precisely enough to test;
2. a valid counterexample is known;
3. the counterexample defeats the statement as written, not just a stronger
   interpretation of it.

Finite empirical failure is enough to refute a universal claim. It does not
automatically refute eventual, density-based, or infinitely-many variants
unless the same counterexample defeats those formulations too.

## Current Index

1. [Monotone separator reconstruction](monotone-separator-reconstruction.md)
   — stronger transition laws around candidate #18 that fail already at
   `Q=17`, `r=5 -> 7`.

## Scope Boundary

At present this folder does **not** mean that any numbered candidate note in
`../` is fully refuted. A candidate note belongs here only if its own main
stated hypothesis is defeated. Stronger auxiliary laws attached to an open
candidate should be cataloged here without moving the candidate note itself.
