# Finite Perfect-Scenario Generator Next Step

**Created:** 2026-07-20
**Status:** Complete
**Owner:** mathematical experiment design

## START HERE

Preserve as a suggested property-catalog next step the distinction between a
finite, certifying perfect-scenario generator and a proof that successful
scenarios occur infinitely often.

## Goal

Add one self-contained note describing:

- what the generator may search;
- what a returned finite certificate must contain;
- how to reconstruct seed ancestry from a safe-window survivor;
- which observations would inform later Type I/Type II work;
- what the generator cannot prove about unbounded success.

## Current State

The property catalog proves the finite certificate conditions and identifies
the infinite-occurrence statement as open. The recent research assessment also
shows that a fixed seed eventually has too few local copies under `q<p^2` for
its complete-period repetition frequency to force safe-window placement.

## Expected State

Add and index a suggested-next-step note that recommends searching all seed
residues, equivalently all safe-window starts, while retaining a complete
modular certificate for every result.

## Risks And Validation

- Risk: present empirical continuation as an infinite generator theorem.
  - Validation: state that no totality or unbounded-success guarantee is made.
- Risk: make the certificate depend on unrecorded primality tests.
  - Validation: state the finite modular filter conditions and strict square
    bound explicitly.
- Risk: rely again on many copies of one fixed seed.
  - Validation: make search across seeds or endpoints the default strategy.
- Final validation: all local links resolve and scoped Markdown checks pass.

## Learning Log

| Date | Progress | Notes |
|------|----------|-------|
| 2026-07-20 | Started the suggested-next-step note. | The implementation target is a sound partial generator: every output is certified, but success for every input or beyond every bound is not claimed. |
| 2026-07-20 | Added and indexed `suggested-next-step-finite-perfect-scenario-generator.md`. | The note defines endpoint and ancestry formulations, the finite certificate, explicit guarantees and non-guarantees, two equivalent implementations, measurements, and a five-part first milestone. |
