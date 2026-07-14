# Integral Cycle Draft Property Audit

**Created:** 2026-07-14
**Status:** Active

## Goal

Check whether the three draft/pending properties in
`articles/chapter4/integral-cycle.md` are truly missing from the current Scala
verification code.

## Current State

The article marks these as mathematically proven but Stainless verification
pending:

- Section 5.1 modulo invariance.
- Section 5.3 right index shift.
- Section 5.4 left index shift.

The user asked to verify whether they are really missing.

## Expected State

Produce a source-backed classification for each property:

- already verified;
- partially covered by existing lemmas;
- genuinely missing.

## Validation Plan

1. Search existing `.holds` lemmas across cycle-integral, gap, filter, modulo,
   cycle, and list property modules.
2. Read the candidate lemma bodies before classifying them.
3. Cross-check TODO/article wording against actual source names and statements.
4. Report the classification without adding new lemmas in this audit pass.

## Learning Log

- Started audit; no code edits planned.
