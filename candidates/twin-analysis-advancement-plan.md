# Twin-Analysis Advancement Plan

**Status:** Adopted roadmap, recorded 2026-10-28 after the parity
assessment closed the classical-sieve subtraction route. Prioritized
directions below; empirical items are labeled empirical; no
infinite-survival claim is presumed anywhere in this plan.

## Context

The joint signed-weight assessment
([classical-sieve input, Section16](../properties/sieve-sequence/research/batched-survival-classical-sieve-input.md#16-a-joint-signed-weight-and-the-parity-barrier))
proved that the separate-budget certificate fails quantitatively
(allowance 16C_2*kappa_geom exceeds the whole-family ceiling 5C_2) and
that the joint certificate is parity-blocked at every distribution
level up to the Elliott–Halberstam boundary. The analytic sieve route is
therefore closed at this level and is recorded as a failed path with
explicit reopening conditions.

The leverage now sits in the layers where this project is unique: the
exact combinatorial structure of the Sieve Sequence, the newly verified
fixed-distance shot geometry, and the empirical measurement tooling.
This plan orders the next work accordingly.

## Priority 1: Generalize the Fixed-Separation Lemma to Arbitrary Gaps

The verified lemma
`assertRightForbiddenLiftOffsetHasFixedSeparation` shows that a real
2-gap's two forbidden lift offsets are a fixed translate pair whose
separation d satisfies d*M == 2 (mod p), depending only on the old
period M and the incoming prime p — not on the particular 2-gap. The
generalization for a real g-gap replaces 2 by g: the separation is the
canonical offset with d*M == g (mod p), and when p divides g the two
shots coincide into one class (the separation is zero, so a single
residue class destroys both endpoints of a copy at once).

- Why: one verified lemma populates the survival-frontiers phase
  diagram with an exact per-block destruction structure for every gap
  size (two distinct forbidden classes, hence two destroyed copies,
  exactly when p does not divide g; one class and one destroyed copy
  when p divides g), instead of a single 2-gap point.
- First step: prove the generalized offset-separation lemma in
  Stainless inside `SpecSieveSeqTwoGapProperties` (or a sibling
  object), keeping the existing 2-gap lemma untouched; then the
  coincident-shot corollary for p | g.
- Progress criteria: focused verification green, Chapter6 regression
  total valid not below the 4691 baseline, promotion to the
  fixed-distance property note and OBJECTS.md.

## Priority 2: Finish the Rigid-Pair Companion (Path B) and Test It Against the Cluster-Exposure Data

The rigid-pair companion ticket remains open at exactly its next step:
draft the companion with fixed-separation shots. The measured mean
exposure (5.78) sits almost on the random baseline (5.74), so the mean
carries little structure; the rigid-pair model predicts structure in
the correlations, because destruction events of two 2-gaps at
copy-distance ±d share exactly one shot and all other pairs are
mutually exclusive.

- Why: this is the first opportunity to detect a real-sieve fingerprint
  of the verified geometry, and it answers a standing question of the
  survival-frontiers phase diagram (where the real sieve sits) with
  data rather than premise.
- First step: extend the cluster-exposure tooling with a
  fixed-separation companion generator; compare variance, tails and
  local-extinction rates against the measured prefix curve.
- Progress criteria: labeled empirical comparison note under
  properties/sieve-sequence/research/, with the random baseline and the
  rigid companion reported side by side; no asymptotic claim.

## Priority 3: Bridge Draft — Sieve Sequence Stages as Imaginary Functions

No document connects the wave/imaginary-height representation to the
sequence model itself. Several equivalences look provable without new
machinery: the stage-p contact set equals the accepted-value set of the
verified sequence; translated-wave folding is the continuous counterpart
of cyclic period expansion; activation is the wave form of installing
the head as a filter after it passes. The most interesting target is the
wave-coordinate expression of the fixed-separation lemma.

- Why: one language for the exact layer and the continuous layer, and a
  natural home for the contact-frequency question the continuous draft
  leaves open.
- First step: a chapter6 draft in the house style stating the
  equivalences with proofs, each connected to the verified objects.
- Progress criteria: draft with all three equivalences proved or
  explicitly marked open; arXiv package only after the draft settles.

## Priority 4: Batched Transport Accounting Across a Bounded Gap Family

The exact transport identities and the block-reserve theorem are
2-gap-specific. With Priority1's generalized destruction counts, the
same telescoping bookkeeping runs for every even g at most G in one
window, turning reserve retention into a portfolio question across the
gap family.

- Why: finite-block protection theorems genuinely strengthen, and the
  result is citable even though the recorded ceiling stands: no
  infinite-survival claim can follow from a conditional invariant, and
  the parity barrier still guards the analytic side.
- First step: re-derive the per-block loss bound with the
  two-versus-one destruction structure in place of the uniform
  two-shot count.
- Progress criteria: exact per-block budget identity across the family;
  promotion to the batched-survival research chain.

## Stopped Route

Further tuning of the classical-sieve subtraction — reweighting,
cutoff adjustment, better constants for the same budgets — is a
recorded failed path. The only reopening conditions are genuinely new
arithmetic inputs (a Type-II estimate for the twin correlation or
bilinear structure); maintaining awareness of literature progress on
those inputs is a watch, not a workstream.

## Discipline

Every item follows the repository rules: ticket-first with persistent
memory, one assertion or lemma per verify cycle, language-scoped gates
per change, empirical results labeled empirical, and no promotion into
articles without the conversion gates.
