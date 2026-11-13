# Signed-discrepancy and propagation check

## START HERE

Micro-goal: check the exact signed-error condition at early heads and derive
what a genuine one-step propagation argument would need.

## Goal

Answer the user's empirical question and induction proposal with exact finite
checks and proved transport identities. Distinguish the reformulated positivity
check from independent evidence for a uniform discrepancy theorem.

## Strategy

For nine starting heads, compute exact rational cubic density main terms and
signed local errors. Separate advancing the starting head at a fixed destination
from moving the destination window. Prove and check the corresponding identities,
then save the derivation and reproducible experiment in a research note.

## Current State

Scoped check complete. All nine exact rational, survivor-oracle, fixed-target
and moving-window transport checks passed. Signed-error positivity and
nonnegative moving balance both held in the sample. The minimum L3/main ratio
was about 0.971611; this is finite evidence only. The research note is saved at
`properties/sieve-sequence/research/batched-survival-propagation-check-2026-10-27.md`
and linked from the candidate. Its exact embedded rerun and independent Critic
reproduction passed. Mathematical transport, shared-region cost, and density/
error updates passed independent review; Monitor and Markdown checks passed.
Infinite moving-window closure remains open.

## Related Work

- [Current margin-renewal work](batched-survival-margin-renewal-2026-10-27.md):
  subsequent actual N/J bounds and B/F->0 are proved; the positive reserve
  remains unproved. Historical observations below retain their original scope.

- [Analytical main/error study](batched-survival-analytic-bound-2026-10-27.md).
- [Finite overlap audit](batched-survival-overlap-audit-2026-10-27.md).
- `candidates/dream-sequence-self-propagating-invariant.md`: seed plus closure
  is an established conditional framework; local preservation remains open.
- `properties/sieve-sequence/incremental-danger-annulus-decomposition.md`:
  local moving-window populations must be separated from full-period totals.

## What is Learned

- At a fixed destination q, removing the next old-head filter from the remaining
  batch discards only nonpositive cubic weights. The lower bound L3 cannot
  decrease; actual final survivors are unchanged.
- For a moving destination t>=q, define all new/lost/shared sets using pair-start
  intervals and intermediate old-head s. Exact transport is
  Lnext=Lcurrent+A+N-R-J, with A>=0 and J>=0 but signed N and R.
- A sufficient monotone-propagation condition is A+N-R-J>=0; a weaker positivity
  condition is A+N-R-J>-Lcurrent. Neither is independently proved recurrently.
- In the shared region each endpoint receives at most one new prime hit, so
  the additional hit count j<=2. Already surviving pairs receive none. For a
  blocked pair, the cubic penalty is j*binomial(h-1,2)+binomial(j,2)*(h-1),
  at most (h-1)^2. This refines the moving-window cost analytically.
- At p=31,s=37,q=967,t=1373, the balance is
  5591+566+4023-11-596=9573. No recurring law follows from this example.
- At fixed q the density main term grows by H*delta_p*(2/p)*e3(s,q);
  the signed error changes by A minus that amount. Neither error monotonicity
  nor a fixed relative-error bound follows automatically.
- E>=0 fails at p=5 (E about -0.701233), while E>-main holds. A later-threshold
  claim is not refuted by this case, but no such claim is established.

## Experiment, Assumptions, and Risks

Heads p=5,7,11,13,17,19,23,29,31; s is the next prime. Let q be the first prime
above p^2 and t the first prime above s^2. Maximum s=37, t=1373, endpoints below
1885129. Compute local weights by exact divisibility and old gcd acceptance.
Compute B3, main, and E with rational arithmetic; compare survivor sets against
an independent Eratosthenes prime oracle. Validate fixed-target monotonicity
and the signed partition identity. Do not interpret positive tested margins as
proof of an all-stage invariant. No complete huge old cycles are materialized.

## Validation

Bounded stdlib Python -B, no file writes or packages. Check exact rational
identities, survivor-set oracle equality, fixed-target monotonicity, signed
transport, and cubic bounds. Rerun the exact embedded research-note snippet.
Check Markdown links/fences/whitespace and independent mathematical review.
No Scala or article gates apply.

## Failed Paths

A fixed-destination monotone bound cannot alone imply infinitude: it certifies
the same finite final window. Revisit only with a proved moving-window balance
or recurrence condition. Checking E>-main is exactly checking L3>0, so it must
not be advertised as an independent proof or estimate of the error.
An unconditional all-stage E>=0 statement is defeated by p=5; revisit only
with a qualified later threshold or an appropriate one-sided negative allowance.

## Open Concerns

An independent structural estimate for the moving-window balance is missing.
The feature condition must eventually be derived from current finitely checkable
information, not merely reassert positivity of the next stage.

## Next Action

None for this scoped check. Subsequent component proofs supply independent
new-region and combined-loss bounds relative to F. Future work must prove
that an actual positive reserve is retained or replenished; this induction
step is not established by the nine observations or transport identity.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-10-27 | Fixed-target purification is provably monotone, while advancing the target introduces a separate signed balance. | Critic PASS and Monitor bootstrap PASS; ticket created. |
| 2026-10-27 | Nine error checks and moving balances are positive; fixed-target monotonicity and shared-region weighted penalty are mathematical identities/bounds. | Diagnostic exit0 and independent-oracle controls PASS; Critic interpretation PASS. Durable save still pending. |
| 2026-10-27 | Exact fixed-target error update exposes a four-filter anchored overlap, while moving targets require independent new-mass/loss bounds. | Saved reviewed proof note and exact snippet; rerun and independent Critic reproduction PASS. |
| 2026-10-27 | Empty-batch endpoint and finite evidence limits must remain explicit; no recurring closure follows. | Clarification and candidate cross-link reviewed; links/fences/whitespace and diff checks PASS. Scoped check complete. |
