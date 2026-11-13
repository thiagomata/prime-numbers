# Analytical bounds for batched survival

## START HERE

Micro-goal: derive the cubic batch main term and explicit local errors; prove
where its main term is positive and what the elementary error budget can certify.

## Goal

Replace further empirical sweeps with a number-theoretic analysis. Save proved
finite inequalities and a precisely isolated missing estimate, without asserting
local survival from a full-period calculation.

## Strategy

Write each local overlap moment as its exact CRT density main term plus a
signed floor-count discrepancy. Bound the cubic density polynomial analytically.
Then assess the elementary absolute-error bound and identify its limitations.
No Scala code, executable snippets, article changes, or new empirical runs.

## Current State

Scoped analytical study complete. Saved the self-contained proof note at
`properties/sieve-sequence/research/batched-survival-analytic-main-and-error.md`
and linked it from the candidate. Independent Critic proof review and Monitor
checks passed, including the dyadic Bertrand corollary. Primary references,
relative links, fences, whitespace, and git diff --check passed. No empirical
sweeps, executable snippets, Scala changes, or article changes were made.
The actual local signed-discrepancy bound remains open.

Subsequent actual N/J bounds and B/F->0 are proved, without establishing that
signed-discrepancy bound. Current positive-margin renewal work is indexed in
[the successor ticket](batched-survival-margin-renewal-2026-10-27.md).

## Related Work

- [Finite overlap audit](batched-survival-overlap-audit-2026-10-27.md).
- [Generic candidate save](batched-window-survival-candidate-save-2026-10-27.md).
- `properties/sieve-sequence/safe-zone-exhaustion-curve.md`: naive independent
  floor-error estimates can overwhelm a sieve main term; do not repeat a density
  substitution without an error argument.
- `properties/sieve-sequence/research/continuous-sieve-attribution.md`: source
  catalog; Pollack is an exposition, not claimed original discoverer.

## What is Learned

- H=q^2-q-2 is the exact number of eligible integer starts.
- Ik=H*(Gp/M)*e_k+Ek, where e_k is the elementary symmetric sum of 2/r.
- A conservative termwise bound is |Ek|<=Gp*2^k*binomial(b,k).
- With lambda=sum(2/r)<=3/2 and p>=13, the cubic density polynomial
  B3=1-e1+e2-e3 is at least 1/16-3/(4p)>0.
- The termwise triangle-budget certificate cancels Gp and cannot certify when
  H<M. This concerns that estimate, not exact floor sums or the candidate.
- Pollack Theorem 3.14 (printed p.97) supplies the reciprocal-prime estimate;
  Theorem 3.6 and its remark (printed p.89) supply Bertrand. Hence for the
  square destination lambda tends to 2 log 2<3/2 and B3 is eventually positive.
- Bertrand also gives M>2^{m(m-1)/2}, m=floor(log2 p), so H<M for every
  square-jump prime p>=2048. This proves eventual failure of the particular
  triangle certificate, not failure of actual survival.

## Assumptions, Alternatives, and Risks

Use actual sieve cycles, p>=5 and any prime q>p. Full-period CRT independence
does not imply independence in the safe window. For the square rule, Bertrand
and the reciprocal-prime Mertens estimate give lambda->2 log 2<3/2; cite their
precise source locations. No explicit numerical starting threshold is claimed.
Exact error correlations may improve the triangle bound; ruling out that bound
must never be described as ruling out the proposal or all analytical routes.

## Validation

Check the mathematical derivations independently through Critic review, verify
primary references, and check Markdown links, balanced fences and whitespace.
No runtime ecosystem gates apply to mathematical prose without executable code.

## Failed Paths

Naively replacing all CRT class counts by density plus unrelated unit errors
cannot give a positive certificate when H<M: even its zero-order error budget
is at least Gp, whereas its main term is at most H*Gp/M<Gp. Retry with a sharper
or correlated error estimate, or a different decomposition; this is not a
universal no-go theorem for batching.

## Open Concerns

The actual signed discrepancy E0-E1+E2-E3 has no useful uniform lower bound yet.
Proving a positive density polynomial alone does not prove twin-prime survival.

## Next Action

None for the scoped analytical audit. Future research must estimate the actual
one-sided combination E0-E1+E2-E3 using arithmetic correlations or a sharper
decomposition. Neither a new empirical sweep nor unproved independence is a
substitute. The generic positive local theorem is not marked complete.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-10-27 | Cubic main-term positivity and local discrepancy control are distinct proof tasks. | Critic analytical plan PASS and Monitor bootstrap PASS; ticket created. |
| 2026-10-27 | The finite bound B3>=1/16-3/(4p) is positive under the stated load condition; Mertens and Bertrand give that condition eventually for square jumps. | Verified primary references; saved analytical derivations; independent Critic and Monitor post-checks PASS. |
| 2026-10-27 | Unit floor-error budgeting loses the local margin; Gp cancels, and a dyadic Bertrand proof makes H<M explicit for square jumps at p>=2048. | Reviewed corollary saved; candidate linked; Markdown and diff checks PASS. Scoped study complete, signed-error theorem open. |
