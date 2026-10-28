# Filtered shot population bound for shared-region cost

## START HERE

Micro-goal: bound the actual number of new shared-region hits using old-filter
acceptance, then prove eventual smallness of actual J relative to density F.

## Goal

Sharpen the previous per-pair cost bounds into a real population estimate.
Use classical prime counting to prove an eventual property of actual square
transitions. Keep comparison with F distinct from comparison with actual L.

## Strategy

Exploit a special square-destination dichotomy: either t=q and J=0, or q<s^2.
Then each new-hit endpoint has a PRIME cofactor, not merely a rough cofactor.
First save the finite factor and population bound in one proof note. Separately
add the prime-number-theorem argument giving J/F->0. Then link the candidate
and record the exact unresolved N/margin task. No empirical or executable work.

## Current State

Finite and asymptotic proofs are saved in
`properties/sieve-sequence/research/batched-survival-filtered-shot-bound.md`.
Independent Critic proof post-review and Monitor checks passed. Actual
J/F->0 and an independent hit-population bound are now proved. Component and
candidate scope updates are saved and reviewed; scoped proof work is complete.
Subsequent N bounds and combined B/F->0 are proved; actual positive-margin
renewal remains open. See [current work](batched-survival-margin-renewal-2026-10-27.md).
All four affected files passed local links, fences and whitespace checks;
git diff --check passed. Primary PNT exposition verified in
Pollack, Chapter7 equation(7.1), printed p.214; final proof uses PNT alone
for the prime-count estimates. No empirical or runtime work occurred.

## Related Work

- [Component bounds](batched-survival-easy-term-bounds-2026-10-27.md).
- [Transport](batched-survival-propagation-check-2026-10-27.md).
- [Positive density main term](batched-survival-analytic-bound-2026-10-27.md).
- `properties/sieve-sequence/research/batched-survival-component-bounds.md`:
  former unconditional square-rule weights10/9, now sharpened through t=q split.

## What is Learned

- If q>s^2, no prime lies between p^2 and q, so t=q. If t>q, necessarily q<s^2.
- For a shared new hit n=r*u with q<=r<t, we have n>=t and n<q^2, hence
  1<u<q<s^2. Old filters exclude factors<s, so u is a prime in [s,q).
- Pair endpoints are disjoint. New-hit incidences inject into ordered prime
  products (r,u), giving K1+2K2<=bP, with b=pi(t-1)-pi(q-1) and
  P=pi(q-1)-pi(s-1).
- When a new hit exists, the j1 old-hit count is <=4, cost<=3; j2 has two
  prime cofactors, old-hit count2, cost1. Thus J<=3K1+K2<=3bP.
- PNT implies t/q->1 and b=o(q/log q), while P=O(q/log q). Therefore
  actual J=o(q^2/log^2 q), giving J/F->0 under the established F lower bound.
- Together with R<=Rcap and Rcap/F->0, every fixed epsilon>0 eventually
  satisfies R+J<=epsilon*F. This is a proved upper-cost statement for actual
  transitions, not an assumed local margin bound.

## Assumptions and Risks

p>=5, s next prime, q first prime above p^2, t first prime above s^2.
Shared endpoints are at least t and strictly below q^2. PNT is an external
proved theorem, not a hypothesis. Its subtraction yields only b=o(q/log q),
not b asymptotic to (t-q)/log q in a short interval. F is a density benchmark;
no uniform lower bound on actual L or positive new-region N is concluded.

## Validation

Independent mathematical Critic review per addition, Monitor gates, verified
primary references, and Markdown links/fences/whitespace checks. No runtime,
Scala, article, or PDF gates apply to proof-only notes without executable code.

## Failed Paths

The initial planning route counted prime and semiprime rough cofactors using
q<s^3. Its auxiliary prime-count difference could be negative unless truncated
at zero. Before implementation, Critic found the stronger t=q / t>q dichotomy,
making the semiprime branch unnecessary for these square transitions. Do not
reuse that longer route here; revisit only for different destination rules
where the dichotomy fails, with nonnegative count definitions enforced.

## Open Concerns

Subsequent work proves absolute N/F->0 and hence a useful lower bound for N.
Preservation of an actual positive reserve remains open. J/F->0 is not J/L->0
without an additional lower bound relating L to F.

## Next Action

None for this scoped J-bound proof. Subsequent new-region work supplies its
absolute bound; next analytical work is a retained or replenished positive
actual margin. Historical Learning Logs below describe the earlier stage.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-10-27 | The square-destination dichotomy removes semiprime cofactors and strengthens the finite estimate. | Revised plan passed Critic; Monitor bootstrap approved; ticket created. |
| 2026-10-27 | Prime-cofactor incidence bounds control actual hit populations; PNT gives actual J/F->0 without a relative short-interval asymptotic. | Separate proof additions, primary source check, independent Critic and Monitor post-checks PASS; Markdown/diff checks PASS. Documentation synchronization pending. |
| 2026-10-27 | Actual shared-region cost is eventually small relative to F; N and actual-margin propagation remain distinct open obligations. | Component and candidate scope synchronized; all four files checked green; scoped proof complete, no empirical/runtime work. |
