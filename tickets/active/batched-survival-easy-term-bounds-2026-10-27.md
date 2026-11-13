# Easy term bounds for batched survival

## START HERE

Micro-goal: prove the easiest useful bounds in the transport formula, beginning
with the lost-region term R and then the per-pair shared-region penalty J.

## Goal

Supply analytical component bounds valid at every allowed stage or eventually
past a stated/existing threshold. Do not substitute empirical positivity for
an induction theorem. Keep A>=0 as an existing result, not a newly proved claim.

## Strategy

Create one research proof note in sequential reviewed additions: finite phase
bound on R; eventual comparison of its upper bound to the explicit density
main term F; factor-budget bounds on J. Link these results from the candidate
after the mathematics passes. No new empirical sweep, executable code, Scala,
or article changes.

## Current State

All three planned mathematical additions are saved in
`properties/sieve-sequence/research/batched-survival-component-bounds.md`:
finite R cap, eventual Rcap/F comparison, and J weight constants. Independent
Critic proof post-review and Monitor gates passed; Markdown and diff checks
passed. No empirical or runtime work occurred. Candidate cross-link is saved
and reviewed; scoped proof work is complete. Mertens' product input was
verified in Pollack, Theorem3.15, printed
p.97; no local population estimate is inferred from it.

Subsequent N/J population and weight bounds are indexed in
[current work](batched-survival-margin-renewal-2026-10-27.md): actual B/F->0
is proved, while positive-margin renewal remains open.

## Related Work

- [Transport and error check](batched-survival-propagation-check-2026-10-27.md).
- [Analytical density/error decomposition](batched-survival-analytic-bound-2026-10-27.md).
- `properties/sieve-sequence/incremental-danger-annulus-decomposition.md`:
  phase5 modulo6 and careful separation of local populations.
- `candidates/local-surplus.md`: established complete-period density
  asymptotic; this is not a local population lower bound.

## What is Learned

- Lost start interval: [q,min(t-1,q^2-3)], length ell=min(t-q,Hq).
  Since w<=1 and admissible starts are5 modulo6, R<=ceil(ell/6).
- For square destinations, this upper budget is O(p^2), while the positive
  density main term F is at least a constant times p^4/log^2(p) eventually.
  Their ratio tends to zero; the comparison is with F, not actual L.
- A new-hit endpoint is r*u with r>=q and u<q. Square-rule geometry gives
  q<s^3 and q^2<s^5. Hence j=1 allows old h<=6; j=2 allows h<=4.
  The cubic penalty is at most10 or9 respectively, so J<=10K1+9K2.
- Combining the bounds gives Lnext>=Lcurrent+A+N-Rcap-10K1-9K2.
  This is a proved sufficient interface, not a bound on N or the hit populations.
- Relevant Scala property/function inventory was also searched read-only;
  no new Scala lemma is required or claimed for this mathematical note.

## Assumptions, Risks, and Alternatives

Use p>=5, s the next prime, and the transport definitions from the existing
note. The finite R bound holds for any q>=s,t>=q; asymptotic and constant-J
statements specialize to q first above p^2 and t first above s^2. Distinct
factor counts, not prime multiplicities, define h. N and R remain signed.
Risks: mistaking F for actual L, assuming R>=0, or treating bounded per-pair
penalties as a bound on how many pairs receive hits. None is justified.

## Validation

Independent mathematical Critic review per small addition, Monitor gates,
verified primary sources, and Markdown link/fence/whitespace checks. No runtime
ecosystem gates apply to proof-only documentation without executable snippets.

## Failed Paths

No failed proof attempt in this scope. Reproving A>=0 would duplicate an
established input. Inferring a positive N from full-period density would leave
the original local-distribution gap; retry only with a proved local estimate.

## Open Concerns

Subsequent proofs control K1,K2 and the absolute N contribution relative to F.
Positive N is not established or required by those bounds. A retained or
replenished actual positive margin remains open.

## Next Action

None for this scoped component-proof task. The successor research now targets
actual positive-margin renewal after the proved N/J bounds; infinite induction
remains open. Historical Learning Log entries describe their original stage.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-10-27 | R can be bounded geometrically and J has a constant per-hit cost under the square rule, leaving population questions separate. | Critic PASS and Monitor bootstrap PASS; ticket created. |
| 2026-10-27 | Finite R cap and eventual Rcap/F decay follow from phase geometry and classical product estimates. | Separate note additions and mathematical checks passed. |
| 2026-10-27 | Shared-region factor budgets bound j1/j2 penalties by10/9 and yield the combined lower-bound interface. | Independent Critic post-review and Monitor checks PASS; links/fences/whitespace and diff checks PASS. Candidate link pending. |
| 2026-10-27 | Component bounds are proved; actual new-region and affected-pair populations remain distinct obligations. | Candidate cross-link and Monitor post-check PASS; all scoped proof work complete, no empirical or runtime changes. |
