# Candidate Conditions for Square-Safe 2-Gap Survival

This folder records research hypotheses that would be sufficient to force
2-gap survival near the head of a sieve sequence. These hypotheses are not
known properties of the merge process and may be false. They are kept outside
`properties/`, which is reserved for established mathematical results.

Each note separates four things:

1. an unproved candidate hypothesis;
2. a proved implication from that hypothesis to square-safe survival;
3. established inputs already documented under `properties/sieve-sequence/`;
4. the exact limitation or missing research obligation.

## Common Notation

Let `p` be the prime installed by a transition and `q` the next prime head. The
eligible 2-gap-start window is

```math
W_q=\{x:q\le x\text{ and }x+2<q^2\}.
```

Let `S_old` be the pre-filter 2-gap starts and `S_q` the starts that remain
after installing `p`. A point of `S_q` in `W_q` is a square-safe twin-prime
certificate.

A condition holding at one stage gives one certificate. Holding at infinitely
many stages gives infinitely many certificates. Holding eventually at every
stage is a stronger requirement than is needed.

## Candidate Index

Each entry's empirical status (from the window-scale stress-test,
`candidates/analysis/`, p to ~19000) distinguishes a direct condition test from
a partial proxy or a deferred measurement. Every note includes its own
strategic assessment; see `candidates/analysis/FINDINGS.md` for the corrected
cross-candidate synthesis.

1. [Protected endpoints](protected-endpoints.md) — **[outcome measured]** 186/186; not a distinct mechanism
2. [Local surplus](local-surplus.md) — **[directly measured]** 186/186; terminal sufficient target
3. [Protected clusters](protected-cluster.md) — **[directly measured]** 185/186 (fails at (5,7))
4. [Bounded consecutive destruction](bounded-consecutive-destruction.md) — **[window-linear proxy]** flat, max run 2; cyclic condition unmeasured
5. [Bounded post-merge spacers](bounded-post-merge-spacer.md) — **[deferred]** whole-period
6. [Controlled merge runs](controlled-merge-run.md) — **[deferred]** composite, needs whole-period ingredient
7. [Balanced spacers](balanced-spacers.md) — **[deferred]** whole-period
8. [Distinguished head spacer](distinguished-head-spacer.md) — **[outcome measured]** 186/186; near-restatement of local survival
9. [Forbidden-copy covered runs](forbidden-copy-covered-run.md) — **[deferred]** copy-index / whole-period
10. [Short-window discrepancy](short-window-discrepancy.md) — **[measurement mismatch]** pre-filter discrepancy recorded; stated post-filter condition unmeasured
11. [Random-like merge survival](random-like-merge-survival.md) — **[benchmark measured]** favorable rate; deterministic transference unmeasured
12. [Local pattern-residue balance](local-pattern-residue-balance.md) — **[partial diagnostic]** prior normalization was insufficient; stated margin untested
13. [Uniform local observable sampling](uniform-local-observable-sampling.md) — **[partial diagnostic]** absolute bias recorded; one-sided survival margin untested
14. [Hereditary shot-spacing capacity](hereditary-shot-spacing-capacity.md) — **[proxy only]** waste ratio recorded; interval/partial-sum and hereditary conditions unmeasured

## Established Background

The conditional arguments use established facts documented in the
[sieve-sequence property catalog](../properties/sieve-sequence/README.md):
filtering copies or merges gaps, later filtering cannot create a missing
2-gap, post-3 2-gaps are endpoint-disjoint, each new prime forbids two copy
classes, and a square-safe surviving pair is prime. Those established facts do
not establish any candidate hypothesis in this folder.
