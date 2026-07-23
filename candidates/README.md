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
`candidates/analysis/`, p to ~19000) is shown in brackets: **[measured]** /
**[deferred]**. Measured candidates carry a per-candidate "Empirical status"
section; see `candidates/analysis/FINDINGS.md` for the cross-candidate
synthesis, distributions, and trends.

1. [Protected endpoints](protected-endpoints.md) — **[measured]** pass 186/186
2. [Local surplus](local-surplus.md) — **[measured]** pass 186/186; surplus ~ p^1.6
3. [Protected clusters](protected-cluster.md) — **[measured]** pass 185/186 (fails at (5,7))
4. [Bounded consecutive destruction](bounded-consecutive-destruction.md) — **[measured]** trajectory flat, max run 2
5. [Bounded post-merge spacers](bounded-post-merge-spacer.md) — **[deferred]** whole-period
6. [Controlled merge runs](controlled-merge-run.md) — **[deferred]** composite, needs whole-period ingredient
7. [Balanced spacers](balanced-spacers.md) — **[deferred]** whole-period
8. [Distinguished head spacer](distinguished-head-spacer.md) — **[measured]** pass 186/186
9. [Forbidden-copy covered runs](forbidden-copy-covered-run.md) — **[deferred]** copy-index / whole-period
10. [Short-window discrepancy](short-window-discrepancy.md) — **[measured]** pass 186/186
11. [Random-like merge survival](random-like-merge-survival.md) — **[measured]** pass 186/186; dest_rate ~ p^-1.6
12. [Local pattern-residue balance](local-pattern-residue-balance.md) — **[measured]** (low power); relative dev shrinks with p
13. [Uniform local observable sampling](uniform-local-observable-sampling.md) — **[measured]** trajectory flat
14. [Hereditary shot-spacing capacity](hereditary-shot-spacing-capacity.md) — **[measured]** building block only (180/186); full chain deferred

## Established Background

The conditional arguments use established facts documented in the
[sieve-sequence property catalog](../properties/sieve-sequence/README.md):
filtering copies or merges gaps, later filtering cannot create a missing
2-gap, post-3 2-gaps are endpoint-disjoint, each new prime forbids two copy
classes, and a square-safe surviving pair is prime. Those established facts do
not establish any candidate hypothesis in this folder.
