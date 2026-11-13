# Cluster Exposure And Local Extinction Of 2-Gaps

**Status:** Draft concept note. Not an article-ready proof.

## Core Idea

The current survival-frontiers companion is clear because it asks a simple
tree-level question: when a parent 2-gap is lifted through a new filter, what
is the chance that one of its two endpoint copies is struck? It deliberately
randomizes the local multiple check while preserving the marginal two-shot
rate.

That model is useful, but it is not the whole local geometry of the real
sieve. In the real gap cycle, a deleted endpoint is not only a deleted point.
It merges neighboring gaps. If the left endpoint of a 2-gap is removed, the
2-gap is absorbed into the gap on its left. If the right endpoint is removed,
it is absorbed into the gap on its right. Near the cyclic cut, the wrap gap
can participate as well.

So the tree model eventually meets a dependency wall:

```text
if this candidate dies, the local object beside it changes.
```

At that point, the natural next scale is not the individual tree. It is the
forest: a local cluster or window containing many candidate 2-gaps. Instead
of asking whether one named lineage survives independently, ask whether the
whole local population can be extinguished.

## The Forest Question

Fix a local window `W` before filter `p`. Suppose `W` contains `N(W)`
candidate 2-gaps. The incoming filter can strike endpoints of those candidates.
Some endpoint strikes destroy a candidate 2-gap directly; some also merge
neighboring gaps and change the local environment.

The forest-level question is:

```text
How much destructive concentration is required for filter p
to leave no 2-gap surviving in W?
```

This is different from the tree-level question. Tree-level survival wants a
lineage probability. Forest-level survival wants an extinction threshold.

## Known Mean, Unknown Local Shape

The global marginal rate is known. For one incoming prime `p`, a copied 2-gap
has two harmful endpoint lift offsets in a complete block of `p` copies. Thus
the first-order expected hit count in a window with `N(W)` randomly spread
candidate 2-gaps is approximately

```text
E[H_p(W)] ~= 2*N(W)/p.
```

This is the same mean that the simple random companion preserves.

But the mean does not specify the local shape. Inside a cluster, close shots
are restricted by arithmetic geometry:

- the two endpoint shots of a copied 2-gap form a rigid pair, not an arbitrary
  two-subset;
- close candidate 2-gaps share nearby gap-cycle structure;
- endpoint deletion has side effects on neighboring gaps;
- the actual local values determine which close residues can be hit together.

We may not know all those values in advance. But we do know the mean, and we
can ask whether the unknown local shape behaves around that mean or whether it
must realize a severe upper-tail concentration to extinguish the cluster.

## Cluster Exposure Curve

Define the local exposure count

```text
H_p(W) = number of harmful endpoint shots from filter p that land in W.
```

More refined versions can distinguish:

```text
H_p^endpoint(W)  = endpoint hits,
H_p^gap(W)       = candidate 2-gaps directly destroyed,
H_p^merge(W)     = merge side effects touching the cluster,
H_p^effective(W) = candidates removed after direct hits and merge effects.
```

The basic object is not only the mean but the exposure distribution:

```text
Pr[H_p(W) >= t]
```

or empirically, over comparable windows,

```text
F_p(t) = fraction of windows W with H_p(W) <= t.
```

Call this the **cluster exposure curve**. It measures how strongly a filter
can concentrate harmful shots inside a local forest.

## Extinction Threshold

For a window `W`, define an extinction threshold

```text
T_p(W) = minimum effective exposure needed for filter p
         to leave no 2-gap surviving in W.
```

The threshold is not always equal to `N(W)`, because side effects matter. One
well-placed endpoint deletion can merge through a local structure and change
more than the directly struck candidate. Conversely, some endpoint hits may be
redundant if they strike candidates whose neighboring structure has already
changed.

This is the "if I die, you do not die in the same way" problem. The forest
model does not pretend those dependencies are absent. It packages them into
the effective extinction threshold.

The adversariality score for a window can then be written as

```text
A_p(W) = T_p(W) / (2*N(W)/p).
```

Interpretation:

```text
A_p(W) ~= 1      extinction is at the random mean scale
A_p(W) > 1       extinction requires above-average concentration
A_p(W) >> 1      extinction is an upper-tail/adversarial event
```

For the crude direct-destruction model, where every one of the `N(W)`
candidates must be destroyed directly, the threshold is `T_p(W) = N(W)`.
Then

```text
A_p(W) ~= p/2.
```

So a single large prime filter would need to behave about `p/2` times more
destructively than the random mean to wipe out the whole cluster. Merge side
effects can lower the threshold, but the score gives a way to quantify how
much they lower it.

## Why This Should Stay Separate From The Simple Companion

The simple survival-frontiers companion is a mean-field relaxation. It asks
what happens when the multiple check is randomized while the two-shot deletion
rate is preserved. That clarity is valuable.

The cluster exposure model is a second article. It asks a different and more
mature question:

```text
given the known mean and the real local constraints,
how extreme must the local exposure curve be to eliminate a whole forest?
```

This keeps the original random model honest without burying it under the full
dependency machinery.

## Possible Structure For A Future Article

1. Tree-level companions and why they are useful.
2. Where tree independence breaks: endpoint deletion creates neighbor merges.
3. Shift from lineages to local forests.
4. Define `N(W)`, `H_p(W)`, exposure curves, and effective exposure.
5. Define the extinction threshold `T_p(W)`.
6. Define adversariality score `A_p(W)`.
7. Compare three levels:

```text
random two-subset companion
rigid-pair companion
rigid-pair plus cluster exposure
```

8. Empirical program: measure exposure curves over real sieve windows.
9. Boundary: what the model can say without a full local-value theorem.

## Empirical Direction

The measurement version is straightforward in principle:

1. Generate or load a stage gap cycle.
2. Choose comparable local windows `W`.
3. Count candidate 2-gaps in each window.
4. Apply the next filter's actual endpoint tests.
5. Record direct endpoint hits, direct 2-gap destruction, and merge side
   effects.
6. Build the empirical curve for `H_p(W)` and compare it to `2*N(W)/p`.

This would turn "adversarial" from a metaphor into a measured local excess:

```text
realized exposure / random mean exposure.
```

The important point is not that every window must look random. The point is
to learn whether full local extinction is typical, or whether it lives deep
in the upper tail of the exposure curve.

