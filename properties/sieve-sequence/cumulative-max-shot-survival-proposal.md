# Cumulative Max-Shot Survival Proposal

**Status:** Candidate proposal under adversarial review. The one-transition
implication is supported by existing local-capacity properties; the cumulative
abundance premise is open.

## The proposed idea

Suppose a layer contains many complete 2-gaps in a target interval. An
incoming prime filter can remove only a bounded number of accepted values, or
only a bounded number of 2-gaps, according to the relevant shot theorem. If
the population is larger than that capacity, at least one 2-gap survives.

For a single transition, let `G_local(p,q)` be the number of pre-filter
2-gaps in the square window for the next head `q`, and let `A(p,q)` be the
exact number of accepted values struck by the incoming prime `p`. Existing
isolation after filter `3` gives

```math
G_{\mathrm{after}}(p,q)
\ge G_{\mathrm{local}}(p,q)-A(p,q).
```

Consequently,

```math
G_{\mathrm{local}}(p,q)>A(p,q)
\Longrightarrow
G_{\mathrm{after}}(p,q)>0.
```

The proposed cumulative version is to define conditioned populations
`G_0,G_1,...,G_k` and per-layer destruction capacities `A_1,...,A_k`, then
seek a lower bound of the form

```math
G_k\ge G_0-\sum_{j=1}^{k}A_j.
```

If the right side is at least one and every surviving 2-gap lies below the
appropriate square boundary, the surviving pair is certified as a twin-prime
pair. A lower bound at infinitely many stages would give infinitely many
pairs.

## What is valid

The one-transition inequality is valid when all quantities refer to the same
local window, the incoming filter is fixed, and the shot capacity counts the
accepted values that can actually destroy a 2-gap. After filter `3`,
endpoint-disjointness makes one removed accepted value destroy at most one
complete 2-gap. The exact local threshold is therefore `A(p,q)+1` gaps.

A genuine cumulative theorem would also be valid if it supplied nested
conditioned sets `S_0\supseteq S_1\supseteq\cdots\supseteq S_k` and proved,
for each layer,

```math
|S_{j-1}\setminus S_j|\le A_j.
```

Telescoping then gives

```math
|S_k|=|S_0|-
\sum_{j=1}^{k}|S_{j-1}\setminus S_j|
\ge |S_0|-\sum_{j=1}^{k}A_j.
```

This is the exact form a successful cumulative max-shot proof would need.

## Adversarial review

### Failure 1: global counts do not locate local gaps

The exact complete-period count

```math
\prod_{r<p}(r-2)
```

counts cyclic residue gaps over a full period. It does not imply that the
square window `[q,q^2)` contains the required local population. A cumulative
argument that substitutes the global count for `G_local` has an unproved
placement step. The existing global-count threshold note gives a rigorous
sufficient condition, but records that its threshold is generally too large.

### Failure 2: raw multiples are not accepted shots

Counting every multiple of `p` overestimates or misstates destruction. The
relevant capacity is the number of accepted strike values in the window, or a
proved local 2-gap shot bound. A formula using `floor((q^2-1)/p)` without
subtracting already rejected values is not the exact local capacity.

### Failure 3: one deleted endpoint can couple to the population

Without endpoint-disjointness, one strike can destroy two adjacent 2-gaps by
their shared endpoint. The subtraction coefficient one is therefore not
automatic. It is valid only after the layer where the isolation property is
available, or after replacing raw gap counts by a disjoint matching.

### Failure 4: summing capacities can use the wrong population

After the first filter, the next layer's population is the surviving subset,
not the original local count. A bound of the form `G_0-sum(A_j)` is valid only
when each `A_j` bounds the actual difference between two nested conditioned
sets. Per-layer maxima computed on different windows or different ambient
populations cannot simply be added.

### Failure 5: the safe boundary changes with the head

A survivor below one square threshold can be certified at that stage, but a
later stage uses a different head and a different local window. A cumulative
population that crosses several windows is not automatically a cumulative
population of certifiable pairs.

### Failure 6: positive global growth is not a local lower bound

The global 2-gap count can grow while its density decreases. This is
compatible with an empty selected short window. To use growth, one needs a
localization theorem, a discrepancy bound, or a count in the exact square
window—not only a complete-period asymptotic.

## Strongest defensible research target

The proposal should therefore be split into two lemmas:

```math
\text{(Local abundance)}quad
G_0(W)>\sum_{j=1}^{k}A_j(W)+1,
```

where every term is defined on the same fixed window and the conditioned
populations are nested; and

```math
\text{(Certification)}quad
x+2<q^2
\Longrightarrow
(x,x+2)\text{ is a twin-prime pair after the }q\text{-filters}.
```

The first is the genuinely open part. The second is the established
square-safe implication. A proof of the local-abundance lemma for infinitely
many heads would prove infinitely many twin-prime pairs.

An even weaker target is enough: if the exact local count exceeds the exact
accepted-shot capacity for infinitely many transitions, then at least one new
survivor occurs infinitely often. Empty windows at some stages are harmless;
the count must be positive for infinitely many stages, not for every stage.

## Verdict

The proposal is mathematically meaningful and worth testing. Its one-step
capacity mechanism is sound and already represented by the local survival
threshold. The naive claim that a growing global 2-gap total automatically
beats the cumulative shot sum is false or incomplete because it lacks local
placement and uses changing conditioned populations. The viable program is to
prove a same-window nested-population lower bound, then apply the existing
shot-capacity and square-certification lemmas. This is a research candidate,
not a twin-prime proof.

## Related properties

- [Sharp local 2-gap survival threshold](sharp-local-two-gap-survival-threshold.md)
- [Global count threshold that forces local survival](global-count-forcing-local-survival.md)
- [A local count forces the k=2 shot-capacity premise](local-count-forces-k2-shot-capacity.md)
- [Exact global 2-gap count](exact-global-two-gap-count.md)
- [Filtering attrition bound for close-pair matchings](filtering-attrition-bound-close-pair-matching.md)
