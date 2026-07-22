# Batched Short-Window Discrepancy Boundary

**Status:** Problem boundary. The complete-period formula is proved; the
required general short-window positivity bound is open here.

## Meaning

Batching future filters gives an exact CRT count over their complete combined
modulus. The same density is only an expected main term in a shorter interval.
The difference between those two counts is the precise missing quantity.

## Setup

Let

```math
P_Q=\prod_{r<Q}r
```

and define the fully filtered 2-gap starts in an interval `W` by

```math
\mathcal S_Q(W)
=\{x\in W:\gcd(x(x+2),P_Q)=1\}.
```

Over a complete interval of length `P_Q`, CRT gives exactly

```math
\prod_{\substack{3\le r<Q\\r\text{ prime}}}(r-2)
```

surviving start classes.

The corresponding complete-period density is

```math
\delta_Q
=\frac12
\prod_{\substack{3\le r<Q\\r\text{ prime}}}
\left(1-\frac2r\right).
```

## The Missing Bound

For the safe window

```math
W_Q=\{x:Q\le x,\ x+2<Q^2\},
```

write

```math
|\mathcal S_Q(W_Q)|
=|W_Q|\delta_Q+E_Q,
```

where `E_Q` is the short-window discrepancy.

Any theorem proving

```math
E_Q>-|W_Q|\delta_Q
```

would prove `|S_Q(W_Q)|>0`. By safe-window certification, that survivor would
be a genuine twin-prime pair.

## Why Complete-Period Uniformity Is Insufficient

When `|W_Q|<P_Q`, the safe window contains only a partial selection of the CRT
classes. Exact uniformity over the full modulus does not bound how many allowed
classes land in that particular selection. Rotation also does not make the
selection random or uniformly distributed.

Applying all filters in one batch removes intermediate rounding losses and
counts overlapping removals correctly, but it does not automatically control
`E_Q`.

This does not mean that the repeated copies have arbitrary positions. Fix an
old 2-gap `(a,a+2)` in a period of length `M`. Its copies are indexed by `j`:

```math
(a+jM,\ a+2+jM).
```

For every new prime `r`, exactly two copy-index classes modulo `r` are
forbidden. Across a batch, CRT therefore gives a known periodic set of allowed
indices modulo the batch product `B`.

The local problem can equivalently be stated as a covering-radius question:

```math
\text{How long can a consecutive run of copy indices be while every index is}
\text{covered by at least one batch-forbidden residue class?}
```

If the safe window contains more consecutive copies of an old 2-gap than this
maximum covered run, at least one copy must survive the whole batch. This
copy-index formulation retains the distribution supplied by repetition; the
missing result is a sufficiently strong bound on its longest covered run.

## Research Value

This formulation identifies a concrete target stronger than informal density:
find a deterministic lower bound for the sifted pair count in `[Q,Q^2)`, or a
bound on `E_Q` smaller in magnitude than the positive main term. Equivalently,
bound the maximum consecutive run covered by the two forbidden copy-index
classes contributed by each prime in the batch.

## Limitation

The displayed main term is not itself a lower bound. Replacing the exact local
count by its complete-period density without controlling `E_Q` would assume
the positional conclusion that remains to be proved.
