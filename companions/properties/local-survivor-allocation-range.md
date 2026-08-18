# Local Survivor Allocation Range

**Status:** Mathematically proved finite-combinatorics fact. Holds for **any**
size-`K` harmful set intersecting a size-`L` relevant set, including the real
sieve's CRT-determined harmful indices. The hypergeometric specialization
assumes the harmful set is a uniform random size-`K` subset. This is the one
property in `companions/properties/` that does not require any companion-process
premise; it is filed here because its home is the companion allocation
framework, but it applies unchanged to the real modular filter.

## Meaning

An adversarial budget says how many parents receive harmful treatment, but it
does not say which parents they are. That missing choice can move the local
outcome across its entire feasible range. Consequently no percentage-only
threshold applies simultaneously to a position-blind mixture and a perfectly
targeted adversary. Allocation is a second independent axis from total budget.

## Setup

At one filter, let

- `N` be the total number of parents;
- `R` be the set of parents with a child in target region `W`, with `L = |R|`;
- `B` be the set of parents assigned harmful (bad) behavior, with `K = |B|`.

Each relevant parent contributes at most one target child (the post-crossover
geometry for windows shorter than the old period), so the number of target
children destroyed is

```math
H=|B\cap R|,
```

and the number surviving is `S = L - H`.

## Property

The intersection size obeys the sharp bounds

```math
\begin{aligned}
H
&\le\min(K,L)
&&[\text{Intersection Cannot Exceed Either Set}],\\
H
&\ge\max(0,K-(N-L))
&&[\text{Only }N-L\text{ Irrelevant Parents Exist}].
\end{aligned}
```

Substituting into `S = L - H`,

```math
\max(0,L-K)
\le S\le
\min(L,N-K).
```

Both endpoints are attainable. A target-aware bad allocator selects members of
`R` first and gives

```math
S_{\mathrm{targeted}}=\max(0,L-K).
```

An optimistic allocator spends harmful labels on the `N - L` irrelevant parents
first and gives

```math
S_{\mathrm{optimistic}}=\min(L,N-K).
```

$\blacksquare$

## Uniform Random Allocation Specialization

If `B` is instead a uniformly random size-`K` subset of the `N` parents, then

```math
H\sim\text{Hypergeometric}(N,L,K),
```

so

```math
\begin{aligned}
\mathbb E[H]&=\frac{KL}{N},\\
\mathbb E[S]&=L\left(1-\frac KN\right).
\end{aligned}
```

When `K >= L`, the exact probability of total local destruction is

```math
\Pr(S=0)
=
\frac{\binom{N-L}{K-L}}{\binom NK}
=
\frac{\binom KL}{\binom NL}.
```

## Head Extreme Case

The head makes the distinction between allocation laws extreme. There `L = 1`:

- a target-aware adversary kills the unique head candidate whenever `K >= 1`,
  requiring only the global share `1/N`;
- uniform allocation kills it with probability `K/N`;
- optimistic allocation preserves it whenever `K <= N - 1`.

This is why total budget and targeting strength are independent axes, not
alternative names for one percentage. See
[Targeted Head Suppression](../balanced-adversarial-2-gap/targeted-head-suppression.md)
for the companion-process endpoint that exploits this.

## What This Does And Does Not Say

The bounds hold for the real sieve as well, with `B` equal to the
CRT-determined set of parents whose copy indices land in the two harmful
classes. They bound what is achievable by allocation; they do not say which
endpoint the real arithmetic approaches. That is the open real-sieve question
framed by the [phase-transition article](../../articles/draft/draft-adversariality-phase-transition-2-gap-companions.md).
