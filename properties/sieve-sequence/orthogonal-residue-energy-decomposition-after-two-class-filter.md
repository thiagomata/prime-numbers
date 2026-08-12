# Orthogonal Residue-Energy Decomposition After A Two-Class Filter

**Status:** Mathematically proved exact identity. Stainless verification is not
claimed.

## Meaning

Residue collision energy before an incoming filter has three independent
components:

1. total excess in the two harmful classes;
2. imbalance between those two classes;
3. nonuniformity among the harmless classes that survive the filter.

These components add as exact squares. This removes the linear cross terms
that obscured the first-deletion calculation and identifies harmless-class
dispersion as the sole remaining distributional quantity after the two
endpoint observables are controlled.

## Setup

Let `r>2` and let

```math
c_a
=
\#\{x\in S:x\equiv a\pmod r\},
\qquad
N=\sum_{a\bmod r}c_a.
```

The two harmful start classes for 2-gaps are `0` and `-2`. Write

```math
k_0=c_0,
\qquad
k_{-2}=c_{-2},
```

```math
K=k_0+k_{-2},
\qquad
\Delta=k_0-k_{-2},
```

and let

```math
M=N-K
```

be the number of starts in the `r-2` harmless classes.

Define the full residue energy

```math
V
=
\sum_{a\bmod r}
\left(
c_a-\frac Nr
\right)^2
```

and the harmless-class energy around its own mean

```math
U
=
\sum_{a\notin\{0,-2\}}
\left(
c_a-\frac{M}{r-2}
\right)^2.
```

Finally, define the signed total harmful excess

```math
b
=
K-\frac{2N}{r}.
```

## Exact Decomposition

The collision form of the full energy is

```math
V
=
\sum_{a\bmod r}c_a^2-\frac{N^2}{r}.
```

The two harmful squares satisfy

```math
k_0^2+k_{-2}^2
=
\frac{K^2+\Delta^2}{2}.
```

The harmless energy definition gives

```math
\sum_{a\notin\{0,-2\}}c_a^2
=
U+\frac{M^2}{r-2}.
```

Therefore

```math
V
=
U
+
\frac{K^2+\Delta^2}{2}
+
\frac{M^2}{r-2}
-
\frac{N^2}{r}.
```

Substitute

```math
K=\frac{2N}{r}+b,
\qquad
M=\frac{r-2}{r}N-b.
```

Expanding the two squares gives

```math
\begin{aligned}
\frac{K^2}{2}
&=
\frac{2N^2}{r^2}
+
\frac{2Nb}{r}
+
\frac{b^2}{2},\\
\frac{M^2}{r-2}
&=
\frac{r-2}{r^2}N^2
-
\frac{2Nb}{r}
+
\frac{b^2}{r-2}.
\end{aligned}
```

The linear terms cancel, and

```math
\frac{2N^2}{r^2}
+
\frac{r-2}{r^2}N^2
-
\frac{N^2}{r}
=
0.
```

The remaining `b^2` coefficient is

```math
\frac12+\frac1{r-2}
=
\frac{r}{2(r-2)}.
```

Hence

```math
\boxed{
V
=
U
+
\frac{r}{2(r-2)}b^2
+
\frac12\Delta^2.
}
\qquad[\text{Q.E.D.}]
```

## Consequences

All three terms are nonnegative, so

```math
V\ge U,
```

```math
V\ge\frac{r}{2(r-2)}b^2,
```

and

```math
V\ge\frac12\Delta^2.
```

More importantly for upper bounds, any estimates

```math
U\le\mathcal U,
\qquad
|b|\le\mathcal B,
\qquad
|\Delta|\le\mathcal D
```

imply

```math
\boxed{
V
\le
\mathcal U
+
\frac{r}{2(r-2)}\mathcal B^2
+
\frac12\mathcal D^2.
}
```

Under perfect total harmful balance and perfect left/right balance,

```math
b=0,
\qquad
\Delta=0,
```

the full pre-filter energy is exactly the harmless survivor energy:

```math
V=U.
```

## Boundary

The unsigned and signed endpoint observables can control `b` and `Delta` when
combined with accepted-strike density. They do not control `U`.

A natural benchmark

```math
U\le M
```

is exactly a relative collision-energy bound on the `r-2` harmless classes:

```math
\sum_{a\notin\{0,-2\}}c_a^2
\le
M+\frac{M^2}{r-2}.
```

Thus the new decomposition does not prove harmless dispersion. It shows that
this smaller-alphabet collision estimate, rather than full residue
equidistribution or endpoint sampling, is the precise remaining theorem.

## Related

- [Two-class survival from residue collision energy](
  two-class-survival-from-collision-energy.md
  )
- [First-deletion pair terminal energy](
  first-deletion-pair-terminal-energy.md
  )
- [Two endpoint observables separate harmful excess and imbalance](
  two-endpoint-observables-separate-harmful-excess-and-imbalance.md
  )
- [Cumulative weighted collision budget](
  ../../candidates/cumulative-weighted-collision-budget.md
  )
