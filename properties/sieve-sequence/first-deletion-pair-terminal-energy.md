# First-Deletion Pair Terminal Energy

**Status:** Mathematically proved exact identity. Stainless verification is not
claimed.

## Meaning

Group ordered pairs of current 2-gaps by the first layer after which at least
one member is absent. At that terminal layer, a same-residue collision has a
very specific meaning: both gaps are destroyed in the same one of the two
harmful start classes.

This gives an exact terminal contribution involving only the current
population, the next population, and the sizes of the two harmful classes.
It exposes a possible negative contribution when the total destruction and
the split between the two endpoint classes are sufficiently balanced.

The identity does not yet bound the earlier-layer history of those pairs.

## Setup

At layer `t`, let `S_t` be the 2-gap starts immediately before filtering by
the prime `r_t`, and write

```math
N_t=|S_t|.
```

Define the two harmful subsets

```math
D_{t,0}
=
\{x\in S_t:r_t\mid x\},
```

```math
D_{t,-2}
=
\{x\in S_t:r_t\mid x+2\}.
```

Since `r_t>2`, these sets are disjoint. Write

```math
k_{t,0}=|D_{t,0}|,
\qquad
k_{t,-2}=|D_{t,-2}|,
```

and define

```math
K_t=k_{t,0}+k_{t,-2},
\qquad
\Delta_t=k_{t,0}-k_{t,-2}.
```

Filtering destroys exactly these `K_t` gaps, so

```math
N_{t+1}=N_t-K_t.
```

## The Terminal Pair Block

Let `s(x)` be the corrected energy stopping index: `x` belongs to `S_i`
exactly when `i<s(x)`. Define

```math
\mathcal P_t
=
\{
(x,y)\in S_0^2:
\min(s(x),s(y))=t+1
\}.
```

These are exactly the ordered pairs for which both members are in `S_t` but
not both are in `S_{t+1}`. Therefore

```math
\boxed{
|\mathcal P_t|
=
N_t^2-N_{t+1}^2.
}
```

## Same-Residue Pairs In The Terminal Block

Suppose `(x,y)` belongs to `P_t` and

```math
r_t\mid x-y.
```

At least one of `x,y` is in a harmful start class. Since their start residues
are equal, the other lies in the same harmful class. Conversely, two starts
in the same harmful class are both destroyed at layer `t`, have equal start
residue modulo `r_t`, and hence belong to `P_t`.

Thus

```math
\boxed{
\#\{
(x,y)\in\mathcal P_t:r_t\mid x-y
\}
=
k_{t,0}^2+k_{t,-2}^2.
}
```

This count includes the diagonal pairs of the destroyed gaps, as required by
the collision energy.

## Exact Terminal Energy

The contribution of layer `t` to the stopped kernel of a pair in `P_t` is

```math
w_t
\left(
\mathbf 1_{r_t\mid x-y}-\frac1{r_t}
\right).
```

Summing over the terminal block and using the two exact counts above gives

```math
\boxed{
T_t
=
w_t
\left[
k_{t,0}^2+k_{t,-2}^2
-
\frac{N_t^2-N_{t+1}^2}{r_t}
\right].
}
```

Since

```math
k_{t,0}^2+k_{t,-2}^2
=
\frac{K_t^2+\Delta_t^2}{2}
```

and

```math
N_t^2-N_{t+1}^2
=
2N_tK_t-K_t^2,
```

the same identity is

```math
\boxed{
T_t
=
w_t
\left[
\frac{K_t^2+\Delta_t^2}{2}
-
\frac{2N_tK_t-K_t^2}{r_t}
\right].
}
```

## Centered Harmful-Count Form

Define the signed harmful excess

```math
b_t
=
K_t-\frac{2N_t}{r_t}.
```

Substitution and simplification give

```math
\boxed{
\frac{T_t}{w_t}
=
-
\frac{2(r_t-2)}{r_t^3}N_t^2
+
\frac{4}{r_t^2}N_tb_t
+
\frac{r_t+2}{2r_t}b_t^2
+
\frac12\Delta_t^2.
}
```

The first term is negative. The remaining terms measure two distinct
departures from the balanced model:

- `b_t` measures excess total destruction beyond `2N_t/r_t`;
- `Delta_t` measures imbalance between the two endpoint classes.

## Exact Earlier-History Telescope

For any subset `A` of starts, define its centered collision count modulo
`r_i` by

```math
V_{r_i}(A)
=
\#\{(x,y)\in A^2:r_i\mid x-y\}
-
\frac{|A|^2}{r_i}.
```

The contribution of layers earlier than `t` to the terminal block is

```math
H_t
=
\sum_{(x,y)\in\mathcal P_t}
\sum_{i<t}
w_i
\left(
\mathbf 1_{r_i\mid x-y}-\frac1{r_i}
\right).
```

Because

```math
\mathcal P_t=S_t^2\setminus S_{t+1}^2,
```

finite sum interchange gives

```math
\boxed{
H_t
=
\sum_{i<t}
w_i
\left(
V_{r_i}(S_t)-V_{r_i}(S_{t+1})
\right).
}
```

The ordered pairs surviving every filter form the final block `S_m^2`. Its
history contribution is

```math
H_m
=
\sum_{i<m}w_iV_{r_i}(S_m).
```

For each fixed `i`, summing the history differences over
`t=i+1,...,m-1` and then adding the final block telescopes:

```math
\sum_{t=i+1}^{m-1}
\left(
V_{r_i}(S_t)-V_{r_i}(S_{t+1})
\right)
+
V_{r_i}(S_m)
=
V_{r_i}(S_{i+1}).
```

Consequently, the complete weighted energy has the exact decomposition

```math
\boxed{
\sum_{i<m}w_iV_i
=
\sum_{t<m}T_t
+
\sum_{i<m}w_iV_{r_i}(S_{i+1}).
}
```

This is equivalently the layerwise partition

```math
\boxed{
V_{r_i}(S_i)
=
\frac{T_i}{w_i}
+
V_{r_i}(S_{i+1}).
}
```

## Sharp Harmless-Class Envelope

After filter `r_i`, the two harmful residue classes are empty. Set

```math
r=r_i,
\qquad
M=N_{i+1},
\qquad
h=r-2.
```

Let the `h` harmless class counts be

```math
d_1,\ldots,d_h,
\qquad
\sum_{j=1}^h d_j=M.
```

Then

```math
V_{r_i}(S_{i+1})
=
\sum_{j=1}^h d_j^2-\frac{M^2}{r}.
```

Write

```math
M=qh+s,
\qquad
0\le s<h.
```

The sum of squares is minimized when `s` classes have size `q+1` and the
remaining classes have size `q`. It is maximized when one class contains all
`M` points. Therefore the sharp unconstrained envelope is

```math
\boxed{
hq^2+2sq+s-\frac{M^2}{r}
\le
V_{r_i}(S_{i+1})
\le
M^2\left(1-\frac1r\right).
}
```

The upper endpoint is compatible with any prescribed values of the earlier
harmful counts `k_{i,0}` and `k_{i,-2}`: those counts have already been
deleted and impose no restriction on how the `M` survivors split among the
harmless classes. Thus `K_i`, `b_i`, and `Delta_i` alone cannot upper-bound
the post-filter variance below quadratic scale.

If an independent theorem gives a common harmless-class capacity

```math
0\le d_j\le B,
```

write

```math
M=q_BB+u,
\qquad
0\le u<B.
```

Convexity now maximizes the square sum by filling `q_B` classes to capacity,
putting `u` points in one further class, and leaving the rest empty. Assuming
the necessary feasibility `M<=hB`, the sharp capacity-constrained upper
envelope is

```math
\boxed{
V_{r_i}(S_{i+1})
\le
q_BB^2+u^2-\frac{M^2}{r}
\le
BM-\frac{M^2}{r}.
}
```

For post-3 2-gap starts in an interval of diameter `L`, the proved phase
capacity supplies

```math
B
=
\left\lfloor\frac{L}{6r}\right\rfloor+1.
```

This is the exact point where the unconditional candidate #19 structure can
enter the cumulative energy program.

## Capacity Recombination Returns The Direct Bound

The same common class capacity also gives

```math
k_{i,0}^2+k_{i,-2}^2
\le
B(k_{i,0}+k_{i,-2})
=
BK_i.
```

Combine this with the terminal identity and the simpler harmless-class bound:

```math
\begin{aligned}
V_{r_i}(S_i)
&=
\frac{T_i}{w_i}
+
V_{r_i}(S_{i+1})\\
&\le
BK_i
-
\frac{N_i^2-N_{i+1}^2}{r_i}
+
BN_{i+1}
-
\frac{N_{i+1}^2}{r_i}\\
&=
\boxed{
BN_i-\frac{N_i^2}{r_i}.
}
\end{aligned}
```

This is exactly the direct whole-histogram estimate

```math
\sum_{a\bmod r_i}c_{i,a}^2
\le
B\sum_{a\bmod r_i}c_{i,a}
=
BN_i.
```

Thus applying the same capacity bound to both the deleted and surviving
classes discards the terminal cancellation and returns the original
one-layer collision-capacity inequality. The first-deletion decomposition
gains nothing unless one side receives a strictly sharper estimate.

## Boundary

This identity is stronger bookkeeping than the ungrouped variance sum, but it
does not by itself prove candidate #21. The earlier histories telescope
exactly to the post-filter variances `V_{r_i}(S_{i+1})`. Those terms are
nonnegative and are not controlled by the negative terminal main term.

Thus grouping by first deletion is a useful structural diagnosis but not an
energy upper bound. A continuation must independently control the
post-filter variances, or exploit a relation between them and the two terminal
errors `b_i` and `Delta_i`. Repeating the history telescope cannot produce
further cancellation; it only reconstructs the layerwise variance partition.

The sharp envelope shows that the terminal observables alone cannot provide
that control: arbitrary harmless-class concentration remains possible.
Adding the existing phase capacity gives a linear-in-`M` upper bound with
coefficient `B`. Applying the same capacity to the harmful classes then
recombines to the direct whole-histogram bound, so this symmetric composition
cannot improve candidate #21. A useful continuation needs asymmetric
information: sharper control of harmful-class imbalance, sharper dispersion
among harmless survivors, or a cross-layer relation between them.

## Related

- [Weighted collision-energy chain survival](
  weighted-collision-energy-chain-survival.md
  )
- [Weighted deletion conservation law](
  weighted-deletion-conservation-law.md
  )
- [Cumulative weighted collision budget](
  ../../candidates/cumulative-weighted-collision-budget.md
  )
