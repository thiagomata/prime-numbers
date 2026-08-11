# Copy-Block Harmful Excess Is Controlled By Residue Energy

**Status:** Mathematically proved exact one-filter identities and bounds.
Stainless verification is not claimed.

## Meaning

When one old period is repeated through the copies required by an incoming
prime, the harmful excess in each old-period copy block is not arbitrary. It
is exactly the sum of two centered entries of the old start histogram modulo
the incoming prime.

Consequently, the total squared discrepancy across all copy blocks is at most
four times the full residue-histogram energy. Any consecutive run of complete
old-period blocks inherits a square-root prefix bound. This gives a precise
bridge from candidate #20's one-layer collision energy to candidate #24's
localized harmful excess.

The theorem does not bound the residue energy itself. An arbitrary numerical
interval also leaves at most two partial old-period boundary fragments, which
need separate control.

## Setup

Let `M>=1`, let `r>=5` be prime, and assume

```math
\gcd(M,r)=1.
```

Let `S` be a finite set of old 2-gap starts represented in `[0,M)`, with

```math
N=|S|.
```

For `t modulo r`, define the old-period residue histogram and its centered
deviation by

```math
c_t
=
\#\{a\in S:a\equiv t\pmod r\},
\qquad
d_t=c_t-\frac Nr.
```

The full residue energy is

```math
V_r=\sum_{t\bmod r}d_t^2.
```

Copy block `j` is `[jM,(j+1)M)`. It contains the lifted starts

```math
a+jM,
\qquad a\in S.
```

Let `K_j` count the lifted starts in block `j` destroyed by filter `r`, and
define their centered harmful excess

```math
B_j=K_j-\frac{2N}{r}.
```

## Exact Copy-Block Formula

Put

```math
t_j\equiv-jM\pmod r.
```

A copied start `a+jM` is destroyed exactly when

```math
a+jM\equiv0\pmod r
```

or

```math
a+jM+2\equiv0\pmod r.
```

The two cases are disjoint because `r>2`. They are respectively equivalent to

```math
a\equiv t_j\pmod r,
\qquad
a\equiv t_j-2\pmod r.
```

Therefore

```math
\boxed{
K_j=c_{t_j}+c_{t_j-2}
}
```

and hence

```math
\boxed{
B_j=d_{t_j}+d_{t_j-2}.
}
\qquad[\text{Q.E.D.}]
```

This is the aggregate counterpart of the exact two forbidden copy-index
classes for each individual old 2-gap.

## Complete-Copy Zero Sum

Because `gcd(M,r)=1`, the map

```math
j\longmapsto t_j=-jM\pmod r
```

permutes all residue classes modulo `r`. Also

```math
\sum_{t\bmod r}d_t
=
\sum_tc_t-N
=0.
```

It follows that

```math
\begin{aligned}
\sum_{j=0}^{r-1}B_j
&=
\sum_{t\bmod r}(d_t+d_{t-2})\\
&=2\sum_{t\bmod r}d_t\\
&=\boxed{0}.
\end{aligned}
```

Thus every complete run of `r` old-period copy blocks contributes zero
harmful excess, agreeing with complete-period CRT cancellation.

## Exact Block-Energy Identity

The same permutation gives

```math
\begin{aligned}
\sum_{j=0}^{r-1}B_j^2
&=
\sum_{t\bmod r}(d_t+d_{t-2})^2\\
&=
2\sum_td_t^2
+2\sum_td_td_{t-2}.
\end{aligned}
```

Therefore

```math
\boxed{
\sum_{j=0}^{r-1}B_j^2
=
2V_r+2\sum_{t\bmod r}d_td_{t-2}.
}
```

Using `2xy<=x^2+y^2` and summing cyclically,

```math
2\sum_td_td_{t-2}
\le
\sum_td_t^2+\sum_td_{t-2}^2
=2V_r.
```

Hence

```math
\boxed{
\sum_{j=0}^{r-1}B_j^2\le4V_r.
}
\qquad[\text{Q.E.D.}]
```

The exact autocorrelation term retains information that the `4V_r` bound
discards. It may be negative.

## Consecutive Complete-Block Bound

Take any `k` consecutive copy blocks, cyclically if necessary, with
`0<=k<r`. Cauchy--Schwarz gives

```math
\begin{aligned}
\left|\sum_{j\in J}B_j\right|^2
&\le
k\sum_{j\in J}B_j^2\\
&\le
k\sum_{j=0}^{r-1}B_j^2\\
&\le
\boxed{4kV_r}.
\end{aligned}
```

Equivalently,

```math
\boxed{
\left|\sum_{j\in J}B_j\right|
\le2\sqrt{kV_r}.
}
```

For an arbitrary consecutive run of `q` complete copy blocks, remove its
complete groups of `r` blocks using the zero-sum identity and put

```math
k=q\bmod r.
```

The same bound applies with that remainder `k`.

## Arbitrary-Interval Boundary

An arbitrary integer interval can be partitioned into:

1. a left partial old-period block;
2. a consecutive run of complete old-period blocks;
3. a right partial old-period block.

The complete-block contribution is bounded by `2sqrt(kV_r)` after complete
`r`-block cycles are removed.

Each partial block contains at most one copy of each start in `S`. Since

```math
\left|
\mathbf1_{r\mid x(x+2)}-\frac2r
\right|
\le1-\frac2r
```

for `r>=5`, each partial contribution has absolute value at most

```math
N\left(1-\frac2r\right).
```

Thus the general deterministic bound is

```math
\boxed{
|b_r(I)|
\le
2N\left(1-\frac2r\right)
+2\sqrt{kV_r},
\qquad 0\le k<r.
}
```

This bound is deliberately honest about the remaining obstruction. When the
old modulus exceeds the interval length, there may be no complete old-period
block and the boundary term dominates. A successful chain theorem must add
short-window information for those partial blocks or average them with signs.

## Filter-Seven Check

For the Filter-Seven Excess Bound property's old period `M=30`, incoming prime `r=7`, and starts

```math
S=\{11,17,29\},
```

the histogram modulo `7` is

```math
(c_0,\ldots,c_6)=(0,1,0,1,1,0,0).
```

The seven copy-block discrepancies are exactly

```math
\frac17(-6,1,8,1,1,1,-6).
```

They sum to zero, and direct arithmetic gives

```math
\sum_jB_j^2=\frac{20}{7}
\le
4V_7=\frac{48}{7}.
```

This is a finite consistency check, not part of the proof.

## Consequence For The Final Programs

Candidate #20's residue-collision energy satisfies

```math
V_r=C_r-\frac{N^2}{r}.
```

Therefore any relative collision theorem for candidate #20 immediately gives
a quantitative bound on candidate #24's harmful excess over complete
old-period block runs. This is a genuine composition bridge between the two
candidates.

It does not finish candidate #24:

- candidate #20's conditioned relative collision bound is open;
- the weighted chain still contains many layers;
- late layers with `M` larger than the square window have no complete block;
- and the two partial boundary fragments retain the original signed
  short-window problem.

The theorem is consequently a reduction, not a survival claim.

## Related

- [Exact Filter Frequency Across Repeated Copies](copy-index-filter-frequency.md)
- [Conditioned Residue-Collision Energy](../../candidates/conditioned-residue-collision-energy.md)
- [Weighted Harmful-Excess Quadratic Survival](../../candidates/weighted-harmful-excess-quadratic-survival.md)
- [Filter-Seven Harmful Excess Is Boundary-Sized](filter-seven-harmful-excess-is-boundary-sized.md)
- [Native-Period Bessel and Capacity Give a Sharp Hybrid Envelope](native-period-bessel-capacity-hybrid-envelope.md)
