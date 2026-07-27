# Weighted Collision-Energy Chain Survival

**Status:** Mathematically proved (conditional chain lemma). Stainless
verification is not claimed here.

## Meaning

A one-layer residue-energy estimate gives a multiplicative survival term minus
an additive error. Applying that inequality separately at every filter can
hide how early errors are attenuated by later survival factors.

This lemma unrolls the complete conditioned chain exactly. The final population
is bounded below by the multiplicative main term minus a weighted sum of the
actual layer collision energies. It identifies one cumulative error budget
whose control is sufficient for a square-window survivor.

## Setup

Fix a future prime head `Q` and a conditioned chain of incoming odd primes

```math
5\le r_0<r_1<\cdots<r_{m-1}<Q.
```

Let `S_i` be the set of complete 2-gap starts in

```math
W_Q=[Q,Q^2)
```

immediately before filter `r_i`, and write

```math
N_i=|S_i|.
```

For each class `a modulo r_i`, define

```math
c_{i,a}
=
\#\{x\in S_i:x\equiv a\pmod{r_i}\}
```

and the layer variance

```math
V_i
=
\sum_{a\bmod r_i}
\left(c_{i,a}-\frac{N_i}{r_i}\right)^2.
```

Set

```math
a_i=1-\frac{2}{r_i},
\qquad
e_i=\sqrt{2V_i}.
```

Because `r_i>2`,

```math
0<a_i<1.
```

## One-Layer Recurrence

Let `K_i` be the number of current 2-gaps destroyed by filter `r_i`. The
two-class collision-energy lemma gives

```math
K_i
\le
\frac{2N_i}{r_i}+e_i.
```

After filter `2`, deleting accepted values cannot create a new 2-gap: a new
merged gap is a sum of positive even old gaps and cannot equal `2`. Therefore
the next population consists exactly of the old 2-gaps whose endpoints both
survive:

```math
N_{i+1}=N_i-K_i.
```

Consequently,

```math
\boxed{
N_{i+1}
\ge
a_iN_i-e_i.
}
```

## Weighted Chain Bound

For `0<=u<=v<=m`, define

```math
A_{u,v}
=
\prod_{j=u}^{v-1}a_j,
```

with the empty product `A_{v,v}=1`.

Then, for every `0<=t<=m`,

```math
\boxed{
N_t
\ge
N_0A_{0,t}
-
\sum_{i=0}^{t-1}e_iA_{i+1,t}.
}
```

### Proof

For `t=0`, the sum is empty and `A_{0,0}=1`, so the statement is the identity

```math
N_0\ge N_0.
```

Assume the statement holds at `t<m`. Since `a_t>0`, the one-layer recurrence
and the induction hypothesis give

```math
\begin{aligned}
N_{t+1}
&\ge a_tN_t-e_t
&&[\text{One-Layer Recurrence}]\\
&\ge
a_t
\left(
N_0A_{0,t}
-
\sum_{i=0}^{t-1}e_iA_{i+1,t}
\right)
-e_t
&&[\text{Induction Hypothesis}]\\
&=
N_0A_{0,t+1}
-
\sum_{i=0}^{t-1}e_iA_{i+1,t+1}
-
e_tA_{t+1,t+1}
&&[\text{Product Definitions}]\\
&=
N_0A_{0,t+1}
-
\sum_{i=0}^{t}e_iA_{i+1,t+1}.
&&[\text{Combine the Final Term}]
\end{aligned}
```

This proves the formula by induction. `[Q.E.D.]`

## Exact Sufficient Budget

At the end of the chain,

```math
N_m
\ge
N_0A_{0,m}
-
\sum_{i=0}^{m-1}
\sqrt{2V_i}\,A_{i+1,m}.
```

Therefore the cumulative inequality

```math
\boxed{
\sum_{i=0}^{m-1}
\sqrt{2V_i}\,A_{i+1,m}
<
N_0A_{0,m}
}
```

implies `N_m>0`.

If the chain installs every missing prime below `Q`, a complete 2-gap
remaining in `[Q,Q^2)` is square-safe and certifies a twin-prime pair.

## Weighted Cauchy--Schwarz Corollary

Write

```math
w_i=A_{i+1,m}.
```

All weights are positive. Cauchy--Schwarz gives

```math
\begin{aligned}
\sum_{i=0}^{m-1}w_i\sqrt{2V_i}
&=
\sum_{i=0}^{m-1}
\sqrt{w_i}\sqrt{2w_iV_i}\\
&\le
\sqrt{\sum_{i=0}^{m-1}w_i}
\sqrt{2\sum_{i=0}^{m-1}w_iV_i}.
\end{aligned}
```

Hence the second-moment budget

```math
\boxed{
2
\left(\sum_{i=0}^{m-1}w_i\right)
\left(\sum_{i=0}^{m-1}w_iV_i\right)
<
\left(N_0A_{0,m}\right)^2
}
```

is also sufficient for `N_m>0`.

This form replaces a sum of square roots by one weighted sum of the actual
collision energies.

## Fixed-Initial-Set Bilinear Form

Although the populations `S_i` change with `i`, they can all be represented by
nested indicator weights on the fixed initial set `S_0`. Define

```math
f_i(x)
=
\prod_{j=0}^{i-1}
\mathbf 1_{r_j\nmid x(x+2)},
\qquad
x\in S_0,
```

with `f_0(x)=1`. Then

```math
S_i=\{x\in S_0:f_i(x)=1\},
\qquad
f_{i+1}(x)\le f_i(x).
```

In particular,

```math
N_i=\sum_{x\in S_0}f_i(x)
```

and

```math
c_{i,a}
=
\sum_{x\in S_0}
f_i(x)\mathbf 1_{x\equiv a\pmod{r_i}}.
```

Squaring the class counts and summing over `a` gives

```math
\begin{aligned}
\sum_{a\bmod r_i}c_{i,a}^2
&=
\sum_{x,y\in S_0}
f_i(x)f_i(y)
\mathbf 1_{r_i\mid(x-y)},\\
\frac{N_i^2}{r_i}
&=
\sum_{x,y\in S_0}
f_i(x)f_i(y)\frac1{r_i}.
\end{aligned}
```

Therefore every layer energy has the exact fixed-domain form

```math
\boxed{
V_i
=
\sum_{x,y\in S_0}
f_i(x)f_i(y)
\left(
\mathbf 1_{r_i\mid(x-y)}-\frac1{r_i}
\right).
}
```

Finite interchange of sums now rewrites the cumulative weighted energy as one
bilinear form:

```math
\boxed{
\sum_{i=0}^{m-1}w_iV_i
=
\sum_{x,y\in S_0}
\sum_{i=0}^{m-1}
w_i f_i(x)f_i(y)
\left(
\mathbf 1_{r_i\mid(x-y)}-\frac1{r_i}
\right).
}
```

The inner kernel records whether the current prime divides the pair
difference, centered by its uniform density, but only while both starts have
survived all earlier filters.

## Deletion Times And Stopped Divisor Sums

For `x in S_0`, define its deletion time

```math
\tau(x)
=
\min\{i:0\le i<m,\ r_i\mid x(x+2)\},
```

and set `tau(x)=m` when no layer hits either endpoint. Then

```math
s(x)
=
\min(\tau(x)+1,m)
```

is the energy stopping index. A start first hit at layer `tau(x)<m` is still
present immediately before that filter, while a final survivor is present
before every layer. Therefore

```math
f_i(x)=\mathbf 1_{i<s(x)}.
```

For a pair `(x,y)`, let

```math
t(x,y)=\min(s(x),s(y)).
```

The coefficient product becomes

```math
f_i(x)f_i(y)
=
\mathbf 1_{i<t(x,y)}.
```

Writing `d=x-y`, the pair's contribution to the fixed-domain bilinear form is
therefore the stopped centered divisor sum

```math
\boxed{
\sum_{i=0}^{t(x,y)-1}
w_i
\left(
\mathbf 1_{r_i\mid d}-\frac1{r_i}
\right).
}
```

For an off-diagonal pair in `W_Q`,

```math
0<|d|<Q^2-Q.
```

Thus the primes contributing positive divisor terms have a product dividing
`|d|` and in particular have product smaller than `Q^2`. This product
constraint is exact. Turning it into an aggregate upper bound strong enough
for the survival budget is a separate open step.

## Telescoping Of The Centering Term

Extend the weight notation by

```math
w_{-1}=A_{0,m}.
```

For every `0<=i<m`,

```math
\begin{aligned}
w_{i-1}
&=A_{i,m}\\
&=a_iA_{i+1,m}\\
&=\left(1-\frac2{r_i}\right)w_i.
\end{aligned}
```

Consequently,

```math
\boxed{
\frac{w_i}{r_i}
=
\frac{w_i-w_{i-1}}2.
}
```

For a stopping index `t>=1`, the centered part of the pair kernel telescopes:

```math
\begin{aligned}
\sum_{i=0}^{t-1}\frac{w_i}{r_i}
&=
\frac12
\sum_{i=0}^{t-1}(w_i-w_{i-1})\\
&=
\frac{w_{t-1}-w_{-1}}2\\
&=
\frac{w_{t-1}-A_{0,m}}2.
\end{aligned}
```

Thus the stopped kernel for difference `d` is exactly

```math
\boxed{
\sum_{\substack{0\le i<t\\r_i\mid d}}w_i
-
\frac{w_{t-1}-A_{0,m}}2.
}
```

For `t=0`, both the original kernel and the corresponding empty divisor sum
are zero.

In particular, if no `r_i` with `i<t` divides `d`, the pair contribution is
nonpositive. Positive off-diagonal energy can come only from differences
having at least one prime divisor from the pair's common survival interval.

## Diagonal And Difference-Grouped Decomposition

For any integer difference `d` and stopping index `0<=t<=m`, define

```math
\kappa_d(t)
=
\sum_{i=0}^{t-1}
w_i
\left(
\mathbf 1_{r_i\mid d}-\frac1{r_i}
\right).
```

For `t>=1`, the telescoped form is

```math
\kappa_d(t)
=
\sum_{\substack{0\le i<t\\r_i\mid d}}w_i
-
\frac{w_{t-1}-A_{0,m}}2,
```

while `kappa_d(0)=0`.

Every start in `S_0` is `5 modulo 6`. Thus every nonzero difference between
two starts is `6h` for some nonzero integer `h`. Let

```math
H
=
\left\lfloor
\frac{\max S_0-\min S_0}{6}
\right\rfloor.
```

The fixed-set bilinear form decomposes exactly as

```math
\boxed{
\begin{aligned}
\sum_{i=0}^{m-1}w_iV_i
&=
\sum_{x\in S_0}
\kappa_0(s(x))\\
&\quad+
2\sum_{h=1}^{H}
\sum_{\substack{x\in S_0\\x+6h\in S_0}}
\kappa_{6h}
\left(
\min(s(x),s(x+6h))
\right).
\end{aligned}
}
```

### Proof

The fixed-set bilinear form sums one kernel over every ordered pair `(x,y)`.
When `x=y`, the difference is `0`, the stopping index is `s(x)`, and the
first displayed sum contains that diagonal term.

When `x!=y`, exactly one orientation has `y=x+6h` for a unique positive
integer `h`. Both orientations have the same difference divisibility and the
same stopping index, so they have equal kernels. Grouping the two orientations
produces the factor `2`. Every ordered pair is included exactly once in either
the diagonal or off-diagonal contribution. `[Q.E.D.]`

This decomposition is the correct place to apply divisor-incidence
information. Maximizing `kappa_d(t)` separately for every pair discards the
distribution of differences and may be much too coarse.

## Aggregate Divisor-Incidence Swap

The positive off-diagonal divisor terms can be summed by layer. Because
`gcd(6,r_i)=1`,

```math
r_i\mid6h
\quad\Longleftrightarrow\quad
r_i\mid h.
```

At layer `i`, the pairs whose common stopping time exceeds `i` are exactly the
pairs of starts still present in `S_i`. The number of ordered distinct pairs
in `S_i` whose difference is divisible by `r_i` is

```math
C_i-N_i,
```

where

```math
C_i
=
\#\{(x,y)\in S_i^2:r_i\mid(x-y)\}.
```

Therefore swapping the difference and layer sums gives the exact positive
off-diagonal incidence

```math
\boxed{
\sum_{i=0}^{m-1}w_i(C_i-N_i).
}
```

For the centered negative part, layer `i` sees all `N_i(N_i-1)` ordered
distinct pairs, each with contribution `-w_i/r_i`. Hence the negative
off-diagonal total is

```math
\boxed{
-\sum_{i=0}^{m-1}
w_i\frac{N_i(N_i-1)}{r_i}.
}
```

The diagonal contribution is

```math
\boxed{
\sum_{i=0}^{m-1}
w_iN_i\left(1-\frac1{r_i}\right).
}
```

Adding the three terms at each layer gives

```math
\begin{aligned}
&(C_i-N_i)
-\frac{N_i(N_i-1)}{r_i}
+N_i\left(1-\frac1{r_i}\right)\\
&=
C_i-\frac{N_i^2}{r_i}\\
&=
V_i.
\end{aligned}
```

Thus the aggregate divisor-incidence swap closes exactly back to

```math
\sum_iw_iV_i.
```

This is a consistency identity, not a new upper bound. Progress requires an
estimate that uses additional structure—such as deletion-time nesting,
correlation across layers, or cancellation in the centered kernels—before the
sums are collapsed into the original per-layer collision counts.

## Why This Is Different From A Pointwise Error Bound

A pointwise program chooses a universal function `B_i` and proves

```math
V_i\le B_i
```

at every layer. The chain lemma does not require each individual `V_i` to be
small. It only consumes their later-survival-weighted total. An unusually
large early error can be tolerable because its weight

```math
A_{i+1,m}
```

includes all later multiplicative attenuation.

The weights are not arbitrary analytic conveniences; they are forced by
unrolling the exact one-layer recurrence.

## Limitation

No bound on the weighted energy sum is proved here. The fixed-set bilinear form
removes the changing-domain problem, but the coefficients `f_i(x)` still vary
with the prime index. A classical large-sieve inequality with one fixed
coefficient sequence therefore cannot be inserted verbatim.

The sufficient budget is also strong enough to imply final square-window
positivity. Any proof must therefore identify a real source of cumulative
cancellation or overlap; replacing each `V_i` by an independent worst-case
maximum merely returns to the already known constant-sensitive square-root
recurrence.

## Related

- [Two-class survival from residue collision energy](
  two-class-survival-from-collision-energy.md
  )
- [Absence of 2-gaps is stable](
  absence-of-two-gaps-is-stable.md
  )
- [Batched short-window discrepancy boundary](
  batched-short-window-discrepancy-boundary.md
  )
