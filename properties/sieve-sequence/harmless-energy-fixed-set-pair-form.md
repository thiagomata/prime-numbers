# Harmless Energy As A Fixed-Set Pair Correlation

**Status:** Mathematically proved exact identities. Stainless verification is
not claimed.

## Meaning

Candidate #22 measures how unevenly the post-filter 2-gap survivors occupy the
`r-2` harmless residue classes. Its energy is exactly a centered ordered-pair
count: two survivors collide when their start difference is divisible by the
prime that just filtered them.

The older first-deletion property contains a closely related post-filter
variance centered over all `r` classes. Correcting the center from `r` to
`r-2` subtracts an explicit positive population-square term. This identifies
the exact extra cancellation available only in the harmless-alphabet
formulation.

## One-Layer Setup

Let `S_i` be the complete 2-gap starts immediately before filter `r_i`, and
let

```math
S_{i+1}
=
\{
x\in S_i:
r_i\nmid x(x+2)
\}
```

be the starts that survive that filter. Write

```math
M_i=|S_{i+1}|.
```

Every start in `S_{i+1}` lies in one of the `r_i-2` harmless residue classes

```math
a\notin\{0,-2\}\pmod{r_i}.
```

Define

```math
d_{i,a}
=
\#\{
x\in S_{i+1}:
x\equiv a\pmod{r_i}
\}.
```

Then

```math
\sum_{a\notin\{0,-2\}}d_{i,a}=M_i
```

and candidate #22's harmless energy is

```math
U_i
=
\sum_{a\notin\{0,-2\}}
d_{i,a}^2
-
\frac{M_i^2}{r_i-2}.
```

## Ordered-Pair Form

For every harmless class `a`,

```math
d_{i,a}^2
=
\#\{
(x,y)\in S_{i+1}^2:
x\equiv y\equiv a\pmod{r_i}
\}.
```

Summing over the harmless classes gives

```math
\sum_{a\notin\{0,-2\}}d_{i,a}^2
=
\#\{
(x,y)\in S_{i+1}^2:
r_i\mid x-y
\}.
```

Therefore

```math
\boxed{
U_i
=
\sum_{x,y\in S_{i+1}}
\left(
\mathbf 1_{r_i\mid(x-y)}
-
\frac1{r_i-2}
\right).
}
\qquad[\text{Q.E.D.}]
```

Separating the `M_i` diagonal pairs gives the equivalent form

```math
\boxed{
U_i
=
M_i
+
\#\{
(x,y)\in S_{i+1}^2:
x\ne y,\ r_i\mid x-y
\}
-
\frac{M_i^2}{r_i-2}.
}
```

This states exactly how much off-diagonal collision candidate #22 can afford.

## Autocorrelation Form

Assume the starts lie in an interval of diameter `L`. After filter `3`, every
2-gap start is `5 modulo 6`. For distinct starts `x<y`,

```math
r_i\mid y-x
```

is therefore equivalent to

```math
6r_i\mid y-x.
```

For `d>0`, define

```math
A_{S_{i+1}}(d)
=
\#\{
x:
x\in S_{i+1},\
x+d\in S_{i+1}
\}.
```

Every unordered positive-separation pair has two ordered orientations.
Consequently,

```math
\boxed{
R_i
=
2
\sum_{1\le h\le\lfloor L/(6r_i)\rfloor}
A_{S_{i+1}}(6r_ih).
}
\qquad[\text{Q.E.D.}]
```

Each summand counts the four endpoint offsets

```math
\{0,2,6r_ih,6r_ih+2\}
```

after all four endpoints have survived filters through `r_i`.

Using the fixed-initial-set indicators,

```math
\boxed{
A_{S_{i+1}}(d)
=
\sum_{\substack{x\\x,x+d\in S_0}}
f_{i+1}(x)f_{i+1}(x+d).
}
```

Thus the complete weighted off-diagonal count is

```math
\boxed{
\sum_iw_iR_i
=
2\sum_iw_i
\sum_{1\le h\le\lfloor L/(6r_i)\rfloor}
\sum_{\substack{x\\x,x+6r_ih\in S_0}}
f_{i+1}(x)f_{i+1}(x+6r_ih).
}
```

This is an exact weighted sum of conditioned four-point correlations on one
fixed initial set.

## Relation To The Existing Post-Filter Variance

The first-deletion property uses the same class square sum centered over all
`r_i` residue classes:

```math
V_{r_i}(S_{i+1})
=
\sum_{a\notin\{0,-2\}}d_{i,a}^2
-
\frac{M_i^2}{r_i}.
```

Subtracting the definitions gives

```math
\begin{aligned}
V_{r_i}(S_{i+1})-U_i
&=
\frac{M_i^2}{r_i-2}
-
\frac{M_i^2}{r_i}\\
&=
\frac{2M_i^2}{r_i(r_i-2)}.
\end{aligned}
```

Hence

```math
\boxed{
U_i
=
V_{r_i}(S_{i+1})
-
\frac{2M_i^2}{r_i(r_i-2)}.
}
\qquad[\text{Q.E.D.}]
```

The correction is nonnegative and is strictly positive whenever `M_i>0`.
Thus #22 is strictly narrower than bounding the older post-filter variance.

## Fixed-Initial-Set Form

Let `S_0` be the initial 2-gap-start set and define the nested survivor
indicators

```math
f_i(x)
=
\prod_{j=0}^{i-1}
\mathbf 1_{r_j\nmid x(x+2)},
\qquad
x\in S_0.
```

Then

```math
S_{i+1}
=
\{
x\in S_0:
f_{i+1}(x)=1
\},
\qquad
M_i
=
\sum_{x\in S_0}f_{i+1}(x).
```

The ordered-pair form becomes

```math
\boxed{
U_i
=
\sum_{x,y\in S_0}
f_{i+1}(x)f_{i+1}(y)
\left(
\mathbf 1_{r_i\mid(x-y)}
-
\frac1{r_i-2}
\right).
}
```

For the candidate #21 weights `w_i`, finite interchange of sums gives

```math
\boxed{
\sum_{i=0}^{m-1}w_iU_i
=
\sum_{x,y\in S_0}
\sum_{i=0}^{m-1}
w_i
f_{i+1}(x)f_{i+1}(y)
\left(
\mathbf 1_{r_i\mid(x-y)}
-
\frac1{r_i-2}
\right).
}
\qquad[\text{Q.E.D.}]
```

This is candidate #22's exact fixed-domain bilinear form.

## Post-Deletion Stopping Kernel

For `x in S_0`, let `tau(x)` be its first deleting layer, with `tau(x)=m` for
a final survivor. Since `f_{i+1}` includes filter `r_i`,

```math
f_{i+1}(x)
=
\mathbf 1_{i<\tau(x)}.
```

For a pair `(x,y)`, define

```math
t_h(x,y)
=
\min(\tau(x),\tau(y)).
```

Then

```math
f_{i+1}(x)f_{i+1}(y)
=
\mathbf 1_{i<t_h(x,y)}.
```

Writing `d=x-y`, the pair kernel is therefore

```math
\boxed{
\kappa_d^{(h)}(t)
=
\sum_{i=0}^{t-1}
w_i
\left(
\mathbf 1_{r_i\mid d}
-
\frac1{r_i-2}
\right).
}
```

and

```math
\boxed{
\sum_iw_iU_i
=
\sum_{x,y\in S_0}
\kappa_{x-y}^{(h)}
\left(
t_h(x,y)
\right).
}
```

Unlike the full-energy kernel, this kernel stops before the first deleting
filter rather than including it. Both members of every counted pair have
already survived `r_i`.

## Exact Centering Telescope

The harmless center splits as

```math
\frac1{r_i-2}
=
\frac1{r_i}
+
\frac{2}{r_i(r_i-2)}.
```

Extend the collision-weight notation by

```math
w_{-1}=A_{0,m}.
```

The established adjacent-weight identity gives

```math
\sum_{i=0}^{t-1}\frac{w_i}{r_i}
=
\frac{w_{t-1}-A_{0,m}}2
```

for `t>=1`. Consequently,

```math
\boxed{
\kappa_d^{(h)}(t)
=
\sum_{\substack{i<t\\r_i\mid d}}w_i
-
\frac{w_{t-1}-A_{0,m}}2
-
\sum_{i<t}
\frac{2w_i}{r_i(r_i-2)}.
}
```

For `t=0`, both the original kernel and the displayed sums are zero.

Relative to the full centered divisor kernel with the same stopping time,
#22 therefore has the additional nonpositive term

```math
\boxed{
-
\sum_{i<t}
\frac{2w_i}{r_i(r_i-2)}.
}
```

This is the pair-kernel counterpart of the population-square correction

```math
-
\frac{2M_i^2}{r_i(r_i-2)}
```

in the layerwise energy.

## Arithmetic Constraint On Positive Pair Terms

For `x\ne y`, every positive divisibility term satisfies

```math
r_i\mid x-y,
\qquad
i<t_h(x,y).
```

Thus both starts survive `r_i` in the same harmless residue class. The product
of all distinct primes contributing positive terms for one pair divides
`|x-y|`. Since `x,y` lie in `[Q,Q^2)`,

```math
0<|x-y|<Q^2-Q.
```

This gives the same exact pairwise prime-product restriction as the full
collision kernel, now only for post-filter harmless pairs.

## Size Of The Additional Centering

Every collision weight satisfies

```math
0<w_i\le1.
```

Also,

```math
\frac{2}{n(n-2)}
=
\frac1{n-2}-\frac1n.
```

The incoming primes form a subset of the odd integers at least `5`.
Consequently, for every stopping time `t`,

```math
\begin{aligned}
0
&\le
\sum_{i<t}
\frac{2w_i}{r_i(r_i-2)}\\
&\le
\sum_{\substack{n\ge5\\n\text{ odd}}}
\frac{2}{n(n-2)}\\
&=
\left(\frac13+\frac15\right)\\
&=
\boxed{\frac8{15}}.
\end{aligned}
```

Thus #22's extra negative centering improves each pair kernel by less than a
universal constant.

The existing worst-difference strategy bounds the number of positive prime
divisors by

```math
\frac{2\log Q}{\log5}.
```

Subtracting at most `8/15` cannot change that logarithmic growth. Therefore
the new correction does not rescue a proof that first applies the
worst-difference bound independently to every ordered pair.

## What The Identity Does Not Prove

The product restriction limits the positive primes for one difference. It
does not by itself bound the sum over all ordered pairs. A worst-pair estimate
multiplied by `|S_0|^2` repeats the already-failed candidate #21 strategy.

Finally, the negative correction

```math
-\frac{2M_i^2}{r_i(r_i-2)}
```

is exact leverage, but exploiting it requires comparing the post-filter pair
correlation with the actual survivor population without first assuming that
population is positive.

## Related

- [Conditioned harmless-class collision energy](
  ../../candidates/conditioned-harmless-class-collision-energy.md
  )
- [First-deletion pair terminal energy](
  first-deletion-pair-terminal-energy.md
  )
- [Weighted collision-energy chain survival](
  weighted-collision-energy-chain-survival.md
  )
- [Orthogonal residue-energy decomposition after a two-class filter](
  orthogonal-residue-energy-decomposition-after-two-class-filter.md
  )
