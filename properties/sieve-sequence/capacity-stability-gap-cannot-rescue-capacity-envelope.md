# Capacity Stability Gap Cannot Rescue the Capacity Envelope

**Status:** Mathematically proved conditional obstruction. The asymptotic
corollary uses the prime number theorem and Mertens' theorem for primes as
explicit external dependencies. Stainless verification is not claimed.

## Meaning

Property #69 enlarges candidate #24's extinction threshold by the stability
gap `Gamma_cap`. Property #70 supplies the separate capacity upper envelope
`U_cap`. The open capacity-only certificate is

```math
\mathcal U_{\mathrm{cap}}
<
\frac{T^2}{2W_-}
+
\Gamma_{\mathrm{cap}}.
```

This property proves that the enlarged threshold is still far too small under
full candidate #17. The filter-`7` coordinate alone makes the upper envelope
of order `P_mD^2`. By contrast, the capacity stability gap eventually comes
only from filter `5` and is smaller by a factor tending to zero.

The stability gap is eventually positive. The obstruction is quantitative:
it does not grow nearly fast enough to absorb the separate capacity envelope.
This exhausts the `Gamma_cap` repair of that envelope, not candidate #17,
candidate #24, or a future localized upper bound for the actual energy.

## Setup

Fix a future prime head `Q>=17` and its complete conditioned chain

```math
r_0=5,
\qquad
r_1=7,
\qquad
r_0<r_1<\cdots<r_{m-1}<Q.
```

Write

```math
D=Q^2-Q-3,
\qquad
a_i=1-\frac2{r_i},
\qquad
P_i=\prod_{j<i}a_j,
```

```math
R_i=\sum_{j=i}^{m-1}\frac1{P_j},
\qquad
S=R_0.
```

Let `N_0` be the number of complete 2-gap starts before filter `5`. Because
these starts occupy one residue class modulo `6`,

```math
\frac D6-1
\le
N_0
\le
\frac D6+1.
```

The total capacity of the two harmful classes at layer `i` is

```math
C_i
=
2\left(
\left\lfloor\frac{D}{6r_i}\right\rfloor+1
\right).
```

Property #69 gives the deletion mass of the extinct Cauchy minimizer:

```math
N_i^\star
=
\frac{N_0P_iR_i}{S},
\qquad
b_i^\star
=
\frac{a_iN_0}{S},
```

```math
K_i^\star
=
\frac2{r_i}N_i^\star+b_i^\star.
```

It defines

```math
\Gamma_{\mathrm{cap}}
=
\max_i
\frac{(K_i^\star-C_i)_+^2}{\mathcal D_i},
```

where `mathcal D_i` is the dual squared norm of the layer-`i` deletion
functional.

## Every Post-5 Violation Has a Negative Capacity Margin

Since `R_i<=S`,

```math
N_i^\star
=
\frac{N_0P_iR_i}{S}
\le
N_0P_i.
```

For every `i>=1`, the product contains `a_0=3/5`, so

```math
P_i\le\frac35.
```

Also `a_i<=1`, `N_0<=D/6+1`, and `C_i>=D/(3r_i)`. Therefore

```math
\begin{aligned}
K_i^\star-C_i
&\le
\frac{2N_0P_i}{r_i}
+
\frac{N_0}{S}
-
\frac{D}{3r_i}
\\
&\le
\frac{6N_0}{5r_i}
+
\frac{N_0}{S}
-
\frac{D}{3r_i}
\\
&\le
\boxed{
\frac{N_0}{S}
-
\frac{2D-18}{15r_i}
}.
\end{aligned}
```

Because `r_i<Q`, the finite condition

```math
\boxed{
S
\ge
\frac{15QN_0}{2D-18}
}
```

implies

```math
\boxed{
K_i^\star\le C_i
\quad\text{for every }i\ge1.
}
```

Thus every post-`5` coordinate contributes zero to `Gamma_cap` whenever the
displayed finite condition holds.

## The Remaining Filter-5 Stability Gap

At `i=0`, one has

```math
p_0=\frac25,
\qquad
a_0=\frac35,
\qquad
R_1=S-1.
```

Consequently,

```math
\begin{aligned}
K_0^\star
&=
\frac{N_0}{S}
\left(
1+\frac25(S-1)
\right)
\\
&=
\boxed{
\frac{2N_0}{5}
+
\frac{3N_0}{5S}
}.
\end{aligned}
```

The elementary bounds

```math
\frac D{15}
\le
C_0
\le
\frac D{15}+2
```

and `D/6-1<=N_0<=D/6+1` give

```math
\frac{3N_0}{5S}-\frac{12}{5}
\le
K_0^\star-C_0
\le
\frac{3N_0}{5S}+\frac25.
```

For the first coordinate, the dual norm contains no earlier terms. Since

```math
P_1=a_0=\frac35,
\qquad
w_0=\frac{P_m}{P_1},
```

its energy coefficient is

```math
\alpha_0
=
\frac{w_0}{2a_0}
=
\boxed{\frac{25P_m}{18}},
```

and `1/mathcal D_0=alpha_0`. Under the finite condition above, only this
coordinate can contribute, so

```math
\boxed{
\Gamma_{\mathrm{cap}}
\le
\frac{25P_m}{18}
\left(
\frac25+\frac{3N_0}{5S}
\right)^2.
}
```

The lower estimate also shows that the gap is positive whenever

```math
\frac{N_0}{S}>4.
```

## Candidate #17 Forces a Much Larger Filter-7 Envelope

Assume candidate #17's local-count threshold at filter `7`. Property #75
then gives the sharp coordinate envelope

```math
X_1\ge B_1^2,
\qquad
B_1
=
\left\lfloor\frac D{42}\right\rfloor+1
\ge
\frac D{42}.
```

Here

```math
P_2
=
\frac35\frac57
=
\frac37,
\qquad
w_1
=
\frac{P_m}{P_2}.
```

Hence the layer-`1` energy coefficient is

```math
\alpha_1
=
\frac{w_1}{2a_1}
=
\boxed{\frac{49P_m}{30}}.
```

Keeping only this nonnegative term in property #70's envelope gives

```math
\begin{aligned}
\mathcal U_{\mathrm{cap}}
&\ge
\alpha_1X_1
\\
&\ge
\frac{49P_m}{30}
\left(\frac D{42}\right)^2
\\
&=
\boxed{
\frac{P_mD^2}{1080}
}.
\end{aligned}
```

Property #78 already gives the original-threshold upper bound

```math
\boxed{
\frac{T^2}{2W_-}
\le
\frac{P_m}{2m}
\left(
\frac D6+1
\right)^2.
}
```

## Finite Obstruction Theorem

Assume

```math
S
\ge
\frac{15QN_0}{2D-18}
```

and candidate #17's local-count threshold at filter `7`. If

```math
\boxed{
\frac{D^2}{1080}
>
\frac1{2m}
\left(
\frac D6+1
\right)^2
+
\frac{25}{18}
\left(
\frac25+\frac{3N_0}{5S}
\right)^2,
}
```

then the preceding bounds give

```math
\boxed{
\mathcal U_{\mathrm{cap}}
>
\frac{T^2}{2W_-}
+
\Gamma_{\mathrm{cap}}.
}
\qquad[\text{Q.E.D.}]
```

Thus property #69's relaxed certificate cannot hold under these explicit
finite hypotheses.

## Prime-Number-Theorem Scale

This subsection uses external classical prime-distribution results; it is not
a Stainless theorem.

Prime Mertens gives

```math
P_i
=
\prod_{5\le p<r_i}
\left(1-\frac2p\right)
\asymp
\frac1{(\log r_i)^2}.
```

Together with PNT and partial summation,

```math
S
=
\sum_{i<m}\frac1{P_i}
\asymp
Q\log Q,
\qquad
m\sim\frac Q{\log Q}.
```

Since `D` is asymptotic to `Q^2` and `N_0` is asymptotic to `D/6`, the finite
post-`5` compatibility condition holds for every sufficiently large `Q`.
Moreover,

```math
\frac{N_0}{S}
\asymp
\frac Q{\log Q}
\longrightarrow\infty.
```

The remaining filter-`5` violation is therefore positive, and its exact scale
is

```math
\boxed{
\Gamma_{\mathrm{cap}}
\sim
\frac{P_mN_0^2}{2S^2}.
}
```

Relative to the filter-`7` envelope floor,

```math
\frac{
T^2/(2W_-)
}{
P_mD^2/1080
}
\longrightarrow0,
\qquad
\frac{
\Gamma_{\mathrm{cap}}
}{
P_mD^2/1080
}
\longrightarrow0.
```

Therefore, under full candidate #17,

```math
\boxed{
\mathcal U_{\mathrm{cap}}
>
\frac{T^2}{2W_-}
+
\Gamma_{\mathrm{cap}}
}
```

for every sufficiently large future head. The capacity stability gap is real,
but it cannot rescue the separate capacity envelope on an unbounded family.

## Boundary

This is a method obstruction, not a refutation of candidate #17 or candidate
#24. Candidate #17 would already imply survival through its close-pair
capacity theorem. The result says that translating its filter-`7` density
into property #70's separately maximized energy envelope loses much more than
property #69's stability gap can restore.

The result does not address an upper bound for the actual `E_b` that is
strictly smaller than `U_cap`. In particular, localized residue correlations
or another genuinely joint cross-layer inequality remain possible.

No empirical evidence is used.

## Related

- [Harmful Capacity Separates the Energy Minimizer](harmful-capacity-separates-energy-minimizer.md)
- [Sharp Harmful-Capacity Excess Envelope](sharp-harmful-capacity-excess-envelope.md)
- [Seven-Layer Density Floor Maximizes Capacity Width](seven-layer-density-floor-maximizes-capacity-width.md)
- [Every Fixed Native Cut Fails the Original Threshold](every-fixed-native-cut-fails-original-threshold.md)
- [Candidate #17: Seven-Layer Capacity Floor](../../candidates/seven-layer-capacity-floor.md)
- [Candidate #24: Weighted Harmful-Excess Quadratic Survival](../../candidates/weighted-harmful-excess-quadratic-survival.md)
