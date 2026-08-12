# Relaxed Almost-Prime Bilinear Remainder Has A Character Obstruction

**Status:** Mathematically proved exact decomposition and complete-wheel
obstruction. Stainless verification is not claimed.

## Meaning

For candidate #25, factoring the tested integer as `mn` does create a genuine
bilinear family. After the installed wheel is removed and the relaxed
condition is centered by its scalar local density, the remainder is exactly a
sum of inverse-residue tests

```math
n\equiv-2m^{-1}\pmod d.
```

Character orthogonality diagonalizes those tests into nonprincipal products
`chi(m)chi(n)`. This identifies the precise Type-II object rather than merely
calling an unsigned count bilinear.

It also exposes a local obstruction. Because the relaxed sieve includes the
prime `3`, quadratic-character coefficients modulo `3` have one constant sign
on every allowed product. On a complete reduced wheel their correlation with
the scalar-centered weight has the full size of the survivor count. Thus a
naive arbitrary-coefficient Type-II theorem centered only by one scalar
density is false on the complete local model. Candidate #25 itself is not
refuted; a successful analytic route must first absorb the local character
structure into its comparison model or coefficient setup.

## Setup

Let `W` and `Z` be squarefree products of primes satisfying

```math
2\mid Z,
\qquad
Z\mid W.
```

Put

```math
Z_{\mathrm{odd}}=\frac Z2
```

and define the relaxed weight

```math
a(x)
=
\mathbf1_{\gcd(x,W)=1}
\mathbf1_{\gcd(x+2,Z)=1}.
```

Conditional on `gcd(x,W)=1`, its complete-wheel density is

```math
\vartheta_Z
=
\prod_{p\mid Z_{\mathrm{odd}}}
\left(1-\frac1{p-1}\right).
```

Use the scalar wheel comparison

```math
b(x)=\vartheta_Z\mathbf1_{\gcd(x,W)=1}
```

and centered weight

```math
w(x)=a(x)-b(x).
```

## Exact Centered Möbius Decomposition

First suppose `gcd(mn,W)=1`. This is equivalent to

```math
\gcd(m,W)=\gcd(n,W)=1.
```

In particular `m` and `n` are odd, so `mn+2` is odd. The even divisors in the
Möbius coprimality identity contribute zero, giving

```math
\mathbf1_{\gcd(mn+2,Z)=1}
=
\sum_{d\mid Z_{\mathrm{odd}}}
\mu(d)\mathbf1_{mn\equiv-2\ (\mathrm{mod}\ d)}.
```

On the other hand, expanding the Euler product for the conditional density
gives

```math
\vartheta_Z
=
\sum_{d\mid Z_{\mathrm{odd}}}\frac{\mu(d)}{\varphi(d)}.
```

Subtracting these identities, and restoring the wheel conditions, proves the
pointwise formula

```math
\boxed{
w(mn)
=
\mathbf1_{\gcd(m,W)=1}
\mathbf1_{\gcd(n,W)=1}
\sum_{d\mid Z_{\mathrm{odd}}}
\mu(d)
\left(
\mathbf1_{mn\equiv-2\ (\mathrm{mod}\ d)}
-\frac1{\varphi(d)}
\right).
}
```

The `d=1` bracket is zero. Since `m` is a unit modulo every remaining `d`,

```math
mn\equiv-2\pmod d
\quad\Longleftrightarrow\quad
n\equiv-2m^{-1}\pmod d.
```

This is the exact inverse-residue bilinear remainder.

## Exact Character Form

For odd `d|Z_odd`, both `mn` and `-2` belong to the reduced residue group
modulo `d`. Character orthogonality gives

```math
\mathbf1_{mn\equiv-2\ (\mathrm{mod}\ d)}
=
\frac1{\varphi(d)}
\sum_{\chi\ (\mathrm{mod}\ d)}
\chi(mn)\overline{\chi(-2)}.
```

The principal character contributes exactly `1/phi(d)`. Hence

```math
\boxed{
\mathbf1_{mn\equiv-2\ (\mathrm{mod}\ d)}
-\frac1{\varphi(d)}
=
\frac1{\varphi(d)}
\sum_{\substack{\chi\ (\mathrm{mod}\ d)\\\chi\ne\chi_0}}
\overline{\chi(-2)}\chi(m)\chi(n).
}
```

For any finite factor domain `D` and arbitrary coefficients `xi_m`, `kappa_n`,
the Type-II sum therefore has the exact form

```math
\begin{aligned}
\sum_{(m,n)\in D}\xi_m\kappa_nw(mn)
&=
\sum_{d\mid Z_{\mathrm{odd}}}
\frac{\mu(d)}{\varphi(d)}
\sum_{\substack{\chi\ (\mathrm{mod}\ d)\\\chi\ne\chi_0}}
\overline{\chi(-2)}\\
&\qquad\cdot
\sum_{\substack{(m,n)\in D\\
                  \gcd(m,W)=\gcd(n,W)=1}}
\xi_m\kappa_n\chi(m)\chi(n).
\end{aligned}
```

The geometry of `D`, such as `X/2<mn<=X`, still couples the two variables.
The formula identifies the modes but does not estimate them.

## An Individual Mode Can Be Selected Exactly

Fix an odd `d>=3` and a nonprincipal character `chi modulo d`. On the complete
reduced grid `G_d x G_d`, put

```math
f_d(m,n)
=
\mathbf1_{mn\equiv-2\ (\mathrm{mod}\ d)}
-\frac1{\varphi(d)}.
```

Choose the unit-modulus coefficients

```math
\xi_m=\overline{\chi(m)},
\qquad
\kappa_n=\overline{\chi(n)}.
```

The character formula and orthogonality give

```math
\begin{aligned}
\sum_{m,n\in G_d}\xi_m\kappa_nf_d(m,n)
&=
\frac{\overline{\chi(-2)}}{\varphi(d)}
\left(\sum_{m\in G_d}|\chi(m)|^2\right)
\left(\sum_{n\in G_d}|\chi(n)|^2\right)\\
&=
\boxed{\varphi(d)\overline{\chi(-2)}}.
\end{aligned}
```

Its absolute value is `phi(d)`, exactly the number of pairs on the congruence
graph. Thus neither formal orthogonality nor a termwise triangle inequality
can bound the arbitrary-coefficient family nontrivially.

## Full Scalar-Comparison Obstruction Modulo Three

Assume additionally `3|Z`, as holds for candidate #25 once `Q` is large. Let
`chi_3` be the nonprincipal real character modulo `3`, and let

```math
G_W=(\mathbb Z/W\mathbb Z)^\times.
```

Choose

```math
\xi_m=\chi_3(m),
\qquad
\kappa_n=\chi_3(n)
```

on `G_W`. If `a(mn)=1`, the relaxed condition at `3` says

```math
mn\not\equiv1\pmod3.
```

Because `m` and `n` are units modulo `3`, necessarily

```math
mn\equiv2\pmod3,
\qquad
\xi_m\kappa_n=\chi_3(mn)=-1.
```

Therefore

```math
\sum_{m,n\in G_W}\xi_m\kappa_na(mn)
=
-\sum_{m,n\in G_W}a(mn).
```

CRT gives equal numbers of reduced residues in the two unit classes modulo
`3`, so

```math
\sum_{m\in G_W}\chi_3(m)=0.
```

Consequently the scalar comparison has zero correlation:

```math
\sum_{m,n\in G_W}\xi_m\kappa_nb(mn)
=
\vartheta_Z
\left(\sum_{m\in G_W}\chi_3(m)\right)
\left(\sum_{n\in G_W}\chi_3(n)\right)
=0.
```

Subtracting yields the exact obstruction

```math
\boxed{
\left|
\sum_{m,n\in G_W}\xi_m\kappa_nw(mn)
\right|
=
\sum_{m,n\in G_W}a(mn).
}
\qquad[\text{Q.E.D.}]
```

The coefficients are bounded by one, yet the correlation equals the entire
relaxed survivor count. Scalar-density centering therefore leaves a complete
local character obstruction.

## Consequence For Candidate #25

This theorem does not show that the short hyperbolic Type-II sum in candidate
#25 is always large; a short domain is not a complete reduced wheel. It does
show that the proposed arbitrary-coefficient estimate cannot be obtained by
treating the scalar-centered periodic weight as locally pseudorandom.

A viable next formulation must do at least one of the following:

1. place all fixed local character factors into the comparison sequence;
2. formulate the coefficient test after a local `W`-trick that removes those
   modes;
3. restrict the coefficient family in a way justified by the combinatorial
   identity used for almost-prime detection; or
4. prove cancellation only after the signed sum over `d` and over the actual
   short hyperbolic domain, without taking absolute values mode by mode.

The remaining analytic question is which locally adapted formulation still
implies positivity of the original relaxed weight.

## Related

- [Relaxed Almost-Prime Divisor Local Factor](relaxed-almost-prime-divisor-local-factor.md)
- [Chen-Type Almost-Prime Survivor](../../candidates/chen-type-almost-prime-survivor.md)
- [Recent Prime-Producing Sieves Deep-Dive](research/recent-prime-producing-sieves-deep-dive.md)
