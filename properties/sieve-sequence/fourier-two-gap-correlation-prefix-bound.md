# Fourier Bound For Two-Gap Correlation Prefixes

**Status:** Mathematically proved (finite Fourier theorem). Stainless
verification is not claimed here.

## Meaning

The quotient set of complete-period 2-gap starts is a CRT product set: at each
installed prime `p>=5`, exactly two local index classes are forbidden. Its
Fourier transform therefore factors into explicit local coefficients.

This theorem computes the exact global fourth moment of that spectrum and uses
it to bound correlation discrepancy on a prefix of the quotient difference
period. The bound is strongest when the prefix is a substantial fraction of
the complete period.

## Setup

Use the quotient notation from the complete-period correlation theorem:

```math
n=M'
=
\prod_{\substack{p\in P\\p\ge5}}p,
\qquad
U\subseteq\mathbb Z/n\mathbb Z,
\qquad
G=|U|.
```

Let

```math
f(u)=\mathbf 1_U(u)
```

and define the cyclic correlation

```math
A(h)
=
\sum_{u\bmod n}f(u)f(u+h).
```

Let `X_n` be the additive character group of `Z/nZ`. For `chi in X_n`, define

```math
\widehat f(\chi)
=
\sum_{u\bmod n}
f(u)\overline{\chi(u)}.
```

## Fourier Formula For Correlation

Finite Fourier inversion gives

```math
\boxed{
A(h)
=
\frac1n
\sum_{\chi\in X_n}
|\widehat f(\chi)|^2\chi(h).
}
```

For the trivial character `1`,

```math
\widehat f(1)=G.
```

Therefore its contribution is the exact complete-period mean `G^2/n`.

## CRT Factorization

The Chinese remainder theorem identifies

```math
\mathbb Z/n\mathbb Z
\cong
\prod_{p\mid n}\mathbb Z/p\mathbb Z.
```

For each `p|n`, let

```math
U_p
=
\mathbb Z/p\mathbb Z
\setminus\{\alpha_p,\beta_p\},
```

where `alpha_p` and `beta_p` are the two index classes for which one endpoint
of `5+6u,7+6u` is divisible by `p`. They are distinct because `p>2`.

Then

```math
U\cong\prod_{p\mid n}U_p.
```

Every global character factors uniquely as

```math
\chi=\prod_{p\mid n}\chi_p,
```

and consequently

```math
\boxed{
\widehat f(\chi)
=
\prod_{p\mid n}
\widehat f_p(\chi_p).
}
```

## Exact Local Coefficients

For the trivial local character,

```math
\widehat f_p(1)=p-2.
```

For a nontrivial local character, the sum over all `p` residues is zero, so

```math
\widehat f_p(\chi_p)
=
-\overline{\chi_p(\alpha_p)}
-\overline{\chi_p(\beta_p)}.
```

Hence

```math
\boxed{
|\widehat f_p(\chi_p)|\le2
\qquad(\chi_p\ne1).
}
```

This gives the normalized product bound

```math
\frac{|\widehat f(\chi)|}{G}
\le
\prod_{\substack{p\mid n\\\chi_p\ne1}}
\frac2{p-2}.
```

## Exact Local Fourth Moment

Let

```math
\delta_p=\alpha_p-\beta_p\ne0\pmod p.
```

As the nontrivial characters range over the nonzero frequencies modulo `p`,
their values at `delta_p` range over the nontrivial `p`th roots. Thus

```math
|\widehat f_p(\chi_p)|^4
=
|1+\chi_p(\delta_p)|^4.
```

For `z` on the unit circle,

```math
|1+z|^4
=
6+4(z+z^{-1})+z^2+z^{-2}.
```

Summing over all `p` characters annihilates the nonconstant powers because
`p>=5`, giving

```math
\sum_{\chi_p}|1+\chi_p(\delta_p)|^4=6p.
```

The trivial character contributes `16`. Therefore

```math
\boxed{
\sum_{\chi_p\ne1}
|\widehat f_p(\chi_p)|^4
=
6p-16.
}
```

Including the trivial local coefficient,

```math
\sum_{\chi_p}
|\widehat f_p(\chi_p)|^4
=
(p-2)^4+6p-16.
```

## Exact Global Fourth Moment

CRT factorization and finite-product expansion give

```math
\begin{aligned}
\sum_{\chi\in X_n}
|\widehat f(\chi)|^4
&=
\prod_{p\mid n}
\left((p-2)^4+6p-16\right)\\
&=
G^4
\prod_{p\mid n}
\left(
1+\frac{6p-16}{(p-2)^4}
\right).
\end{aligned}
```

Define

```math
R_P
=
\prod_{p\mid n}
\left(
1+\frac{6p-16}{(p-2)^4}
\right)-1.
```

Subtracting the trivial global character yields

```math
\boxed{
\sum_{\chi\ne1}
|\widehat f(\chi)|^4
=
G^4R_P.
}
```

## Prefix Discrepancy

Let `r` be coprime to `n`, and let `0<=H<=n`. Define

```math
\mathcal E(H;r)
=
\sum_{h=1}^{H}A(rh)
-
\frac{H}{n}G^2.
```

For a character `chi`, write

```math
D_H(\chi;r)
=
\sum_{h=1}^{H}\chi(rh).
```

The trivial character supplies the subtracted mean, so Fourier inversion gives

```math
\mathcal E(H;r)
=
\frac1n
\sum_{\chi\ne1}
|\widehat f(\chi)|^2D_H(\chi;r).
```

Because multiplication by `r` permutes the character frequencies and
`H<=n`, character orthogonality gives

```math
\sum_{\chi\in X_n}|D_H(\chi;r)|^2=nH.
```

The trivial character contributes `H^2`; hence

```math
\sum_{\chi\ne1}|D_H(\chi;r)|^2=nH-H^2.
```

Cauchy--Schwarz now gives

```math
\begin{aligned}
|\mathcal E(H;r)|
&\le
\frac1n
\sqrt{
\sum_{\chi\ne1}|\widehat f(\chi)|^4
}
\sqrt{
\sum_{\chi\ne1}|D_H(\chi;r)|^2
}\\
&=
G^2
\sqrt{
R_P
\frac{H}{n}
\left(1-\frac{H}{n}\right)
}.
\end{aligned}
```

Therefore

```math
\boxed{
|\mathcal E(H;r)|
\le
G^2
\sqrt{
R_P
\frac{H}{n}
\left(1-\frac{H}{n}\right)
}.
}
\qquad[\text{Q.E.D.}]
```

At `H=n`, the right side is zero, recovering the exact complete-period
average.

## Comparison With The Elementary Bound

The complete-period property also gives

```math
|\mathcal E(H;r)|\le HG.
```

The best immediate combined estimate is

```math
\boxed{
|\mathcal E(H;r)|
\le
\min\left\{
HG,\;
G^2
\sqrt{
R_P
\frac{H}{n}
\left(1-\frac{H}{n}\right)
}
\right\}.
}
```

The Fourier term is effective when `H/n` is not too small. In the late
primorial regime, `H<<n`, and `G^2 sqrt(H/n)` may exceed `HG`. Thus the exact
fourth moment alone does not solve the short-prefix problem needed by
candidate #21.

## Conductor-Sensitive Bound

Because `n` is squarefree, every global character has a conductor

```math
q\mid n
```

equal to the product of the primes at which its local component is
nontrivial.

For a local prime `p`, Parseval gives

```math
\sum_{\chi_p}
|\widehat f_p(\chi_p)|^2
=
p|U_p|
=
p(p-2).
```

The trivial local character contributes `(p-2)^2`. Therefore

```math
\boxed{
\sum_{\chi_p\ne1}
|\widehat f_p(\chi_p)|^2
=
2(p-2).
}
```

Fix a squarefree divisor `q|n`. Summing over all global characters with exact
conductor `q` and using CRT factorization gives

```math
\begin{aligned}
\sum_{\operatorname{cond}(\chi)=q}
|\widehat f(\chi)|^2
&=
\prod_{p\nmid q}(p-2)^2
\prod_{p\mid q}2(p-2)\\
&=
G^2
\prod_{p\mid q}\frac2{p-2}.
\end{aligned}
```

Hence

```math
\boxed{
\sum_{\operatorname{cond}(\chi)=q}
|\widehat f(\chi)|^2
=
G^2
\prod_{p\mid q}\frac2{p-2}.
}
```

Every nontrivial character of conductor `q` has period `q`. Its sum over each
complete `q`-block vanishes, so

```math
|D_H(\chi;r)|
\le
\min(H,q),
```

where multiplication by `r` preserves the conductor because `gcd(r,n)=1`.

Grouping the Fourier discrepancy by exact conductor and applying the triangle
inequality gives

```math
\boxed{
|\mathcal E(H;r)|
\le
\frac{G^2}{n}
\sum_{\substack{q\mid n\\q>1}}
\min(H,q)
\prod_{p\mid q}\frac2{p-2}.
}
```

This bound retains both parts of the local tradeoff:

- characters supported on small primes can have relatively large
  coefficients, but their prefix sums stop growing after their small
  conductor;
- characters with large conductors pay a product of factors `2/(p-2)`.

The divisor weights have the exact total

```math
\sum_{q\mid n}
\prod_{p\mid q}\frac2{p-2}
=
\prod_{p\mid n}
\left(1+\frac2{p-2}\right)
=
\prod_{p\mid n}\frac{p}{p-2}
=
\frac nG.
```

Replacing every `min(H,q)` by `H` recovers the elementary nontrivial-spectrum
bound

```math
|\mathcal E(H;r)|
\le
H\left(G-\frac{G^2}{n}\right).
```

Thus conductor localization never worsens that triangle estimate and can
improve it when a significant part of the spectral mass has conductor below
`H`.

## Product Measure On Conductors

Define

```math
a(q)
=
\prod_{p\mid q}\frac2{p-2},
\qquad
Z=\sum_{q\mid n}a(q)=\frac nG.
```

Then

```math
\mu(q)=\frac{a(q)}Z
```

is a probability measure on the squarefree divisors of `n`. Because `a(q)` is
multiplicative over the prime choices, those choices are independent under
`mu`. For each `p|n`,

```math
\begin{aligned}
\Pr_\mu(p\mid q)
&=
\frac{2/(p-2)}{1+2/(p-2)}\\
&=
\frac2p.
\end{aligned}
```

Thus the conductor weights have an exact product-measure interpretation with
prime inclusion probability `2/p`.

For every `0<=sigma<=1`,

```math
\min(H,q)
\le
H^{1-\sigma}q^\sigma.
```

Consequently, the conductor-sensitive bound also gives the factorized family

```math
\boxed{
|\mathcal E(H;r)|
\le
\frac{G^2}{n}
H^{1-\sigma}
\left[
\prod_{p\mid n}
\left(
1+\frac{2p^\sigma}{p-2}
\right)-1
\right].
}
```

This exposes the tradeoff between prefix length and conductor moments without
assuming a probabilistic model for the sieve itself.

## Conductor-Fourth Hybrid Bound

For exact conductor `q`, CRT factorization of the fourth moment gives

```math
\boxed{
\sum_{\operatorname{cond}(\chi)=q}
|\widehat f(\chi)|^4
=
G^4
\prod_{p\mid q}
\frac{6p-16}{(p-2)^4}.
}
```

Let

```math
T_q(H;r)
=
\sum_{\operatorname{cond}(\chi)=q}
|D_H(\chi;r)|^2.
```

Every such character factors through `Z/qZ`. After complete `q`-blocks cancel,
character orthogonality over all characters modulo `q` gives

```math
\boxed{
T_q(H;r)
\le
q\min(H,q).
}
```

Apply Cauchy--Schwarz separately inside each exact-conductor block:

```math
\begin{aligned}
|\mathcal E(H;r)|
&\le
\frac1n
\sum_{\substack{q\mid n\\q>1}}
\sqrt{
\sum_{\operatorname{cond}(\chi)=q}
|\widehat f(\chi)|^4
}
\sqrt{T_q(H;r)}\\
&\le
\frac{G^2}{n}
\sum_{\substack{q\mid n\\q>1}}
\sqrt{q\min(H,q)}
\prod_{p\mid q}
\frac{\sqrt{6p-16}}{(p-2)^2}.
\end{aligned}
```

Using `min(H,q)<=H` makes the divisor sum factor:

```math
\boxed{
|\mathcal E(H;r)|
\le
\frac{G^2\sqrt H}{n}
\left[
\prod_{p\mid n}
\left(
1+
\frac{\sqrt{p(6p-16)}}{(p-2)^2}
\right)-1
\right].
}
```

This hybrid uses both forms of localization:

- fourth-moment decay of the coefficient mass at conductor `q`;
- the period-sensitive prefix norm of conductor-`q` characters.

It can be substantially sharper than the global fourth-moment bound when
`H<<n`.

## Limitation

The conductor-sensitive bound is explicit, but it has not yet been shown to
fit candidate #21's weighted collision budget. That requires a uniform
estimate for the truncated divisor sum

```math
\sum_{\substack{q\mid n\\q>1}}
\min(H,q)
\prod_{p\mid q}\frac2{p-2}
```

in the regime where both `n` and the relevant prefix length vary with the
conditioned layer.

All bounds in this file still use the complete cyclic origin average inside
`A(h)`. A collision count in a square window restricts the starting index as
well as the difference. Applying these results locally therefore requires a
two-dimensional rectangle-discrepancy theorem; the one-dimensional
correlation-prefix estimate is only one marginal of that problem.

## Related

- [Complete-period two-gap pair-correlation average](
  complete-period-two-gap-pair-correlation-average.md
  )
- [Two-gap pair local factor by separation](
  two-gap-pair-local-factor-by-separation.md
  )
- [Cumulative weighted collision budget](
  ../../candidates/cumulative-weighted-collision-budget.md
  )
