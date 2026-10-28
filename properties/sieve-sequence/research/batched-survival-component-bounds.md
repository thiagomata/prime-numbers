# Component Bounds for Batched Survival

**Status:** Mathematical proofs of the component bounds stated below.
No general induction closure, new empirical sweep, historical novelty, or
Stainless verification is claimed.

## Setup and Existing Inputs

Let p>=5 be prime and s its next prime. Let q>=s and t>=q be prime
destinations. The existing [transport proof](batched-survival-propagation-check-2026-10-27.md)
defines the cubic lower bound and its exact transition:

```math
L(s,t)=L(p,q)+A+N-R-J,
\qquad A\ge0,\quad J\ge0.
```

A is the improvement from advancing the starting filter at fixed q; N and R
are signed contributions from the new and lost regions; J is the additional
shared-region penalty. The inequality A>=0 is an established input, not a new
result of this note.

For destination u>=s, define

```math
\begin{aligned}
M_s&=\prod_{r<s,\ r\ \mathrm{prime}}r,\\
W_u&=\{a\in\mathbb Z:u\le a\le u^2-3\},\\
\mathcal A_{s,u}&=\{a\in W_u:\gcd(a(a+2),M_s)=1\},\\
h_u(a)&=|\{r:s\le r<u,\ r\ \mathrm{prime},\ r\mid a(a+2)\}|,\\
w(h)&=1-h+\binom h2-\binom h3.
\end{aligned}
```

Binomial coefficients with nonnegative upper index smaller than the lower
index are zero. Then w(0)=1 and w(h)=-binomial(h-1,3)<=0 for h>=1.
In particular w(h)<=1 for every nonnegative integer h. The lost contribution is

```math
R=\sum_{a\in\mathcal A_{s,q}\setminus\mathcal A_{s,t}}w(h_q(a)).
```

No nonnegativity of R is assumed.

## 1. Finite Upper Bound on the Lost-Region Cost

The old and new candidates use the same installed filters below s. A candidate
can therefore leave their intersection only because its start leaves the window.
Since t>=q, the lost starts lie in the integer interval

```math
[q,\min(t-1,q^2-3)],
\qquad
\ell=\min(t-q,q^2-q-2).
```

The interval has exactly ell integer positions, with zero positions when t=q.
Every accepted pair start is 5 modulo6: filters2 and3 are installed, so among
the residues modulo6 only5 allows both a and a+2 to avoid those filters.

Any ell consecutive integers contain at most ceil(ell/6) members of one fixed
residue class modulo6. Each candidate weight is at most1. Consequently,

```math
\begin{aligned}
R
&\le|\mathcal A_{s,q}\setminus\mathcal A_{s,t}|\\
&\le|\{a\in[q,\min(t-1,q^2-3)]:a\equiv5\pmod6\}|\\
&\le\left\lceil\frac\ell6\right\rceil
=:R_{\mathrm{cap}}.
\end{aligned}
```

Thus the proved bound is

```math
\boxed{R\le R_{\mathrm{cap}}
       =\left\lceil\frac{\min(t-q,q^2-q-2)}6\right\rceil.}
```

This holds for every allowed p,q,s,t, without an eventual threshold or a local
primality assumption. Negative weights can only reduce R, so the bound remains
valid when R itself is negative. The estimate deliberately ignores further
old-prime filtering and can be sharpened using actual old residues.

## 2. Lost-Region Budget Is Eventually Small Relative to the Density Main Term

Now specialize to q the first prime above p squared and t the first prime
above s squared. Bertrand gives s<2p and t<2s^2<8p^2. Hence

```math
0\le R_{\mathrm{cap}}
\le\frac{t-q}{6}+1
<\frac43p^2+1.
```

This bounds the possible positive cost of R by O(p squared). It is not an
absolute-value bound on signed R.

Compare this budget with the explicit main term

```math
F(p,q)=H_q\delta_p B_3(p,q),
\qquad H_q=q^2-q-2.
```

The [analytical main-term proof](batched-survival-analytic-main-and-error.md)
establishes B_3>=1/16-3/(4p) when the batch reciprocal load is at most3/2,
and proves that this condition holds eventually under the square rule.
Consequently B_3>=1/32 for all sufficiently large p: p>=24 suffices for
the numerical inequality once the load condition holds.

For completeness, the complete-period pair density has an unconditional
product estimate. Define

```math
P(p)=\prod_{r<p,\ r\ \mathrm{prime}}\left(1-\frac1r\right),
\qquad
C_2(p)=\prod_{3\le r<p,\ r\ \mathrm{prime}}
            \left(1-\frac1{(r-1)^2}\right).
```

Factoring each odd-prime term gives

```math
\begin{aligned}
1-\frac2r
 &=\left(1-\frac1r\right)^2
   \left(1-\frac1{(r-1)^2}\right),\\
\delta_p
 &=\frac12\prod_{3\le r<p}\left(1-\frac2r\right)
 =2C_2(p)P(p)^2.
\end{aligned}
```

All products are over primes. The positive factors in C_2(p) converge to a
positive limit because the sum of their deficits is bounded by the convergent
series sum over n>=2 of 1/n squared. Mertens' product theorem gives
P(p) asymptotic to a positive constant divided by log(p); see Paul Pollack,
[*Not Always Buried Deep*, Theorem3.15, printed p.97](https://www.pollack-math.net/NABDofficial.pdf#page=110).
Thus there are constants c_1,c_2>0 such that, eventually,

```math
\frac{c_1}{\log^2p}\le\delta_p\le\frac{c_2}{\log^2p}.
```

Bertrand also gives p^2<q<2p^2, so H_q is bounded above and below by positive
constant multiples of p to the fourth power. The positive lower bound on B_3
therefore implies, for some c>0 and all sufficiently large prime heads,

```math
F(p,q)\ge c\frac{p^4}{\log^2p}.
```

Combining the estimates proves

```math
\boxed{
\frac{R_{\mathrm{cap}}}{F(p,q)}
=O\!\left(\frac{\log^2p}{p^2}\right)
\longrightarrow0.
}
```

Equivalently, for any epsilon>0 there is a threshold after which the upper
lost-region budget is at most epsilon times F. The onset is not made
numerically explicit here. This is a theorem about the defined density main
term. No lower bound for actual L(p,q) is substituted or assumed, and no
conclusion about the size of |R| follows.

## 3. Constant Per-Pair Bound for the Shared-Region Penalty

Retain the square-rule destinations. Write

```math
\mathcal H=\mathcal A_{s,q}\cap\mathcal A_{s,t},
\qquad h=h_q(a),\qquad j=h_t(a)-h_q(a)
\quad(a\in\mathcal H).
```

Here h counts distinct old batch primes in [s,q), while j counts distinct
newly hitting primes in [q,t). The [shared-region proof](batched-survival-propagation-check-2026-10-27.md)
establishes j<=2 and shows that a pair with h=0 receives no new hits.
For h>=1 its added cubic penalty is

```math
\Delta(h,j)=w(h)-w(h+j)
=j\binom{h-1}2+\binom j2(h-1).
```

The old accepted endpoints have no prime divisor below s. The square rule
and Bertrand give, for every p>=5,

```math
q<2p^2<p^3<s^3,
\qquad
q^2<4p^4<p^5<s^5.
```

These inequalities place a finite budget on their distinct prime factors.
An integer smaller than s to the d-th power cannot contain d distinct prime
factors all at least s, since their product would already be at least s^d.
Repeated prime factors do not increase h.

### Exactly One Newly Hitting Prime

Suppose j=1, and let r>=q be the new prime dividing one endpoint n. Since
n<q^2, write n=r*u with u<q<s^3. Every old batch prime dividing n must divide
u, because r is not an old batch prime. At most two such primes divide u.
The opposite endpoint is smaller than q^2<s^5 and therefore has at most four
distinct old prime divisors. Consequently

```math
h\le2+4=6,
\qquad
\Delta(h,1)=\binom{h-1}2\le\binom52=10.
```

### Exactly Two Newly Hitting Primes

Suppose j=2. No endpoint can contain two distinct new primes: both are at
least q and their product would be at least q squared. The two hits therefore
occur on opposite endpoints. Each endpoint has a cofactor smaller than q<s^3,
containing at most two distinct old batch primes. Thus

```math
h\le2+2=4,
\qquad
\Delta(h,2)=(h-1)^2\le9.
```

Define the affected populations precisely by

```math
K_i=|\{a\in\mathcal H:h_t(a)-h_q(a)=i\}|,
\qquad i=1,2.
```

Summing the per-pair bounds proves

```math
\boxed{0\le J\le10K_1+9K_2\le10(K_1+K_2).}
```

Unlike the eventual scale comparison, these constants hold at every square-rule
starting head p>=5. They bound the cost per affected candidate, not the number
of affected candidates. This subsection alone gives no upper estimate for
K_1 or K_2. The [filtered shot proof](batched-survival-filtered-shot-bound.md)
uses the square-destination ordering to improve these constants to3/1 and
derive an independent population bound.

## Proof Status and Remaining Terms

The existing A>=0 input, finite upper bound on R, its eventual smallness
relative to F, and constant per-pair bounds for J are established. Together
they give the concrete sufficient estimate

```math
L(s,t)\ge L(p,q)+A+N-R_{\mathrm{cap}}-10K_1-9K_2.
```

A subsequent [filtered shot proof](batched-survival-filtered-shot-bound.md)
establishes, with b counting primes in [q,t) and P counting primes in [s,q),

```math
K_1+2K_2\le bP,
\qquad J\le3K_1+K_2\le3bP,
\qquad \frac{J}{F(p,q)}\longrightarrow0.
```

Thus an independent hit-population bound is now proved. The
[new-region proof](batched-survival-new-region-bound.md) also establishes
|N|<=35(t^2-q^2)/6 and, using quantitative classical PNT, |N|/F->0.
Consequently B=|N|+R_cap+J satisfies B/F->0, and L_next>=L_current-B.
For every fixed eta>0, sufficiently late transitions with L_current>=eta F
have L_next>=eta F/2>0 in the old F units. The eventual positive-margin
premise and a reproduced or replenished reserve remain unproved.
The earlier component interface remains valid: if current structural information proves
N>=n, K_1<=k_1, K_2<=k_2, and

```math
A+n\ge R_{\mathrm{cap}}+10k_1+9k_2,
```

then a positive current margin is preserved. These additional estimates are
not assumed proved; the component bounds alone do not close the induction.

A later [block-reserve proof](batched-survival-block-reserve.md) bounds the
actual total budget across a growing finite block by o(F_start). Positivity
throughout that block is conditional on a fixed positive starting reserve;
its existence and renewal are not established by the cumulative estimate.
