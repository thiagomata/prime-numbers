# Pre-Final-Filter Twin/Semiprime Decomposition

**Short name:** Pre-Final Twin Decomposition.

**Status:** The finite decomposition is mathematically proved. The benchmark
calibration is conditional on the Hardy–Littlewood twin-prime asymptotic.
Neither local survival nor Stainless verification is claimed.

## Meaning

Immediately before the last filter for a square-safe window, the accepted
2-gap population is already almost the actual twin-prime population. Every
additional pair consists of one prime and one semiprime divisible by the
incoming filter. Thus a large lower bound for this prefilter population already
contains a large lower bound for twin primes. This makes explicit what a
local-abundance argument must accomplish.

## Setup

Let p<q be consecutive primes, p>=5, with every prime below p installed.
Use complete pairs with starts in

```math
W_q=\{x\in\mathbb Z:q\le x,\ x+2<q^2\}.
```

Let L count prefilter 2-gap starts in W_q, T count genuine twin-prime starts
there, and D count prefilter pairs destroyed by installing p. Define

```math
K=\left\lfloor\frac{q^2-1}{p}\right\rfloor,
\qquad
A=\pi(K)-\pi(p-1).
```

By [Accepted Local Strikes](exact-accepted-local-filter-strikes.md), A counts
accepted strike values, not necessarily harmful strikes.

## Exact Decomposition

The prefilter pairs partition into genuine twins and pairs with exactly one
semiprime endpoint. Consequently,

```math
\begin{aligned}
L&=T+D,\\
0&\le D\le A\le3p,\\
U&:=A-D\ge0,\\
L-A&=T-U.
\end{aligned}
```

Here U counts accepted strikes that destroy no pair in this window. Therefore
the sufficient surplus L>A holds exactly when T>U. It is stronger than the
mere existence condition T>0; an implication in the reverse direction is not
provided by this identity.

### Proof

Take an accepted composite n with q<=n<q². Its least prime factor s satisfies
s>=p because all smaller primes have been installed, and s<=sqrt(n)<q.
Consecutiveness gives s=p. Write n=pr. If r were composite, its prime factors
would also be at least p, and Bertrand's postulate would give

```math
n\ge p^3>4p^2>q^2,
```

a contradiction. Thus r is prime and p<=r<=K. Conversely each such pr is
accepted before installing p and is then removed.

Both endpoints of an accepted 2-gap cannot be composite: each would be
divisible by p, forcing p to divide their difference 2. Thus each pair is
either two primes, which survive, or one prime and one pr, which is destroyed.
Accepted odd endpoints two apart are consecutive because the intervening
integer is even. This proves L=T+D.

By [2-Gap Isolation](two-gap-isolation-after-filter-three.md), each accepted
strike destroys at most one pair, so D<=A. With d=q-p, the accepted-strike
bound gives

```math
\begin{aligned}
A&\le2d+\left\lceil\frac{d^2}{p}\right\rceil,\\
0<d<p&\ \Longrightarrow\ A\le3p.
\end{aligned}
```

The identities involving U follow by substitution. In particular,

```math
0\le L-T\le3p.
\qquad[\text{Q.E.D.}]
```

## Exact Arithmetic Form of Destruction

Define the character on integers coprime to 3 by

```math
\chi_3(v)=
\begin{cases}
1,&v\equiv1\pmod3,\\
-1,&v\equiv2\pmod3.
\end{cases}
```

The same decomposition identifies the destroyed pairs exactly:

```math
D=
\sum_{\substack{p\le r\le K\\r\ \mathrm{prime}}}
\mathbf1_{\mathrm{prime}}\!\left(pr-2\chi_3(pr)\right).
```

For each strike v=pr, one neighbor v±2 is divisible by 3 and exceeds 3. The
displayed neighbor is the other one. If it is prime, it forms a prefilter pair
with v; if the pair is prefilter-accepted, the preceding classification forces
that neighbor to be prime, since it is not divisible by p.

The lower boundary is automatic: v-2>=p²-2>2p>q. Since v and q² are odd and
v<q², the upper neighbor satisfies v+2<=q². The only possible excluded value
is q² itself, whose prime indicator is zero. Finally two distinct strikes
cannot represent one pair, as p cannot divide both endpoints. This proves the
formula including its endpoint conventions.

## Conditional Calibration of the Period-Density Benchmark

This section assumes the Hardy–Littlewood twin-prime asymptotic; it does not
prove it. Define C₂ as the product with value approximately 0.66016, and let
Π₂(X) count prime starts t<=X for which t+2 is prime. The assumed asymptotic is

```math
C_2=\prod_{\ell>2\ \mathrm{prime}}
\left(1-\frac1{(\ell-1)^2}\right),
\qquad
\Pi_2(X)\sim2C_2\frac{X}{\log^2X}.
```

This conjectural normalization is described in Tao's
[Structure and randomness in the prime numbers](https://terrytao.wordpress.com/wp-content/uploads/2009/09/primes_paper.pdf),
Section 4 (that text calls 2C₂ the twin-prime constant).

The exact endpoint convention gives

```math
T=\Pi_2(q^2-3)-\Pi_2(q-1).
```

The lower-cut term is O(q). Bertrand gives p<q<2p, hence log(q)/log(p) tends
to 1. Conditional on the stated asymptotic, the finite decomposition yields

```math
\begin{aligned}
T&\sim\frac{C_2}{2}\frac{q^2}{\log^2p},\\
L&=T+O(p)
\sim\frac{C_2}{2}\frac{q^2}{\log^2p}.
\end{aligned}
```

The project's complete-period benchmark is

```math
\delta_p=\frac12\prod_{3\le\ell<p\ \mathrm{prime}}
\left(1-\frac2\ell\right),
\qquad
\widehat L=(q^2-q)\delta_p.
```

Mertens' product estimate gives δ_p~2C₂ exp(-2γ)/log²p, with γ the
Euler–Mascheroni constant; see equation (8) in Tao's
[sieve theory notes](https://terrytao.wordpress.com/2015/01/21/254a-notes-4-some-sieve-theory/).
It follows, still conditional on Hardy–Littlewood, that

```math
\boxed{\frac{L}{\widehat L}\longrightarrow
\frac{e^{2\gamma}}4\approx0.793.}
```

Thus the hypothesis L/Ĺ→1 would predict a different twin asymptotic. This is
a conditional incompatibility, not an unconditional disproof of that
hypothesis. The existing local-surplus candidate does not require convergence
to 1 and is not refuted by this calibration. Using the strict-start benchmark
(q²-q-2)δ_p changes none of these limits.

## Consequence for the Research Target

Exact matching to the period-density benchmark is unnecessary. Any fixed
c>0 and a proof of L>=cĹ at infinitely many transitions would suffice, since
Ĺ/p tends to infinity and A<=3p. But L=T+O(p) shows that this premise already
produces a twin-prime lower bound of order q²/log²p along those transitions.
It is much more quantitative than bare nonextinction.

Positive T at infinitely many heads is equivalent to infinitely many twins:
unbounded heads require unbounded twin starts, and a twin start t itself can
be chosen as head q=t. Requiring positive T at every sufficiently large head
adds a uniform square-window placement requirement. No equivalence between
twin infinitude and the stronger surplus L>A is claimed.

The contribution here is the arithmetic classification and conditional
benchmark calibration. Neither bounds T from below unconditionally. A proof
of local safety still needs new information ensuring actual prime-pair
existence; refining final-filter capacity alone does not supply it.
