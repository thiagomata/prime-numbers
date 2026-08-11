# Relaxed Almost-Prime Production in Sieve Sequences

*Local Factors, Bilinear Obstructions, And The Prime-Progression Boundary*

**Status:** Review draft — mathematical proofs included; Stainless
verification pending for the new properties.

**Author:** Mata, T. H.
Independent Researcher

## Abstract

The square-safe Sieve Sequence certifies that every survivor
$p\in[Q,Q^2)$ is prime. Requiring $p+2$ to survive the same filters would ask
for a twin-prime pair. This article studies a deliberately weaker target:
require $p+2$ to avoid primes below $z=Q^{2\alpha}$ for some fixed
$\alpha>1/3$. Positivity then implies that $p+2$ has at most two prime
factors for all sufficiently large $Q$.

The article proves three exact algebraic results for this relaxed weight. The
one-divisor count has an explicit local factor and one periodic boundary
remainder. The natural pre-sieved divisor remainder is exactly a discrepancy
of primes in the progression $-2$ modulo $d$. Finally, the scalar-centered
final weight decomposes into nonprincipal character products
$\chi(m)\chi(n)$. A quadratic character modulo $3$ correlates with the full
relaxed survivor count on the complete reduced wheel, refuting the shortcut
that scalar-density centering creates arbitrary-coefficient Type-II
orthogonality.

These results do not prove positivity of the relaxed weight. They identify its
correct Type-I comparison, refute one over-strong Type-II formulation, and
isolate the remaining need for an averaged prime-progression theorem followed
by a locally adapted bilinear estimate.

## 1. Introduction

The twin-prime program requires both endpoints to survive every missing prime
filter below a future head. This article investigates a distinct and weaker
program: the first endpoint is square-safe prime, while the shifted endpoint
is required only to avoid primes below a smaller threshold. The conclusion is
a prime plus an integer with at most two prime factors, not a twin-prime pair.

The proof develops the following results in dependency order:

1. relaxed-weight positivity implies prime-plus-$P_2$ production — §3;
2. the exact divisor local factor and periodic remainder — §4;
3. the exact shifted-divisor prime-progression discrepancy — §5;
4. the exact bilinear character decomposition — §6; and
5. the refuted scalar-density Type-II shortcut — §7.

Sections 8--9 state the remaining analytic program and the exact claim
boundary. No complete-period identity is substituted for an averaged
short-interval distribution theorem.

### 1.1 Scope And Evidence Status

Let $Q$ be a prime head and put

```math
X=Q^2,
\qquad
W=P(Q)=\prod_{p\lt Q}p.
```

The installed-wheel survivors in the square-safe interval are

```math
S_Q
=
\{n\in[Q,Q^2):\gcd(n,W)=1\}.
```

Every $n\in S_Q$ is prime: if it were composite and smaller than $Q^2$, it
would have a prime divisor smaller than $Q$.

This article does not prove a new existence theorem. Classical Chen theory
already supplies infinitely many primes $p$ for which $p+2$ has at most two
prime factors. The project-specific question is whether positivity can be
derived from the Sieve Sequence's own relaxed weights.

The implication in §3 and the properties from Divisor Local Factor through Cofactor Progression Discrepancy in §§4--6 are mathematically
proved. Their Scala/Stainless
representations are pending and are identified explicitly. No statement in
this draft should be described as formally verified.

The maintained Sieve Sequence construction is Stainless-verified in the
companion chapter article. This draft uses that construction as an input but
does not call its new number-theoretic properties verified. Every property
section states its population, quantifier scope, proof status, and canonical
source.

## 2. Preliminaries And The Relaxed Candidate Weight

Choose a fixed exponent

```math
\frac13\lt\alpha\lt\frac12
```

and define

```math
z=X^\alpha=Q^{2\alpha},
\qquad
Z=P(z).
```

The upper restriction $\alpha\lt 1/2$ is useful because it gives $z\lt Q$, hence
$Z\mid W$. Define

```math
a_Q(n)
=
\mathbf1_{\gcd(n,W)=1}
\mathbf1_{\gcd(n+2,Z)=1}.
```

The candidate asks whether, for some fixed $\alpha>1/3$ and infinitely many
heads $Q$,

```math
\sum_{Q\le n\lt Q^2}a_Q(n)>0.
```

This is weaker than twin-prime positivity because $n+2$ is not required to
survive every prime below $Q$.

## 3. Relaxed Positivity Implies Prime-Plus-$P_2$ Production

**Population:** Integers in one future head's square-safe interval weighted by
$a_Q$.

**Scope and quantifier:** Every fixed exponent
$1/3\lt\alpha\lt1/2$ and every sufficiently large prime future head $Q$.

**Status:** **Mathematically proved, Stainless verification pending.**
The implication is proved; positivity for infinitely many heads remains open.

The relaxed weight keeps enough filtering to certify the first endpoint as
prime and to bound the factorization depth of the second. It does not certify
the second endpoint as prime.

Suppose $a_Q(n)=1$ for some $Q\le n\lt Q^2$. By the installed-wheel factor,
$\gcd(n,W)=1$, so square-safe certification proves that $n$ is prime. By the
relaxed factor, $\gcd(n+2,P(z))=1$, so every prime factor of $n+2$ is at least
$z=X^\alpha$.

Because $3\alpha>1$, there is $X_0(\alpha)$ such that
$X^{3\alpha}>X+1$ whenever $X\ge X_0(\alpha)$. If $n+2$ had at least three
prime factors counted with multiplicity, then

```math
\begin{aligned}
\Omega(n+2)\ge3
&\Longrightarrow n+2\ge z^3
&&[\text{Three Factor Lower Bound}]\\
&=X^{3\alpha}
&&[\text{By Definition Of }z]\\
&>X+1
&&[\text{Since }3\alpha>1\text{ And }X\ge X_0(\alpha)].
\end{aligned}
```

On the other hand,

```math
\begin{aligned}
n\lt Q^2=X
&\Longrightarrow n\le X-1
&&[\text{Integer Bound}]\\
&\Longrightarrow n+2\le X+1.
&&[\text{Add }2]
\end{aligned}
```

The inequalities contradict each other. Therefore

```math
\boxed{
a_Q(n)=1
\Longrightarrow
n\text{ is prime and }\Omega(n+2)\le2.
}
\qquad[\text{Q.E.D.}]
```

Consequently,

```math
\sum_{Q\le n\lt Q^2}a_Q(n)>0
\Longrightarrow
\exists n:\ n\text{ prime and }\Omega(n+2)\le2.
```

This is prime-plus-almost-prime production. It is neither a twin-prime
certificate nor a proof that the relaxed sum is positive for any unbounded
family of heads.

### Stainless And Source Evidence For The Relaxed Implication

The project-specific candidate and this conditional proof are maintained in
[Chen-Type Almost-Prime Survivor](
../../candidates/chen-type-almost-prime-survivor.md). The first-endpoint input
is [Safe-Window 2-Gaps Certify Twin Primes](
../../properties/sieve-sequence/safe-window-two-gaps-certify-twin-primes.md).
No `.holds` theorem currently encodes the factor-count argument; Stainless
verification is pending.

## 4. Exact Divisor Local Factor And Boundary Remainder

**Population:** Relaxed-weight integers in one arbitrary interval that are
also divisible by one fixed integer $m$.

**Scope and quantifier:** Every pair of squarefree prime wheels $W,Z$ with
$2\mid W$, every integer interval $[L,U)$ with $L\lt U$, and every $m\ge1$.

**Status:** **Mathematically proved, Stainless verification pending.**

Before studying divisor averages, the comparison density must account for how
the tested divisor meets the two wheels. Let $W$ and $Z$ be squarefree with
$2\mid W$, and define

```math
\mathcal N_m[L,U)
=
\#\{n\in[L,U):m\mid n,\ \gcd(n,W)=1,\ \gcd(n+2,Z)=1\}.
```

Writing $n=mk$ converts the numerical interval to

```math
K_m[L,U)
=
\left[
\left\lceil\frac Lm\right\rceil,
\left\lceil\frac Um\right\rceil
\right)\cap\mathbb Z,
\qquad
\ell_m=|K_m[L,U)|.
```

If $\gcd(m,W)>1$, choose a prime $p\mid\gcd(m,W)$. Every $n=mk$ then has
$p\mid n$ and cannot be coprime to $W$. Thus

```math
\boxed{\mathcal N_m[L,U)=0.}
```

Assume now $\gcd(m,W)=1$. For every prime $p\mid WZ$, let
$\lambda_p(m)$ count the allowed residues of $k$ modulo $p$. Direct local
analysis gives

```math
\lambda_p(m)=
\begin{cases}
p-1,&p\mid W,\ p\nmid Z,\\
1,&p=2,\ p\mid W,\ p\mid Z,\\
p-2,&p>2,\ p\mid W,\ p\mid Z,\\
p,&p\mid Z,\ p\nmid W,\ p\mid m,\\
p-1,&p\mid Z,\ p\nmid W,\ p\nmid m.
\end{cases}
```

Each row follows from an exact residue count:

- If $p\mid W$ and $p\nmid Z$, the hypothesis $\gcd(m,W)=1$ makes $m$
  invertible modulo $p$. The installed condition forbids only
  $k\equiv0\pmod p$, leaving $p-1$ classes.
- If $p\mid W$ and $p\mid Z$, the two conditions forbid
  $k\equiv0\pmod p$ and $k\equiv-2m^{-1}\pmod p$. They coincide for $p=2$,
  leaving one class, and are distinct for $p>2$, leaving $p-2$ classes.
- If $p\mid Z$ and $p\nmid W$, then $p$ is odd because $2\mid W$. When
  $p\mid m$, one has $mk+2\equiv2\not\equiv0\pmod p$ for every $k$, so all
  $p$ classes survive. When $p\nmid m$, invertibility of $m$ leaves exactly
  one forbidden class and therefore $p-1$ allowed classes.

These cases are exhaustive because every prime dividing $WZ$ belongs to the
installed wheel only, both wheels, or the relaxed wheel only. This proves the
local table.

Put

```math
R=\prod_{p\mid WZ}p,
\qquad
\rho(m)=\prod_{p\mid WZ}\frac{\lambda_p(m)}p.
```

CRT proves that every complete block of $R$ consecutive $k$ values contains
exactly $R\rho(m)$ allowed values.

Let the $k$ interval have length $\ell_m=qR+s$, with $0\le s\lt R$, and let
$C_m$ count allowed values in its final $s$ positions. Then

```math
\begin{aligned}
\mathcal N_m[L,U)
&=qR\rho(m)+C_m
&&[\text{Complete Periods Plus Remainder}]\\
&=\rho(m)\ell_m+
\left(C_m-s\rho(m)\right).
&&[\text{Substitution}]
\end{aligned}
```

Defining $E_m[L,U)=C_m-s\rho(m)$ gives

```math
\boxed{
\mathcal N_m[L,U)
=\rho(m)\ell_m+E_m[L,U),
\qquad
|E_m[L,U)|\le s\le R-1.
}
\qquad[\text{Q.E.D.}]
```

In the candidate range $Z\mid W$, all divisors coprime to $W$ have the same
density

```math
\boxed{
\rho_{Q,z}
=
\frac12
\prod_{2\lt p\lt z}\left(1-\frac2p\right)
\prod_{z\le p\lt Q}\left(1-\frac1p\right).
}
```

This is sieve dimension two below $z$ and dimension one from $z$ to $Q$.
The exact pointwise remainder bound is not a Type-I theorem because the
primorial $R$ is much larger than the square-safe interval.

### Stainless And Source Evidence For the Divisor Local Factor property

No maintained Scala theorem currently models both squarefree wheels, all five
local cases, CRT composition, and the arbitrary interval remainder. A future
verification should prove the local table one prime at a time and then use a
verified CRT product lemma. The property remains explicitly pending rather
than being represented by speculative code. The complete mathematical proof
is maintained in [Relaxed Almost-Prime Weight Has An Exact Divisor Local
Factor](
../../properties/sieve-sequence/relaxed-almost-prime-divisor-local-factor.md).

## 5. Shifted Divisor Discrepancy

**Population:** Installed-wheel survivors in one arbitrary interval, with the
shift $n+2$ constrained by one odd squarefree divisor $d$.

**Scope and quantifier:** Every squarefree installed wheel $W$ with $2\mid W$,
every odd squarefree divisor $d\mid W$, and every finite integer interval
$I=[L,U)$.

**Status:** **Mathematically proved, Stainless verification pending.**
The exact reduction is proved; the accumulated prime-progression estimate is
open.

The lower-bound sieve should be applied before the final relaxed filtering
step. Its base sequence is

```math
\mathcal A_Q=\{n+2:n\in S_Q\}.
```

For an odd squarefree divisor $d\mid W$, define

```math
A_d(I)
=
\#\{n\in I:\gcd(n,W)=1,\ d\mid n+2\},
\qquad
A_1(I)=\#\{n\in I:\gcd(n,W)=1\}.
```

In one complete residue system modulo $W$, every prime dividing $d$ fixes
$n=-2$, while every other wheel prime permits all nonzero classes. Therefore

```math
\begin{aligned}
A_d([a,a+W))
&=\prod_{\substack{p\mid W\\p\nmid d}}(p-1)
&&[\text{CRT}]\\
&=\frac{\varphi(W)}{\varphi(d)}
&&[\text{Squarefree Products}]\\
&=\frac{A_1([a,a+W))}{\varphi(d)}.
&&[\text{Q.E.D.}]
\end{aligned}
```

Thus the centered word

```math
h_d(n)
=
\mathbf1_{\gcd(n,W)=1}
\left(\mathbf1_{d\mid n+2}-\frac1{\varphi(d)}\right)
```

is $W$-periodic with zero mean. For every interval $I$,

```math
r_d(I)
:=
A_d(I)-\frac{A_1(I)}{\varphi(d)}
```

is exactly the sum of $h_d$ over the one incomplete wheel remainder after
complete blocks are removed. More explicitly, write

```math
|I|=qW+t,
\qquad
0\le t\lt W.
```

Partition $I$ from its left endpoint into $q$ complete consecutive blocks of
length $W$ and one final block of length $t$. Periodicity and the complete
wheel identity give

```math
\begin{aligned}
r_d(I)
&=\sum_{n\in I}h_d(n)
&&[\text{By Definition}]\\
&=\sum_{u=0}^{q-1}\sum_{j=0}^{W-1}h_d(L+uW+j)
  +\sum_{j=0}^{t-1}h_d(L+qW+j)
&&[\text{Block Decomposition}]\\
&=\sum_{j=0}^{t-1}h_d(L+qW+j).
&&[\text{Complete Blocks Have Zero Mean}]
\end{aligned}
```

Since $|h_d(n)|\le1$, the exact representation gives only the pointwise bound

```math
\boxed{|r_d(I)|\le t\le W-1.}
```

For a primorial $W$, this magnitude bound is too large to be a Type-I theorem;
the useful fact is the exact signed remainder.

In the square-safe interval, wheel survivors are primes. Hence

```math
\boxed{
r_d(I)
=
\pi(I;d,-2)-\frac{\pi(I)}{\varphi(d)}.
}
\qquad[\text{Q.E.D.}]
```

The missing Type-I input is consequently an averaged theorem of the form

```math
\sum_{\substack{d\le D\\d\mid P(z)/2}}
\tau_B(d)
\max_I
\left|
\pi(I;d,-2)-\frac{\pi(I)}{\varphi(d)}
\right|
\ll
\frac{Q^2}{(\log Q)^A},
```

with a range $D$ and interval family strong enough for the chosen lower-bound
sieve. This displayed estimate is an open target, not a theorem of this
article.

### Stainless And Source Evidence For the Cofactor Progression Discrepancy property

The complete-period CRT identity and periodic remainder are suitable for
future formalization. The prime-progression interpretation also depends on
square-safe certification. No maintained theorem currently connects all these
pieces for arbitrary squarefree $d$, so Stainless verification is pending.
The accumulated analytic inequality lies outside what has been formalized.
The complete mathematical reduction is maintained in [Relaxed Cofactor
Divisor Sum Is A Prime-Progression Discrepancy](
../../properties/sieve-sequence/relaxed-cofactor-divisor-sum-is-prime-progression-discrepancy.md).

## 6. Exact Bilinear Character Decomposition

**Population:** Scalar-centered relaxed weights evaluated at products $x=mn$.

**Scope and quantifier:** Every pair of squarefree nested wheels
$2\mid Z\mid W$, every factor pair with $\gcd(mn,W)=1$, every finite factor
domain $\mathcal D$, and arbitrary coefficients $\xi_m,\kappa_n$.

**Status:** **Mathematically proved, Stainless verification pending.**

Assume $2\mid Z\mid W$ and put $Z_{\mathrm{odd}}=Z/2$. Conditional on
$\gcd(x,W)=1$, the complete-wheel relaxed density is

```math
\vartheta_Z
=
\prod_{p\mid Z_{\mathrm{odd}}}
\left(1-\frac1{p-1}\right).
```

Center the final weight by

```math
w(x)
=
\mathbf1_{\gcd(x,W)=1}
\left(
\mathbf1_{\gcd(x+2,Z)=1}-\vartheta_Z
\right).
```

If $\gcd(mn,W)=1$, then $m,n$ are odd units modulo every divisor of
$Z_{\mathrm{odd}}$, so $mn+2$ is odd. The even terms in the Möbius
coprimality identity vanish, while expansion of the squarefree Euler product
for $\vartheta_Z$ gives

```math
\begin{aligned}
\mathbf1_{\gcd(mn+2,Z)=1}
&=
\sum_{d\mid Z_{\mathrm{odd}}}
\mu(d)\mathbf1_{mn\equiv-2\ (\mathrm{mod}\ d)},\\
\vartheta_Z
&=
\sum_{d\mid Z_{\mathrm{odd}}}\frac{\mu(d)}{\varphi(d)}.
\end{aligned}
```

Subtracting yields the exact pointwise decomposition

```math
\boxed{
w(mn)
=
\mathbf1_{\gcd(m,W)=\gcd(n,W)=1}
\sum_{d\mid Z_{\mathrm{odd}}}
\mu(d)
\left(
\mathbf1_{n\equiv-2m^{-1}\ (\mathrm{mod}\ d)}
-\frac1{\varphi(d)}
\right).
}
```

Character orthogonality on the reduced residue group gives

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

This is the genuine arbitrary-coefficient bilinear family. It is not removed
by subtracting one scalar density. Indeed, for every finite factor domain
$\mathcal D$ and arbitrary coefficients $\xi_m,\kappa_n$, substitution gives

```math
\begin{aligned}
\sum_{(m,n)\in\mathcal D}\xi_m\kappa_nw(mn)
&=
\sum_{d\mid Z_{\mathrm{odd}}}
\frac{\mu(d)}{\varphi(d)}
\sum_{\substack{\chi\ (\mathrm{mod}\ d)\\\chi\ne\chi_0}}
\overline{\chi(-2)}\\
&\qquad\cdot
\sum_{\substack{(m,n)\in\mathcal D\\
\gcd(m,W)=\gcd(n,W)=1}}
\xi_m\kappa_n\chi(m)\chi(n).
&&[\text{Finite Sum Rearrangement; Q.E.D.}]
\end{aligned}
```

The formula diagonalizes the local congruence modes. It does not estimate
them: the geometry of $\mathcal D$, for example a hyperbolic restriction on
$mn$, still couples the two variables.

### Stainless And Source Evidence For the Bilinear Character Obstruction property

The proof uses Möbius inversion and finite character orthogonality, neither of
which currently has a maintained representation for this weight in the
project. Stainless verification is pending. The exact finite algebra is proved
mathematically above and maintained in [Relaxed Almost-Prime Bilinear
Remainder Has A Character Obstruction](
../../properties/sieve-sequence/relaxed-almost-prime-bilinear-character-obstruction.md).

## 7. Refuted Route — Scalar-Density Type-II Orthogonality

**Population:** Product pairs on the complete reduced wheel
$G_W\times G_W$.

**Scope and quantifier:** Every pair of squarefree wheels $2\mid Z\mid W$
with $3\mid Z$; the counterexample uses bounded character coefficients.

**Status:** **[Refuted] Exact auxiliary statement.** Candidate #25 and
short-domain locally adapted Type-II estimates are not refuted.

The failed shortcut claimed that scalar centering makes the complete-wheel
weight orthogonal to all bounded product coefficients, or at least gives a
universal strict contraction $c\lt1$ relative to the relaxed survivor count.
The quadratic character modulo $3$ disproves both claims.

Assume $3\mid Z$. Let $\chi_3$ be the nonprincipal real character modulo $3$
and let

```math
G_W=(\mathbb Z/W\mathbb Z)^\times.
```

Choose bounded product coefficients

```math
\xi_m=\chi_3(m),
\qquad
\kappa_n=\chi_3(n).
```

If the relaxed weight accepts $mn$, then $mn+2$ is nonzero modulo $3$.
Because $mn$ is a unit, necessarily $mn\equiv2\pmod3$, and therefore

```math
\xi_m\kappa_n=\chi_3(mn)=-1.
```

Hence the relaxed indicator has correlation

```math
\sum_{m,n\in G_W}\xi_m\kappa_na(mn)
=
-\sum_{m,n\in G_W}a(mn).
\qquad[\text{Constant Character Sign}]
```

The scalar comparison is

```math
b(x)=\vartheta_Z\mathbf1_{\gcd(x,W)=1}.
```

CRT balances the reduced residues between the two unit classes modulo $3$,
so $\sum_{m\in G_W}\chi_3(m)=0$. Since every product of two wheel units is
again a wheel unit,

```math
\begin{aligned}
\sum_{m,n\in G_W}\xi_m\kappa_nb(mn)
&=\vartheta_Z
  \left(\sum_{m\in G_W}\chi_3(m)\right)
  \left(\sum_{n\in G_W}\chi_3(n)\right)
&&[\text{Scalar Comparison}]\\
&=0.
&&[\text{CRT Balance}]
\end{aligned}
```

Because $w=a-b$, subtraction gives

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

Thus scalar-density centering does not produce complete-wheel orthogonality or
any strict universal contraction against arbitrary product coefficients:
the ratio to the survivor count is exactly $1$.

This counterexample does not refute relaxed-weight positivity. It refutes only
the proof shortcut that treats the final scalar-centered periodic weight as
locally pseudorandom. A short hyperbolic factor domain is not a complete
reduced wheel, so the counterexample also does not decide every locally
adapted Type-II estimate.

### Source Evidence For The Refuted Route

The exact failed statement, counterexample, and retry boundary are preserved
in [Scalar-Density Type-II Orthogonality For The Relaxed Weight](
../../candidates/refuted/relaxed-weight-scalar-density-type-ii.md). The same
character calculation is derived from the Bilinear Character Obstruction property's canonical source. No
empirical sample is used in the refutation.

## 8. The Correct Remaining Program

The proved results impose an order on the remaining work.

First, match a theorem on primes in arithmetic progressions to the exact
shifted-divisor remainder

```math
\pi(I;d,-2)-\frac{\pi(I)}{\varphi(d)}.
```

The theorem must cover the divisor range and interval uniformity required by
the chosen lower-bound sieve. A complete-period CRT count cannot replace that
average.

Second, formulate Type II before the final relaxed sifting step, or use a
comparison sequence that already includes every fixed local character mode.
The scalar-centered final indicator is not an admissible pseudorandom model.

Third, verify that the proved Type-I and bilinear ranges actually make the
lower-bound almost-prime weight positive. Neither local factors nor
orthogonality formulas imply positivity on their own.

## 9. Claim Boundary

This article proves:

1. positivity of the relaxed weight implies a prime plus an integer with at
   most two prime factors;
2. the exact one-divisor local factor and periodic boundary remainder;
3. the exact shifted-divisor reduction to prime-progressions;
4. the exact inverse-residue and nonprincipal-character bilinear family; and
5. failure of scalar-density Type-II orthogonality on the complete wheel.

It does not prove:

- positivity for any unbounded family of heads;
- the accumulated prime-progression estimate;
- a locally adapted Type-II estimate;
- a new proof of Chen's theorem; or
- any twin-prime statement.

## 10. Conclusion

The relaxed program has a proved conditional conclusion. For fixed
$1/3\lt\alpha\lt1/2$ and sufficiently large $Q$,

```math
a_Q(n)=1
\Longrightarrow
n\text{ is prime and }\Omega(n+2)\le2.
```

The Divisor Local Factor property gives the exact one-divisor comparison. Wheel-sharing divisors
vanish; coprime divisors have

```math
\begin{aligned}
\mathcal N_m[L,U)
&=\rho(m)\ell_m+E_m[L,U),
&&[\text{Exact Interval Decomposition}]\\
|E_m[L,U)|&\le R-1,
&&[\text{Periodic Boundary}]\\
\rho_{Q,z}
&=
\frac12
\prod_{2\lt p\lt z}\left(1-\frac2p\right)
\prod_{z\le p\lt Q}\left(1-\frac1p\right).
&&[\text{Nested-Wheel Specialization}]
\end{aligned}
```

The Cofactor Progression Discrepancy property identifies the natural pre-sieved Type-I remainder exactly:

```math
\begin{aligned}
r_d(I)
&=A_d(I)-\frac{A_1(I)}{\varphi(d)}
&&[\text{Shifted Divisor Discrepancy}]\\
&=\pi(I;d,-2)-\frac{\pi(I)}{\varphi(d)}.
&&[\text{Square-Safe Prime Identity}]
\end{aligned}
```

The Bilinear Character Obstruction property gives the exact nonprincipal bilinear spectrum

```math
\mathbf1_{mn\equiv-2\ (\mathrm{mod}\ d)}
-\frac1{\varphi(d)}
=
\frac1{\varphi(d)}
\sum_{\chi\ne\chi_0}
\overline{\chi(-2)}\chi(m)\chi(n),
```

and the modulo-$3$ character refutes scalar-only centering:

```math
\left|
\sum_{m,n\in G_W}\chi_3(m)\chi_3(n)w(mn)
\right|
=
\sum_{m,n\in G_W}a(mn).
```

The next theorem must therefore add genuine averaged prime-distribution
information and use a locally adapted bilinear formulation. Even those two
estimates must still be inserted into a lower-bound almost-prime identity that
proves positivity. The article establishes the algebraic reductions and one
failed shortcut; it does not supply that final analytic argument, a new proof
of Chen's theorem, or a twin-prime result.

## References

1. [Chen-Type Almost-Prime Survivor](
   ../../candidates/chen-type-almost-prime-survivor.md).
2. [Relaxed Almost-Prime Weight Has An Exact Divisor Local Factor](
   ../../properties/sieve-sequence/relaxed-almost-prime-divisor-local-factor.md).
3. [Relaxed Almost-Prime Bilinear Remainder Has A Character Obstruction](
   ../../properties/sieve-sequence/relaxed-almost-prime-bilinear-character-obstruction.md).
4. [Relaxed Cofactor Divisor Sum Is A Prime-Progression Discrepancy](
   ../../properties/sieve-sequence/relaxed-cofactor-divisor-sum-is-prime-progression-discrepancy.md).
5. [Scalar-Density Type-II Orthogonality For The Relaxed Weight](
   ../../candidates/refuted/relaxed-weight-scalar-density-type-ii.md).
6. [Formal Verification of Sieve Sequence Stages and Their Transitions](
   ../chapter6/sieve-sequence.md).

## Appendix A: Evidence And Verification Status

| Result | Mathematical status | Stainless status | Canonical evidence |
|--------|---------------------|------------------|--------------------|
| Relaxed positivity implies prime-plus-$P_2$ | Conditional implication proved; positivity for infinitely many heads open | Pending | [Candidate #25](../../candidates/chen-type-almost-prime-survivor.md) |
| the Divisor Local Factor property — exact divisor local factor | Proved, including all five local cases and arbitrary-interval remainder | Pending | [Divisor Local Factor](../../properties/sieve-sequence/relaxed-almost-prime-divisor-local-factor.md) |
| the Cofactor Progression Discrepancy property — shifted divisor discrepancy | Exact reduction proved; accumulated prime-progression estimate open | Pending | [Cofactor Progression Discrepancy](../../properties/sieve-sequence/relaxed-cofactor-divisor-sum-is-prime-progression-discrepancy.md) |
| the Bilinear Character Obstruction property — bilinear character decomposition | Exact pointwise and arbitrary-domain decompositions proved | Pending | [Bilinear Character Obstruction](../../properties/sieve-sequence/relaxed-almost-prime-bilinear-character-obstruction.md) |
| Scalar-density Type-II shortcut | [Refuted] on the complete reduced wheel; short locally adapted domains remain open | Not applicable to a false statement | [Archived refutation](../../candidates/refuted/relaxed-weight-scalar-density-type-ii.md) |

The operational Sieve Sequence construction and its square-safe inputs are
documented separately in [Formal Verification of Sieve Sequence Stages and
Their Transitions](../chapter6/sieve-sequence.md). The new arithmetic results
in this draft remain mathematically proved with Stainless representations
pending.
