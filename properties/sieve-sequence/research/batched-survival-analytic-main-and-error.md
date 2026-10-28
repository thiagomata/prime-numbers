# Analytical Main Term and Local Error in Batched Survival

**Status:** Mathematical derivations, with classical external inputs identified.
No empirical sweep, generic local-survival theorem, historical novelty, or
Stainless verification is claimed.

**Current progress:** Later transport and component proofs establish actual
B/F->0 for square transitions, while an eventual positive actual margin
remains open. See the [research summary](batched-survival-progress.md).
These transition bounds do not supply the local signed-error theorem sought here.

The [classical lower-sieve audit](batched-survival-classical-sieve-input.md)
separately tests a standard theorem at the square cutoff and proves actual
old-candidate abundance with positive cubic density for exponent11/5. That
different rule still has no final-survivor or T_33 estimate.

## Purpose and Scope

The batch construction allows an analytical question: can its local survivor
bound be separated into a controllable arithmetic main term and a bounded
remainder? This note performs that separation, proves a finite positivity
criterion for the cubic density term, and shows precisely why one elementary
absolute-error estimate cannot complete the local proof.

The positivity theorem concerns a full-period density expression. It is not
a theorem that every destination safe window contains twins. The missing local
estimate is stated at the end without assuming it.

## Setup

Let p>=5 and q>p be primes. Write

```math
\begin{aligned}
M&=\prod_{\substack{r<p\\r\ \mathrm{prime}}}r,
&\mathcal B&=\{r:r\ \mathrm{prime},\ p\le r<q\},\\
b&=|\mathcal B|,
&H&=q^2-q-2.
\end{aligned}
```

The eligible integer starts form the interval [q,q^2-3], containing exactly H
integers. Let G be the number of old cyclic 2-gaps in one period M and set
delta=G/M. Define the old local candidates and their hit multiplicities by

```math
\begin{aligned}
\mathcal A&=\{a\in\mathbb Z:q\le a\le q^2-3,
                  \ \gcd(a(a+2),M)=1\},\\
h(a)&=|\{r\in\mathcal B:r\mid a(a+2)\}|,\\
I_k&=\sum_{a\in\mathcal A}\binom{h(a)}k,
\qquad C=I_0.
\end{aligned}
```

For k>b, set I_k=0. The number S of surviving pairs satisfies

```math
S\ge L_3=I_0-I_1+I_2-I_3.
```

This is the classical Bonferroni inequality. A modern exposition is Paul
Pollack, [*Not Always Buried Deep*, Theorem 6.8, printed p.177](https://www.pollack-math.net/NABDofficial.pdf#page=190).
The [earlier overlap note](batched-survival-overlap-audit-2026-10-27.md)
derives its application to these pairs and gives the exact binomial remainder.
Only mathematical bounds, not additional measurements, are used below.

## 1. Exact Main-Term and Error Decomposition

For r in B put x_r=2/r. Define the elementary symmetric sums

```math
e_0=1,\qquad
e_k=\sum_{\substack{\mathcal R\subseteq\mathcal B\\|\mathcal R|=k}}
                  \prod_{r\in\mathcal R}\frac2r,
\qquad e_k=0\text{ for }k>b.
```

For a fixed k-subset R, write d_R for its prime product. Each old cyclic
pair start imposes one residue class modulo M. Requiring a hit by every prime
in R gives two choices per prime: the left or right endpoint is divisible by
that prime. Since r>=5 and gcd(r,M)=1, the Chinese remainder theorem gives
exactly 2^k distinct classes modulo M*d_R for each old start. Classes from
different old starts are also distinct modulo M*d_R.

Each class c modulo a positive integer D contributes exactly

```math
\left\lfloor\frac{q^2-3-c}{D}\right\rfloor
-\left\lfloor\frac{q-1-c}{D}\right\rfloor
=\frac HD+\varepsilon_{D,c},
\qquad |\varepsilon_{D,c}|<1.
```

Summing over the G old starts, the 2^k classes, and the k-subsets gives the
exact identity and conservative bound

```math
\boxed{
I_k=H\delta e_k+E_k,
\qquad
|E_k|\le G\,2^k\binom bk.
}
```

The binomial coefficient is zero when k>b. This is an exact decomposition:
the error E_k is defined by actual signed class remainders, not an assumed
random fluctuation. For k=0 it gives C=H*delta+E_0 and |E_0|<=G.

Consequently, with

```math
B_3=1-e_1+e_2-e_3,
\qquad \mathcal E_3=E_0-E_1+E_2-E_3,
```

we have

```math
\boxed{S\ge L_3=H\delta B_3+\mathcal E_3.}
```

The full-period quantity B_3 is explicit in the filter primes. The local
signed discrepancy mathcal E_3 is the separate quantity requiring control.

## 2. A Finite Positive-Main-Term Theorem

The cubic density term is provably positive when the reciprocal-prime load
is not too large. Specifically, define

```math
\lambda=\sum_{r\in\mathcal B}\frac2r,
\qquad s_2=\sum_{r\in\mathcal B}\left(\frac2r\right)^2.
```

For every p>=13 and every later prime q satisfying lambda<=3/2,

```math
\boxed{B_3\ge\frac1{16}-\frac3{4p}>0.}
```

To prove it, all x_r are nonnegative and at most 2/p. Thus

```math
\begin{aligned}
s_2&\le\frac{2\lambda}{p},
&&[\text{Since }x_r\le2/p]\\
e_2&=\frac{\lambda^2-s_2}{2},
&&[\text{Expanding }\lambda^2]\\
3e_3&\le\lambda e_2.
&&[\text{Expanding }\lambda e_2]
\end{aligned}
```

The last expansion contains every product of three distinct x_r exactly
three times, together with nonnegative repeated-index terms. Since
1-lambda/3>=0, substitution preserves the inequality direction:

```math
\begin{aligned}
B_3
&\ge1-\lambda+\left(1-\frac\lambda3\right)e_2\\
&\ge1-\lambda+
       \left(1-\frac\lambda3\right)
       \frac{\lambda^2-2\lambda/p}{2}\\
&=f(\lambda)-\frac{\lambda(1-\lambda/3)}p,
\qquad
f(t)=1-t+\frac{t^2}{2}-\frac{t^3}{6}.
\end{aligned}
```

On [0,3/2],

```math
\begin{aligned}
f'(t)&=-\frac{(t-1)^2+1}{2}<0,\\
f(t)&\ge f(3/2)=\frac1{16},\\
t(1-t/3)&=\frac34-\frac{(t-3/2)^2}{3}\le\frac34.
\end{aligned}
```

These inequalities prove B_3>=1/16-3/(4p), which is positive for p>12.
No information about a measured sieve sequence was used.

## 3. Application to the Destination Above p Squared

Let q be the first prime greater than p squared. Bertrand's theorem gives
p^2<q<2p^2, hence log(q)/log(p) tends to 2. The reciprocal-prime estimate of
Mertens gives

```math
\begin{aligned}
\sum_{r\le x,\ r\ \mathrm{prime}}\frac1r
  &=\log\log x+B+O(1/\log x),\\
\lambda
  &=2\log\left(\frac{\log q}{\log p}\right)
       +O(1/\log p)\\
  &\longrightarrow2\log2<\frac32.
\end{aligned}
```

Changing inclusive to exclusive prime endpoints contributes only O(1/p).
The classical inputs are presented in Pollack's book:
[Theorem 3.6, printed p.89, for Bertrand](https://www.pollack-math.net/NABDofficial.pdf#page=102)
and [Theorem 3.14, printed p.97, for the reciprocal-prime estimate](https://www.pollack-math.net/NABDofficial.pdf#page=110).
Pollack is cited as an exposition, not as their original discoverer.

It follows that lambda<=3/2, and therefore B_3>0, for all sufficiently large
p under this rule. No explicit numerical starting threshold is derived here.
This proves eventual positivity of the density main term, not of S or L_3 in
the actual safe window. That distinction does not disappear asymptotically.

## 4. What the Independent Absolute-Error Budget Can Prove

If every class remainder is bounded separately, the triangle inequality gives

```math
\begin{aligned}
\mathcal E_3&\ge-GQ_b,\\
Q_b&=\sum_{k=0}^{3}2^k\binom bk,\\
S&\ge G\left(\frac HM B_3-Q_b\right).
\end{aligned}
```

Thus the strict inequality (H/M)*B_3>Q_b is one sufficient certificate.
The old count G cancels from this particular test: multiplying both its main
term and its allowed error by the same number of old pairs does not improve
the relative margin.

This certificate cannot succeed when H<M. To see this, apply Bonferroni to
the complete batch period. Equivalently, use independent Bernoulli events
with probabilities 2/r as an algebraic representation of the CRT proportions:

```math
B_3\le\prod_{r\in\mathcal B}(1-2/r)\le1.
```

Since Q_b>=1, it follows that

```math
\boxed{
H<M\quad\Longrightarrow\quad
\frac HM B_3<1\le Q_b.
}
```

This is a proof about the stated coarse estimate. It does not prove that the
actual local error is large, that exact floor sums cannot certify survival,
or that correlated remainders cannot be controlled. The earlier finite
certificates indeed use more exact information than this triangle budget.

### Elementary Eventual Failure of This Budget for the Square Rule

For the first prime q above p squared, H<M holds for every prime p>=2048.
This conservative explicit threshold follows from Bertrand alone; no
prime-number-theorem estimate for the primorial is required.

Choose m with 2^m<=p<2^(m+1), so m>=11. For each j=1,...,m-1,
Bertrand provides a prime r_j strictly between 2^j and 2^(j+1). These intervals
are disjoint and all selected primes are smaller than p. Therefore

```math
M\ge\prod_{j=1}^{m-1}r_j
  >2^{\sum_{j=1}^{m-1}j}
  =2^{m(m-1)/2}.
```

At m=11, m(m-1)/2-(4m+6)=5; increasing m by one increases this difference
by m-4>0. Consequently, for all such m,

```math
H<q^2<4p^4<2^{4m+6}<2^{m(m-1)/2}<M.
```

The preceding obstruction now applies to every square-jump starting head in
this range: the stated independent unit-error budget cannot certify survival.
This does not constrain the signs or size of the actual correlated remainders.

## 5. Precise Remaining Number-Theoretic Obligation

For a destination rule with B_3>0, a sufficient next theorem is a one-sided
bound on the actual combined signed error, for some fixed 0<eta<1:

```math
\mathcal E_3\ge-(1-\eta)H\delta B_3.
```

It would imply S>=eta*H*delta*B_3>0. This bound is open here; writing it is
not proving it. A weaker sufficient bound could hold only at unboundedly many
heads, or use a different proved lower bound for L_3.

The analytical task is to exploit correlations among the actual CRT class
remainders, or replace the expansion with sharper sieve weights or a different
arithmetic decomposition. Treating their signs as independent random data, or
substituting density directly for local counts, is not justified.

The proved progress is the explicit separation, finite positivity criterion,
eventual positive density term for the square rule, and the narrow limitation
of the elementary error budget. The [generic batch-window candidate](../../../candidates/batched-window-survival.md)
remains open.

## 6. High-Order Moments Require Nonnegligible Density Corrections

The [higher-order transport analysis](batched-survival-propagation-check-2026-10-27.md#seventh-order-penalty-is-small-relative-to-the-cubic-benchmark)
proves that L_7 closely approximates S on the scale H*delta. This does not
make the individual overlap moments close to their full-period density
terms. The endpoint size actually forces nonzero limiting corrections.

Throughout this section q is the first prime above p squared. Let H_j count
old-accepted starts with h(a)=j, and let K count primes in [p,4p). Every
endpoint is below q squared<4p to the fourth power<p to the fifth power.
Old acceptance excludes factors below p, so each endpoint has at most four
prime factors counted with multiplicity and h<=8.

If h>=7, one endpoint has four distinct factors. It is squarefree, since
an additional repetition would give at least five factors with multiplicity.
Each factor is smaller than4p, as its three partners are at least p. A
choice of endpoint orientation and four-prime subset determines the start.
Consequently

```math
\begin{aligned}
H_7+H_8&\le2\binom K4,\\
I_7=H_7+8H_8&\le16\binom K4,\\
I_8=H_8&\le\binom K4,\\
I_k&=0\qquad(k\ge9).
\end{aligned}
```

The sharper H_8 bound uses the lower endpoint alone, since both endpoints
then have four factors. Chebyshev gives K=O(p/log p), as in
[Pollack, Theorem 3.5](https://www.pollack-math.net/NABDofficial.pdf#page=102).
The product estimate in the
[component analysis](batched-survival-component-bounds.md) gives
H*delta comparable to p^4/log squared p. Thus

```math
\frac{I_7}{H\delta}\longrightarrow0,
\qquad\frac{I_8}{H\delta}\longrightarrow0.
```

Their density factors do not tend to zero. Section3 established
lambda=sum(2/r)->ell=2 log2 using Mertens' reciprocal-prime estimate.
For any fixed integer k>=2, expand lambda to the kth power into ordered
prime-index tuples. Distinct-index tuples sum to k!*e_k. If an index repeats,
some pair of positions agrees. Summing over such pairs, with possible
overcounting and nonnegative weights, gives

```math
\begin{aligned}
0\le\lambda^k-k!e_k
 &\le\binom k2s_2\lambda^{k-2},\\
s_2=\sum_{r\in\mathcal B}(2/r)^2
 &\le\frac2p\lambda\longrightarrow0,\\
e_k&\longrightarrow\frac{\ell^k}{k!},
\qquad\ell=2\log2.
\end{aligned}
```

The load lambda stays bounded, so the repeated-index contribution vanishes.
Combining these limits with the exact CRT decomposition I_k=H*delta*e_k+E_k
proves

```math
\boxed{\frac{E_k}{H\delta}
       \longrightarrow-\frac{(2\log2)^k}{k!}<0,
       \qquad k=7,8.}
```

These are individual moment errors E_7 and E_8. They are not the combined
certificate discrepancy mathcal E_7=sum from k=0 to7 of (-1)^k E_k.
The displayed limits do not determine that sum, its sign, or a sufficient
one-sided bound for survival. They rule out an approximation demanding
negligible individual errors at these orders. No existing candidate is
claimed refuted merely because it asks for a different combined bound.
Near-exactness of the score and correctness of the density approximation
are distinct questions; neither provides a positive twin count here.

## 7. The Fifth Penalty Reduces to a Balanced Triple-Product Correlation

Keep the square rule and K,H_j from Section6. Define T_33 to count starts
in the old-accepted window for which each endpoint is a squarefree product
of exactly three distinct primes in the BATCH [p,q). Such a pair has six
distinct hits: no prime at least5 divides endpoints differing by2. Thus
T_33<=H_6. The condition that all six factors belong to the batch is part
of the definition, not an assumption inferred from the endpoint size.

The remaining six-hit pairs have one of two forms. A4+2 or2+4 split has an
endpoint with four distinct factors. Section6 bounds all such starts by
2*binomial(K,4). In a3+3 split, any failure of squarefreeness means that
one endpoint has a repeated factor.

For a three-hit endpoint, there is no additional prime factor outside the
batch. A factor below p is excluded by old acceptance; a factor at least q
would make the endpoint at least p cubed*q>p to the fifth power, impossible.
Since five factors counted with multiplicity are also impossible, the
nonsquarefree endpoint is exactly three distinct batch primes with one of
them doubled. All its factors are smaller than4p: the other three factors
counted with multiplicity are at least p. A choice of its orientation,
three-prime subset and doubled prime determines the candidate start. Hence

```math
0\le H_6-T_{33}\le2\binom K4+6\binom K3.
```

The classical fifth-order remainder, using h<=8, is

```math
S-L_5=H_6+6H_7+21H_8.
```

Combining the preceding bound with H_7+H_8<=2*binomial(K,4) and
H_8<=binomial(K,4) proves the finite refinement

```math
\begin{aligned}
L_5&=S-T_{33}-D,\\
0\le D
 &=(H_6-T_{33})+6H_7+21H_8\\
 &\le29\binom K4+6\binom K3.
\end{aligned}
```

Likewise the exact sixth moment satisfies

```math
\begin{aligned}
I_6&=H_6+7H_7+28H_8=T_{33}+D_6,\\
0\le D_6&\le37\binom K4+6\binom K3.
\end{aligned}
```

Chebyshev's K=O(p/log p) gives D,D_6=O(p^4/log^4 p), negligible relative
to H*delta and to the positive cubic F. The bound on the binomial(K,3)
term is smaller, since (p^3/log^3 p)/(p^4/log^4 p)=log(p)/p tends to zero.

Thus squarefree balanced3+3 pairs are the only POSSIBLE leading contribution
to the fifth penalty at this scale. No leading contribution is asserted to
exist: T_33 might itself be small. Its count is a shifted-product correlation,
requiring six distinct batch primes with

```math
r_1r_2r_3+2=s_1s_2s_3,
\qquad q\le r_1r_2r_3<q^2-2,
\qquad p\le r_i,s_i<q.
```

Ordinary prime counts alone do not automatically estimate this correlation
or compare it with the true twin count S. The reduction identifies a concrete
arithmetic population; it does not prove its abundance, its negligibility,
or a positive fifth-order reserve.

As a check on the role of truncation, h<=8 makes the ninth-order certificate
equal S exactly by the same alternating-binomial identity. Increasing the
order can remove the certificate penalty entirely, but exact representation
of the twin count is not a positive lower bound for it. A fresh-supply proof
still needs independent arithmetic information.
