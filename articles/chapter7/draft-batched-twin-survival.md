# Batched Twin Survival at Square Jumps: Explicit Budgets and the Parity Barrier

**Proof status:** Mathematical draft.

**Author:** Thiago Henrique Ramos da Mata  
Independent Researcher  
**Email:** [thiago.henrique.mata@gmail.com](mailto:thiago.henrique.mata@gmail.com)  
**ORCID:** [0009-0002-7366-939X](https://orcid.org/0009-0002-7366-939X)  
**GitHub:** [@thiagomata](https://github.com/thiagomata)  
**License:** [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)

## Abstract

<div align="justify">
<p style="text-align: justify">

A Sieve Sequence 2-gap whose endpoints survive every filter installed
between one square jump and the next is a twin-prime pair. This article
asks whether classical sieve arithmetic can certify that at least one
such 2-gap survives, and it answers negatively at two successive levels
of the attempt.

The supply side uses a rough Chen input: the square window contains at
least a positive constant times $Y/(\log Y)^2$ prime-endpoint candidates
whose partner is prime or a product of two large primes. The rejection
side evaluates, with explicit constants, the total weight of the exact
integer intervals on which each smaller factor could act: the geometric
coefficient is $\kappa=5/16+(1/2)\log(8/3)$ and the leading rejection
allowance is $16C_2\kappa=C_2(5+8\log(8/3))\approx12.85\,C_2$, where
$C_2$ is the twin-prime product. A prime-conditioned linear sieve then
bounds the whole family by $5C_2\,Y/(\log Y)^2$, strictly below the
allowance, so the separate-budget subtraction is provably insufficient;
cutoff tuning at the same level cannot repair it.

Replacing the subtraction by one joint signed certificate changes the
diagnosis but not the outcome. The pointwise weight has the exact sum
$T-B=2T-|\mathcal G|$, and bounding the excess $B-T$ below
$(1-\delta)|\mathcal G|$ in a single large window would prove a twin
there. Each tested input class fails structurally: certifying primality
of a partner requires sifting parameter $s=2\theta<2<\beta_2\approx4.266$
at every distribution level $\theta\le1$, including the
Elliott--Halberstam boundary; the upper estimates cap only parts of the
semiprime population or their common sifted superset; and the weighted
and switched sieve sources reproduce exactly the two budgets already
recorded. The needed estimate is an instance of the classical parity
phenomenon.

The negative conclusions are the main results. They leave behind the
exact identity, the explicit constants, and the precise condition under
which this route could reopen. The proofs are mathematical and are not
Stainless-verified. No twin-prime infinitude theorem follows.

</p>
</div>

## 1. Introduction

Begin with the Sieve Sequence of [Formal Verification of Sieve Sequence
Stages and Their Transitions](https://doi.org/10.5281/zenodo.22955782)
[[1]](#ref1): after the primes below a head $p$ have been installed as
filters, the accepted values are the integers not divisible by any of
them, and the sequence repeats periodically. A 2-gap is a pair of
consecutive accepted values $x$ and $x+2$. If both endpoints also
survive every later filter, they are twin primes.

Fix the **square rule**: let $p$ be the current head and let $q$ be the
first prime above $p^2$. Between the heads $p$ and $q$, the sieve
installs the batch of all filters headed by primes in $(p,q]$. A 2-gap
of the $p$-stage that survives the entire batch is a twin-prime pair,
because both endpoints exceed $q$ and lie below $q^2$, where every
composite has a filter divisor. The **batched survival question** is
whether arithmetic can certify, for at least one square jump, that some
member of a large candidate family survives the whole batch.

The natural strategy is a subtraction. A supply theorem guarantees many
candidates; a rejection estimate bounds how many the batch can destroy;
if the second number is smaller than the first, a survivor exists. This
article executes that strategy with explicit constants, watches it fail
for a structural reason, and then executes its strongest repair — one
joint signed certificate instead of two separate budgets — and
identifies the obstruction that kills the repair as well.

The attempt is honest about being an attempt: the final conclusion is
that the decisive estimate was not found, and the article records why
in a form that separates what is proved from what is missing. Three
kinds of usable information survive the failure:

- an exact partition identity connecting the twin count of a window to
  its guaranteed family ([§7](#7-the-joint-signed-certificate));
- explicit constants for both budgets, including the geometric
  coefficient $\kappa$ and the whole-family ceiling
  ([§4](#4-rejection-accounting-by-exact-interval-lengths),
  [§5](#5-the-whole-family-ceiling),
  [§6](#6-the-separate-budget-obstruction));
- a structural diagnosis — the parity barrier — that converts the
  failure from a numerical accident into a property of the method
  ([§8](#8-the-parity-barrier)).

We derive the following results:

- The guaranteed family and its rejection structure —
  [§3](#3-the-guaranteed-family-at-a-square-jump).
- Exact interval lengths, the geometric weight sum, and the leading
  rejection allowance — [§4](#4-rejection-accounting-by-exact-interval-lengths).
- The whole-family ceiling by a prime-conditioned linear sieve —
  [§5](#5-the-whole-family-ceiling).
- The quantitative obstruction and the limit of cutoff tuning —
  [§6](#6-the-separate-budget-obstruction).
- The joint signed certificate and its exact identity —
  [§7](#7-the-joint-signed-certificate).
- The three parity tests and the barrier —
  [§8](#8-the-parity-barrier).

All sieve inputs are classical and are cited to their primary sources;
the combinations and the negative conclusions are ours. No historical
priority claim is made for any sieve theorem used, and no result is
claimed for the real sieve beyond those displayed with proofs.

## 2. Preliminaries

Throughout, $p$ is a prime head, $q$ is the first prime above $p^2$, and

```math
\begin{aligned}
X&=q^2-3,& Y&=X+2,& Z&=(X/2)^{3/11}.
\end{aligned}
```

The working window is the dyadic interval $(X/2,X]$, whose pairs
$(a,a+2)$ satisfy $a+2\le Y$. Since $q>p$, Bertrand's postulate gives
$q<2p^2$, so $\log Z/\log p\to12/11>1$ and $\log Z/\log q\to6/11<1$;
in particular $p<Z<q$ eventually, and $Z\to\infty$.

- The twin-prime product and the dimension-two sieve product.
- The upper and lower sieve functions and the sifting limit $\beta_2$.

For the pair of linear forms $a(a+2)$, the local root counts are
$\rho(2)=1$ and $\rho(\ell)=2$ at each odd prime $\ell$, extended
multiplicatively. The sieve product over primes below $y$ is

```math
\begin{aligned}
V(y)&=\prod_{\ell<y}\left(1-\frac{\rho(\ell)}{\ell}\right)
     =2C_2(y)\left(\prod_{\ell<y}\left(1-\frac1\ell\right)\right)^2,
&&[\text{By Definition}]
\end{aligned}
```

where

```math
C_2(y)=\prod_{3\le\ell<y}\left(1-\frac1{(\ell-1)^2}\right)
```

has a positive limit $C_2$. Mertens' product estimate
[[10]](#ref10), Theorem 3.15, evaluates the normalization:

```math
\begin{aligned}
V(y)&=\frac{2C_2e^{-2\gamma}+o(1)}{(\log y)^2},
&&[\text{Mertens Product}]
\end{aligned}
```

with $\gamma$ Euler's constant.

The combinatorial sieve of dimension two has an upper function $F_2$
and a lower function $f_2$ in the sifting parameter
$s=\log D/\log z$, where $D$ is the level of distribution and $z$ the
cutoff. Two classical inputs are used. First, the initial values of
Booker--Browning [[3]](#ref3), Theorem 3.1, equations (7)--(8), give, in
dimension two,

```math
\begin{aligned}
\sigma_2(t)&=\frac{t^2}{8e^{2\gamma}}\quad(0<t\le2),
& F_2(2)&=\frac1{\sigma_2(2)}=2e^{2\gamma};
\end{aligned}
```

the initial range of $F_2$ includes $s=2$. Second, the lower function
vanishes through its sifting limit,

```math
\begin{aligned}
f_2(u)&=0\quad(u\le\beta_2),
& \beta_2&\approx4.266,
\end{aligned}
```

as recorded with the computed values in Franze [[5]](#ref5), Table 1,
and stated with the lower-sieve estimate of Franze--Kao [[4]](#ref4),
Section 4, equation (20). The linear sieve of dimension one enters
once, through its upper function

```math
\begin{aligned}
F_1(s)&=\frac{2e^\gamma}{s}\quad(1\le s\le3),
&&[\text{Linear Sieve}]
\end{aligned}
```

as stated, with the needed remainder input, in Tao's exposition
[[9]](#ref9), Supplement 5, Theorem 2.

These ingredients are standard. The sections below combine them for one
window at one square jump and record where the combinations stop.

## 3. The Guaranteed Family at a Square Jump

The supply input is a rough Chen statement. Green and Tao
[[2]](#ref2), Section 6, Theorem 6.1, prove a lower bound for the
strengthened Chen condition in a dyadic interval: for every
sufficiently large integer $X$, the number of $a\in(X/2,X]$ such that
$a$ is prime and $a+2$ is either prime or a product $uv$ of primes
$u,v>a^{3/11}$ is at least $c_1X/(\log X)^2$ for an absolute $c_1>0$.
They attribute the roughness improvement to Iwaniec's 1996 course
notes; we use their published formulation.

Define the family of this article by

```math
\begin{aligned}
\mathcal G(p,q)=\{a\in(X/2,X]:\;&a\text{ prime},\\
&a+2\text{ prime, or }a+2=uv
 \text{ with primes }Z<u<v\}.
\end{aligned}
```

The source theorem admits partners with both factors above $a^{3/11}>Z$;
the only partners it admits and this definition excludes are prime
squares $a+2=u^2$, of which there are at most $\lfloor\sqrt{X+2}\rfloor$
in the window. Since $\sqrt{X+2}=o(X/(\log X)^2)$,

```math
\begin{aligned}
|\mathcal G(p,q)|
&\ge c_1\frac X{(\log X)^2}-\lfloor\sqrt{X+2}\rfloor
&&[\text{Subtraction}]\\
&\ge\frac{c_1}{2}\frac X{(\log X)^2}
&&[\text{Simplification}]
\end{aligned}
```

eventually. Every member has both endpoints free of prime factors below
$Z$: the first endpoint is a prime above $X/2>Z$, a prime partner is
above $X/2>Z$, and both semiprime factors exceed $Z$. The family
therefore survives every filter below $Z$, and $Z>p$ eventually, so the
whole initial segment of the batch passes without touching any member.

If the partner is composite, its smaller factor satisfies

```math
\begin{aligned}
Z&<u<\sqrt{a+2}\le\sqrt Y,
&&[\text{Least Factor}]
\end{aligned}
```

so a remaining filter can reject the member only through such a factor
$u$. Under a hypothetical last twin pair, every sufficiently late member
of $\mathcal G$ would have a semiprime partner. That outcome is
compatible with the quoted theorem; recognizing this compatibility is
where the subtraction attempt begins, not where it ends.

## 4. Rejection Accounting by Exact Interval Lengths

Write $b_u$ for the number of members of $\mathcal G$ whose partner has
least prime factor exactly $u$. A member with semiprime partner
$a+2=uv$ has $a=uv-2\in(X/2,X]$, so $v$ ranges over an exact integer
interval whose length is

```math
\begin{aligned}
L_u&=\left\lfloor\frac Yu\right\rfloor
     -\left\lfloor\frac{Y/2+1}{u}\right\rfloor,
&&[\text{By Definition}]
\end{aligned}
```

and distinct members have distinct pairs $(u,v)$ of factors, so summing
$b_u$ over the allowed $u$ counts each rejected member once. This
section bounds each $b_u$ by an interval sieve and evaluates the total
weight of the lengths.

### 4.1 The Per-Interval Upper Sieve

Sieving the values $v(uv-2)$ over the $L=L_u$ integers $v$ of the
interval, each prime $\ell$ removes $\rho_u(\ell)$ residue classes:

```math
\begin{aligned}
\rho_u(2)&=1,& \rho_u(u)&=1,&
\rho_u(\ell)&=2\quad(\ell>2,\ \ell\ne u),
\end{aligned}
```

extended multiplicatively; at $u$ the second factor equals $-2$, and at
any other odd prime the two roots are distinct. Counting classes in
$L$ consecutive integers leaves a position-independent remainder,

```math
\begin{aligned}
|A_d|&=L\frac{\rho_u(d)}d+R_u(d),
& |R_u(d)|&\le\rho_u(d)\le2^{\omega(d)},
\end{aligned}
```

and the elementary divisor-sum bound of the dimension-two setup gives
$\sum_{d<D}\mu^2(d)7^{\omega(d)}|R_u(d)|\le D(1+\log D)^{13}$
uniformly in $u$ and the interval position. The local densities are at
most their generic dimension-two counterparts, so the uniform dimension
condition of [§2](#2-preliminaries) holds. Choose

```math
\begin{aligned}
D&=\frac L{(\log L)^{20}},& z&=\sqrt D,& s&=\frac{\log D}{\log z}=2.
&&[\text{By Definition}]
\end{aligned}
```

On the bulk $Z<u\le\sqrt Y/2$ the lengths satisfy $L_u\ge\sqrt Y-2$, so
$D$ and $z$ tend to infinity uniformly there. The cutoff may exceed
$u$; this changes one factor of the product by
$V_u(z)/V(z)=(u-1)/(u-2)=1+O(1/Z)$, uniformly because $u>Z$. The
actual prime values still survive the sieve: the lower endpoint gives
$v>(Y/2+1)/u\ge\sqrt Y$, while $z\le\sqrt L=o(\sqrt Y)$, and the other
value $uv-2$ exceeds $Y/2>z$. Applying the upper estimate of
Franze--Kao [[4]](#ref4), Section 4, equation (19), with the initial
value of [§2](#2-preliminaries),

```math
\begin{aligned}
b_u&\le LV_u(z)\left(F_2(2)+o(1)\right)
      +O\!\left(\frac L{(\log L)^7}\right)
&&[\text{Upper Sieve}]\\
&\le\left(16C_2+o(1)\right)\frac L{(\log L)^2}.
&&[\text{Substitution}]
\end{aligned}
```

The constant $16C_2$ per interval is the classical twin upper bound
coefficient in this normalization; the calculation recovers it rather
than inventing a new one.

### 4.2 The Geometric Weight Sum

The bulk lengths are $L_u=Y/(2u)+O(1)$, and on the bulk
$L_u/(\log L_u)^2=(1+o(1))\,L_u/(\log(Y/u))^2$ uniformly, since
$u\le\sqrt Y/2$ makes $\log(Y/u)$ comparable to $\log Y$. Writing
$t=\log u/\log Y$ and applying Mertens' reciprocal-prime estimate
[[10]](#ref10), Theorem 3.14, with partial summation over the fixed
exponent range $[3/11,1/2]$,

```math
\begin{aligned}
\sum_{\substack{Z<u\le\sqrt Y/2\\u\text{ prime}}}
  \frac1{u\,\log^2(Y/u)}
&=\frac1{(\log Y)^2}
  \left\{\int_{3/11}^{1/2}\frac{dt}{t(1-t)^2}+o(1)\right\}
&&[\text{Partial Summation}]
\end{aligned}
```

and the integral is elementary:

```math
\begin{aligned}
\int_{3/11}^{1/2}\frac{dt}{t(1-t)^2}
&=\left[\log\frac t{1-t}+\frac1{1-t}\right]_{3/11}^{1/2}
&&[\text{By Definition}]\\
&=2-\log\frac38-\frac{11}8
=\frac58+\log\frac83.
&&[\text{Simplification}]
\end{aligned}
```

Multiplying by $Y/2$ gives the bulk weight with coefficient

```math
\begin{aligned}
\kappa&=\frac12\left(\frac58+\log\frac83\right)
=\frac5{16}+\frac12\log\frac83\approx0.8029.
&&[\text{Q.E.D.}]
\end{aligned}
```

On the edge $\sqrt Y/2<u<\sqrt Y$ all lengths are at most $2\sqrt Y$,
and Chebyshev's bound [[10]](#ref10), Theorem 3.5, gives
$O(\sqrt Y/\log Y)$ edge primes, so their total weight is
$O(Y/(\log Y)^3)$, negligible on the asserted scale. Combining the
bulk and the edge,

```math
\begin{aligned}
\sum_u b_u
&\le\left(16C_2\kappa+o(1)\right)\frac Y{(\log Y)^2}
=\left(5+8\log\frac83\right)C_2\frac{Y}{(\log Y)^2},
&&[\text{Q.E.D.}]
\end{aligned}
```

since $16\kappa=5+8\log(8/3)\approx12.8466$. This is an upper bound for
the semiprime rejections, not their asymptotic count.

## 5. The Whole-Family Ceiling

The rejection allowance of [§4](#4-rejection-accounting-by-exact-interval-lengths)
can be compared with an upper bound for the entire family, prime and
semiprime partners alike. Weight each integer $a\in(X/2,X]$ by the von
Mangoldt value $\Lambda(a)$ and sift the forbidden classes
$a\equiv-2\pmod\ell$ at each odd prime $\ell$; the event at $\ell=2$ is
empty. The multiplicative densities are

```math
\begin{aligned}
g(2)&=0,& g(\ell)&=\frac1{\ell-1}=\frac1\ell+O(1/\ell^2)
&&[\text{By Definition}]
\end{aligned}
```

and $0\le g(\ell)\le1/2$. For odd squarefree $d$ the residue $-2$ is
coprime to $d$, so the classical Bombieri--Vinogradov estimate supplies
the local formula and the summed remainders at the fixed level

```math
\begin{aligned}
\sum_{\substack{X/2<a\le X\\a\equiv-2\pmod d}}\Lambda(a)
&=g(d)\frac X2+r_d,
& D&=(X/2)^{2/5},&
\sum_{\substack{d\le D\\d\text{ odd, sqfree}}}|r_d|
&=O\!\left(\frac X{(\log X)^{10}}\right),
\end{aligned}
```

since any fixed exponent strictly between $2/5$ and $1/2$ is admissible
[[9]](#ref9), equations (10), (12), and (39). The product of the
complement densities is, by the identity of
[§2](#2-preliminaries) and Mertens' theorem,

```math
\begin{aligned}
W(Z)&=\prod_{3\le\ell<Z}\frac{\ell-2}{\ell-1}
=\frac{V(Z)}{\prod_{\ell<Z}(1-1/\ell)}
=\frac{2C_2e^{-\gamma}+o(1)}{\log Z}.
&&[\text{Mertens Product}]
\end{aligned}
```

Because $Z=(X/2)^{3/11}$, the sifting parameter is exactly constant:

```math
\begin{aligned}
s&=\frac{\log D}{\log Z}=\frac{2/5}{3/11}=\frac{22}{15}\in(1,3).
&&[\text{Substitution}]
\end{aligned}
```

The prime density bounds meet the linear-sieve hypotheses, and the
upper estimate of [[9]](#ref9), Theorem 2, gives for the sifted sum

```math
\begin{aligned}
S_\Lambda
&\le\left(F_1(s)+o(1)\right)\frac X2W(Z)+o\!\left(\frac X{\log X}\right)
&&[\text{Linear Sieve}]\\
&\le\frac{2e^\gamma}{s}\cdot\frac X2\cdot\frac{2C_2e^{-\gamma}}{\log Z}
+o\!\left(\frac X{\log X}\right)
&&[\text{Substitution}]\\
&=\frac{2C_2X}{\log D}+o\!\left(\frac X{\log X}\right)
=\left(5C_2+o(1)\right)\frac X{\log X},
&&[\text{Simplification}]
\end{aligned}
```

using $\log D=(2/5)\log(X/2)$. Every member $a$ of $\mathcal G$ is
prime, has $a+2$ free of primes below $Z$, and contributes
$\Lambda(a)=\log a\ge\log(X/2)$ to this nonnegative sum; extra prime
powers only enlarge the bound. Therefore

```math
\begin{aligned}
|\mathcal G(p,q)|
&\le\frac{S_\Lambda}{\log(X/2)}
\le\left(5C_2+o(1)\right)\frac Y{(\log Y)^2}.
&&[\text{Q.E.D.}]
\end{aligned}
```

## 6. The Separate-Budget Obstruction

The subtraction certificate asks for a lower constant $c_*$ with
$|\mathcal G|\ge c_*Y/(\log Y)^2$ eventually and an upper rejection
bound strictly below it. The two preceding sections determine both
sides:

```math
\begin{aligned}
c_*&\le5C_2
&&[\text{[§5] Ceiling}]\\
\sum_ub_u&\le16C_2\kappa\,\frac{Y}{(\log Y)^2}
=12.8466\,C_2\frac{Y}{(\log Y)^2}.
&&[\text{[§4] Allowance}]
\end{aligned}
```

Since

```math
\begin{aligned}
5<5+8\log\frac83=16\kappa\approx12.8466,
&&[\text{Substitution}]
\end{aligned}
```

the allowance exceeds the largest possible valid lower constant by the
factor $2.57$. The separate-budget subtraction is therefore provably
insufficient: no evaluation of the supply constant, and no sharpening
within this rejection estimate, can make the difference positive.

One natural repair is cutoff tuning. Keep the level
$D=L/(\log L)^{20}$ of [§4](#4-rejection-accounting-by-exact-interval-lengths)
and choose a fixed $s\ge1$ with $z=D^{1/s}$. The leading local upper
coefficient becomes $K(s)=2C_2e^{-2\gamma}s^2F_2(s)$. Put
$Q(s)=s^2F_2(s)$. The initial values of [[3]](#ref3), Theorem 3.1,
give $Q(s)=8e^{2\gamma}$ on $0<s\le2$; beyond that, the
Diamond--Halberstam--Richert differential equations, as recorded in
[[4]](#ref4), equations (21)--(24), give

```math
\begin{aligned}
Q'(s)&=\frac{2\sigma_2(s-2)}{s^3\sigma_2(s)^2}>0
\quad(2<s\le\alpha_2),
&&[\text{Differential Equation}]\\
Q'(s)&=2s\,f_2(s-1)\ge0\quad(s>\alpha_2),
&&[\text{Differential Equation}]
\end{aligned}
```

with both cited functions positive on their ranges. Hence

```math
\begin{aligned}
K(s)&\ge2C_2e^{-2\gamma}\cdot8e^{2\gamma}=16C_2,
& K(s)&=16C_2\iff1\le s\le2.
&&[\text{Q.E.D.}]
\end{aligned}
```

The tested cutoff $s=2$ already attains the floor, so fixed-cutoff
tuning at this level cannot improve the allowance. This closes the
separate-budget route at its own level of distribution and sieve
weights; it does not show that actual rejections attain the allowance,
nor that survivors are absent.

## 7. The Joint Signed Certificate

The repair attempted next keeps supply and rejection attached pointwise
instead of subtracting two separately estimated budgets. Define, for
each integer $a\in(X/2,X]$, the signed weight

```math
\begin{aligned}
\sigma(a)=\mathbf 1_{\substack{a\text{ prime}\\ a+2\text{ prime}}}
-\mathbf 1_{\substack{a\text{ prime}\\ a+2=uv,\ Z<u<v\text{ prime}}}.
&&[\text{By Definition}]
\end{aligned}
```

Prime-square partners are excluded from both indicators;
[§3](#3-the-guaranteed-family-at-a-square-jump) already accounted for
the at most $\lfloor\sqrt{X+2}\rfloor$ of them. Writing $T$ for the
twin count of the window and $B$ for the semiprime-partner count, the
family partitions into its twin members and its semiprime members, so

```math
\begin{aligned}
|\mathcal G|&=T+B
&&[\text{Partition}]\\
\sum_{X/2<a\le X}\sigma(a)&=T-B=2T-|\mathcal G|.
&&[\text{Substitution}]
\end{aligned}
```

The identity is exact and, by itself, carries no arithmetic
information. Under a hypothetical last twin pair it gives
$\sum\sigma(a)=-|\mathcal G|\le-(c_1/2)X/(\log X)^2$. Conversely, for
any fixed $\delta>0$,

```math
\begin{aligned}
\sum_{X/2<a\le X}\sigma(a)\ge-(1-\delta)|\mathcal G|
&\Longrightarrow
2T\ge\delta|\mathcal G|
&&[\text{Substitution}]\\
&\Longrightarrow
T\ge\frac\delta2|\mathcal G|>0,
&&[\text{Q.E.D.}]
\end{aligned}
```

so a single one-sided estimate of the signed sum proves a twin in that
window. Equivalently, writing the excess as $E=B-T=|\mathcal G|-2T$,
the target is an upper bound $E\le(1-\delta)|\mathcal G|$ in one
arbitrarily large window. On the family, the weight is the parity
function of the partner,

```math
\begin{aligned}
\sigma(a)&=(-1)^{\Omega(a+2)+1}\quad(a\in\mathcal G):
& \Omega&=1\text{ gives }+1,\quad \Omega=2\text{ gives }-1,
&&[\text{By Definition}]
\end{aligned}
```

and all other integers contribute zero. The joint certificate asks
exactly for arithmetic that measures this parity.

## 8. The Parity Barrier

Three tests, one per input class available at the admissible
distribution levels, each end with the same structural failure.

### 8.1 The Lower Sieve at Every Distribution Level

Certifying primality of a partner by a distribution-based sieve
requires sieving every prime up to $\sqrt{a+2}\le\sqrt Y$, that is, the
cutoff $z=\sqrt{X+2}$. Let $D$ be any level with $D\le Y^{1-\varepsilon}$
for fixed $\varepsilon>0$, and write $\theta=\log D/\log Y$. The
sifting parameter at the primality cutoff is exactly

```math
\begin{aligned}
s&=\frac{\log D}{\log\sqrt{X+2}}
=\frac{\log D}{\log\sqrt Y}=2\theta<2.
&&[\text{Substitution}]
\end{aligned}
```

Since $\beta_2\approx4.266>2$, the lower function of
[§2](#2-preliminaries) vanishes throughout the entire admissible range:

```math
\begin{aligned}
s=2\theta<2<\beta_2
&\Longrightarrow f_2(s)=0
&&[\text{Sifting Limit}]\\
&\Longrightarrow\text{zero lower main term for }T.
&&[\text{Q.E.D.}]
\end{aligned}
```

For levels with $\theta<1/2$ the cutoff exceeds the level and the
lower-sieve statement does not even apply. The conclusion holds at
every distribution level contemplated by current hypotheses, including
the Elliott--Halberstam boundary $\theta\to1$ with $s\to2$: no level of
distribution below the theoretical maximum rescues the pure lower
sieve.

### 8.2 The Upper Estimates and the Common Sifted Set

For every cutoff $z\le Z$, the twin members and the semiprime members
lie in one common sifted set,

```math
\begin{aligned}
\{a\in(X/2,X]:\;&a\text{ prime},\ a+2\text{ has no prime factor}<z\},
&&[\text{By Definition}]
\end{aligned}
```

because a twin partner exceeds $X/2>Z$ and both semiprime factors
exceed $Z\ge z$. The upper estimates of
[§4](#4-rejection-accounting-by-exact-interval-lengths) cap parts of the
semiprime population, and [§5](#5-the-whole-family-ceiling) caps the
common set itself; none yields information about the difference $B-T$.
The constants make the shared scale quantitative: the semiprime
allowance $12.85\,C_2$ exceeds even the whole-family ceiling $5C_2$ by
the factor $2.57$. An upper bound built from this data cannot be pushed
below the common main-term scale that both parts share.

### 8.3 Weighted and Switched Sources

Richert's weighted sieve [[6]](#ref6), Chapters 9--10, Theorem 9.1,
converts the same distribution data into lower bounds for partners with
at most $r$ prime factors. Its $r=2$ output in this window is precisely
the Chen-type supply of [§3](#3-the-guaranteed-family-at-a-square-jump),
already an input; its $r=1$ demand — certifying that a sifted partner
has no second large factor — is the full-cutoff lower sieve of
[§8.1](#81-the-lower-sieve-at-every-distribution-level), whose main
term vanishes at every $\theta\le1$. The switching principle, applied to
the switched forms $v$ and $uv-2$, produces upper bounds for
composite-partner populations; those inputs bound $B$ from above only
and contribute no estimate of the difference $B-T$. Each tested
weighted or switched source supplies exactly one of the two recorded
budgets, never their difference.

### 8.4 The Barrier

The common obstruction is the parity phenomenon: records of divisibility
of $a$ and $a+2$ by primes below a cutoff, together with distribution of
the remainder sums, are insensitive to the parity of $\Omega(a+2)$, and
no weighting or switching constructed from that information isolates the
odd-parity part. The phenomenon is classical; Selberg's example and the
limits it imposes on congruence-sum evidence are presented in Watkins's
lecture notes [[8]](#ref8), Section 10, and the known bypasses, which
require bilinear structure among the sifted forms, are developed in
Friedlander--Iwaniec [[7]](#ref7). The pair $a,a+2$ is a pair of linear
forms in a single variable; the bilinear structure that made
$x^2+y^4$ primes accessible is absent here. The signed certificate is
therefore exact but unevaluable by every input class tested, and the
route of this article terminates at that barrier.

## 9. Limitations

The constants $c_1$ and $C_0$-type absolute factors are not numerically
evaluated; only the leading coefficients $16C_2\kappa$ and $5C_2$ are
explicit.

The rejection allowance is an upper bound. Nothing shows that actual
rejections attain any fixed fraction of it; the failure of the
certificate is a property of the estimate, not evidence about the true
semiprime population.

The parity conclusion covers the input classes actually tested: pure
lower sieves, the dimension-two upper sieve at fixed cutoffs, Richert
weights, and switching. It is not a theorem about all conceivable
methods, and it does not rule out survival; it rules out this route at
every distribution level $\theta\le1$.

The analysis concerns one candidate family at one jump rule. Other
windows, other families, or genuinely new arithmetic input — a Type-II
estimate for the twin correlation, or a bilinear reorganization — lie
outside everything tested and are the recorded conditions for
reopening.

There is no empirical content: every statement is either an exact
identity or an asymptotic bound with an explicit leading constant. The
proofs are mathematical and are not Stainless-verified; in particular
the transport of these bounds through the exact Sieve Sequence
recurrences of [[1]](#ref1) is not attempted here.

## 10. Conclusion

The article set out to certify a surviving 2-gap at a square jump by
sieving and failed at two successive levels, each failure more
informative than the last. What remains is the following exact account
of the attempt:

```math
\begin{aligned}
|\mathcal G|&\ge\frac{c_1}{2}\frac X{(\log X)^2},
&&[\text{Supply}]\\
\sum_ub_u&\le\left(5+8\log\frac83\right)C_2\frac Y{(\log Y)^2},
&&[\text{Allowance}]\\
|\mathcal G|&\le5C_2\frac Y{(\log Y)^2},
&&[\text{Ceiling}]\\
\sum_{X/2<a\le X}\sigma(a)&=2T-|\mathcal G|,
&&[\text{Identity}]\\
s&=2\theta<2<\beta_2\quad(\theta\le1).
&&[\text{Barrier}]
\end{aligned}
```

The separate-budget certificate dies on the displayed numbers: the
allowance exceeds the ceiling by the factor $2.57$, and cutoff tuning
provably cannot shrink the allowance at the tested level. The joint
signed certificate then dies on structure: the weight is the parity
function of the partner, the primality cutoff forces
$s=2\theta<2<\beta_2$ at every distribution level up to the
Elliott--Halberstam boundary, and every weighted or switched input
reproduces one of the two budgets already on the table. The decisive
estimate was not found because, at this level of the method, it does
not exist: the obstruction is the parity barrier, not a missing
constant.

The usable residue of the failure is threefold: an exact partition
identity for any window of this family; explicit constants — the
geometric coefficient $\kappa=5/16+(1/2)\log(8/3)$, the allowance
$16C_2\kappa$, the ceiling $5C_2$ — against which any future estimate
can be measured; and a precise reopening condition. No twin-prime
infinitude theorem follows, and none is claimed.

## 11. Future Work

- A Type-II estimate for the twin correlation, or any bilinear
  reorganization of the family, is the recorded condition for
  reopening the joint certificate; no such input is currently known
  for a pair of linear forms in one variable.
- The exact transport of the window identity through the Sieve Sequence
  recurrences of [[1]](#ref1) — connecting the family counts to the
  sequence's gap cycles — is a separate combinatorial project.
- Other candidate families and jump rules retain the same two-sided
  bookkeeping and would have to clear both the numerical comparison and
  the parity diagnosis before any certificate is attempted.

## 12. References

<a name="ref1" id="ref1" href="#ref1">[1]</a>
Mata, T. H. (2026). *Formal Verification of Sieve Sequence Stages and Their
Transitions*. Available at: [https://doi.org/10.5281/zenodo.22955782](https://doi.org/10.5281/zenodo.22955782).

<a name="ref2" id="ref2" href="#ref2">[2]</a>
Green, B. and Tao, T. (2006). *Restriction theory of the Selberg sieve,
with applications*. Journal de théorie des nombres de Bordeaux, 18(1),
147--182, Section 6, Theorem 6.1.
Available at: [https://www.numdam.org/item/10.5802/jtnb.538.pdf](https://www.numdam.org/item/10.5802/jtnb.538.pdf).

<a name="ref3" id="ref3" href="#ref3">[3]</a>
Booker, A. and Browning, T. (2016). *Square-free values of reducible
polynomials*. Discrete Analysis, 2016:8, Theorem 3.1, equations (7)--(8).
Available at: [https://arxiv.org/abs/1511.00601](https://arxiv.org/abs/1511.00601).

<a name="ref4" id="ref4" href="#ref4">[4]</a>
Franze, C. S. and Kao, P. H. (2019). *Almost-prime values of reducible
polynomials at prime arguments*. Journal of Number Theory, Section 4,
equations (19)--(24).
Available at: [https://arxiv.org/abs/1812.11280](https://arxiv.org/abs/1812.11280).

<a name="ref5" id="ref5" href="#ref5">[5]</a>
Franze, C. (2010). *Sifting Limits for the $\Lambda^2\Lambda^-$ Sieve*,
Table 1. arXiv:1012.3809.
Available at: [https://arxiv.org/abs/1012.3809](https://arxiv.org/abs/1012.3809).

<a name="ref6" id="ref6" href="#ref6">[6]</a>
Halberstam, H. and Richert, H.-E. (1974). *Sieve Methods*. Academic
Press, London, Chapters 9--10, Theorem 9.1.

<a name="ref7" id="ref7" href="#ref7">[7]</a>
Friedlander, J. and Iwaniec, H. (2010). *Opera de Cribro*. American
Mathematical Society Colloquium Publications, 57.
Available at: [https://doi.org/10.1090/coll/057](https://doi.org/10.1090/coll/057).

<a name="ref8" id="ref8" href="#ref8">[8]</a>
Watkins, M. *Sieves: phrasing of sieve problems*, lecture notes,
Section 10 (Bombieri and the asymptotic sieve; Selberg's example).
Available at: [https://magma.maths.usyd.edu.au/~watkins/papers/SIEVES.pdf](https://magma.maths.usyd.edu.au/~watkins/papers/SIEVES.pdf).

<a name="ref9" id="ref9" href="#ref9">[9]</a>
Tao, T. (2015). *254a Supplement 5: The linear sieve and Chen's theorem
(optional)*, Theorem 2, equations (10), (12), (39).
Available at: [https://terrytao.wordpress.com/2015/01/29/254a-supplement-5-the-linear-sieve-and-chens-theorem-optional/](https://terrytao.wordpress.com/2015/01/29/254a-supplement-5-the-linear-sieve-and-chens-theorem-optional/).

<a name="ref10" id="ref10" href="#ref10">[10]</a>
Pollack, P. (2009). *Not Always Buried Deep: A Second Course in
Elementary Number Theory*. American Mathematical Society, Theorems 3.5,
3.14, and 3.15.
Available at: [https://www.pollack-math.net/NABDofficial.pdf](https://www.pollack-math.net/NABDofficial.pdf).
