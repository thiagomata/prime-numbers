# Filtered Shot Bound for the Shared-Region Cost

**Status:** Mathematical proofs for actual square-destination sieve transitions.
No general survival theorem, historical novelty, new empirical check, or
Stainless verification is claimed.

## Setup

Let p>=5 be prime, s the next prime, q the first prime greater than p squared,
and t the first prime greater than s squared. Then t>=q. Use the old filters
below s in both windows and define

```math
\begin{aligned}
M_s&=\prod_{\ell<s,\ \ell\ \mathrm{prime}}\ell,\\
\mathcal H&=\{a\in\mathbb Z:t\le a,\ a+2<q^2,
                        \ \gcd(a(a+2),M_s)=1\},\\
h(a)&=|\{\ell:s\le\ell<q,\ \ell\ \mathrm{prime},\ \ell\mid a(a+2)\}|,\\
j(a)&=|\{r:q\le r<t,\ r\ \mathrm{prime},\ r\mid a(a+2)\}|,\\
K_i&=|\{a\in\mathcal H:j(a)=i\}|,\qquad i=1,2.
\end{aligned}
```

The [transport proof](batched-survival-propagation-check-2026-10-27.md)
establishes j<=2, the absence of new hits on shared certified pairs, and
the cubic cost formula

```math
\begin{aligned}
J&=\sum_{a\in\mathcal H}\Delta(h(a),j(a)),\\
\Delta(h,j)&=j\binom{h-1}2+\binom j2(h-1)
\quad(h\ge1),
\end{aligned}
```

with zero contribution for h=0. The earlier
[component bounds](batched-survival-component-bounds.md) give constants10/9;
the destination ordering below sharpens them and bounds affected populations.

## 1. A Square-Destination Dichotomy

If q>s squared, no prime lies strictly between p squared and q, since q is
the first prime above p squared. As s squared lies between them, q is also
the first prime above s squared. Thus t=q. Equality q=s squared is impossible
because q is prime and s squared is composite. Consequently

```math
\boxed{t=q\quad\text{or}\quad q<s^2.}
```

In the first case there are no new filters and J=K_1=K_2=0. All following
factor arguments concern the other case t>q, which forces q<s squared.

## 2. Each Newly Hit Endpoint Has a Prime Cofactor

Take a shared candidate and a new filter prime r in [q,t) dividing its
endpoint n. The endpoint lies in [t,q squared), so n=r*u gives

```math
1<u<q<s^2.
```

Here u>1 follows from n>=t>r, and u<q from n<q squared and r>=q. Old
acceptance excludes every prime factor below s from u. If u were composite,
it would therefore be at least s squared. This is impossible. Hence

```math
\boxed{n=r\ell,\qquad q\le r<t,\quad s\le\ell<q,
       \quad r,\ell\text{ prime}.}
```

The old filters thus restrict the cofactor to a prime, yielding a genuine
population reduction compared with counting every multiple of r.

## 3. Sharper Cubic Costs: Three and One

For j=1, the newly hit endpoint has exactly one old batch prime factor,
its cofactor ell. The opposite endpoint is smaller than q squared<s to the
fourth power and has no prime factor below s, so at most three distinct old
batch primes divide it. Thus h<=4 and

```math
\Delta(h,1)=\binom{h-1}2\le3.
```

For j=2 the new primes hit opposite endpoints. Each has exactly one old
prime cofactor. Those cofactors are distinct, since a prime at least s cannot
divide two endpoints differing by2. Therefore h=2 and

```math
\Delta(2,2)=(2-1)^2=1.
```

Summation, including the zero-cost flat case, proves

```math
\boxed{0\le J\le3K_1+K_2.}
```

This holds for every square-rule starting head p>=5, without an eventual
threshold. A newly hit candidate can still have zero added cubic cost; the
bound is deliberately conservative.

## 4. A Filtered Population Bound Using Ordinary Prime Counts

Write pi(x) for the number of primes at most x and define

```math
b=\pi(t-1)-\pi(q-1),
\qquad
P=\pi(q-1)-\pi(s-1).
```

These count new filter primes and eligible cofactor primes respectively.
Both are nonnegative; q>s follows from q>p squared and s<2p<p squared.

Each new pair/filter incidence selects exactly one endpoint n=r*ell.
A new prime cannot divide both endpoints. Also each accepted endpoint belongs
to at most one candidate pair, because filters2 and3 are installed. Thus the
map from a pair/filter incidence to the ordered pair (r,ell) is injective.
There are b*P possible ordered pairs. Consequently

```math
\boxed{K_1+2K_2\le bP.}
```

Ignoring the restrictions on the product location and the other endpoint
only increases this upper bound. Combining the incidence and cost bounds gives

```math
\boxed{
J\le3K_1+K_2
  \le3(K_1+2K_2)
  \le3[\pi(t-1)-\pi(q-1)]
       [\pi(q-1)-\pi(s-1)].
}
```

The finite bound concerns actual filter incidences and uses ordinary prime
counts. It does not assume the existence of any surviving pair or use an
equidistribution approximation. In particular, the flat case has b=J=0.

## 5. Actual Shared-Region Cost Is Eventually Small Relative to F

The finite bound yields an eventual property of actual sieve transitions,
using the classical prime number theorem

```math
\pi(x)\sim\frac{x}{\log x}.
```

This theorem was proved independently by Hadamard and de la Vallee-Poussin
in1896. A modern exposition is Paul Pollack,
[*Not Always Buried Deep*, Chapter7, equation(7.1), printed p.214](https://www.pollack-math.net/NABDofficial.pdf#page=227).

Let rho(x) be the first prime strictly greater than x. For every fixed
epsilon>0, the prime number theorem gives

```math
\pi((1+\epsilon)x)-\pi(x)
\sim\frac{\epsilon x}{\log x}>0.
```

Thus x<rho(x)<=(1+epsilon)x for all sufficiently large x, proving
rho(x)/x->1. Applied at p, p squared, and s squared, this gives

```math
\frac sp\longrightarrow1,
\qquad
\frac q{p^2}\longrightarrow1,
\qquad
\frac t{s^2}\longrightarrow1,
\qquad
\frac tq\longrightarrow1.
```

Normalize the two prime counts defining b by q/log(q). Since t/q->1,
the prime number theorem gives

```math
\frac{\pi(t-1)}{q/\log q}\longrightarrow1,
\qquad
\frac{\pi(q-1)}{q/\log q}\longrightarrow1.
```

Subtracting these normalized limits proves

```math
b=o\!\left(\frac q{\log q}\right).
```

This is an absolute scale estimate. No relative short-interval formula
b asymptotic to (t-q)/log(q) is asserted or needed. Also

```math
0\le P\le\pi(q-1)=O\!\left(\frac q{\log q}\right).
```

The proved finite bound therefore implies, by squeeze,

```math
\boxed{J=o\!\left(\frac{q^2}{\log^2q}\right).}
```

The [positive-main-term proof](batched-survival-analytic-main-and-error.md)
and [component scale comparison](batched-survival-component-bounds.md)
establish, for some c>0 and all sufficiently large p under this rule,

```math
F(p,q)\ge c\frac{p^4}{\log^2p}.
```

Since q is asymptotic to p squared, this is at least a positive constant
times q squared divided by log squared q. Consequently

```math
\boxed{\frac{J}{F(p,q)}\longrightarrow0.}
```

Equivalently, for every epsilon>0 there is a threshold p_0 after which the
actual shared-region penalty satisfies J<=epsilon*F(p,q). This property is
proved here, not imposed as an additional hypothesis. No explicit numerical
threshold or convergence rate is derived.

## Scope and the Remaining Margin Problem

The finite estimate controls affected populations as well as pair weights;
the asymptotic argument proves smallness of actual J relative to F. Together
with the existing R<=R_cap and R_cap/F->0, it follows that for every epsilon>0,
eventually

```math
R+J\le\epsilon F(p,q),
\qquad
L(s,t)\ge L(p,q)+A+N-\epsilon F(p,q).
```

These are upper-cost and transition bounds for actual sequences. They do not
give J/L->0, because no uniform positive lower bound on actual L/F has been
proved. The subsequent [new-region proof](batched-survival-new-region-bound.md)
establishes |N|<=35(t^2-q^2)/6 and |N|/F->0 using quantitative classical PNT.
Thus B=|N|+R_cap+J satisfies B/F->0 and L_next>=L_current-B. For fixed
eta>0, sufficiently late transitions with L_current>=eta F have
L_next>=eta F/2>0 in old F units. No eventual positive-margin premise has
been proved; this implication halves the reserve and does not reproduce it.
Sustaining or replenishing an actual positive reserve remains unresolved.

In particular, this note proves an eventual small-cost property. It does not
prove that the complete preservation condition A+N>=R+J holds eventually or
that twin primes are infinite. The input prime number theorem concerns
ordinary primes, not a conjecture about prime pairs.

The [block-reserve proof](batched-survival-block-reserve.md) sums disjoint
new-prime intervals to control actual cumulative J together with the other
losses. The total is o(F_start) over a growing finite block. Positivity
throughout remains conditional on an unproved positive starting reserve;
no indefinite renewal follows.
