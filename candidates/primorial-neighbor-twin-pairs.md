# Primorial-neighbor twin pairs

**Status:** Unnumbered exploratory research. Elementary deductions below have
mathematical proofs; the final infinitude conjecture remains open. No Stainless
verification or historical-priority claim is made.

**Empirical status:** No systematic experiment is reported. The small examples
illustrate the deductions and a failed unconditional strengthening.

## A particular pair

Let p_k be the kth prime, with k>=2, and fix

```math
P=p_k,\qquad m_k=P\#=\prod_{j=1}^{k}p_j.
```

Study the particular pair (m_k-1,m_k+1). Its center is fixed while we examine
future filters. Passing to another primorial later means studying another
pair. This direction uses divisibility and functional tests rather than
population or shot-capacity counts.

The [continuous wave research](continuous-wave-twin-research.md) provides the
integer wave indicators used below; the arithmetic deductions are proved here.

## Protection against installed primes

Every installed prime divides the center, so it divides neither neighbor:

```math
\begin{aligned}
q\le P,\ q\text{ prime}
&\Longrightarrow q\mid m_k\\
&\Longrightarrow m_k-1\equiv-1\pmod q,
\quad m_k+1\equiv1\pmod q\\
&\Longrightarrow q\nmid m_k-1,\quad q\nmid m_k+1.
\qquad[\text{Q.E.D.}]
\end{aligned}
```

Consequently every prime factor of either endpoint is greater than P. This
guarantees a candidate pair at the current filter stage, not primality.

For P=5, m_k=30 gives the twin pair (29,31). For P=7, m_k=210 gives
(209,211), but 209=11*19. The latter pair avoids all installed primes and
is nevertheless removed by the future filter 11.

## The endpoints have disjoint prime factors

The two endpoints are odd and their difference is two. Hence

```math
\begin{aligned}
d\mid m_k-1,\ d\mid m_k+1
&\Longrightarrow d\mid2\\
\gcd(m_k-1,m_k+1)&=1.
\qquad[\text{Q.E.D.}]
\end{aligned}
```

No prime can reject both endpoints. This does not guarantee that either
endpoint is prime: different primes can reject the two sides.

For a prime q, define the integer indicator

```math
\delta_q(x)=\begin{cases}1,&q\mid x,\\0,&q\nmid x.\end{cases}
```

The disjointness gives an exact simplification of the endpoint OR test:

```math
\begin{aligned}
\delta_q(m_k-1)\delta_q(m_k+1)&=0,\\
1-(1-\delta_q(m_k-1))(1-\delta_q(m_k+1))
&=\delta_q(m_k-1)+\delta_q(m_k+1).
\qquad[\text{Q.E.D.}]
\end{aligned}
```

At integers the selective wave W_q equals delta_q, so the same simplification
holds for those wave samples. It is not asserted for the interpolation at
noninteger arguments.

## One modular condition on the center

The prime-divisor test can be expressed entirely using m_k. Euclid's lemma
applied to the factorization of m_k^2-1 gives

```math
\begin{aligned}
q\mid m_k-1\ \text{or}\ q\mid m_k+1
&\Longleftrightarrow q\mid(m_k-1)(m_k+1)\\
&\Longleftrightarrow m_k^2\equiv1\pmod q\\
&\Longleftrightarrow m_k\equiv1\ \text{or}\ m_k\equiv q-1\pmod q.
\qquad[\text{Q.E.D.}]
\end{aligned}
```

Here q must be prime for the reverse product implication. The rejected pair
is detected when the center lies one unit from a multiple of q.

## A finite future-filter function

A composite endpoint has a prime divisor no larger than its square root.
Together with the old-prime protection, this confines a possible first
rejection to

```math
P<q\le\sqrt{m_k+1},\qquad q\text{ prime}.
```

The existence of a small prime divisor is the fact used here; it would be
false to say that every proper divisor is at most the square root.

Define the finite product, with an empty product interpreted as one,

```math
R_k=
\prod_{\substack{P<q\le\sqrt{m_k+1}\\q\text{ prime}}}
\left(1-\delta_q(m_k^2-1)\right).
```

Each factor is zero or one. Therefore

```math
\begin{aligned}
R_k=1
&\Longleftrightarrow
\text{no prime in the future band divides either endpoint}\\
&\Longleftrightarrow m_k-1\text{ and }m_k+1\text{ are prime}.
\qquad[\text{Q.E.D.}]
\end{aligned}
```

For the forward direction, a composite endpoint would supply a small prime
factor in that band, contradicting R_k=1. For the reverse direction, a prime
endpoint cannot divide its own test band: m_k-1>sqrt(m_k+1) for m_k>=6.
Thus the formula never mistakes a prime's own divisibility for rejection.
The square root supplies a finite certification horizon; it does not predict
a favorable primorial or prove survival.

## Absorbing an earlier rejecting prime

Suppose a future prime q divides one endpoint of the fixed pair at stage k.
At any later stage j with p_j>=q, that prime divides the new center m_j.
Consequently

```math
\begin{aligned}
q\mid m_j
&\Longrightarrow m_j-1\equiv-1\pmod q,
\quad m_j+1\equiv1\pmod q\\
&\Longrightarrow q\nmid(m_j-1)(m_j+1).
\qquad[\text{Q.E.D.}]
\end{aligned}
```

For example, 11 rejects 209 at center 210. Once the center becomes
2310=210*11, neither 2309 nor 2311 is divisible by 11. No assertion of
primality follows from this example. The old endpoint 209 remains composite;
absorption protects the new pair rather than repairing the old one.

## Consequences of a last twin pair

Assume there is a largest twin-prime start L. For all sufficiently large k,
m_k-1>L, so at least one endpoint is composite. Choose q_k to be the smallest
prime dividing a composite endpoint. Then

```math
p_k<q_k\le\sqrt{m_k+1},\qquad m_k^2\equiv1\pmod{q_k}.
```

Since p_k tends to infinity, q_k must also exceed every fixed bound eventually.
In particular, a finite collection of rejecting primes cannot reject every
later primorial pair. This does not require q_k to increase at each step;
the same prime may recur before it is absorbed.

If m_k-1=q_ka, all prime factors of a also exceed p_k, and q_ka+1=m_k.
If m_k+1=q_kb, all prime factors of b exceed p_k, and q_kb-1=m_k. Thus a
rejection places a number with only larger prime factors beside the specific
squarefree product of all primes through p_k.

There is no contradiction yet. The last-pair assumption is compatible with a
succession of new rejecting primes within these growing finite bands. Ruling
out that succession is the unresolved step. Even a last primorial twin pair
would not imply a last arbitrary twin pair.

## Concluding conjecture

For a complementary direction that retains families of actual sieve
candidates, see [Protected arithmetic families](protected-arithmetic-families.md).
That note studies one-filter protection and its persistence limitations,
rather than restricting pair centers to primorials.

The following conjecture records the proposed research target; no assertion
that the conjecture or its ingredients are historically new is intended.

For arbitrarily large k, both neighbors of m_k are prime:

```math
\begin{aligned}
&\forall K\ge2\ \exists k>K:\quad
m_k-1\text{ and }m_k+1\text{ are prime},\\
&\text{equivalently}\quad
\forall K\ge2\ \exists k>K:\quad R_k=1.
\end{aligned}
```

This primorial-neighbor twin conjecture is stronger than twin-prime infinitude.
Its truth would provide infinitely many distinct twin pairs because m_k is
strictly increasing. Its failure would leave open infinitely many twin pairs
with other centers. The elementary protection and absorption properties
motivate this question but do not prove the conjecture.
