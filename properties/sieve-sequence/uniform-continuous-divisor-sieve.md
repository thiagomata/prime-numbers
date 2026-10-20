# Uniform Continuous Divisor Sieve

**Status:** Mathematical definitions and proofs. No formal implementation is
required for this research note. Distribution estimates and twin-prime
existence beyond the stated equivalences remain open.

## Purpose

Apply the same filter rule at every integer 2,3,4,..., rather than selecting
prime filters first. Composite filters add redundant rejection information
without changing the integer contact set. This removes prime selection from
the recurrence: primes emerge as real-axis contacts of its continuous limit.

The construction is a continuous complex-valued function of a real variable.
It is not claimed to be holomorphic. Selecting contacts means retaining values
with zero imaginary part; projecting every value onto its real part would
instead retain every input.

## 1. Definitions

For every integer m>=2 and real t>=2, define

```math
\begin{aligned}
D_m(t)&=\frac1m\sum_{\ell=0}^{m-1}e^{2\pi i\ell t/m},\\
a_m(t)&=\min(1,\max(0,t-m)),\\
h_M(t)&=\sin^2(\pi t)+\sum_{m=2}^{M}a_m(t)|D_m(t)|^2,\\
F_M(t)&=t+i h_M(t),\qquad M\ge1.
\end{aligned}
```

The sum is empty at M=1. The activation a_m is zero through m, grows linearly
to one at m+1, and stays one afterwards. Thus a filter preserves its own
integer, which is essential for retaining primes.

Every update uses the next integer, without a primality test:

```math
F_M(t)=F_{M-1}(t)+i a_M(t)|D_M(t)|^2,\qquad M\ge2.
```

All imaginary contributions are nonnegative. Taking squared modulus prevents
cancellation between filters. The same finite geometric-sum identity works
for composite moduli as for prime moduli.

## 2. Integer height is a truncated proper-divisor count

At integer n, the geometric-sum ratio is z=exp(2 pi i n/m). If m divides n,
every term is one. Otherwise z is not one but z^m=1, and the geometric sum
vanishes. Consequently

```math
|D_m(n)|^2=
\begin{cases}
1,&m\mid n,\\
0,&m\nmid n.
\end{cases}
```

For integer inputs the activation is zero when n<=m and one when n>m.
The sine term also vanishes. Therefore

```math
\boxed{
h_M(n)=\sum_{m=2}^{\min(M,n-1)}\mathbf 1_{m\mid n}.
}
```

Here the indicator is one when m divides n exactly and zero otherwise.
In words, height counts divisors between 2 and M that are smaller than n.
No set-cardinality notation is needed to interpret the formula.

For example, after all relevant filters, 12 has height four because its
nontrivial divisors are 2,3,4,6. Prime 7 has height zero.

## 3. Continuous limit and exact contacts

On a bounded real interval [2,B], every activation with m>=B is identically
zero. Thus only finitely many summands contribute on that interval. The limit

```math
h(t)=\sin^2(\pi t)+\sum_{m=2}^{\infty}a_m(t)|D_m(t)|^2,
\qquad F(t)=t+i h(t)
```

is a locally finite sum of continuous functions and is continuous. In fact,
F_M agrees exactly with F throughout [2,B] once M>=ceil(B). No interchange of
an uncontrolled infinite sum and a limit is required. Piecewise activation
does not by itself justify a general smoothness claim.

Let tau(n) be the number of positive divisors of n, including 1 and n.
The integer-height identity gives

```math
\boxed{h(n)=\tau(n)-2,\qquad n\ge2.}
```

A prime has precisely those two divisors. A composite has at least one
additional divisor. Nonintegers have a strictly positive sin^2(pi t) term.
Hence

```math
\boxed{F(t)\in\mathbb R\quad\Longleftrightarrow\quad t\text{ is prime},
\qquad t\ge2.}
```

Positive alternative filter weights preserve the same contacts, but alter
the divisor-count heights and their unit thresholds. The identities in this
note concern unweighted filters.

## 4. Heights increase; contacts never return

At all real inputs, every added contribution is nonnegative:

```math
h_M(t)\ge h_{M-1}(t).
```

Thus contacts can disappear but cannot reappear. At integer n, one update is
particularly simple:

```math
h_M(n)-h_{M-1}(n)=
\begin{cases}
1,&M<n\text{ and }M\mid n,\\
0,&\text{otherwise}.
\end{cases}
```

The ordinary curve remains unchanged for all real t<=M when adding filter M.
For pair curves using t+2, preservation must be interpreted at each endpoint.

## 5. Only prime steps remove new integer contacts

Suppose M is composite. Any integer n whose height increases satisfies
M|n and n>M. Choose a prime divisor r of M; then r<M<n and r|n. Filter r
already gave n positive height. Therefore a composite step removes no new
integer contacts, although the continuous curve and existing positive heights
can change.

If M=p is prime, p^2 had zero height before step p: every proper divisor of
p^2 other than 1 is p, and that filter was not yet installed. At step p its
height becomes one, so this step does remove a contact.

Moreover, no smaller integer contact disappears at that step. A multiple
n=kp<p^2 with n>p has 2<=k<p. A prime divisor of k is smaller than p and
already rejected n. The integer p itself is protected by activation. Thus

```math
\boxed{p^2\text{ is the first new integer contact removed at prime step }p.}
```

Equivalently, a step changes the integer contact set somewhere on the
unbounded domain if and only if its index is prime. This is a structural
characterization, not an efficiency claim about testing infinitely many inputs.

## 6. A growing certified region

After applying filters through integer M>=1, every contact in

```math
2\le n<(M+1)^2
```

is prime. If a composite n lay there, it would have a prime divisor
r<=sqrt(n)<M+1. Since r is an integer, r<=M, so n was already rejected.
Conversely every prime remains a contact. Noninteger contacts are excluded
by the sine term.

This square bound is sufficient, not always sharp. If q is the first prime
greater than M, the first composite integer contact is exactly q^2: every
composite below q^2 has a prime divisor less than q and hence at most M,
whereas no installed divisor divides q^2. This sharper description uses q
for analysis; q is not needed in the recurrence.

## 7. Low heights reveal factorization types

The prime factorization n=product p_j^(e_j) gives

```math
h(n)+2=\tau(n)=\prod_j(e_j+1).
```

Each divisor independently chooses an exponent from 0 through e_j, proving
the formula. It yields these exact classifications:

| Height | Factorization type | Examples |
|---:|---|---|
| 0 | A prime | 7,11 |
| 1 | A prime squared | 9,25 |
| 2 | A prime cubed, or a product of two distinct primes | 8,6,10 |
| 3 | A prime to the fourth power | 16,81 |

For example, height two means tau(n)=4, whose multiplicative partitions are
4 and 2*2, giving exponent patterns 3 and (1,1).

## 8. Odd heights detect perfect squares

Divisors normally pair as d and n/d. A divisor pairs with itself precisely
when d^2=n. Therefore tau(n) is odd exactly when n is a perfect square.
Subtracting two does not change parity:

```math
\boxed{h(n)\text{ is odd}\quad\Longleftrightarrow\quad n\text{ is a square},
\qquad n\ge2.}
```

## 9. Coprime multiplication law

For coprime integers a,b>=2, every divisor of ab factors uniquely into a
divisor of a times a divisor of b. Hence tau(ab)=tau(a)tau(b), giving

```math
\boxed{h(ab)+2=(h(a)+2)(h(b)+2),\qquad \gcd(a,b)=1.}
```

The coprimality premise matters: multiplying repeated prime factors changes
the exponent choices rather than multiplying two independent divisor sets.

## 10. Pair contacts and the research boundary

Define a pair curve and its limiting integer height by

```math
\begin{aligned}
T_M(t)&=t+i\bigl(h_M(t)+h_M(t+2)\bigr),\\
b(n)&=h(n)+h(n+2)=\tau(n)+\tau(n+2)-4.
\end{aligned}
```

Nonnegativity means the sum is zero exactly when both heights vanish. Thus

```math
\boxed{b(n)=0\quad\Longleftrightarrow\quad(n,n+2)\text{ is a twin-prime pair}.}
```

At finite stages the contacts are candidate pairs. If n>=2 and
n+2<(M+1)^2, both endpoints of any contact are in the certified region and
are prime. Composite-filter steps cannot remove new integer pair contacts,
because they remove no new integer endpoint contacts.

The activation preserves earlier prime contacts. Correspondence with a
particular sieve stream must still respect its head/domain; the curve retains
history as well as future candidates. After filter2, candidate pairs above2
are consecutive survivors since their intervening integer is even.

None of these equivalences guarantees infinitely many zeros of b, a zero in
a specified interval, or a quantitative separator-distribution bound. The
substantial research objective is to control the locations and joint survival
of zero heights, particularly in moving certified windows. Divisor-count and
factorization identities are established elementary ingredients, not claims
of new number-theoretic discoveries.

## Related work in this repository

- [Continuous-contact research directions](../../candidates/continuous-contact-research-directions.md):
  height, pair-height and damped-count interfaces and open estimates.
- [Safe-Window Certification](safe-window-two-gaps-certify-twin-primes.md):
  the corresponding prime-head square boundary.
- [2-Focused Alternation Law](two-focused-alternation-law.md) and
  [2-Focused Bad-Separator Bound](two-focused-bad-separator-deletion-bound.md):
  ordered separator structure and deterministic pair-survival bounds.
- [ManimGL illustrations](../../presentations/continuous-complex-sieve/README.md):
  existing prime-filter and pair-filter animations; these do not yet animate
  the all-integer recurrence.

The finite Fourier and roots-of-unity ingredients are described in the
[University of Amsterdam discrete Fourier series notes](https://staff.fnwi.uva.nl/r.vandenboomgaard/SignalProcessing/FrequencyDomain/DTP.html)
and the [Archive of Formal Proofs roots-of-unity development](https://www.isa-afp.org/browser_info/current/AFP/Gauss_Sums/document.pdf).
These references support the ingredients; the activated construction is
derived here rather than attributed to those sources.
