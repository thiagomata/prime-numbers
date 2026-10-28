# Uniform Continuous Divisor Sieve

**Status:** Mathematical definitions and proofs. No formal implementation is
required for this research note. Distribution estimates and twin-prime
existence beyond the stated equivalences remain open.

The arithmetic and Fourier ingredients below are classical. The activated
interpolation is presented here without a historical-priority claim; see the
[attribution inventory](research/continuous-sieve-attribution.md) for the
distinction between original sources, modern references and unresolved priority.

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

### 1.1 Equivalent sine-wave construction

The selective wave is a normalized **Fejér kernel**, named for Lipót Fejér;
see his [1900 paper, *Sur les fonctions bornées et intégrables*](https://history-of-approximation-theory.com/fpapers/fej1OCR.pdf).
With the convention mathcal F_m(theta)=m^(-1)|sum exp(i r theta)|^2,
our W_m(t)=mathcal F_m(2 pi t/m)/m. A modern formula with its normalization
specified appears in [MIT's Lecture16, Proposition173](https://ocw.mit.edu/courses/18-102-introduction-to-functional-analysis-spring-2021/eb44436072623f60f8f416875d4b2c11_MIT18_102s21_lec16.pdf).
The sine quotient and Fourier coefficients are classical kernel formulas;
the activation is an additional choice of this interpolation.

The construction can be understood directly as adding continuous waves,
without first calculating divisor counts. Begin with

```math
F_1(t)=t+i\sin^2(\pi t),
```

which touches the real axis at every integer. For each next integer m>=2,
define the continuous wave

```math
W_m(t)=
\begin{cases}
\displaystyle\left(\frac{\sin(\pi t)}{m\sin(\pi t/m)}\right)^2,
&t\notin m\mathbb Z,\\[6pt]
1,&t\in m\mathbb Z.
\end{cases}
```

The apparent holes at multiples of m are removable. At t=km, the limit of
the unsquared ratio is (-1)^(k(m-1)); its square is one. This proves that
the specified value makes W_m continuous. Away from those points it is a
quotient of continuous functions with nonzero denominator.

At integer inputs the sine numerator vanishes. If the integer is not a
multiple of m, its denominator is nonzero, giving zero. At multiples, the
extension gives one. With the same activation a_m as above, the update is

```math
\boxed{F_m(t)=F_{m-1}(t)+i a_m(t)W_m(t).}
```

It adds zero at every nonmultiple integer and one at every integer multiple
strictly after m. All real inputs t<=m, including the filter's own integer,
remain unchanged by that step. For filter 4 the changes are:

| Integer input | Added imaginary height |
|---|---:|
| 4 | 0: its own value is protected |
| 5, 6, 7 | 0 |
| 8 | 1 |
| 9, 10, 11 | 0 |
| 12 | 1 |

In particular, adding filter 4 leaves the existing heights at 6 and 10
unchanged, although earlier filters already rejected those inputs. The height
at 8 rises again because 8 is a later multiple of 4.

The exact zero-change statement concerns nonmultiple integer inputs. Between
integers the new wave may change the curve. A continuous wave cannot be
positive at an isolated multiple while vanishing at every neighboring real
input. Squaring also keeps each contribution nonnegative, preventing accidental
cancellation with the baseline or other filters.

This is the same function as the complex-exponential detector, not a different
sieve. The geometric-sum identity gives, away from removable points,

```math
\begin{aligned}
D_m(t)&=e^{\pi i(m-1)t/m}
\frac{\sin(\pi t)}{m\sin(\pi t/m)},\\
|D_m(t)|^2&=W_m(t).
\end{aligned}
```

The phase has modulus one. Continuity extends the equality to multiples of m.
There is also a finite cosine-sum form without any quotients or holes:

```math
\boxed{
W_m(t)=\frac1{m^2}\left[
m+2\sum_{r=1}^{m-1}(m-r)\cos\left(\frac{2\pi rt}{m}\right)
\right].
}
```

To derive it, expand the squared modulus of D_m as a double sum. Difference
zero occurs m times; differences r and -r each occur m-r times. Pairing the
two exponentials yields the displayed cosine term. Thus a selective wave is
generally a combination of harmonics, not one ordinary sine wave. For example,
W_2(t)=cos^2(pi t/2).

The divisor-count heights derived next are a consequence of summing these
waves at integer inputs, not a prerequisite or a replacement definition.

### 1.2 From the recurrence to one infinite sum

Every step adds a wave; it does not transform or rescale the previous curve.
We can therefore substitute the recurrence repeatedly:

```math
\begin{aligned}
F_2(t)&=F_1(t)+i a_2(t)W_2(t),\\
F_3(t)&=F_1(t)+i a_2(t)W_2(t)+i a_3(t)W_3(t).
\end{aligned}
```

For any integer M>=2, sum the differences F_m-F_(m-1) from m=2 to M.
Every intermediate F_m cancels, leaving F_M-F_1. This telescoping gives

```math
\begin{aligned}
F_M(t)-F_1(t)
&=\sum_{m=2}^{M}\bigl(F_m(t)-F_{m-1}(t)\bigr)\\
&=i\sum_{m=2}^{M}a_m(t)W_m(t).
\end{aligned}
```

```math
\boxed{F_M(t)=t+i\left[\sin^2(\pi t)+\sum_{m=2}^{M}a_m(t)W_m(t)\right].}
```

The same expression holds at M=1 with an empty sum. Extending the index to
infinity defines the completed curve directly, without computing its earlier
stages:

```math
\boxed{
F(t)=t+i\left[\sin^2(\pi t)+
\sum_{m=2}^{\infty}a_m(t)W_m(t)\right].
}
```

Despite the infinite notation, every fixed input has only finitely many
active waves: a_m(t)=0 whenever m>=t. At t=12.5, for example, only filters
2 through 12 can contribute. At t=12, even filter12 is inactive, so only
filters2 through11 can contribute.

This also justifies the limit rigorously. On any bounded interval [2,B],
all terms indexed m>=B vanish identically. Once M>=ceil(B), F_M and F agree
everywhere in that interval. Consequently the sequence converges uniformly
on each compact interval by eventual exact equality, and F is continuous
there as a finite sum of continuous functions. No global uniform-convergence
claim on the entire unbounded domain is needed.

If H(t) denotes the real expression inside the brackets, the completed
twin-contact curve is

```math
\begin{aligned}
H(t)&=\sin^2(\pi t)+\sum_{m=2}^{\infty}a_m(t)W_m(t),\\
T(t)&=t+i\bigl(H(t)+H(t+2)\bigr).
\end{aligned}
```

H is the same limiting height denoted h below. For t in [2,B], the shifted
height uses inputs through B+2, so enough finite stages must cover that larger
interval when drawing T. These formulas retain t as the real coordinate;
adding the complex values F(t) and F(t+2) instead would change that coordinate.

The recurrence and the infinite sum are two descriptions of the same
construction. The recurrence exposes each filter's effect; the sum describes
the completed function. Neither form alone supplies a new estimate for the
number or spacing of prime or twin-prime contacts.

## 2. Integer height is a truncated proper-divisor count

This uses classical roots-of-unity orthogonality. Rodrigo Raya and Manuel
Eberl's [AFP development](https://isa-afp.org/browser_info/current/AFP/Gauss_Sums/document.pdf),
section4, gives a modern formal proof (`unity-root-sum`); they are credited
for that formalization, rather than identified as the original discoverers.

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
This is the classical divisor function d(n) of
[NIST DLMF section27.2](https://dlmf.nist.gov/27.2).
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

This is the usual sieve-of-Eratosthenes rejection rule expressed in contact
language; a modern reference is [NIST DLMF section27.18](https://dlmf.nist.gov/27.18).
The change in representation does not make the underlying sieve fact new.

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

The certification uses the classical square-root divisor test, also stated
in [NIST DLMF section27.18](https://dlmf.nist.gov/27.18).

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

The input is the standard divisor-product formula
[DLMF27.3.5](https://dlmf.nist.gov/27.3.E5); the following cases translate
that classical formula into height notation.

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

This is the classical parity property of the divisor function, also immediate
from [its product formula](https://dlmf.nist.gov/27.3.E5). No first-discoverer
attribution has been established in this source audit.

Divisors normally pair as d and n/d. A divisor pairs with itself precisely
when d^2=n. Therefore tau(n) is odd exactly when n is a perfect square.
Subtracting two does not change parity:

```math
\boxed{h(n)\text{ is odd}\quad\Longleftrightarrow\quad n\text{ is a square},
\qquad n\ge2.}
```

## 9. Coprime multiplication law

This rewrites the classical multiplicativity of the divisor function;
see [DLMF27.3.1](https://dlmf.nist.gov/27.3.E1). The reference is a modern
exposition, not a historical-priority attribution to its authors.

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

For finite Fourier inversion, see Rein van den Boomgaard's
[University of Amsterdam notes](https://staff.fnwi.uva.nl/r.vandenboomgaard/SignalProcessing/FrequencyDomain/DTP.html).
For the formal roots-of-unity ingredient, see Raya and Eberl's AFP development
cited above. These modern expositions complement the original Fejér source;
none is being credited with this specific activated sieve. The priority of
that combination has not been determined. Full source roles and the remaining
article audit are recorded in the [attribution inventory](research/continuous-sieve-attribution.md).
