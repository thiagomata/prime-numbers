# Continuous-wave twin analysis

**Status:** Mathematical investigation of the
[five wave-based research directions](../../../candidates/continuous-wave-twin-research.md).
Each numbered result below has a proof. Quantitative distribution claims are
not implied by changing representation, and no literature-wide novelty claim
is made. This note does not require a formal-code companion.

## Setup

For integer m>=2 and real t, we use a normalized **Fejér kernel**.
Credit Lipót Fejér's
[1900 paper](https://history-of-approximation-theory.com/fpapers/fej1OCR.pdf);
[MIT's modern Lecture16, Proposition173](https://ocw.mit.edu/courses/18-102-introduction-to-functional-analysis-spring-2021/eb44436072623f60f8f416875d4b2c11_MIT18_102s21_lec16.pdf)
provides a kernel convention. Our normalization has peak one.

```math
W_m(t)=\left|\frac1m\sum_{r=0}^{m-1}e^{2\pi irt/m}\right|^2.
```

It is continuous, nonnegative and at most one, by the triangle inequality.
At integer n it is one if m divides n and zero otherwise, by the finite
geometric-sum identity. For sieve inputs t>=2 use

```math
a_m(t)=\min(1,\max(0,t-m)),\qquad
h_M(t)=\sin^2(\pi t)+\sum_{m=2}^{M}a_m(t)W_m(t).
```

Empty sums/products below use M=1. The complete height h is the locally
finite limit, and h(n)=tau(n)-2 at integer n>=2, where tau counts positive
divisors. These definitions and elementary facts are developed in
[Uniform Continuous Divisor Sieve](../uniform-continuous-divisor-sieve.md).
The roots-of-unity ingredient is classical; Raya and Eberl's
[AFP formalization](https://isa-afp.org/browser_info/current/AFP/Gauss_Sums/document.pdf),
section4, is a modern reference, not an original-discovery attribution.

## 1. Exact folding of translated waves

This identity follows directly from the classical kernel coefficients and
roots-of-unity orthogonality. The proof below checks it in this normalization;
the first historical source for this exact form has not been established.

For integers m>=2, k>=1 and every real t,

```math
\boxed{\sum_{j=0}^{k-1}W_{km}(t+jm)=W_m(t).}
```

This combines a translated group of higher-period waves into a lower-period
wave without approximation. It concerns bare waves, before activation.

### Proof

Expanding a squared modulus and grouping the differences between its two
indices gives the finite Fourier expression

```math
W_N(t)=\frac1{N^2}\sum_{|r|<N}(N-|r|)e^{2\pi irt/N}.
```

Indeed, the difference r occurs N-|r| times in the double sum. Set N=km.
Translating by jm multiplies the term indexed r by exp(2 pi i rj/k).
The sum over j is k when k divides r and zero otherwise. Only r=ks remain:

```math
\begin{aligned}
\sum_{j=0}^{k-1}W_{km}(t+jm)
&=\frac1{k^2m^2}\sum_{|s|<m}k(km-k|s|)e^{2\pi ist/m}\\
&=\frac1{m^2}\sum_{|s|<m}(m-|s|)e^{2\pi ist/m}\\
&=W_m(t).
\end{aligned}
```

Every sum is finite, and the wave definition has no singular points, so the
identity holds for all real t, including multiples of m.

### Twin-shift instance and its scope

Taking k=2 and m=2 gives

```math
W_4(t)+W_4(t+2)=W_2(t).
```

This directly combines the two bare endpoint waves of filter4. More general
folding groups require the shifts0,m,...,(k-1)m. Those shifts are not present
for every filter in a fixed-distance-two pair sieve. Thus the theorem supplies
an exact translated-wave simplification, not an automatic compression of the
whole all-integer filter sum. Activations require a separate boundary analysis.

## 2. Exact activation correction for the filter-4 pair wave

This is algebraic bookkeeping for the chosen activation, rather than a
claim that a new general Fourier theorem has been discovered. Priority of
this particular activated formula is unestablished.

For t>=2, define

```math
\begin{aligned}
V_4(t)&=a_4(t)W_4(t)+a_4(t+2)W_4(t+2),\\
C_4(t)&=(1-a_4(t))W_4(t)+(1-a_4(t+2))W_4(t+2).
\end{aligned}
```

Then the exact activated identity is

```math
\boxed{V_4(t)=W_2(t)-C_4(t),\qquad 0\le V_4(t)\le W_2(t).}
```

The correction is nonnegative and vanishes throughout t>=5. It need not
vanish in the earlier activation region, although it can vanish at isolated
earlier inputs.

### Proof and boundary examples

Add and subtract the unactivated wave sum from section1:

```math
\begin{aligned}
V_4(t)
&=W_4(t)+W_4(t+2)\\
&\quad-\bigl[(1-a_4(t))W_4(t)+(1-a_4(t+2))W_4(t+2)\bigr]\\
&=W_2(t)-C_4(t).
\end{aligned}
```

Since 0<=a_4<=1 and both waves are nonnegative, C_4>=0 and V_4>=0.
For t>=5, a_4(t)=a_4(t+2)=1, proving the tail identity. On [2,5) the
explicit correction must be retained. At integer inputs,

```math
C_4(2)=1,\qquad C_4(4)=1,\qquad C_4(3)=0.
```

For example, at t=2 the endpoint4 is protected by its own activation, so
V_4(2)=0 even though W_2(2)=1. At t=3 both bare waves vanish and equality
holds early. The tail threshold is a sufficient interval guarantee, not a
necessary condition for every individual equality.

This gives a valid way to simplify the activated pair wave: one coarser wave
plus an explicit term confined to a bounded initial interval. It does not
justify ignoring initial values or changing the retained prime contacts.

## 3. A bounded continuous twin amplitude

At integer inputs this uses the standard sieve product of complementary
rejection indicators. Expanding that product is inclusion-exclusion; see
Paul Pollack's [modern exposition](https://www.pollack-math.net/NABDofficial.pdf),
Chapter6, section3.1, Theorem6.1. That reference supports the classical
indicator mechanism, not authorship of this continuous interpolation.

For integer M>=1 and real t>=2, define

```math
\begin{aligned}
J_m(t)&=1-a_m(t)W_m(t),\\
A_M(t)&=\cos^2(\pi t)\prod_{m=2}^{M}J_m(t)J_m(t+2),\\
\widetilde T_M(t)&=t+i\bigl(1-A_M(t)\bigr).
\end{aligned}
```

Then A_M is continuous and lies in [0,1]. At an integer n>=2 it equals one
exactly when h_M(n)=h_M(n+2)=0, and otherwise equals zero. The curve
has no noninteger real-axis contacts. Consequently this is a continuous
candidate-pair curve whose imaginary height is bounded between zero and one.
Its completed locally finite product has contacts precisely at twin starts.

### Proof

Both a_m and W_m lie in [0,1], so 0<=J_m<=1. Finite products and the cosine
factor preserve these bounds and continuity.

At integer n, a_m(n)W_m(n) is one exactly when m is a proper divisor of n
that has already been installed. It is zero otherwise. Thus J_m(n) is zero
for a discovered proper divisor and one otherwise. The two endpoint factors
in the product make A_M(n) zero if either endpoint is rejected, and one if
neither is. Also cos^2(pi n)=1.

For noninteger t, cos^2(pi t)<1. Every other factor is at most one, so
A_M(t)<1 and 1-A_M(t)>0. Hence no noninteger can be a contact of the curve.
It is the unit level of A_M, not the zero level of A_M, that selects pairs.

For t in a fixed bounded interval [2,B], all factors indexed m>=B+2 equal
one: both arguments t and t+2 are at or below m, so both activations vanish.
The product therefore stabilizes exactly on that interval once sufficiently
many filters are installed. Its infinite form

```math
A(t)=\cos^2(\pi t)\prod_{m=2}^{\infty}J_m(t)J_m(t+2)
```

is locally finite and continuous, with 0<=A<=1. Every composite integer
endpoint eventually supplies a zero factor, whereas every prime endpoint
keeps every factor one. Therefore

```math
\boxed{A(t)=1\quad\Longleftrightarrow\quad
t\text{ and }t+2\text{ are prime},\qquad t\ge2.}
```

### What this changes

At integer starts, the imaginary height of the bounded curve is exactly zero
or one, instead of counting all discovered divisors. Both choices have the
same pair contacts at every stage. Their shapes between integers differ.
This removes large composite heights from the visualization but gives no
automatic estimate for how often the unit level is attained.

Source roles and outstanding priority questions are collected in the
[attribution inventory](continuous-sieve-attribution.md).
