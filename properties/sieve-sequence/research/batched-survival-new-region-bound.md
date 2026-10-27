# New-Region Bound for Square-Destination Transitions

**Status:** Mathematical research proofs for actual sieve transitions; no
Stainless verification, empirical check, historical novelty, or infinite
survival theorem is claimed.

## Setup

Let p>=5 be prime, s its next prime, q the first prime strictly above p squared,
and t the first prime strictly above s squared. Thus t>=q. Install all old
filters below s and put

```math
\begin{aligned}
M_s&=\prod_{r<s,\ r\ \mathrm{prime}}r,\\
W_u&=\{a\in\mathbb Z:u\le a\le u^2-3\},\\
\mathcal A_{s,u}&=\{a\in W_u:\gcd(a(a+2),M_s)=1\},\\
h_{s,u}(a)&=|\{r:s\le r<u,\ r\ \mathrm{prime},\ r\mid a(a+2)\}|,\\
w(h)&=1-h+\binom h2-\binom h3,\\
\mathcal V_{\rm new}&=\mathcal A_{s,t}\setminus\mathcal A_{s,q},\\
N&=\sum_{a\in\mathcal V_{\rm new}}w(h_{s,t}(a)).
\end{aligned}
```

This N is the signed fresh-region contribution in the
[exact transport identity](batched-survival-propagation-check-2026-10-27.md).
We bound its negative part without assuming fresh candidates contribute
positively. Binomial coefficients with lower index exceeding the nonnegative
upper index are zero.

## 1. Exact Fresh-Region Geometry

If t=q, both windows coincide and N=0. Otherwise the windows still overlap:
Bertrand's postulate gives s<2p and t<2s squared, whence

```math
\begin{aligned}
t&<2s^2<8p^2<p^4-2<q^2-2 \qquad(p\ge5),\\
W_t\setminus W_q&=\{q^2-2,\ldots,t^2-3\},\\
D:=|W_t\setminus W_q|&=t^2-q^2.
\end{aligned}
```

The old acceptance condition is identical in both windows. Therefore fresh
accepted starts are precisely the old-accepted starts in this interval.
Bertrand's postulate is classical; see Pollack,
[*Not Always Buried Deep*, Theorem 3.6](https://www.pollack-math.net/NABDofficial.pdf#page=102).

Both endpoints of an accepted pair avoid2 and3, so its start is5 modulo6.
Since q and t are primes greater than3, their squares are1 modulo6. The
fresh interval starts at5 modulo6 and its length D is a multiple of6.
Consequently, writing C_new for the number of fresh accepted starts,

```math
0\le C_{\rm new}=|\mathcal V_{\rm new}|\le D/6.
```

This includes the empty flat case t=q. No assumption of uniform placement
under the remaining old filters is used.

## 2. A Uniform Bound on Each Cubic Weight

Every fresh endpoint n is smaller than t squared. Bertrand and s>=7 give

```math
n<t^2<4s^4<s^5.
```

All its prime factors are at least s, by old acceptance. Five distinct batch
prime factors would have product at least s to the fifth power, which is
impossible. Each endpoint thus contributes at most four distinct batch
primes, and h_{s,t}(a)<=8. For integer h>=1 the cubic identity gives

```math
\begin{aligned}
w(0)&=1,& w(h)&=-\binom{h-1}3\quad(h\ge1),\\
-35=-\binom73&\le w(h)\le1\quad(0\le h\le8).
\end{aligned}
```

Summing over the actual fresh candidates proves

```math
\begin{aligned}
-35C_{\rm new}&\le N\le C_{\rm new},\\
\boxed{|N|&\le\frac{35}{6}(t^2-q^2).}
\end{aligned}
```

This finite bound holds at every prime starting head p>=5. It bounds an
actual signed sieve term, but does not establish N>=0 or a positive total
survival certificate. Comparison with the density benchmark requires a
separate bound on the growth of the destination window.

## 3. Actual New-Region Cost Is Eventually Small Relative to F

We use the classical quantitative prime number theorem of de la Vallée
Poussin (1899), in the form stated in
[Evertse's Leiden notes, equation (1.1), printed p.53](https://pub.math.leidenuniv.nl/~evertsejh/ant18-1.pdf#page=3):

```math
\pi(x)=\operatorname{Li}(x)+O\!\left(xe^{-c\sqrt{\log x}}\right),
\qquad c>0.
```

Here pi counts primes at most x and Li(x) is the integral from2 to x of
1/log(u). Fix any real m>0 and set d=x/(log x)^m. Subtracting the estimates
at x+d and x gives

```math
\begin{aligned}
\operatorname{Li}(x+d)-\operatorname{Li}(x)
 &=\int_x^{x+d}\frac{du}{\log u}
 \sim\frac{x}{(\log x)^{m+1}},\\
xe^{-c\sqrt{\log x}}
 &=o\!\left(\frac{x}{(\log x)^{m+1}}\right),\\
\pi(x+d)-\pi(x)&>0\quad\text{for all sufficiently large }x.
\end{aligned}
```

The error at x+d has the same upper order as the displayed error at x.
Thus the first prime strictly greater than x lies at most d beyond x,
eventually. This interval consequence is derived from the quoted theorem;
it does not assume a conjectural short-interval prime estimate. Applying it
at p and s squared, and using s<2p, proves

```math
\begin{aligned}
s-p&=O\!\left(\frac p{(\log p)^m}\right),\\
t-s^2&=O\!\left(\frac {p^2}{(\log p)^m}\right),\\
0\le t-q&\le(s^2-p^2)+(t-s^2)
 =O\!\left(\frac {p^2}{(\log p)^m}\right),\\
D=(t-q)(t+q)&=O\!\left(\frac {p^4}{(\log p)^m}\right).
\end{aligned}
```

The last line uses q<2p squared and t<8p squared from Bertrand. Constants
and sufficiently-large thresholds may depend on the chosen fixed m.
No explicit numerical threshold is asserted.

The [density main-term proof](batched-survival-analytic-main-and-error.md),
together with the scale calculation in the
[component bounds](batched-survival-component-bounds.md), gives a constant
c_0>0 such that F(p,q)>=c_0 p^4/(log p)^2 at every sufficiently large prime
head. Combining it with Section2 yields, for every fixed m>2,

```math
\boxed{\frac{|N|}{F(p,q)}
 =O\!\left((\log p)^{2-m}\right)\longrightarrow0.}
```

This is an unconditional eventual property of the actual signed N for these
square destinations. It controls negative contributions as well as positive
ones. Qualitative PNT alone would only give D=o(p^4), which does not suffice
for this comparison. Neither N>=0 nor a lower bound for actual L is inferred.

## 4. What This Proves About the Actual Margin

The [component bounds](batched-survival-component-bounds.md) prove
R<=R_cap and R_cap/F->0. The
[filtered shared-region bound](batched-survival-filtered-shot-bound.md) proves
J>=0 and J/F->0. Define the nonnegative combined loss budget

```math
\begin{aligned}
B(p)&:=|N|+R_{\mathrm{cap}}+J,\\
\frac{B(p)}{F(p,q)}&\longrightarrow0.
\end{aligned}
```

This eventual estimate is proved for actual square transitions. It is not a
new hypothesis. The exact transport identity, together with A>=0, gives

```math
\begin{aligned}
L(s,t)&=L(p,q)+A+N-R-J\\
      &\ge L(p,q)+A-B(p)\\
      &\ge L(p,q)-B(p).
\end{aligned}
```

Thus for every fixed eta>0, there is a threshold beyond which every prime
starting head satisfies the following conditional implication:

```math
\boxed{L(p,q)\ge\eta F(p,q)
\quad\Longrightarrow\quad
L(s,t)\ge\frac\eta2 F(p,q)>0.}
```

Indeed, beyond that threshold B(p)<=eta F(p,q)/2. A positive cubic
certificate forces at least one actual surviving pair in the destination
window. The conclusion measures the next margin in the OLD benchmark
F(p,q), not in F(s,t).

The premise L(p,q)>=eta F(p,q) has not been proved for all sufficiently late
actual sequences. Also this conclusion does not reproduce that premise:
the guaranteed reserve has halved. We cannot iterate it indefinitely with
the same fixed eta and threshold. An estimate that retains or replenishes a
positive reserve, or another argument that forces repeated positive
certificates, remains missing.

For a logical illustration only, consider the scalar sequences

```math
F_k=k^4,\qquad U_k=k^4\sin(\log k).
```

The derivative of x^4 sin(log x) is
x^3(4 sin(log x)+cos(log x)), so |U_{k+1}-U_k|=O(k^3)=o(F_k).
Nevertheless U_k takes both positive and negative values arbitrarily far
out: the corresponding sign intervals in x have lengths tending to infinity
and therefore contain integers. Small relative changes alone permit sign
changes. These are abstract scalar sequences, not sieve sequences or an
arithmetic counterexample to survival.

The progress is a proved bound on all three possible loss terms, giving a
conditional next-step positivity result. An eventual positive actual-margin
invariant, an explicit onset, and infinite twin-prime survival remain open.

The subsequent [block-reserve proof](batched-survival-block-reserve.md)
controls the actual cumulative budget across roughly p/(log p)^4 consecutive
heads: its ratio to the starting F tends to zero. A fixed positive starting
reserve then protects the whole finite block. That starting premise and its
renewal remain open; this strengthens one-step control without closing the
infinite argument.
