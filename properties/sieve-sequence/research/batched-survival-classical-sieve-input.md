# Classical Lower-Sieve Inputs for Batched Candidate Counts

**Status:** Mathematical research audit of classical sieve inputs. No
historical novelty, empirical check, Stainless verification, or twin-prime
survival theorem is claimed. Candidate counts before the remaining batch
filters are distinct from final survivors.

## 1. Exact Arithmetic Setup and a Weighted Remainder Bound

Let p>=5 and q>p be prime, and use the integer start window

```math
W_q=\{q,\ldots,q^2-3\},\qquad H=q^2-q-2.
```

Consider the indexed sequence A={a(a+2):a in W_q}. The values increase
strictly with a, so its cardinality is exactly H. This cardinality, not the
largest polynomial value, is the size parameter in the sieve. For z>=3 put

```math
\begin{aligned}
P(z)&=\prod_{\ell<z,\ \ell\ \mathrm{prime}}\ell,\\
\mathcal C_q(z)&=|\{a\in W_q:\gcd(a(a+2),P(z))=1\}|.
\end{aligned}
```

The actual old candidate count is C(p,q)=mathcal C_q(p). Both endpoints
survive primes below p; since filter2 is installed, the intervening integer
does not survive, so these are actual old-sequence 2-gaps. Final survivors
would instead be mathcal C_q(q).

For squarefree d let rho(d) be the number of residue classes a modulo d
with d dividing a(a+2). The local roots and CRT give

```math
\rho(2)=1,\qquad \rho(\ell)=2\quad(\ell>2\text{ prime}),\qquad
\rho(d)=\prod_{\ell\mid d}\rho(\ell).
```

In particular rho(ell)<ell, including at2 and3; there is no fixed local
obstruction. Counting these classes in H consecutive integers gives

```math
|A_d|=H\frac{\rho(d)}d+R_d,\qquad |R_d|\le\rho(d),
```

where A_d is the subsequence divisible by d. This is exact interval
arithmetic, without random-placement assumptions.

Write omega(d) for the number of distinct prime factors, mu for the Möbius
function and tau_14 for the number of ordered factorizations into14 positive
integer factors. For squarefree d, tau_14(d)=14 to the power omega(d).
For real D>=2, the harmonic-sum bound therefore gives

```math
\begin{aligned}
\sum_{d<D}\mu^2(d)7^{\omega(d)}|R_d|
&\le\sum_{n\le D}\tau_{14}(n)\\
&\le D\left(\sum_{n\le D}\frac1n\right)^{13}
 \le D(1+\log D)^{13}.
\end{aligned}
```

To see the middle inequality, choose the first13 factors of an ordered
factorization. The number of choices for the last is at most D divided
by their product; extending each of the first13 sums to all integers at
most D only increases this upper bound.

For sufficiently large H, set D=H/(log H)^20, so D>=2. Then

```math
\boxed{\sum_{d<D}\mu^2(d)7^{\omega(d)}|R_d|
       =O\!\left(\frac H{(\log H)^7}\right).}
```

This also bounds the sum restricted to d dividing P(z), and dominates the
same sum with4 instead of7. It is stronger than the dimension-two weighted
remainder requirement H/(log H)^3 appearing in
[Franze, equations (2)–(4)](https://arxiv.org/pdf/1012.3809#page=1).
Only squarefree d enter this requirement; their multiplicative density is
1/f(d)=rho(d)/d.

The sieve dimension is2. Mertens' weighted-prime estimate yields

```math
\sum_{\ell<y}\frac{\rho(\ell)\log\ell}{\ell}
 =2\log y+O(1).
```

The prime2 changes only a constant. See Pollack,
[*Not Always Buried Deep*, Section4.1, equations (3.22)–(3.25)](https://www.pollack-math.net/NABDofficial.pdf#page=109)
for the classical weighted estimate. The corresponding product is

```math
V(z)=\prod_{\ell<z}\left(1-\frac{\rho(\ell)}\ell\right)
 =\frac12\prod_{3\le\ell<z}\left(1-\frac2\ell\right)
 \asymp\frac1{(\log z)^2}.
```

The product estimate and its Mertens attribution are derived in the
[component analysis](batched-survival-component-bounds.md). These verified
inputs permit a classical lower-sieve test, but the setup alone gives no
positive lower bound: the sieve's cutoff and positivity threshold must still
be checked.

## 2. The Uniform Dimension-Two Product Condition

The local density g(ell)=rho(ell)/ell lies between0 and2/3 at every prime.
The product estimate can be sharpened to the uniform form needed by the
classical lower sieve. Factoring odd-prime terms as in the component analysis,

```math
\begin{aligned}
V(y)&=2C_2(y)\left(\prod_{\ell<y}(1-1/\ell)\right)^2,\\
C_2(y)&=\prod_{3\le\ell<y}\left(1-\frac1{(\ell-1)^2}\right).
\end{aligned}
```

The positive product C_2(y) has limit C_2>0 and relative tail O(1/y): its
logarithmic tail is bounded by a constant times the tail of sum n to the
power -2. Mertens' product estimate with relative error O(1/log y) gives

```math
V(y)=\frac c{(\log y)^2}\left(1+O(1/\log y)\right),\qquad c>0.
```

See [Pollack, Theorem3.15](https://www.pollack-math.net/NABDofficial.pdf#page=110)
for that classical Mertens error term. For sufficiently large w and all z>=w,
the two relative errors are uniformly O(1/log w). Hence

```math
\frac{V(w)}{V(z)}
=\left(\frac{\log z}{\log w}\right)^2
 \left(1+O(1/\log w)\right).
```

Choosing a larger fixed constant L absorbs the bounded range of smaller w.
Thus, for every 2<=w<=z,

```math
\boxed{\prod_{w\le\ell<z}\left(1-\frac{\rho(\ell)}\ell\right)^{-1}
\le\left(\frac{\log z}{\log w}\right)^2
   \left(1+\frac L{\log w}\right).}
```

When w=2 the product identity uses V(2)=1; the earlier half-product formula
was only used for larger arguments. The finite prime2 adjustment is absorbed
by L. This verifies a uniform dimension condition rather than inferring it
from an unqualified asymptotic at one point.

## 3. The Standard Lower-Sieve Threshold at a Square Jump

Use the dimension-two Diamond–Halberstam–Richert lower sieve, with cardinality
H, the verified multiplicative density and level D. A convenient statement is
[Franze–Kao, Section4, equation (20)](https://arxiv.org/pdf/1812.11280#page=5):

```math
\begin{aligned}
\mathcal C_q(z)
&\ge HV(z)\left\{f_2(u)-O\!\left(
 \frac{(\log\log D)^2}{(\log D)^{1/6}}\right)\right\}
 -2\mathcal R_4(D,z),\\
u&=\frac{\log D}{\log z},\qquad 2\le z\le D,\\
\mathcal R_4(D,z)
&=\sum_{\substack{d<D\\d\mid P(z)}}4^{\omega(d)}|R_d|.
\end{aligned}
```

Their following initial conditions give f_2(u)=0 for u<=beta_2; it is
positive above that sifting limit. The reported DHR value is beta_2
approximately4.266; see [Franze, Table1](https://arxiv.org/pdf/1012.3809#page=2).
These classical inputs are not new sieve theorems. Sections1–2 check their
arithmetic hypotheses for this interval sequence. Our weighted remainder
satisfies mathcal R_4=o(HV(z)) over the cutoffs used below: its bound
H/log^7 H is smaller than H/log^2 H, and V(z) is at least a positive
constant times1/log squared H for z<=D.

For q the first prime above p squared, Bertrand gives H comparable to p
to the fourth power, and therefore

```math
\frac{\log D}{\log p}
=\frac{\log H-20\log\log H}{\log p}\longrightarrow4<\beta_2.
```

The standard lower main term for the actual old candidates C(p,q) is thus
zero at all sufficiently large square-rule heads. This theorem, with this
verified level and cutoff, supplies no positive candidate lower bound.
It does not show that candidates are absent, that another estimate cannot
work, or that batching is invalid.

For final survivors the sieve cutoff would be z=q. Whenever q tends to
infinity, H=q squared-q-2 gives

```math
\frac{\log D}{\log q}\longrightarrow2<\beta_2.
```

Thus merely changing the power relating q to p does not make this standard
final-sifting lower bound positive. A longer jump may improve the supply
before the batch while still leaving its final survivors uncontrolled.
No optimality or impossibility theorem for other sieve weights or additional
arithmetic information is asserted.

## 4. An Unconditional Old-Candidate Bound for a Longer Jump

Choose q to be the first prime greater than p to the power11/5. This is a
different destination rule, permitted by the general batch construction.
Bertrand gives

```math
p^{11/5}<q<2p^{11/5},\qquad
H\asymp p^{22/5},\qquad
\frac{\log D}{\log p}\longrightarrow\frac{22}5>\beta_2.
```

The previously verified DHR inputs apply to this interval too. The lower
function f_2 is continuous and positive at22/5; its continuity is also stated
in [Franze–Kao, Section4, equation (25)](https://arxiv.org/pdf/1812.11280#page=5).
The error in the lower-sieve formula and the normalized remainder vanish.
Consequently every sufficiently large starting prime satisfies

```math
\begin{aligned}
C(p,q)=\mathcal C_q(p)
&\ge\frac12 f_2(22/5)\,H V(p),\\
\boxed{C(p,q)&\gg\frac H{(\log p)^2}
             \asymp\frac{p^{22/5}}{(\log p)^2}.}
\end{aligned}
```

This is an actual local candidate lower bound, not a substitution of
complete-period density for the local count and not a hypothesis about
future stages. It is a classical DHR consequence in the present notation;
no priority claim is made. Its constants and onset are not evaluated here.

These candidates have survived only primes below p. They still face the
batch from p up to q. Section3 explains why the same theorem gives no
positive final-survivor bound at cutoff q. No estimate of T_33 or positive
reserve after that batch follows from candidate abundance alone.

## 5. The Longer Rule Also Has a Positive Cubic Density Factor

The new candidate bound does not require a certificate, but its compatibility
with the cubic benchmark can be checked independently. Put

```math
\lambda(p,q)=\sum_{p\le\ell<q}\frac2\ell,
\qquad B_3(p,q)=1-e_1+e_2-e_3.
```

Mertens' reciprocal-prime estimate and the new destination rule give

```math
\lambda(p,q)
=2\log\left(\frac{\log q}{\log p}\right)+O(1/\log p)
\longrightarrow\lambda_0=2\log(11/5).
```

The [fixed-degree symmetric-sum argument](batched-survival-analytic-main-and-error.md#6-high-order-moments-require-nonnegligible-density-corrections)
applies here as well: the load stays bounded and the largest term2/ell tends
to zero. Thus e_k tends to lambda_0 to the kth power divided by k factorial
for each fixed k, and B_3 tends to

```math
b(\lambda_0),\qquad b(v)=1-v+v^2/2-v^3/6.
```

To prove this cubic polynomial is positive without a decimal approximation,
set t=3/8 and use the convergent logarithm series:

```math
\begin{aligned}
\log(11/5)
 &=2\sum_{j\ge0}\frac{t^{2j+1}}{2j+1}
 <2t+\frac{2t^3}{3(1-t^2)}=\frac{87}{110},\\
\lambda_0&<\frac{87}{55}<\frac{19}{12},\\
b'(v)&=-\frac{(v-1)^2+1}{2}<0,\\
\lim_{p\to\infty}B_3(p,q)
 &=b(\lambda_0)>b(19/12)=\frac{89}{10368}>0.
\end{aligned}
```

Hence the actual old-candidate lower bound from Section4 and eventual
positivity of the cubic density term coexist for exponent11/5. The earlier
finite sufficient condition lambda<=3/2 does not apply to this load; the
argument above is a separate asymptotic proof.

The corresponding density benchmark H*V(p)*B_3 is eventually positive, but
is still not a lower bound for L_3 or final survivors. Nor have the square-rule
H_8/F decay, J_5=0, or retention estimates been established for this new
destination. A complete proof would need additional local control through
the remaining filters. This note supplies a genuine classical input and a
compatible benchmark, not that missing control.

## 6. A Large Subfamily with an Already-Prime Endpoint

There is a stronger classical input than an unrestricted old-candidate
count. The Introduction of Matomäki and Zuniga–Alterman,
[*Weighted sieves with switching* (2025)](https://www.cambridge.org/core/journals/mathematical-proceedings-of-the-cambridge-philosophical-society/article/weighted-sieves-with-switching/986429394BA969687D48224E177E2F1C),
states the following consequence of the linear sieve and the
Bombieri–Vinogradov theorem. For fixed sufficiently small epsilon>0,

```math
\begin{aligned}
Q_\varepsilon(X)
&=|\{r\le X:r\text{ prime},\ \gcd(r+2,P(X^{1/4-\varepsilon}))=1\}|,\\
Q_\varepsilon(X)&\ge c_\varepsilon\frac X{(\log X)^2},
\qquad c_\varepsilon>0,
\end{aligned}
```

for sufficiently large X. We use this published consequence directly;
we do not infer an additional divisor-weighted remainder estimate from
unweighted prime-distribution bounds. Here X is the physical prime range,
not the cardinality of the prime sequence. This is a classical input, with
no claim of historical novelty or Stainless verification.

Keep the exponent11/5 destination and choose

```math
\begin{aligned}
X&=q^2-3,\qquad \varepsilon=1/100,\qquad z=X^{6/25},\\
\mathcal B(p,q)
&=\{a\in W_q:a\text{ prime},\ \gcd(a+2,P(z))=1\}.
\end{aligned}
```

The upper start boundary agrees exactly with X. Removing starts below q
from the cumulative count removes at most q integers. Since
q=o(X/(log X)^2), the published bound gives, eventually,

```math
\begin{aligned}
|\mathcal B(p,q)|
&\ge Q_{1/100}(X)-q\\
&\ge c_{1/100}\frac X{(\log X)^2}-q\\
&\ge\frac{c_{1/100}}2\frac X{(\log X)^2}
\gg\frac H{(\log p)^2}.
\end{aligned}
```

Bertrand's bounds on q imply

```math
\frac{\log z}{\log p}\longrightarrow\frac{132}{125}>1,
\qquad
\frac{\log z}{\log q}\longrightarrow\frac{12}{25}<1.
```

Thus p<z<q eventually. Each first endpoint is prime and at least q;
its partner has no prime factor below z. Consequently these are actual
old-sequence 2-gaps, and they remain candidates after all prime filters
below z have been applied. In particular the prime2 causes no exceptional
obstruction: every such first endpoint is odd and its partner is odd too.

The remaining difficulty is confined to the second endpoint. Write
Omega(n) for the number of prime factors counted with multiplicity. Every
factor of a+2 is at least z, and eventually

```math
z^5=X^{6/5}>X+2\ge a+2,
\qquad \Omega(a+2)\le4.
```

If a+2 is composite, its least prime factor ell satisfies

```math
z\le\ell\le\sqrt{a+2}<q.
```

So a remaining filter can still reject the pair. The partner is either
prime or composite with two to four factors; the bound does not establish
that any partner is prime. It supplies an actual large family surviving
an initial segment of the batch, not a positive final count or a positive
cubic certificate. Square-rule transport estimates are not imported.

The abundance argument also works for any fixed exponent alpha>2, with
q the first prime above p to the power alpha. Choose a fixed
0<epsilon<min(1/20,1/4-1/(2alpha)) and put z=X^(1/4-epsilon).
Then p<z<q eventually, and the same subtraction proves a subfamily of size
at least a positive constant times H/log squared p. The extra epsilon<1/20
also gives z^5>X+2 eventually. Constants and thresholds depend on alpha
and epsilon. This does not reach the boundary alpha=2 or final cutoff q.

## 7. A Rough Chen Family at the Original Square Jump

A stronger classical input reaches the original square destination and
reduces the composite partners to two prime factors. Green and Tao,
[*Restriction theory of the Selberg sieve, with applications* (2006),
Section6, Theorem6.1](https://www.numdam.org/item/10.5802/jtnb.538.pdf#page=20),
use a strengthened Chen condition: a is prime and a+2 is either prime or
a product uv of primes with u,v>a^(3/11). They state a lower bound
c_1 X/log squared X for such a in (X/2,X], for every sufficiently large
integer X. Their discussion credits Chen's theorem and attributes this
roughness improvement to Iwaniec's Rutgers1996 course notes. Footnote3
explicitly asserts the dyadic adaptation of that input; we use their
published formulation, without supplying a proof of Chen's theorem here.

Return to q the first prime above p squared and put

```math
X=q^2-3,\qquad Z=(X/2)^{3/11}.
```

For q>3, the whole interval (X/2,X] lies inside W_q. Define

```math
\begin{aligned}
\mathcal G(p,q)=\{a\in(X/2,X]:\;&a\text{ prime},\\
&a+2\text{ prime, or }a+2=uv
 \text{ with primes }Z<u<v\}.
\end{aligned}
```

The source theorem gives factors greater than a^(3/11)>Z. Its only
possible partners not admitted by this definition are prime squares.
There are at most floor(sqrt(X+2)) such squares, even before requiring
that their value minus2 be prime. Since sqrt(X+2)=o(X/log squared X),

```math
\begin{aligned}
|\mathcal G(p,q)|
&\ge c_1\frac X{(\log X)^2}-\lfloor\sqrt{X+2}\rfloor\\
&\ge\frac{c_1}{2}\frac X{(\log X)^2}
 \gg\frac H{(\log p)^2}
 \asymp\frac{p^4}{(\log p)^2}
\end{aligned}
```

eventually. Bertrand's bounds p^2<q<2p^2 give

```math
\frac{\log Z}{\log p}\longrightarrow\frac{12}{11}>1,
\qquad
\frac{\log Z}{\log q}\longrightarrow\frac6{11}<1.
```

Hence p<Z<q eventually. Each first endpoint is prime and greater than q.
Each partner is prime and greater than Z, or has exactly two distinct
prime factors greater than Z. Both endpoints therefore avoid every prime
below Z. These are actual old-sequence 2-gaps surviving that initial part
of the batch, with the quantitative lower bound above. This establishes
old-candidate abundance at the square rule using stronger classical
arithmetic; the zero main term of the particular DHR estimate in Section3
remains a true limitation of that estimate, not of candidate existence.

If the partner is composite, its smaller factor still satisfies

```math
Z<u<\sqrt{a+2}<q.
```

Thus a remaining filter can reject it. No positive count of prime partners,
final twins, or cubic certificates follows. In particular, under a
hypothetical last twin start L, taking X/2>L would make every member of
this large family have a semiprime partner. That outcome is compatible
with the quoted theorem; it is not a contradiction.

The same argument permits any fixed destination exponent alpha>11/6:
log Z/log p tends to6alpha/11>1, and the lower count remains a positive
constant times H/log squared p. For exponent11/5 specifically, Z>X^(6/25)
eventually, so this family lies inside the prime-endpoint family of
Section6. This is a direct stronger existence input, not an estimate
subtracting all composite cases from the earlier family. No square-rule
transport theorem is being extended to other exponents.

The remaining arithmetic task is to separate prime partners from these
two-prime products. Neither the positive total nor the reduction from four
factors to two supplies that separation. These are consequences of cited
classical results in this window, with no historical novelty or Stainless
verification claimed.

## 8. A Uniform Upper Bound for Each First Rejection Prime

The remaining semiprimes admit an actual uniform upper bound, rather than
only a definition of the count needed for subtraction. Retain the square
rule and Section7's family G. Set Y=X+2=q^2-1. For an odd prime
Z<u<sqrt(Y), write

```math
\begin{aligned}
N&=\lfloor Y/u\rfloor,\qquad F_u(v)=v(uv-2),\\
M_u&=|\{v\le N:v\text{ prime},\ uv-2\text{ prime}\}|.
\end{aligned}
```

This counts a larger set than the relevant partners: it does not require
v>u or uv-2>X/2. Upper-bounding it is therefore legitimate. Uniformity
in u matters; a theorem stated only for one fixed progression would not
justify summing over a growing set of factors.

We use the coefficient-uniform restriction estimate of
[Green–Tao, Theorem1.1](https://www.numdam.org/item/10.5802/jtnb.538.pdf#page=5).
For k integer linear forms with nonzero discriminant, admissible local
densities and coefficients bounded in absolute value by N, it bounds the
L^4 norm of their prime-product exponential sum by a constant times
the singular series times N^(3/4)/(log N)^k. The constant for fixed k
is independent of the forms. This is a classical external input.

Here N>=u, since u^2<Y. Thus the coefficients 1,0,u,-2 are within N
for large Y, including the negative intercept. The determinant is -2.
The fraction gamma_u(ell) of residues avoiding F_u(v)=0 at a prime ell is

```math
\gamma_u(2)=\frac12,\qquad
\gamma_u(u)=1-\frac1u,\qquad
\gamma_u(\ell)=1-\frac2\ell\quad(\ell>2,\ \ell\ne u).
```

All are positive. The singular series is therefore bounded uniformly:

```math
\mathfrak S_u
=\prod_\ell\frac{\gamma_u(\ell)}{(1-1/\ell)^2}
=2C_2\frac{u-1}{u-2}\le4C_2.
```

To pass from the cited Fourier bound to a count, let T_u be the source's
set of v<=N for which F_u(v) is a product of two primes, let m_u=|T_u|,
and put E_u(theta)=sum over v in T_u of exp(2 pi i v theta). The prime
pairs counted by M_u form a subset of T_u; equality is not assumed for
exceptional v=1. On the arc |theta|<=1/(6N), each summand has real part
at least1/2. With normalized Lebesgue measure on R/Z, the cited estimate
gives an absolute constant A such that

```math
\begin{aligned}
\|E_u\|_4
&\ge\frac{m_u}{2}(3N)^{-1/4},\\
\|E_u\|_4
&\le A\mathfrak S_u\frac{N^{3/4}}{(\log N)^2},\\
M_u\le m_u
&\le 2\,3^{1/4}A\mathfrak S_u\frac N{(\log N)^2}.
\end{aligned}
```

Uniformly for u<sqrt(Y), N>sqrt(Y)-1, while N<=Y/u. Hence
log N>=(log Y)/3 for all sufficiently large Y, independently of u.
Absorbing the preceding absolute constants into K yields

```math
\boxed{M_u\le K\frac{Y}{u(\log Y)^2}
\quad\text{for every prime }Z<u<\sqrt Y.}
```

For any set J of possible least factors, define

```math
B(J)=|\{a\in\mathcal G(p,q):a+2=uv,
                  \ Z<u<v\text{ prime},\ u\in J\}|.
```

Unique factorization assigns exactly one smaller factor to each such
partner. Thus this is a bound on actual first rejections:

```math
\boxed{B(J)\le\frac{KY}{(\log Y)^2}
             \sum_{\substack{u\in J\\Z<u<\sqrt Y\\u\text{ prime}}}\frac1u.}
```

The first endpoint is prime and greater than q, so u really is the first
filter that rejects this member of G. A larger factor v may also lie
below q, but it does not create a second first rejection.

For the whole factor range, Mertens' reciprocal-prime estimate gives

```math
\sum_{Z<u<\sqrt Y}\frac1u
=\log\left(\frac{\log\sqrt Y}{\log Z}\right)+o(1)
\longrightarrow\log(11/6).
```

Consequently the total semiprime-partner count is O(Y/log squared Y).
This is the same scale as the guaranteed family, not a smaller-order
error. No upper constant below the Chen lower constant has been proved;
this bound alone therefore leaves the all-semiprime possibility open.
It is neither an asymptotic formula nor a positive final-twin bound.

## 9. Late Filters Cannot Exhaust the Family by First Rejections

The uniform estimate has a quantitative consequence even without a
favourable whole-range constant comparison. There is a fixed exponent
eta<1 such that at least half the family G is outside the class first
rejected by primes in [q^eta,q). Those remaining members may be twins or
semiprimes rejected earlier. This is a restriction on rejection locations,
not additional survival through the earlier filters.

Since X/Y tends to1, Section7 supplies a fixed c_*>0 such that, eventually,

```math
|\mathcal G(p,q)|\ge c_*\frac Y{(\log Y)^2}.
```

Fix eta in (6/11,1). Then q^eta>Z eventually. Write
B_late=B([q^eta,q)) using Section8's smaller-factor definition. Mertens'
reciprocal-prime estimate and the uniform bound give

```math
\begin{aligned}
\sum_{q^\eta\le u<q}\frac1u
 &=\log(1/\eta)+o(1),\\
B_{\mathrm{late}}
 &\le\frac{KY}{(\log Y)^2}
             \bigl(\log(1/\eta)+o(1)\bigr).
\end{aligned}
```

The sums are over primes. Extending the actual least-factor ceiling
sqrt(Y) to q only increases this upper bound. The constant K is independent
of eta. Choose eta once, sufficiently close to1, so that
K log(1/eta)<c_*/4. Then take q sufficiently large, depending on that
fixed choice, that the absolute K-weighted error is less than c_*/4.
It follows that

```math
\begin{aligned}
B_{\mathrm{late}}
 &\le\frac{c_*}{2}\frac Y{(\log Y)^2}
 \le\frac12|\mathcal G(p,q)|,\\
|\mathcal G(p,q)|-B_{\mathrm{late}}
 &\ge\frac12|\mathcal G(p,q)|
 \ge\frac{c_*}{2}\frac Y{(\log Y)^2}.
\end{aligned}
```

Each member in this complement has a prime partner, or has a semiprime
partner whose smaller factor is less than q^eta. A larger factor may still
belong to the late band, but that candidate was already rejected by its
smaller factor. It must not be counted as first rejected a second time.

Under a hypothetical last twin start L, for X/2>L all complement members
must take the early-semiprime alternative. At least half of this large
family must then be first rejected before q^eta. This is compatible with
the hypothesis; no lower bound on candidates actually reaching q^eta has
been established. In particular, the complement above is not a surviving
reserve at that cutoff.

The band is narrow in its logarithmic exponent, not in additive length:
for fixed eta<1, q-q^eta is asymptotic to q. No numerical eta or onset is
computed here. The result is a consequence of the cited classical inputs
and the uniform bound, not a twin-prime theorem or a claimed new classical
sieve result.

## 10. Keeping the Exact Product Window in the Upper Bound

Section8 deliberately counted all v<=N. The actual semiprime partners
also require v>u and X/2<uv-2<=X. These restrictions can be retained
without translating the polynomial coefficients outside the cited theorem's
uniform range. The device is a finite interval kernel and Hölder's
inequality, applied to the same unshifted exponential sum.

Keep Y=X+2, Z<u<sqrt(Y) and N=floor(Y/u). The exact integer interval is

```math
\begin{aligned}
\ell_u&=\max\left\{u+1,
           \left\lfloor\frac{X/2+2}{u}\right\rfloor+1\right\},\\
\mathcal I_u&=\{v\in\mathbb Z:\ell_u\le v\le N\},\\
L_u&=\max\{0,N-\ell_u+1\},\\
b_u&=|\{v\in\mathcal I_u:v\text{ prime},\ uv-2\text{ prime}\}|.
\end{aligned}
```

Here b_u counts precisely the members of G with smaller factor u.
If L_u=0 the count is zero. Since (X/2+2)/u=(Y/2+1)/u>=N/2,

```math
\left\lfloor\frac{X/2+2}{u}\right\rfloor
 \ge\lfloor N/2\rfloor,
\qquad L_u\le\lceil N/2\rceil.
```

For any nonempty consecutive integer interval I of length L, put
D_I(theta)=sum over v in I of exp(2 pi i v theta). Translation changes
only a unit-modulus factor, so the geometric-series estimate gives

```math
|D_I(\theta)|\le\min\{L,(2\|\theta\|)^{-1}\},
```

where the double bars denote distance to the nearest integer and the
second term is interpreted as infinite at integers. Integrating over the
circle, split at distance 1/(2L):

```math
\begin{aligned}
\|D_I\|_{4/3}^{4/3}
&\le2\int_0^{1/2}\min\{L,(2t)^{-1}\}^{4/3}\,dt\\
&=4L^{1/3}-3\le4L^{1/3},\\
\|D_I\|_{4/3}&\le2\sqrt2\,L^{1/4}.
\end{aligned}
```

Use the same T_u, E_u, singular series and absolute constant A as in
Section8. Orthogonality selects the interval exactly; Hölder with conjugate
exponents4 and4/3 then gives

```math
\begin{aligned}
b_u
&\le|T_u\cap\mathcal I_u|
 =\int_{\mathbb R/\mathbb Z}E_u(\theta)
                  \overline{D_{\mathcal I_u}(\theta)}\,d\theta\\
&\le\|E_u\|_4\|D_{\mathcal I_u}\|_{4/3}\\
&\le2\sqrt2\,A\mathfrak S_u
            \frac{N^{3/4}L_u^{1/4}}{(\log N)^2}.
\end{aligned}
```

Only the kernel is translated. The forms v and uv-2 and their coefficient
bounds are unchanged, so this still uses the checked coefficient-uniform
classical input rather than an unproved shifted-interval version.

This improves the particular upper expression displayed in Section8 before
its constants and logarithms were coarsened. For nonempty intervals, the
ratio of the two expressions is bounded by

```math
\frac{2\sqrt2\,A\mathfrak S_u N^{3/4}L_u^{1/4}/(\log N)^2}
     {2\,3^{1/4}A\mathfrak S_u N/(\log N)^2}
\le\frac{\sqrt2}{3^{1/4}}
     \left(\frac{\lceil N/2\rceil}{N}\right)^{1/4}
\longrightarrow\left(\frac23\right)^{1/4}<1.
```

The limiting comparison is uniform over the allowed u because
N>sqrt(Y)-1. Empty intervals contribute zero. This is a constant-factor
sharpening of these upper-bound expressions, not a proved reduction of
the actual semiprime population or an optimality statement.

The ambient factor N^(3/4) remains when the interval is very short; the
bound is not linear in L_u. The total bound still has scale Y/log squared Y,
and no comparison below the Chen lower constant follows. This finite
physical prime-form estimate does not establish the separate open CRT
spectral-localization bound, positive final twins or reserve renewal.

## 11. A Direct Interval Upper Sieve Removes the Ambient Range

An upper sieve applied directly to the exact integer interval gives a
stronger dependence on its length. There are absolute constants C_0 and
Y_0 such that every member of the square-rule family with Y>=Y_0 and
every allowed prime Z<u<sqrt(Y) satisfies

```math
\boxed{b_u\le C_0\Phi(L_u),\qquad
\Phi(L)=\begin{cases}
0,&L=0,\\
L/(1+\log L)^2,&L\ge1.
\end{cases}}
```

Here the interval and b_u are exactly those of Section10. The estimate is
uniform even when an interval is empty or much shorter than N. This
statement concerns this sufficiently-large-Y family; no common onset for
unrelated polynomial intervals is asserted.

Write L=L_u>0. Sieve all integers v in the interval, with indexed values
F_u(v)=v(uv-2). These values are strictly increasing on the positive
interval, so the size parameter is its cardinality L, not the largest
polynomial value. For squarefree d the number of local roots is

```math
\rho_u(2)=1,\qquad \rho_u(u)=1,\qquad
\rho_u(\ell)=2\quad(\ell>2,\ \ell\ne u),
\qquad \rho_u(d)=\prod_{\ell\mid d}\rho_u(\ell).
```

At u the second linear factor equals -2; at any other odd prime the
two roots are distinct. Counting these residue classes in any L consecutive
integers gives a position-independent remainder:

```math
|A_d|=L\frac{\rho_u(d)}d+R_u(d),\qquad
|R_u(d)|\le\rho_u(d)\le2^{\omega(d)}.
```

Thus the elementary divisor-sum proof from Section1 applies with L in
place of H, uniformly over u and interval position:

```math
\sum_{d<D}\mu^2(d)7^{\omega(d)}|R_u(d)|
\le D(1+\log D)^{13}.
```

The uniform dimension condition is also checked, rather than assumed.
The densities equal the generic dimension-two densities of Section2
except at u, where the density is smaller. Every inverse product over
prime factors is consequently at most its generic counterpart, with the
same absolute dimension-condition constant. This remains true when u
varies with Y.

For sufficiently large L choose

```math
D=\frac L{(\log L)^{20}},\qquad z=L^{1/3},\qquad
s=\frac{\log D}{\log z}
 =3-60\frac{\log\log L}{\log L}\longrightarrow3.
```

There is an absolute L_0 such that 2<=z<=D and s stays in a fixed
neighbourhood of3 for L>=L_0. Uniformly over the allowed factor primes,

```math
L\le N\le Y/u<Y/Z,\qquad
\frac{Z^4}{Y}\longrightarrow\infty,
\qquad z<(Y/Z)^{1/3}<Z<u
```

once Y is sufficiently large. Hence the sieve product V_u(z) equals
the generic V(z), which is comparable to1/log squared L. The actual
prime pairs have v>u>z and uv-2>X/2>z, so every one survives this
integer upper sieve.

Apply the classical DHR upper estimate as stated in
[Franze–Kao, Section4, equation (19)](https://arxiv.org/pdf/1812.11280#page=5).
Its size is L and its checked dimension is2. With
R_4 the weighted remainder restricted to d dividing P(z),

```math
\begin{aligned}
b_u&\le S(A,z)\\
&\le LV(z)\left\{F_2(s)+O\!\left(
   \frac{(\log\log D)^2}{(\log D)^{1/6}}\right)\right\}
   +2R_4,\\
R_4&=O\!\left(\frac L{(\log L)^7}\right).
\end{aligned}
```

The function F_2 is bounded near3, and the product/error constants above
are independent of u and interval position. Therefore there is an absolute
C such that b_u<=C L/(log L)^2 for every L>=L_0 in this large-Y family.
This is a consequence of the classical upper sieve and the explicitly
checked local arithmetic, not a new sieve theorem or a Stainless result.

For 1<=L<L_0, the trivial count b_u<=L applies. Enlarging one absolute
constant absorbs this finite range and replaces log L by1+log L; for
example take C_0 at least both4C and (1+log L_0)^2, increasing L_0
to at least e if necessary. Empty intervals contribute zero. This proves
the displayed all-length bound with absolute constants and a single
sufficiently-large-Y threshold.

The ambient N^(3/4) factor of Section10 has been removed. No numerical
constant or onset is evaluated, and the bound does not by itself place
the total semiprime contribution below the Chen lower supply. Final twin
survival, reserve renewal and the separate CRT spectral problem remain open.

## 12. Summing the Actual Interval-Length Weights

The sum of the weights in Section11 can be evaluated, including the short
intervals near the largest possible smaller factor. The result is about
the known interval lengths, not an asymptotic formula for rejected pairs:

```math
\begin{aligned}
\sum_{\substack{Z<u<\sqrt Y\\u\text{ prime}}}\Phi(L_u)
 &=\bigl(\kappa_{\mathrm{geom}}+o(1)\bigr)
                  \frac Y{(\log Y)^2},\\
\kappa_{\mathrm{geom}}
 &=\frac5{16}+\frac12\log\frac83.
\end{aligned}
```

All variables retain the square-rule definitions. Split the primes into
the bulk Z<u<=sqrt(Y)/2 and the edge sqrt(Y)/2<u<sqrt(Y).
In the bulk, u^2<=Y/4 makes the product-window lower endpoint dominate
the condition v>u. The exact floors therefore give

```math
\begin{aligned}
L_u&=\left\lfloor\frac Yu\right\rfloor
       -\left\lfloor\frac{Y/2+1}{u}\right\rfloor
     =\frac{Y}{2u}+O(1),\\
L_u&\ge\sqrt Y-2,\\
\Phi(L_u)
 &=\left(1+O\!\left(\frac1{\log Y}\right)\right)
       \frac{Y}{2u\,\log^2(Y/u)}.
\end{aligned}
```

These errors are uniform over the whole bulk: its lengths are at least
of order sqrt(Y), and log(Y/u) is comparable to log Y.

For the edge, all lengths satisfy 0<=L_u<=2sqrt(Y). Extending Phi to
real L>=1, its derivative has sign log L-1. Consequently

```math
\max_{\substack{L\in\mathbb Z\\0\le L\le2\sqrt Y}}\Phi(L)
\le\max\{1,\Phi(2\sqrt Y)\}
=O\!\left(\frac{\sqrt Y}{(\log Y)^2}\right).
```

The maximum includes the separately defined value Phi(0)=0. Chebyshev's
upper bound gives O(sqrt(Y)/log Y) edge primes, so their total weight is
O(Y/(log Y)^3), negligible on the asserted scale. This explicitly covers
tiny and empty intervals, where replacing log L by log Y would be invalid.
See [Pollack, Theorem3.5](https://www.pollack-math.net/NABDofficial.pdf#page=102)
for the classical prime-count bound.

For the bulk, apply Mertens' reciprocal-prime estimate and partial
summation with t=log u/log Y. Its remainder is o(1) uniformly for endpoints
at least Z, since Z tends to infinity. The normalized test function
(1-t)^(-2) and its derivative are bounded on the fixed exponent range.
Thus the limits log Z/log Y to3/11 and
log(sqrt(Y)/2)/log Y to1/2 give

```math
\begin{aligned}
\sum_{\substack{Z<u\le\sqrt Y/2\\u\text{ prime}}}
       \frac1{u\,\log^2(Y/u)}
 &=\frac1{(\log Y)^2}
     \left\{\int_{3/11}^{1/2}\frac{dt}{t(1-t)^2}+o(1)\right\},\\
\int_{3/11}^{1/2}\frac{dt}{t(1-t)^2}
 &=\left[\log\frac t{1-t}+\frac1{1-t}\right]_{3/11}^{1/2}
  =\frac58+\log\frac83.
\end{aligned}
```

The classical reciprocal-prime estimate is stated in
[Pollack, Theorem3.14](https://www.pollack-math.net/NABDofficial.pdf#page=110).
Multiplying the bulk expression by Y/2 and adding the negligible edge
proves the displayed weight-sum asymptotic.

Unique smaller factors now give an actual global upper bound:

```math
B_{\mathrm{total}}
=\sum_{\substack{Z<u<\sqrt Y\\u\text{ prime}}}b_u
\le C_0\bigl(\kappa_{\mathrm{geom}}+o(1)\bigr)
              \frac Y{(\log Y)^2}.
```

The known geometric coefficient is separated from the uncomputed sieve
constant C_0. The rejected-pair count itself has not been shown asymptotic
to this expression. No inequality putting C_0*kappa_geom below the Chen
lower constant is established, and earlier-rejection alternatives remain
possible. This computes actual geometric weights rather than assuming
local full-cycle density; it supplies no final twin or novelty claim.

## 13. An Explicit Leading Rejection Coefficient

The unspecified constant needed for all interval lengths can be removed
from the leading total. On the bulk intervals, a stronger admissible cutoff
also lets us use an explicit initial value of the classical sieve function.
The result, with all square-rule definitions unchanged, is

```math
\boxed{B_{\mathrm{total}}
\le\left(16C_2\kappa_{\mathrm{geom}}+o(1)\right)
           \frac Y{(\log Y)^2},\qquad
16C_2\kappa_{\mathrm{geom}}
=C_2\left(5+8\log\frac83\right).}
```

Here C_2 is the positive twin-prime product defined in Section2. This
is an upper bound for the semiprime rejections, not their asymptotic count.
It is a mathematical consequence of classical sieve estimates; no Stainless
verification or optimality of this coefficient is claimed.

Use the bulk Z<u<=sqrt(Y)/2 from Section12. Its lengths satisfy
L=L_u>=sqrt(Y)-2, so D and z tend to infinity uniformly with the choices:

```math
D=\frac L{(\log L)^{20}},\qquad z=\sqrt D,\qquad
s=\frac{\log D}{\log z}=2,\qquad
\frac{\log D}{\log L}=1-o(1).
```

For sufficiently large Y, 2<=z<=D. The local root counts, the uniform
dimension condition and the weighted remainder bound of Section11 still
apply. Unlike its earlier cutoff, z can exceed u. That changes precisely
one factor in the product:

```math
\frac{V_u(z)}{V(z)}=
\begin{cases}
1,&z\le u,\\
\dfrac{u-1}{u-2},&z>u,
\end{cases}
\qquad \frac{V_u(z)}{V(z)}=1+O(1/Z).
```

The correction is uniform because u>Z tends to infinity. Actual prime
pairs are still counted among the sifted values. Indeed, the exact lower
endpoint of the product interval gives v>(Y/2+1)/u>=sqrt(Y), whereas
L<Y/Z=O(Y^(8/11)) gives z<=sqrt(L)=O(Y^(4/11))=o(sqrt(Y)). The other
prime value uv-2 exceeds X/2 and hence z as well. This explicitly checks
prime survival for the new cutoff, without assuming z<u.

The DHR initial-value normalization is stated in
[Booker–Browning, Theorem3.1, equations (7)–(8)](https://arxiv.org/pdf/1511.00601#page=5).
In dimension two it gives

```math
\sigma_2(t)=\frac{t^2}{8e^{2\gamma}}\quad(0<t\le2),\qquad
F_2(2)=\frac1{\sigma_2(2)}=2e^{2\gamma}.
```

The initial range of F_2 includes2 since alpha_2>beta_2>2. Combining
Section2's product identity with Mertens' product theorem, with gamma
Euler's constant, now keeps the leading constant explicitly:

```math
\begin{aligned}
V(z)&=\frac{2C_2e^{-2\gamma}+o(1)}{(\log z)^2},\\
V_u(z)&=\frac{8C_2e^{-2\gamma}+o(1)}{(\log D)^2}.
\end{aligned}
```

Apply [Franze–Kao, equation (19)](https://arxiv.org/pdf/1812.11280#page=5)
at s=2. Its error tends to zero uniformly, and the checked remainder
is O(L/(log L)^7). Therefore, throughout the bulk,

```math
\begin{aligned}
b_u&\le LV_u(z)\left(F_2(2)+o(1)\right)
                 +O\!\left(\frac L{(\log L)^7}\right)\\
&\le\left(16C_2+o(1)\right)\frac L{(\log L)^2}.
\end{aligned}
```

Uniformity matters when summing this inequality. Since all bulk lengths
tend to infinity uniformly, L/(log L)^2=(1+o(1))*Phi(L) uniformly there.
Section12 evaluates their sum with coefficient kappa_geom. On the edge,
the older all-length bound remains sufficient: its total is
C_0*O(Y/(log Y)^3), so the finite-small-length enlargement of C_0
does not enter the leading coefficient. Adding bulk and edge proves the
boxed inequality.

The coefficient multiplying C_2 is approximately12.8466, just an evaluation
of 5+8log(8/3). The rough Chen input supplies a positive lower constant
c_* but has not supplied a comparison c_*>16C_2*kappa_geom. Consequently
subtracting this upper bound from that lower bound has not proved a
positive twin count. The new result makes the quantitative comparison
explicit; it does not establish that the comparison succeeds.

## 14. The Limit of Cutoff Tuning in This Upper Bound

Changing only the cutoff cannot improve Section13's leading coefficient
within the same DHR upper expression and remainder level. This identifies
a limit of this particular estimate, rather than a lower bound for actual
rejections or an optimality statement about other sieve methods.

Keep D=L/(log L)^20 and choose a fixed s>=1 with z=D^(1/s). Only
cutoffs satisfying 2<=z<=D and preserving the actual prime pairs are
admissible. The product calculation from Section13 then makes the leading
local upper-expression coefficient

```math
\begin{aligned}
K(s)&=2C_2e^{-2\gamma}s^2F_2(s),\\
K(s)&\ge16C_2,\\
K(s)&=16C_2\quad(1\le s\le2),\qquad
K(s)>16C_2\quad(s>2).
\end{aligned}
```

To prove the assertion about the classical function, put Q(s)=s^2F_2(s).
The initial values in [Booker–Browning, Theorem3.1](https://arxiv.org/pdf/1511.00601#page=5)
give Q(s)=8e^(2gamma) for 0<s<=2. Write alpha=alpha_2>2. On
2<s<=alpha, F_2(s)=1/sigma_2(s); the differential equation gives

```math
\begin{aligned}
H(s)&=s^{-2}\sigma_2(s),\qquad Q(s)=\frac1{H(s)},\\
H'(s)&=-2s^{-3}\sigma_2(s-2)<0,\\
Q'(s)&=\frac{2\sigma_2(s-2)}{s^3H(s)^2}>0.
\end{aligned}
```

The signs are justified by the source's positivity: F_2 decreases to1,
so it is positive, and sigma_2=1/F_2 is positive throughout its initial
range. Both s and s-2 lie in that range here. Beyond alpha, the other
DHR equation yields

```math
Q'(s)=2s f_2(s-1)\ge0\qquad(s>\alpha).
```

Indeed, f_2 is initially zero and is nondecreasing. Continuity at2 and
alpha joins the three ranges. Q is constant up to2, increases strictly
between2 and alpha, and never decreases thereafter. This proves the
displayed bound and its equality range without numerical integration.
These differential identities and monotonicity statements are also recorded
in [Franze–Kao, equations (21)–(24)](https://arxiv.org/pdf/1812.11280#page=5).

For a fixed admissible s, Mertens' product estimate and the same uniform
exceptional-u correction give

```math
LV_u(z)F_2(s)
=\left(K(s)+o(1)\right)\frac L{(\log L)^2}.
```

Thus summing these bulk upper expressions cannot produce a coefficient
below16C_2*kappa_geom by selecting a different fixed s. Section13's s=2
is admissible and attains this floor. Some other s in the formal equality
range may be inadmissible because a prime value falls below z; no such
cutoff is used. This result concerns leading expressions at the specified
level only. Different remainder levels, sieve weights, arithmetic estimates
or treatments of the rejection correlations are outside its scope, and
no lower bound on the actual semiprime population follows. This is an
application of classical sieve-function identities, not a new sieve theorem
or a Stainless-verified property.

## 15. A Quantitative Obstruction to This Subtraction

The entire rough Chen family has an upper bound smaller than Section13's
rejection allowance. Therefore evaluating a better lower constant for that
same family cannot make this particular subtraction prove survival. This
is a limitation of the displayed rejection estimate, not evidence that all
candidates are actually rejected.

With G denoting the exact family mathcal G of Section7, the claim is

```math
\begin{aligned}
|\mathcal G|&\le\left(5C_2+o(1)\right)\frac Y{(\log Y)^2},\\
5C_2&<16C_2\kappa_{\mathrm{geom}}
 =C_2\left(5+8\log\frac83\right).
\end{aligned}
```

The coefficient5 is a convenient upper bound, not a claim of optimality.
We derive it using the classical prime-conditioned linear sieve. The
needed statement and function normalization appear in
[Tao's Supplement5, Theorem2, equations (10) and (12)](https://terrytao.wordpress.com/2015/01/29/254a-supplement-5-the-linear-sieve-and-chens-theorem-optional/).
The same source's equation (39) supplies the Bombieri–Vinogradov remainder
input for the shifted prime problem.

Let Lambda be the von Mangoldt function and give each integer a the
nonnegative weight Lambda(a) when X/2<a<=X, and zero otherwise. Its
unsifted main mass is X/2. For each odd prime ell forbid a congruent to
-2 modulo ell; the event at2 is empty. The multiplicative density is

```math
g(2)=0,\qquad g(\ell)=\frac1{\ell-1}\quad(\ell>2),\qquad
g(\ell)=\frac1\ell+O(1/\ell^2),\quad 0\le g(\ell)\le\frac12.
```

For odd squarefree d, the residue -2 is coprime to d. The classical
Bombieri–Vinogradov estimate consequently gives the required local formula
and summed remainders at the fixed level below:

```math
\begin{aligned}
\sum_{\substack{X/2<a\le X\\a\equiv-2\pmod d}}\Lambda(a)
 &=g(d)\frac X2+r_d,\\
D&=(X/2)^{2/5},\qquad
\sum_{\substack{d\le D\\d\text{ odd, squarefree}}}|r_d|
 =O\!\left(\frac X{(\log X)^{10}}\right).
\end{aligned}
```

Even d have empty events, density zero and remainder zero. The source's
interval is [X/2,X-2]; changing to (X/2,X] changes O(1) endpoints.
Each remainder changes by O(log X), so their total change is at most
O(D log X), still negligible relative to X/log X. Its stated fixed-power
distribution range includes this D: any fixed exponent strictly between
2/5 and1/2 suffices. No distribution claim about prime pairs is assumed.

Write W(z) for the product of1-g(ell). The product identity of Section2
and Mertens' theorem evaluate its normalization:

```math
\begin{aligned}
W(z)&=\prod_{3\le\ell<z}\frac{\ell-2}{\ell-1}
 =\frac{V(z)}{\prod_{\ell<z}(1-1/\ell)}
 =\frac{2C_2e^{-\gamma}+o(1)}{\log z},\\
s&=\frac{\log D}{\log Z}=\frac{22}{15}\in(1,3),\qquad
F_1(s)=\frac{2e^\gamma}{s}.
\end{aligned}
```

Here Z=(X/2)^(3/11), so s is exactly constant. The prime density bounds
above meet the linear-sieve hypotheses. Applying its upper estimate gives

```math
\begin{aligned}
S_\Lambda
&:=\sum_{X/2<a\le X}\Lambda(a)
     \prod_{\substack{3\le\ell<Z\\\ell\text{ prime}}}
            1_{\ell\nmid a+2}\\
&\le\left(F_1(s)+o(1)\right)\frac X2 W(Z)
       +o\!\left(\frac X{\log X}\right)\\
&\le\left(2C_2+o(1)\right)\frac X{\log D}
 =\left(5C_2+o(1)\right)\frac X{\log X}.
\end{aligned}
```

To justify the o(1) from the source's arbitrarily small sieve error,
fix its error parameter first, take X sufficiently large, then take
the resulting upper limit as that parameter tends to zero. No uniform
onset for a moving error parameter is assumed.

Every member a of G is prime, has a+2 free of primes below Z, and
contributes Lambda(a)=log a>=log(X/2) to this nonnegative sum. Extra
prime powers in S_Lambda only enlarge the upper bound. Hence

```math
|\mathcal G|\log(X/2)\le S_\Lambda,\qquad
|\mathcal G|\le\left(5C_2+o(1)\right)\frac Y{(\log Y)^2},
```

using Y=X+2. This proves the claimed whole-family bound.

In particular, any constant c_* for an eventual lower bound
|G|>=c_*Y/(log Y)^2 must satisfy c_*<=5C_2. Section13's allowance has
strictly larger coefficient. Thus the lower expression obtained by
subtracting that allowance cannot have a positive leading coefficient,
even with the largest possible valid lower constant for this G. Section14
also rules out repairing that allowance by fixed-cutoff tuning alone.

This conclusion does not show that actual rejections attain their upper
bound, nor that actual survivors are absent. A sharper rejection estimate,
a joint weighted treatment retaining the shared arithmetic of supply and
rejections, or a different candidate family would require a new analysis.
Only the present separate-budget certificate is ruled out. The ingredients
are classical; this application is not a novelty claim or a Stainless result.
