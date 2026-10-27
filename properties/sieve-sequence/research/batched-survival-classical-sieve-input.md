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
