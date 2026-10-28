# Survival Frontiers In Balanced 2-Gap Companion Processes: A Detailed Guide

**Side version of:** [Survival Frontiers in Balanced 2-Gap Companion
Processes](survival-frontiers.md)

This is a detailed companion version. It does not replace the full article. It
slows down the hazard calculations, the threshold tests, and the quota model.
The original article remains the complete statement of the conditional results
and their limitations.

## 1. The Basic Question

A 2-gap is a pair of consecutive surviving values with difference `2`.

At a filter prime `r`, each old 2-gap parent produces `r` lifted copies. In the
balanced companion models, exactly two of those copies are removed. The only
thing that changes from model to model is where those two removals are placed.

So the global count is easy:

```math
\begin{aligned}
\text{children per parent} &= r,\\
\text{removed children per parent} &= 2,\\
\text{surviving children per parent} &= r-2.
\end{aligned}
```

If there are `N_k` parents before this filter, then after this filter:

```math
N_{k+1}=(r_k-2)N_k.
```

This is why global survival is not the hard part. As long as the process starts
with at least one 2-gap and every later prime satisfies `r_k >= 5`, the global
population keeps multiplying by positive factors:

```math
N_k
=N_0(r_0-2)(r_1-2)\cdots(r_{k-1}-2)>0.
```

The hard question is local:

```text
Do 2-gaps survive near the head, or inside a chosen square-safe window?
```

Placement matters locally even when the global population is huge.

The full article develops this distinction in
[Section 3.1](survival-frontiers.md#31-global-persistence-is-independent-of-allocation).

## 2. Random Damage And Relative Damage

For one tracked local candidate, the balanced random benchmark removes two of
the `r` copy positions. So its destruction probability is

```math
d_r=\frac{2}{r}.
```

The article compares a model's actual local destruction probability `f_r` to
that random benchmark:

```math
w_r=\frac{f_r}{2/r}=\frac{rf_r}{2}.
```

This is called the relative worsening factor.

Read it like this:

```math
\begin{aligned}
w_r=0
&\Longleftrightarrow
f_r=0
&&\text{no local damage},\\
w_r=1
&\Longleftrightarrow
f_r=2/r
&&\text{random-level damage},\\
w_r=10
&\Longleftrightarrow
f_r=20/r
&&\text{ten times random-level damage}.
\end{aligned}
```

This scale is useful because the random benchmark itself changes with `r`.
When `r` is large, `2/r` is small, so a fixed absolute damage percentage is not
a fixed amount worse than random.

For example, a `1%` local destruction probability means:

```math
f_r=0.01.
```

Then

```math
w_r=\frac{r(0.01)}{2}=0.005r.
```

So at `r = 100`, this is only `0.5` times the random benchmark. At
`r = 10,000`, it is `50` times the random benchmark. A fixed absolute
percentage becomes more and more hostile relative to random.

This is the point of
[Section 3.2](survival-frontiers.md#32-local-destruction-relative-to-random).

## 3. Why Survival Probabilities Multiply

Follow one candidate through several filters. At filter `r`, suppose the local
destruction probability is `f_r`. Then the survival probability at that filter
is

```math
1-f_r.
```

To survive every filter below `Q`, it must survive the first one, then the next,
then the next, and so on. Conditional probabilities multiply:

```math
P(Q)=\prod_{r<Q}(1-f_r).
```

Products are hard to estimate directly, so the article converts the product
into a sum by taking logarithms:

```math
\begin{aligned}
\log P(Q)
&=\log\left(\prod_{r<Q}(1-f_r)\right)\\
&=\sum_{r<Q}\log(1-f_r).
\end{aligned}
```

Define the cumulative hazard:

```math
D(Q)=\sum_{r<Q}-\log(1-f_r).
```

Then:

```math
\begin{aligned}
\log P(Q)&=-D(Q),\\
P(Q)&=e^{-D(Q)}.
\end{aligned}
```

That is the whole meaning of the hazard formula. It is not magic; it is just
"multiply survival factors" plus "logs turn products into sums."

The full article states this in
[Section 3.3](survival-frontiers.md#33-the-general-cumulative-local-hazard-law).

## 4. The Random Benchmark, Slowly

For random balanced damage:

```math
f_r=\frac{2}{r}.
```

For large `r`, the approximation

```math
-\log(1-x)\approx x
```

gives

```math
-\log\left(1-\frac{2}{r}\right)\approx \frac{2}{r}.
```

So

```math
D_{\mathrm{random}}(Q)
\approx
\sum_{r<Q}\frac{2}{r}
=2\sum_{r<Q}\frac{1}{r}.
```

The sum is over primes `r`. A standard prime-number-theory estimate says:

```math
\sum_{r<Q,\ r\text{ prime}}\frac{1}{r}
=\log\log Q+O(1).
```

Therefore:

```math
D_{\mathrm{random}}(Q)
=2\log\log Q+O(1).
```

Now exponentiate:

```math
\begin{aligned}
P_{\mathrm{random}}(Q)
&=e^{-D_{\mathrm{random}}(Q)}\\
&\asymp e^{-2\log\log Q}\\
&=(e^{\log\log Q})^{-2}\\
&=(\log Q)^{-2}.
\end{aligned}
```

So the random benchmark gives survival on the order of

```math
\frac{1}{(\log Q)^2}.
```

## 5. Why Every Fixed Worsening Factor Still Survives In Large Windows

Now suppose the local damage is `w` times random, where `w` is a fixed number:

```math
f_r=\frac{2w}{r}.
```

The same calculation gives:

```math
\begin{aligned}
D_w(Q)
&\approx
\sum_{r<Q}\frac{2w}{r}\\
&=2w\sum_{r<Q}\frac{1}{r}\\
&=2w\log\log Q+O(1).
\end{aligned}
```

So:

```math
\begin{aligned}
P_w(Q)
&\asymp e^{-2w\log\log Q}\\
&=(\log Q)^{-2w}.
\end{aligned}
```

This gets smaller when `w` is larger. But a square-safe window supplies many
possible starting positions. The article models that supply as roughly

```math
B(Q)\asymp C_0Q^2.
```

The expected number of survivors is approximately:

```math
\lambda_w(Q)
=B(Q)P_w(Q)
\asymp
C_0\frac{Q^2}{(\log Q)^{2w}}.
```

For any fixed finite `w`, the numerator `Q^2` eventually beats the denominator
`(\log Q)^{2w}`. That is why:

```math
\lambda_w(Q)\to\infty.
```

So every fixed finite worsening factor still leaves growing expected occupancy
in quadratic windows, under the article's blind-placement assumptions.

The same fixed-factor calculation also supports head recurrence under the
extra head-availability and mixing assumptions stated in the full article.
Those are assumptions, not facts proved for the real sieve.

See
[Section 3.4](survival-frontiers.md#34-every-fixed-finite-worsening-factor-survives).

## 6. Where The First Real Threshold Appears

A fixed worsening factor is not enough to kill quadratic windows. The first
important transition appears when the worsening factor grows like a logarithm:

```math
w_r=1+c\log r.
```

Then:

```math
\begin{aligned}
f_r
&=\frac{2w_r}{r}\\
&=\frac{2(1+c\log r)}{r}\\
&=\frac{2}{r}+\frac{2c\log r}{r}.
\end{aligned}
```

The hazard has two parts:

```math
\begin{aligned}
D_c(Q)
&\approx
\sum_{r<Q}\frac{2}{r}
+
\sum_{r<Q}\frac{2c\log r}{r}.
\end{aligned}
```

The first sum is the familiar random part:

```math
\sum_{r<Q}\frac{2}{r}
=2\log\log Q+O(1).
```

The second prime sum grows like:

```math
\sum_{r<Q}\frac{\log r}{r}
=\log Q+O(1).
```

So:

```math
D_c(Q)=2\log\log Q+2c\log Q+O(1).
```

Exponentiating gives:

```math
\begin{aligned}
P_c(Q)
&\asymp e^{-2\log\log Q}e^{-2c\log Q}\\
&=\frac{1}{(\log Q)^2}\cdot\frac{1}{Q^{2c}}\\
&=\frac{1}{Q^{2c}(\log Q)^2}.
\end{aligned}
```

Now compare two local questions.

### 6.1 Square Windows

A square window has roughly `Q^2` possible starts, so:

```math
\begin{aligned}
\lambda_c(Q)
&\asymp Q^2P_c(Q)\\
&\asymp
\frac{Q^2}{Q^{2c}(\log Q)^2}\\
&=
\frac{Q^{2-2c}}{(\log Q)^2}.
\end{aligned}
```

If `c < 1`, then `2-2c > 0`, so the power of `Q` grows and beats the logarithm:

```math
\lambda_c(Q)\to\infty.
```

If `c >= 1`, the numerator no longer has a positive power reserve. At `c = 1`,

```math
\lambda_1(Q)\asymp \frac{1}{(\log Q)^2}\to0.
```

So the square-window threshold is:

```math
c=1.
```

### 6.2 The Head

At one distinguished head position there is no `Q^2` supply. The probability
scale is just:

```math
\Pr(H_Q)\asymp \frac{1}{Q^{2c}(\log Q)^2}.
```

To decide whether head hits happen infinitely often, the article sums this over
prime heads. The prime-sum test behaves like the integral

```math
\int^\infty \frac{dx}{x^{2c}(\log x)^3}.
```

This integral diverges when `2c < 1` and converges when `2c >= 1`. Therefore
the head threshold is:

```math
c=\frac12.
```

That is why the article has two different frontiers:

```math
\begin{aligned}
c<1
&\quad\text{supports square-window survival},\\
c<\frac12
&\quad\text{supports infinitely recurring head hits}.
\end{aligned}
```

The full derivation is in
[Section 3.5](survival-frontiers.md#35-logarithmically-growing-worsening-has-two-thresholds).

## 7. Exact Quota: Random Locations With A Fixed Number Of Strikes

The exact-quota model asks a different question.

Instead of saying "each parent loses exactly two children," suppose one layer
has:

- `N_r` eligible values;
- exactly `J_r` harmful strikes.

Choose exactly `J_r` values uniformly from the `N_r` eligible values.

For one 2-gap, both endpoints survive only if all `J_r` strikes are chosen
from the other `N_r-2` values. Therefore:

```math
s_r
=
\frac{\binom{N_r-2}{J_r}}{\binom{N_r}{J_r}}.
```

Now expand the binomial ratio:

```math
\begin{aligned}
\binom{N_r-2}{J_r}
&=
\frac{(N_r-2)!}{J_r!(N_r-2-J_r)!},\\
\binom{N_r}{J_r}
&=
\frac{N_r!}{J_r!(N_r-J_r)!}.
\end{aligned}
```

Divide them:

```math
\begin{aligned}
s_r
&=
\frac{(N_r-2)!}{J_r!(N_r-2-J_r)!}
\cdot
\frac{J_r!(N_r-J_r)!}{N_r!}\\
&=
\frac{(N_r-2)!(N_r-J_r)!}
{(N_r-2-J_r)!N_r!}.
\end{aligned}
```

Now cancel factorials:

```math
\begin{aligned}
(N_r-J_r)!
&=(N_r-J_r)(N_r-J_r-1)(N_r-J_r-2)!,\\
N_r!
&=N_r(N_r-1)(N_r-2)!.
\end{aligned}
```

So:

```math
s_r
=
\frac{(N_r-J_r)(N_r-J_r-1)}{N_r(N_r-1)}.
```

Let the strike fraction be

```math
u_r=\frac{J_r}{N_r}.
```

When the finite-population errors are controlled, the logarithm behaves like:

```math
\log s_r=-2u_r+\text{small error}.
```

Thus, if the cumulative quota satisfies

```math
\sum_{r<Q}u_r=\log\log Q+O(1),
```

then:

```math
\begin{aligned}
P_{\mathrm{quota}}(Q)
&=\prod_{r<Q}s_r\\
&\asymp
e^{-2\log\log Q}\\
&\asymp
\frac{1}{(\log Q)^2}.
\end{aligned}
```

So the neutral exact-quota companion has the same one-position survival scale
as the random balanced parent model, provided the article's cumulative quota
and finite-population error assumptions hold.

See
[Section 7.1](survival-frontiers.md#71-exact-crt-quotas-with-random-locations).

## 8. Biased Quotas: Why Raw Preference Is Not The Same As Effective Damage

The biased quota model keeps the exact number of strikes but makes endpoints of
2-gaps more likely to be struck.

Let:

- `x_r` be the fraction of eligible values that are special endpoints;
- `p_r^E` be the strike probability for an endpoint;
- `p_r^O` be the strike probability for an ordinary value;
- `beta_r = p_r^E / p_r^O` be the raw preference ratio;
- `u_r = J_r/N_r` be the fixed quota fraction.

Because the total quota is fixed, the average strike probability must be `u_r`:

```math
x_rp_r^E+(1-x_r)p_r^O=u_r.
```

Since

```math
p_r^E=\beta_r p_r^O,
```

substitute:

```math
\begin{aligned}
x_r\beta_r p_r^O+(1-x_r)p_r^O
&=u_r,\\
p_r^O(1+(\beta_r-1)x_r)
&=u_r,\\
p_r^O
&=\frac{u_r}{1+(\beta_r-1)x_r}.
\end{aligned}
```

Then:

```math
p_r^E
=
\frac{\beta_ru_r}{1+(\beta_r-1)x_r}.
```

This is why raw preference `beta_r` is not the same thing as effective local
damage. The fixed quota forces the model to take probability away from ordinary
values when it gives more probability to endpoints.

The effective multiplier is:

```math
\kappa_r^{\mathrm{eff}}
=
\frac{\beta_r}{1+(\beta_r-1)x_r}.
```

The full article then measures the realized local hazard by

```math
\kappa_r=\frac{f_r}{2/r},
```

which is the same role played earlier by `w_r`. Once the problem is expressed
in terms of the realized effective factor, the same logarithmic thresholds
return:

```math
\begin{aligned}
\kappa_r \le 1+(1/2-\varepsilon)\log r
&\Longrightarrow
\text{head recurrence, with the stated assumptions},\\
\kappa_r \le 1+(1-\varepsilon)\log r
&\Longrightarrow
\text{square-window occupancy, with the stated assumptions}.
\end{aligned}
```

The full version is in
[Section 7.2](survival-frontiers.md#72-biased-exact-quotas-and-the-logarithmic-skew-frontier).

## 9. What This Guide Does Not Claim

This guide explains the main calculations. It does not prove that the real
sieve satisfies the spatial, availability, or mixing assumptions used by the
companion theorems.

The full article is careful about this:

- the companion identities are exact inside their models;
- the asymptotic survival statements are conditional on their stated premises;
- Stainless verification is pending for the survival-frontier article;
- no theorem in the article proves the twin prime conjecture for the real
  sieve.

The right way to read the result is:

```text
These companion models show which kinds of local damage are still survivable,
provided the stated placement and mixing assumptions hold.
```

For the full proof boundary, limitations, and relation to the real sieve, read
[Sections 8-10 of the original article](survival-frontiers.md#8-relation-to-the-real-sieve).
