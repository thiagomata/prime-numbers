# Relaxed Cofactor Divisor Sum Is A Prime-Progression Discrepancy

**Status:** Mathematically proved exact reduction. The accumulated
prime-progression estimate is open and Stainless verification is not claimed.

## Meaning

The natural lower-bound sieve for candidate #25 starts with the base sequence

```math
\{n+2:n\text{ survives the installed wheel}\}
```

and asks how often a squarefree divisor `d` divides `n+2`. The expected local
factor is exactly `1/phi(d)`, not `1/d`.

On a complete wheel this factor is exact. On an arbitrary interval, its error
is one signed periodic boundary discrepancy. In the square-safe window, wheel
survivors are primes, so this boundary discrepancy is exactly the discrepancy
of primes in the reduced arithmetic progression `-2 modulo d`.

This identifies the first genuine arithmetic input for the relaxed
almost-prime program. More sieve-sequence representation algebra cannot prove
its required divisor average by itself.

## Setup

Let `W` be a squarefree product of primes with `2|W`, and define the survivor
indicator

```math
s_W(n)=\mathbf1_{\gcd(n,W)=1}.
```

Let `d` be an odd squarefree divisor of `W`. For an integer interval
`I=[L,U)`, put

```math
A_d(I)
=
\sum_{n\in I}s_W(n)\mathbf1_{d\mid n+2},
\qquad
A_1(I)=\sum_{n\in I}s_W(n).
```

Define the centered shifted-divisor discrepancy

```math
\boxed{
r_d(I)=A_d(I)-\frac{A_1(I)}{\varphi(d)}.
}
```

The prime `2` is excluded from `d`: every survivor is odd, so `n+2` is odd
and an even shifted divisor count is identically zero.

## Exact Complete-Wheel Factor

In one complete residue system modulo `W`, the condition at a prime `p|W` is:

- if `p|d`, the residue of `n` is fixed to `-2 modulo p`;
- if `p` does not divide `d`, any of the `p-1` nonzero residues is allowed.

Because `d` is odd, `-2` is nonzero at every prime dividing `d`. CRT therefore
gives

```math
\begin{aligned}
A_d([a,a+W))
&=
\prod_{\substack{p\mid W\\p\nmid d}}(p-1)\\
&=
\frac{\varphi(W)}{\varphi(d)}.
\end{aligned}
```

Since

```math
A_1([a,a+W))=\varphi(W),
```

every complete wheel has zero centered discrepancy:

```math
\boxed{
r_d([a,a+W))=0.
}
\qquad[\text{Q.E.D.}]
```

The identity holds for every starting integer `a`, not only for a block
starting at zero.

## Exact Arbitrary-Interval Boundary

Define the `W`-periodic centered word

```math
h_d(n)
=
s_W(n)
\left(
\mathbf1_{d\mid n+2}-\frac1{\varphi(d)}
\right).
```

The complete-wheel theorem says

```math
\sum_{j=0}^{W-1}h_d(a+j)=0
```

for every `a`. If `|I|=qW+t` with `0<=t<W`, remove the first `q` consecutive
complete wheel blocks. The remainder is the exact formula

```math
\boxed{
r_d(I)
=
\sum_{j=0}^{t-1}h_d(L+qW+j).
}
```

Since `|h_d(n)|<=1`, this gives only

```math
\boxed{
|r_d(I)|\le t\le W-1.
}
```

For the candidate's primorial wheel, this pointwise boundary bound is much
larger than the square-safe interval and is analytically useless. Its value is
the exact zero-mean representation, not the trivial magnitude estimate.

## Square-Safe Prime-Progression Identity

Now let

```math
W=P(Q)
```

and take `I subset [Q,Q^2)`. Every `n in I` coprime to `P(Q)` is prime by
square-safe certification. Therefore

```math
A_1(I)=\pi(I)
```

and, for every odd `d|P(Q)`,

```math
A_d(I)=\pi(I;d,-2),
```

where `pi(I;d,-2)` counts primes in `I` congruent to `-2 modulo d`. Hence

```math
\boxed{
r_d(I)
=
\pi(I;d,-2)-\frac{\pi(I)}{\varphi(d)}.
}
\qquad[\text{Q.E.D.}]
```

The relaxed cofactor Type-I remainder is thus literally a prime arithmetic-
progression discrepancy.

## The Accumulated Type-I Obligation

Let

```math
z=Q^{2\alpha},
\qquad
\frac13<\alpha<\frac12.
```

The divisors used by the relaxed lower-bound sieve are odd squarefree
divisors of `P(z)`. A genuine Type-I theorem must prove cancellation of a
shape such as

```math
\boxed{
\sum_{\substack{d\le D\\d\mid P(z)/2}}
\tau_B(d)
\max_{I}
\left|
\pi(I;d,-2)-\frac{\pi(I)}{\varphi(d)}
\right|
\ll
\frac{Q^2}{(\log Q)^A}
}
```

for a divisor range `D` and interval family strong enough for the chosen
almost-prime sieve. The displayed inequality is a target, not a proved result.
Its exact admissible `D`, powers, and interval uniformity must be matched to
the combinatorial lower-bound identity before publication as a theorem.

## Finite Consistency Check

For `W=30`, there are `phi(30)=8` survivor classes. CRT gives

```math
A_3=4=\frac8{\varphi(3)},
\qquad
A_5=2=\frac8{\varphi(5)},
\qquad
A_{15}=1=\frac8{\varphi(15)}.
```

These complete-wheel counts are finite falsifiers, not proof inputs.

## Consequence For The Final Program

The Divisor Local Factor property supplies the exact local factor when the final relaxed weight is
tested by `m|n`. This property locates the more natural divisor sum for the
lower-bound cofactor sieve: `d|n+2` before the final sifting step.

The distinction matters. The missing theorem is no longer “some Type-I
uniformity.” It is an averaged distribution theorem for the certified-prime
survivors in the progression `-2 modulo d`. Obtaining it requires new
arithmetic information about primes in progressions, not another complete-
period count.

## Related

- [Relaxed Almost-Prime Divisor Local Factor](relaxed-almost-prime-divisor-local-factor.md)
- [Relaxed Almost-Prime Bilinear Character Obstruction](relaxed-almost-prime-bilinear-character-obstruction.md)
- [Square-Safe Two-Gaps Certify Twin Primes](safe-window-two-gaps-certify-twin-primes.md)
- [Chen-Type Almost-Prime Survivor](../../candidates/chen-type-almost-prime-survivor.md)
