# Relaxed Almost-Prime Weight Has An Exact Divisor Local Factor

**Status:** Mathematically proved exact local factor and boundary
decomposition. Stainless verification is not claimed.

## Meaning

Candidate #25 counts integers `n` that survive the installed prime wheel while
`n+2` avoids a smaller relaxed wheel. After additionally imposing `m|n`, the
correct comparison density is not an unspecified constant: it is an explicit
product of local factors depending on how `m` meets the two wheels.

The count over any interval is exactly that density times the corresponding
`k`-interval length, plus one named incomplete-period remainder. This proves
the local model needed before a Type-I argument can begin. It does not prove
that the remainders cancel when summed over divisors; the trivial remainder
bound is primorial-sized and is therefore not a short-interval estimate.

## Setup

Let `W` and `Z` be squarefree products of primes, assume `2|W`, and put

```math
R=\prod_{p\mid WZ}p.
```

For integers `0<=L<U` and `m>=1`, define

```math
\mathcal N_m[L,U)
=
\#\{n\in[L,U):m\mid n,\ \gcd(n,W)=1,\ \gcd(n+2,Z)=1\}.
```

Writing `n=mk` converts the numerical interval into

```math
K_m[L,U)
=
\left[
\left\lceil\frac Lm\right\rceil,
\left\lceil\frac Um\right\rceil
\right)\cap\mathbb Z.
```

Let its length be `ell_m`.

## Wheel-Sharing Divisors Vanish

If `gcd(m,W)>1`, choose a prime `p|gcd(m,W)`. Every multiple `n=mk` then
satisfies `p|n`, contradicting `gcd(n,W)=1`. Therefore

```math
\boxed{
\gcd(m,W)>1
\quad\Longrightarrow\quad
\mathcal N_m[L,U)=0.
}
\qquad[\text{Q.E.D.}]
```

The remaining sections assume `gcd(m,W)=1`.

## Exact Local Residue Table

For every prime `p|WZ`, let `lambda_p(m)` be the number of allowed residues
of `k modulo p`.

### Prime In The Installed Wheel Only

If `p|W` and `p` does not divide `Z`, multiplication by `m` is invertible
modulo `p`. The sole forbidden class is `k=0`, so

```math
\lambda_p(m)=p-1.
```

### Prime In Both Wheels

If `p|W` and `p|Z`, the two conditions forbid

```math
k\equiv0\pmod p,
\qquad
k\equiv-2m^{-1}\pmod p.
```

For `p=2` these are the same class. For odd `p` they are distinct. Hence

```math
\lambda_p(m)
=
\begin{cases}
1,&p=2,\\
p-2,&p>2.
\end{cases}
```

### Prime In The Relaxed Wheel Only

Suppose `p|Z` and `p` does not divide `W`. Because `2|W`, this prime is odd.
If `p|m`, then

```math
mk+2\equiv2\not\equiv0\pmod p
```

for every `k`, so all `p` classes are allowed. If `p` does not divide `m`,
exactly the class `k=-2m^{-1}` is forbidden. Thus

```math
\lambda_p(m)
=
\begin{cases}
p,&p\mid m,\\
p-1,&p\nmid m.
\end{cases}
```

Combining the cases gives the complete table

```math
\boxed{
\lambda_p(m)=
\begin{cases}
p-1,&p\mid W,\ p\nmid Z,\\
1,&p=2,\ p\mid W,\ p\mid Z,\\
p-2,&p>2,\ p\mid W,\ p\mid Z,\\
p,&p\mid Z,\ p\nmid W,\ p\mid m,\\
p-1,&p\mid Z,\ p\nmid W,\ p\nmid m.
\end{cases}
}
```

## Complete-Period CRT Count

The restrictions at distinct primes are independent by the Chinese remainder
theorem. Consequently, in every complete block of `R` consecutive `k` values,
the exact number of allowed values is

```math
A(m)=\prod_{p\mid WZ}\lambda_p(m).
```

Define the divisor local density

```math
\boxed{
\rho(m)=\frac{A(m)}R
=
\prod_{p\mid WZ}\frac{\lambda_p(m)}p
}
```

when `gcd(m,W)=1`, and define `rho(m)=0` otherwise. This is the exact
divisor-dependent comparison factor.

## Exact Arbitrary-Interval Decomposition

Put

```math
k_0=\left\lceil\frac Lm\right\rceil,
\qquad
\ell_m=|K_m[L,U)|,
\qquad
\ell_m=qR+s,
\quad 0\le s<R.
```

Let `C_m(k_0,s)` count the allowed residues among

```math
k_0,k_0+1,\ldots,k_0+s-1.
```

Periodicity and the complete-period CRT count give

```math
\begin{aligned}
\mathcal N_m[L,U)
&=qA(m)+C_m(k_0,s)\\
&=\rho(m)(qR+s)
 +\left(C_m(k_0,s)-s\rho(m)\right).
\end{aligned}
```

Therefore, with

```math
E_m[L,U)=C_m(k_0,s)-s\rho(m),
```

one has the exact formula

```math
\boxed{
\mathcal N_m[L,U)
=
\rho(m)\ell_m+E_m[L,U).
}
```

Since both `C_m(k_0,s)` and `s rho(m)` lie in `[0,s]`,

```math
\boxed{
|E_m[L,U)|\le s\le R-1.
}
\qquad[\text{Q.E.D.}]
```

For `gcd(m,W)>1`, take `rho(m)=E_m[L,U)=0`, consistently with the exact
vanishing theorem.

## Candidate-25 Specialization

Let

```math
X=Q^2,
\qquad
W=P(Q),
\qquad
Z=P(z),
\qquad
z=X^\alpha.
```

Choose the useful range

```math
\frac13<\alpha<\frac12.
```

Then `z<Q`, so every prime in `Z` is also in `W`. For every divisor with
`gcd(m,W)=1`, the local density is independent of `m` and equals

```math
\boxed{
\rho_{Q,z}
=
\frac12
\prod_{2<p<z}\left(1-\frac2p\right)
\prod_{z\le p<Q}\left(1-\frac1p\right).
}
```

Divisors sharing any prime with `P(Q)` have density zero. The relaxed weight
therefore has sieve dimension two below `z` and dimension one from `z` to
`Q`.

For candidate #25's interval `I subset [Q,Q^2)`, the exact one-divisor model is

```math
\boxed{
\mathcal N_m(I)
=
\mathbf1_{\gcd(m,P(Q))=1}\rho_{Q,z}\ell_m+E_m(I).
}
```

## Type-I Boundary

The theorem identifies the correct accumulated remainder target. For
coefficients `alpha_m`, any proposed Type-I estimate must control

```math
\sum_{m\le M}\alpha_mE_m(I),
```

after separating the exact main factors above. The pointwise estimate
`|E_m(I)|<=R-1` is generally useless because `R=P(Q)` is much larger than the
square-safe interval.

Thus complete-period CRT proves the local factor but does not prove Type-I
cancellation. Any advance must exploit averaging over `m`, arithmetic
structure of the coefficients, or a shorter modulus decomposition.

## Finite Consistency Checks

These checks are falsifiers, not proof inputs.

- For `W=30`, `Z=6`, and `m=7`, exactly four of the 30 `k` classes are
  allowed, agreeing with `rho=(1/2)(1-2/3)(1-1/5)=2/15`.
- For the same wheels and `m=5`, the count is zero because `m` shares a prime
  with `W`.
- For `W=6`, `Z=10`, and `m=5`, the relaxed-only prime `5` imposes no
  restriction; ten of the 30 classes are allowed, agreeing with density
  `(1/2)(2/3)=1/3`.

## Consequence For The Final Program

The missing first theorem for candidate #25 is no longer an unspecified local
density statement. It is precisely a nontrivial average of the signed
boundary discrepancies `E_m(I)` over a useful divisor range.

After that Type-I obligation, a genuine Type-II statement must allow arbitrary
coefficients on two factor variables. The CRT identity alone supplies neither
estimate.

## Related

- [Chen-Type Almost-Prime Survivor](../../candidates/chen-type-almost-prime-survivor.md)
- [Recent Prime-Producing Sieves Deep-Dive](research/recent-prime-producing-sieves-deep-dive.md)
- [Exact Batched Two-Gap Survival](exact-batched-two-gap-survival.md)
- [Square-Safe Two-Gaps Certify Twin Primes](safe-window-two-gaps-certify-twin-primes.md)
