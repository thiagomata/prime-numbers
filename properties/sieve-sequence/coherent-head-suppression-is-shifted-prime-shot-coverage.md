# Coherent Head Suppression Is Shifted Prime-Shot Coverage

**Status:** Mathematically proved exact equivalence. Stainless verification is
not claimed here.

## Meaning

Once filter shots are required to be real coherent multiples rather than
independent per-parent choices, permanent suppression of head 2-gaps becomes
an exact deterministic covering statement. At a prime head `q`, failure of the
head gap `2` means that the prospective endpoint `q+2` lies on an earlier
prime's shot train. In the head coordinate, that train is the shifted residue
class `-2 modulo r`.

This equivalence incorporates shot spacing, cyclic sums, shared endpoints, and
CRT compatibility automatically. It does not prove whether eventual coverage
or infinitely many escapes occur.

## Setup

Let `q>=5` be prime. At the sieve stage headed by `q`, every prime `r<q` is an
active filter. Define the shifted shot family

```math
\mathcal C_r
=
\{x:x\equiv-2\pmod r\}.
```

Membership `q in C_r` is equivalent to the actual value `q+2` being a
multiple of `r`.

## Pointwise Equivalence

The following statements are equivalent:

1. The stage headed by `q` does not have head gap `2`.
2. The value `q+2` is rejected by an earlier filter.
3. The value `q+2` is composite.
4. There is a prime `r` satisfying

   ```math
   r\le\sqrt{q+2}<q
   \qquad\text{and}\qquad
   q\equiv-2\pmod r.
   ```

### Proof

Because `q>=5` is odd, `q+1` is even and is rejected by filter `2`. Therefore
the stage has head gap `2` exactly when `q+2` is accepted.

If an earlier filter rejects `q+2`, then some prime `r<q` divides it, so `q+2`
is composite. Conversely, if `q+2` is composite, it has a prime divisor

```math
r\le\sqrt{q+2}.
```

The strict inequality `sqrt(q+2)<q` follows from `q+2<q^2` for `q>=5`.
Hence `r<q`, so filter `r` is already active and rejects `q+2`. Finally,

```math
r\mid q+2
\quad\Longleftrightarrow\quad
q\equiv-2\pmod r.
```

Thus all four statements are equivalent. `[Q.E.D.]`

## Finite-Block Covering Form

Let `H` be any finite set of prime heads, all at least `5`. There is no head
2-gap at any `q in H` exactly when

```math
\boxed{
\forall q\in H,\ \exists r\text{ prime}:
r\le\sqrt{q+2}
\ \land\
q\in\mathcal C_r.
}
```

The bound on `r` is pointwise. Replacing it by a common upper bound such as
`sqrt(max(H)+2)` is safe only if the divisibility witness for each individual
`q` is retained.

## Eventual-Coverage Form

There is a final head 2-gap followed by permanent suppression exactly when
there is a threshold `Q_0` such that every prime `q>=Q_0` is covered:

```math
\boxed{
\forall q\ge Q_0,\ q\text{ prime}
\Longrightarrow
\exists r\le\sqrt{q+2}\text{ prime}:
q\equiv-2\pmod r.
}
```

Equivalently, only finitely many prime heads escape all coherent shifted shot
families. An escaping prime head has `q+2` prime and therefore is the lower
member of a twin-prime pair. Consequently:

```math
\begin{aligned}
&\text{eventual coherent coverage of all prime heads}\\
&\qquad\Longleftrightarrow
\text{only finitely many head 2-gaps}\\
&\qquad\Longleftrightarrow
\text{only finitely many twin-prime pairs}.
\end{aligned}
```

This is an equivalence, not an existence result in either direction.

## Why The Shots Are Coherent

For one fixed filter prime `r`, every witness has the form

```math
q+2=rk.
```

These are points on the single arithmetic shot train of multiples of `r`.
After conditioning on earlier filters, the retained shots are the same train
sampled at accepted cofactors, so their gaps are `r` times the cofactor gaps.
Their cyclic gap sum and fixed-`k` spans are therefore inherited from the
cofactor period.

The same removed value is shared by every incident gap; it is not selected
separately for each parent. Intersections between shot trains for distinct
primes are ordinary simultaneous divisibility conditions and are governed by
CRT. Thus the covering formulation respects exactly the coherence that the
free per-parent adversarial companion discards.

## Consequences

- Independent per-parent harmful-copy choices are not needed and are not valid
  evidence about the real filter.
- Enforcing all literal shot families leaves no adversarial phase choice: the
  cover is determined by divisibility of `q+2`.
- Fixed shot sums and spacing are already present in every hypothetical
  permanently suppressing cover. They do not by themselves contradict it.
- A recurrence proof must establish deterministic noncoverage: sufficiently
  often, a prime head `q` must escape every class `-2 modulo r` with
  `r<=sqrt(q+2)`.

## Worked Values

| Head `q` | `q+2` | Coherent cover | Head gap |
|---:|---:|---|---:|
| `11` | `13` | none | `2` |
| `13` | `15` | `13 == -2 mod 3` | `4` |
| `17` | `19` | none | `2` |
| `19` | `21` | `19 == -2 mod 3` | `4` |

The composite rows are suppressed by actual filter `3` shots; the prime rows
escape every earlier filter and appear as head 2-gaps.

## Limitation

The exact cover identifies the coherent deterministic problem but does not
bound its uncovered set. Proving that infinitely many prime heads escape is
exactly a twin-prime-strength lower-bound sieve statement. Complete-period
counts, total shot sums, and per-filter spacing do not provide that local
noncoverage theorem; this is the familiar parity boundary in the present
coordinates.

## Related

- [Safe-window 2-gaps certify twin primes](
  safe-window-two-gaps-certify-twin-primes.md)
- [Exact filter frequency across repeated copies](
  copy-index-filter-frequency.md)
- [Fixed-k shot spacing](stable-small-k-shot-spacing.md)
- [Incremental danger-annulus decomposition](
  incremental-danger-annulus-decomposition.md)
- [Recent prime-producing sieves deep dive](
  research/recent-prime-producing-sieves-deep-dive.md)
