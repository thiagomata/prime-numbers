# Accepted-Strike CRT Lift-Index Transform

**Status:** Mathematically proved exact finite identities. Stainless
verification is not claimed.

## Meaning

The Strike Divisor-Activation Kernel property expresses each accepted-strike discrepancy through the old
boundary error and the newly activated divisor shell. CRT splits every new
modulus `re` residue into its old residue modulo `e` plus one lift index
between `0` and `r-1`.

After this split is inserted, the complete old boundary error cancels exactly.
The accepted-strike discrepancy becomes one signed Möbius transform of the
difference between two bounded CRT lift indices.

This is a sharper interface for candidate #23. The bulk term, the old
boundary term, and the activation-shell bookkeeping are all eliminated. The
remaining theorem is a weighted mean-square bound for explicit bounded-index
Möbius transforms.

## Setup

Let `P` be squarefree, let

```math
\gcd(P,r)=1,
```

and let `x` be coprime to every divisor under consideration. For `e|P`, write
`[x]_e` for the least positive residue of `x modulo e`.

Define the CRT lift index `t_{x,r}(e)` by

```math
\boxed{
t_{x,r}(e)
\in
\{0,\ldots,r-1\},
\qquad
[x]_{re}
=
[x]_e+e\,t_{x,r}(e).
}
```

The right side is the unique number in `{1,...,re}` that is congruent to `x`
modulo both `e` and `r`.

## Exact Floor Formula

By the least-positive residue convention,

```math
x
=
[x]_e
+
e\left\lfloor\frac{x-1}{e}\right\rfloor.
```

Reducing the quotient modulo `r` therefore gives

```math
\boxed{
t_{x,r}(e)
=
\left[
\left\lfloor\frac{x-1}{e}\right\rfloor
\right]_r^{(0)},
}
```

where `[.]_r^(0)` denotes the least nonnegative residue modulo `r`.

Thus the lift index is explicit and satisfies

```math
0\le t_{x,r}(e)<r.
```

## CRT Split Of A Boundary Summand

For the prime-square endpoints, define

```math
\epsilon_Q(e)
=
\frac{[Q]_e-[Q^2]_e}{e}.
```

The lift identity gives

```math
[Q]_{re}
=
[Q]_e+e\,t_{Q,r}(e)
```

and

```math
[Q^2]_{re}
=
[Q^2]_e+e\,t_{Q^2,r}(e).
```

Subtracting and dividing by `re` proves

```math
\boxed{
\epsilon_Q(re)
=
\frac1r\epsilon_Q(e)
+
\frac1r
\left(
t_{Q,r}(e)-t_{Q^2,r}(e)
\right).
}
\qquad[\text{Q.E.D.}]
```

This is the exact old-modulus plus lift-index factorization requested by the
candidate #23 ticket.

## Cancellation Of The Old Boundary Error

At layer `i`, let `P=P_i` and `r=r_i`. The Strike Divisor-Activation Kernel property gives the newly activated
shell

```math
Z_{i+1}
=
-\sum_{e\mid P_i}
\mu(e)\epsilon_Q(r_i e).
```

Insert the CRT split:

```math
\begin{aligned}
Z_{i+1}
&=
-\frac1{r_i}
\sum_{e\mid P_i}\mu(e)\epsilon_Q(e)\\
&\quad
-\frac1{r_i}
\sum_{e\mid P_i}
\mu(e)
\left(
t_{Q,r_i}(e)-t_{Q^2,r_i}(e)
\right).
\end{aligned}
```

The `e=1` old-boundary summand is zero, so the first sum is exactly `E_i`.
Hence

```math
Z_{i+1}
=
-\frac{E_i}{r_i}
-\frac1{r_i}
\sum_{e\mid P_i}
\mu(e)
\left(
t_{Q,r_i}(e)-t_{Q^2,r_i}(e)
\right).
```

The Strike Divisor-Activation Kernel property also gives

```math
D_i
=
-\frac{E_i}{r_i}-Z_{i+1}.
```

The complete old boundary error cancels, proving

```math
\boxed{
D_i
=
\frac1{r_i}
\sum_{e\mid P_i}
\mu(e)
\left(
t_{Q,r_i}(e)-t_{Q^2,r_i}(e)
\right).
}
\qquad[\text{Q.E.D.}]
```

## Bounded-Index Möbius Transform

Define

```math
\mathcal M_i(Q)
=
\sum_{e\mid P_i}
\mu(e)
\left(
t_{Q,r_i}(e)-t_{Q^2,r_i}(e)
\right).
```

Then

```math
\boxed{
D_i=\frac{\mathcal M_i(Q)}{r_i}.
}
```

Using the exact floor formula,

```math
\boxed{
\mathcal M_i(Q)
=
\sum_{e\mid P_i}\mu(e)
\left(
\left[
\left\lfloor\frac{Q-1}{e}\right\rfloor
\right]_{r_i}^{(0)}
-
\left[
\left\lfloor\frac{Q^2-1}{e}\right\rfloor
\right]_{r_i}^{(0)}
\right).
}
```

Every individual coefficient difference has absolute value at most `r_i-1`.
Taking absolute values term by term would still give an exponential divisor
bound, so the Möbius signs remain essential.

## Exact Weighted Budget

Candidate #23 uses

```math
\mathcal E_D
=
\sum_i
w_i
\frac{r_i}{2(r_i-2)}
D_i^2.
```

Substituting `D_i=mathcal M_i(Q)/r_i` gives

```math
\boxed{
\mathcal E_D
=
\sum_i
\frac{w_i}{2r_i(r_i-2)}
\mathcal M_i(Q)^2.
}
\qquad[\text{Q.E.D.}]
```

This is the weakest exact coefficient-level interface currently known for
candidate #23.

## Consequence For The Proof Strategy

The remaining theorem is no longer an unspecified boundary-error estimate.
It is the explicit weighted mean-square statement

```math
\sum_i
\frac{w_i}{r_i(r_i-2)}
\mathcal M_i(Q)^2
\le
\text{usable initial-scale allowance}.
```

It is noncircular: `mathcal M_i(Q)` is defined from the endpoints, installed
divisors, and incoming prime, even if the final 2-gap population is zero.

Finite inclusion--exclusion alone does not bound this mean square. A useful
proof must exploit cancellation of the Möbius transform, averaging across
the incoming primes, correlation between the two endpoint lift indices, or
averaging across future heads `Q`.

## Related

- [Accepted-strike density as a Möbius boundary sum](
  accepted-strike-density-boundary-decomposition.md
  )
- [Prime-square window boundary residue formula](
  prime-square-window-boundary-residue-formula.md
  )
- [Accepted-strike divisor activation kernel](
  accepted-strike-divisor-activation-kernel.md
  )
- [Accepted-anchor strike density](
  ../../candidates/accepted-anchor-strike-density.md
  )
