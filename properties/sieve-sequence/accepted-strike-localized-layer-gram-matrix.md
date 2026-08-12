# Accepted-Strike Localized Layer Gram Matrix

**Status:** Mathematically proved. Stainless verification is not claimed.

## Meaning

Restricting the centered strike functions to the actual safe window destroys
their complete-period orthogonality in an exactly computable way. Every
off-diagonal Gram entry is a later accepted-strike discrepancy divided by an
earlier incoming prime.

This converts candidate #23 into a finite local spectral problem. It also
shows why the generic Gram trace bound makes no progress: it is exactly the
sum of the separate per-layer Cauchy bounds. A successful use of the local
matrix must control its largest eigenvalue more sharply by exploiting the
signed off-diagonal structure.

## Setup

Use the nested squarefree chain

```math
P_{i+1}=P_i r_i
\qquad(0\le i<m)
```

and an integer interval `I` of length `L`. Define

```math
g_i(n)
=
\mathbf 1_{\gcd(n,P_i)=1}
\left(
\mathbf 1_{r_i\mid n}-\frac1{r_i}
\right),
```

```math
A_i
=
\#\{n\in I:\gcd(n,P_i)=1\},
```

and

```math
D_i
=
\sum_{n\in I}g_i(n).
```

Thus `D_i=H_i-A_i/r_i` is candidate #23's accepted-strike
discrepancy. Let

```math
G_{ij}
=
\sum_{n\in I}g_i(n)g_j(n)
```

be the local Gram matrix.

## Exact Off-Diagonal Entries

Suppose `i<j`. If `g_j(n)` is nonzero, then `n` is coprime to `P_j`.
Because `r_i` divides `P_j`, this implies `r_i` does not divide `n`.
Therefore `g_i(n)=-1/r_i` throughout the support of `g_j`, and

```math
\begin{aligned}
G_{ij}
&=
\sum_{n\in I}g_i(n)g_j(n)\\
&=
-\frac1{r_i}\sum_{n\in I}g_j(n)
&&[\text{Nested support}]\\
&=
\boxed{-\frac{D_j}{r_i}}
&&[\text{Definition of }D_j].
\end{aligned}
```

By symmetry,

```math
\boxed{
G_{ij}
=
-\frac{D_{\max(i,j)}}{r_{\min(i,j)}}
\qquad(i\ne j).
}
```

Complete-period orthogonality from the Cross-Layer CRT Orthogonality property is the special case in which
every complete-period discrepancy `D_j` is zero.

## Exact Diagonal Entries

Among the `A_i` accepted points, let `H_i` be divisible by `r_i`. Directly,

```math
\begin{aligned}
G_{ii}
&=
H_i\left(1-\frac1{r_i}\right)^2
+
(A_i-H_i)\frac1{r_i^2}\\
&=
H_i\left(1-\frac2{r_i}\right)
+
\frac{A_i}{r_i^2}
&&[\text{Simplification}].
\end{aligned}
```

Substituting `H_i=A_i/r_i+D_i` gives

```math
\boxed{
G_{ii}
=
A_i\frac{r_i-1}{r_i^2}
+
\left(1-\frac2{r_i}\right)D_i.
}
```

Although the second term is signed, the complete expression is nonnegative
because it is a squared norm.

## Weighted Spectral Reduction

Let

```math
c_i
=
w_i\frac{r_i}{2(r_i-2)}
```

and let `C` be the diagonal matrix with entries `c_i`. Candidate #23's energy
is

```math
\mathcal E_D
=
\sum_i c_iD_i^2.
```

Apply the analysis operator of the local vectors
`sqrt(c_i) g_i` to the constant vector `1_I`. Its Gram matrix is
`C^(1/2) G C^(1/2)`, so

```math
\boxed{
\mathcal E_D
\le
L\,
\lambda_{\max}\left(C^{1/2}GC^{1/2}\right).
}
```

Every entry of this matrix is explicit in `A_i`, `D_i`, `r_i`, and `w_i`.
This is a local-window normalization: the final primorial from the Cross-Layer CRT Orthogonality property
has disappeared.

## Why The Generic Trace Bound Does Not Advance The Proof

Because the weighted Gram matrix is positive semidefinite,

```math
\lambda_{\max}\left(C^{1/2}GC^{1/2}\right)
\le
\operatorname{tr}(CG).
```

Consequently,

```math
\boxed{
\mathcal E_D
\le
L\sum_i c_i
\left[
A_i\frac{r_i-1}{r_i^2}
+
\left(1-\frac2{r_i}\right)D_i
\right].
}
```

This is exactly what results from applying Cauchy separately to

```math
D_i=\langle\mathbf 1_I,g_i\rangle_I
```

and then summing. The trace deletes every off-diagonal entry, so the new Gram
identity supplies no gain under this generic inequality.

For an entirely nonnegative bound, put

```math
B
=
\sum_i c_iA_i\frac{r_i-1}{r_i^2},
\qquad
C_0
=
\sum_i c_i\left(1-\frac2{r_i}\right)^2.
```

Weighted Cauchy gives

```math
\sum_i
c_i\left(1-\frac2{r_i}\right)D_i
\le
\sqrt{C_0\mathcal E_D}.
```

Hence

```math
\mathcal E_D
\le
L\left(B+\sqrt{C_0\mathcal E_D}\right).
```

Solving this quadratic inequality for `sqrt(mathcal E_D)` yields

```math
\boxed{
\sqrt{\mathcal E_D}
\le
\frac{
L\sqrt{C_0}
+
\sqrt{L^2C_0+4LB}
}{2}.
}
```

The `L sqrt(C_0)` term is of generic interval scale and does not
automatically fit candidate #21's much smaller remaining allowance. Thus the
trace/self-bound route is a classification result, not a proof of candidate
#23.

## Remaining Spectral Theorem

The exact matrix isolates a sharper possible route:

```math
\lambda_{\max}\left(C^{1/2}GC^{1/2}\right)
\ll
\operatorname{tr}(CG).
```

Such an improvement cannot come from positive semidefiniteness alone. It
would need arithmetic control of the signed discrepancies in

```math
G_{ij}=-\frac{D_{\max(i,j)}}{r_{\min(i,j)}}.
```

Universal sign and sign preservation are already refuted, while absolute row
sums discard the potentially useful signs. The next useful theorem must
therefore prove spectral cancellation for this nested matrix or average it
over an additional variable.

## Validation

The identities were checked with exact rational arithmetic on:

```math
I=[19,19^2),\quad P_0=30,\quad(r_0,r_1)=(7,11),
```

where

```math
(A_0,A_1)=(91,78),
\qquad
(D_0,D_1)=\left(0,-\frac1{11}\right),
```

and on

```math
I=[17,17^2),\quad P_0=6,\quad(r_0,r_1,r_2)=(5,7,11),
```

where

```math
(A_0,A_1,A_2)=(91,73,63),
```

```math
(D_0,D_1,D_2)
=
\left(-\frac15,-\frac37,-\frac8{11}\right).
```

Every diagonal and cross entry matched the displayed formulas. These finite
checks validate the derivation only.

## Related

- [Accepted-strike cross-layer CRT orthogonality](
  accepted-strike-cross-layer-crt-orthogonality.md
  )
- [Accepted-strike summatory coprime remainder](
  accepted-strike-summatory-coprime-remainder.md
  )
- [Accepted-strike quadratic variation](
  accepted-strike-quadratic-variation.md
  )
- [Accepted-anchor strike density](
  ../../candidates/accepted-anchor-strike-density.md
  )
