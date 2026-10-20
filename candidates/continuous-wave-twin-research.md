# Five wave-based directions for continuous twin sieves

**Status:** Unnumbered mathematical research program. The formulas below are
algebraic starting points; written proofs and limitations are the next work.
Open distribution questions are not established consequences of the identities.
No global novelty claim or new empirical evidence is asserted.

## Context

Use the continuous waves and activations from
[Uniform Continuous Divisor Sieve](../properties/sieve-sequence/uniform-continuous-divisor-sieve.md):

```math
W_m(t)=\left|\frac1m\sum_{r=0}^{m-1}e^{2\pi irt/m}\right|^2,
\qquad a_m(t)=\min(1,\max(0,t-m)).
```

These definitions have no removable singularities. The equivalent sine ratio
and the locally finite infinite sum are derived in the linked note. This
program complements the earlier [continuous-contact directions](
continuous-contact-research-directions.md), concentrating on the wave algebra.
It does not add numbered sufficient-condition hypotheses to the main catalog.

## 1. Folding translated waves

For integers m>=2 and k>=1, investigate the exact folding identity

```math
\sum_{j=0}^{k-1}W_{km}(t+jm)=W_m(t).
```

In particular, W_4(t)+W_4(t+2)=W_2(t). This fits the twin shift directly.
With activation, however, the pair-filter contribution

```math
V_4(t)=a_4(t)W_4(t)+a_4(t+2)W_4(t+2)
```

is guaranteed to equal W_2(t) once both activations are fully on, for t>=5.
Equality can also occur at isolated earlier inputs.

**Open direction:** Reorganize translated filter groups into lower-frequency
waves plus explicit activation-boundary terms. Determine what is actually
compressed; one translated identity does not compress all unshifted filters.

## 2. Bounded continuous twin amplitude

For M>=1 and real t>=2, define

```math
\begin{aligned}
J_m(t)&=1-a_m(t)W_m(t),\\
A_M(t)&=\cos^2(\pi t)\prod_{m=2}^{M}J_m(t)J_m(t+2),\\
\widetilde T_M(t)&=t+i\bigl(1-A_M(t)\bigr).
\end{aligned}
```

The empty product is one. Each factor lies in [0,1]. At integer starts the
amplitude is exactly one if both endpoints survive and zero otherwise.
Noninteger inputs have cos^2(pi t)<1, preventing accidental real-axis contacts
of the resulting curve. The infinite product is locally finite, with all
factors indexed m>=t+2 equal to one.

**Open direction:** Compare this bounded height with additive divisor counts
for Fourier estimates and integer sampling. Positive continuous area alone
does not imply the existence of a unit-amplitude integer start; this shortcut
must be audited before using an integral to count twins.

## 3. Quadratic divisor-height minimum

For odd integer n>=3, n and n+2 are coprime. Let h be the completed additive
height, h(n)=tau(n)-2, and B(n)=h(n)+h(n+2). Divisor multiplication suggests

```math
\begin{aligned}
E(n)&=h\bigl(n(n+2)\bigr)-2\\
&=2B(n)+h(n)h(n+2).
\end{aligned}
```

The twin level is E(n)=0, equivalently h(n(n+2))=2; every other odd start has
E(n)>=2. The restriction to odd starts is essential: n=2 gives the false
quadratic-level example n(n+2)=8.

**Open direction:** Investigate whether estimates at the quadratic argument
can control joint survival more effectively. The displayed identity alone
re-encodes the same information, and the larger argument may cost more.

## 4. Sixfold coordinate and filter reduction

Except for (3,5), twin primes have endpoints6k-1 and6k+1 for integer k>=1.
Every divisor of either endpoint is coprime to6. Consider

```math
G(k)=\sin^2(\pi k)+
\sum_{\substack{m\ge5\\\gcd(m,6)=1}}
\left[a_m(6k-1)W_m(6k-1)+a_m(6k+1)W_m(6k+1)\right].
```

At integer k>=1 this equals the original pair height at start6k-1.
Off-grid it is a new interpolation: its sine baseline enforces integer k.
The infinite sum is locally finite on k>=1. It removes the filter indices
containing factors2 or3, but still includes composite indices coprime to6.

**Open direction:** Measure or bound the remaining arithmetic interactions
after forced parity/modulo3 structure has been removed. The familiar6k±1
restriction is not itself a new distribution result; it excludes (3,5), which
must be represented separately if all twins are desired.

## 5. Independent lower bounds for integer contact counts

For a finite set I of integer starts above the installed filter range,

```math
N_M(I)=\sum_{n\in I}A_M(n)
```

counts candidate pairs exactly. A positive bound in an appropriate
prime-certified window would force a twin pair there.

**Open direction:** Obtain an independent estimate of this count from wave
coefficients, cancellations or other structure. Directly computing the sum,
renaming the terminal count, or using positivity between integers is not an
independent lower bound. Existing complete-period Fourier results do not
automatically control a short interval.

## Investigation order and existing boundaries

First prove folding and its activation correction. Then prove the bounded
construction, audit its continuous/discrete sampling distinction, establish
the quadratic identity and sixfold reduction, and record what remains open
about independent bounds. Each exact result should have a complete proof
before becoming a reusable input.

Relevant existing work includes [Fourier Correlation Bound](
../properties/sieve-sequence/fourier-two-gap-correlation-prefix-bound.md),
[Localized Fourier Boundary](
../properties/sieve-sequence/localized-two-gap-correlation-fourier-boundary.md),
and [Weighted Deletion Conservation](
../properties/sieve-sequence/weighted-deletion-conservation-law.md).

The waves are scaled Fejer kernels, whose standard Fourier properties are
described in [MIT's Topics in Fourier Analysis notes](https://ocw.mit.edu/courses/res-18-015-topics-in-fourier-analysis-spring-2024/mitres_18_015_s24_full_lec.pdf).
The proposed activated sieve constructions and research obligations are not
attributed to that reference.
