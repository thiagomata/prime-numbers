# Filter-Seven Harmful Excess Is Boundary-Sized

**Status:** Mathematically proved exact interval-discrepancy theorem.
Stainless verification is not claimed.

## Meaning

The Harmful-Capacity Excess Envelope property bounds each harmful-excess coefficient by maximizing over all
residue histograms compatible with a common capacity. At filter `7`, that
forgets almost all available arithmetic. The incoming 2-gap starts are the
fixed classes `11,17,29 modulo 30`, so their filter-`7` harmful excess is a
mean-zero periodic sequence modulo `210`.

This property computes the complete period and proves the sharp universal
interval bound

```math
\boxed{|b_7|\le\frac{18}{7}.}
```

The bound is independent of the square-window length. Consequently, the
actual filter-`7` energy is boundary-sized, while the separate capacity
envelope can charge an amount proportional to the square of the window
length. This is the first concrete localized saving after the properties from Filter-Seven Cut Failure through Capacity Stability Gap
exhausted the separate/native capacity routes.

The theorem controls one fixed early layer. It does not yet bound the growing
collection of later harmful-excess coefficients.

## Setup

Immediately before filter `7`, filters `2`, `3`, and `5` are installed.
the Local Count Shot-Capacity Premise property's exact seven-layer analysis proves that the complete 2-gap
starts are precisely

```math
x\equiv11,17,29\pmod{30}.
```

Define the incoming-start indicator

```math
F_7(x)
=
\mathbf1_{\{11,17,29\}\bmod30}(x).
```

Filter `7` destroys a start exactly when `x` or `x+2` is divisible by `7`.
Thus

```math
h_7(x)
=
\mathbf1_{\{0,5\}\bmod7}(x).
```

The centered harmful-excess observable is

```math
g_7(x)
=
F_7(x)
\left(
h_7(x)-\frac27
\right).
```

For any integer interval `I`, the actual filter-`7` harmful excess is

```math
b_7(I)=\sum_{x\in I}g_7(x).
```

Because the two congruence systems have coprime moduli `30` and `7`, this
observable is periodic modulo

```math
\operatorname{lcm}(30,7)=210.
```

## Exact Modulo-210 Certificate

The 21 admissible start residues in increasing order are

```math
\begin{aligned}
&11,17,29,41,47,59,71,77,89,101,107,\\
&119,131,137,149,161,167,179,191,197,209.
\end{aligned}
```

It is convenient to clear the denominator `7`. At an admissible residue,

```math
7g_7(x)
=
\begin{cases}
5,&x\equiv0,5\pmod7,\\
-2,&\text{otherwise}.
\end{cases}
```

In the residue order above, the exact weight sequence is

```math
\boxed{
-2,-2,-2,-2,5,-2,-2,5,5,-2,-2,5,5,-2,-2,5,-2,-2,-2,-2,-2.
}
```

There are six harmful weights `5` and fifteen harmless weights `-2`, so the
complete-period sum is

```math
6\cdot5+15\cdot(-2)=0.
```

This is the Paired CRT Primorial Scale property's complete-block cancellation specialized to filter `7`.

## Sharp Cumulative-Sum Range

Starting from zero, the cumulative sums of the displayed integer weights are

```math
\begin{aligned}
0,&-2,-4,-6,-8,-3,-5,-7,-2,3,1,-1,\\
&4,9,7,5,10,8,6,4,2,0.
\end{aligned}
```

Their minimum and maximum are

```math
\min=-8,
\qquad
\max=10.
```

Every non-wrapping consecutive subsum is the difference of two cumulative
sums, so its absolute value is at most

```math
10-(-8)=18.
```

Every wrapping subsum is the negative of its non-wrapping complement because
the full-period sum is zero. It obeys the same bound. Therefore every cyclic
interval in one period satisfies

```math
\left|
\sum 7g_7(x)
\right|
\le18.
```

The bound is attained by the consecutive admissible residues from `47`
through `161`, whose weights sum to `18`. Hence `18` is the sharp universal
cyclic-interval constant.

## Arbitrary Integer Intervals

Partition an arbitrary integer interval `I` into complete consecutive blocks
of length `210` and one remainder interval of length less than `210`. Every
complete block contributes zero. The remainder selects one cyclic interval of
the residue certificate above. Consequently,

```math
\begin{aligned}
|7b_7(I)|
&\le18,\\
|b_7(I)|
&\le\boxed{\frac{18}{7}}.
\end{aligned}
\qquad[\text{Q.E.D.}]
```

The integer interval from `47` through `161` within one period attains
`b_7=18/7`, so the constant is sharp over arbitrary intervals.

## Exact Energy Consequence

In candidate #24's complete conditioned chain, filter `7` has index `i=1`.
Its energy coefficient is

```math
\alpha_1
=
\frac{w_1}{2a_1}
=
\frac{49P_m}{30}.
```

Therefore its actual contribution to the harmful-excess energy satisfies

```math
\begin{aligned}
\alpha_1b_7^2
&\le
\frac{49P_m}{30}
\left(\frac{18}{7}\right)^2\\
&=
\boxed{\frac{54}{5}P_m}.
\end{aligned}
```

Here $D=Q^2-Q-3$ is the eligible-window population proxy from
[Capacity Stability Gap](capacity-stability-gap-cannot-rescue-capacity-envelope.md).

By contrast, under candidate #17, the Seven-Layer Density Floor property and #81 give the separate
capacity-envelope charge

```math
\alpha_1M_1
\ge
\frac{P_mD^2}{1080}.
```

Their ratio obeys

```math
\frac{
(54/5)P_m
}{
P_mD^2/1080
}
=
\boxed{\frac{11664}{D^2}},
```

which tends to zero. Thus the `D^2` filter-`7` obstruction in the separate
capacity envelope is entirely an artifact of discarding the known periodic
residue structure at this layer.

## Boundary

This theorem neither proves candidate #24 nor refutes the Harmful-Capacity Excess Envelope property. Property
#70 is sharp given only population and common capacity; the Filter-Seven Excess Bound property adds
strictly more information by using the exact ordered residue pattern.

The same argument gives a finite discrepancy constant for every fixed layer,
because its observable is mean-zero and periodic over its native modulus.
That observation alone is not uniform in the layer index: the native modulus
and a naive cumulative-sum constant can grow rapidly. The next theorem must
control that growth strongly enough to sum the coefficients through a chain
whose length increases with `Q`.

The general coefficient is already identified by the Sampling-Density Recombination property as

```math
b_i=\delta_{0,i}+\delta_{-2,i}.
```

Thus its cumulative-sum problem is exactly the two-residue accepted-boundary
discrepancy studied by candidate #23. Independent inclusion--exclusion terms
give a bound exponential in the number of installed primes, while direct
total variation grows with the native accepted population. Neither is a
scalable continuation of this theorem. Further progress requires genuinely
new signed mean-square or cross-layer cancellation, not enumeration of each
larger native period.

No empirical evidence is used.

## Related

- [Exact Seven-Layer Capacity Floor](exact-seven-layer-capacity-floor.md)
- [Paired Harmful-Excess CRT Orthogonality Has Primorial Scale](paired-harmful-excess-crt-orthogonality-has-primorial-scale.md)
- [Sharp Harmful-Capacity Excess Envelope](sharp-harmful-capacity-excess-envelope.md)
- [Capacity Stability Gap Cannot Rescue the Capacity Envelope](capacity-stability-gap-cannot-rescue-capacity-envelope.md)
- [Endpoint Sampling and Strike Density Recombine the Harmful Residues](endpoint-sampling-strike-density-harmful-residue-bridge.md)
- [Candidate #23: Accepted-Anchor Strike Density](../../candidates/accepted-anchor-strike-density.md)
- [Candidate #24: Weighted Harmful-Excess Quadratic Survival](../../candidates/weighted-harmful-excess-quadratic-survival.md)
