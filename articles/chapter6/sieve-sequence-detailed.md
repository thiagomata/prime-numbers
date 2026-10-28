# Sieve Sequence Stages and Transitions: A Detailed Guide

**Side version of:** [Formal Verification of Sieve Sequence Stages and Their
Transitions](sieve-sequence.md)

This is a detailed companion version. It does not replace the full article.
Its purpose is to slow down the advanced steps, show the arithmetic in small
pieces, and make the proof boundary easier to see.

## 1. What A Sieve Stage Is

A sieve stage has two pieces of data:

- a current head prime, written `h`;
- all smaller primes, used as filters.

At the stage headed by `h = 5`, the installed filters are `2` and `3`. The
accepted values are the integers at least `5` that are not divisible by `2` or
`3`:

```text
5, 7, 11, 13, 17, 19, 23, 25, 29, 31, ...
```

Notice the important common trap: `25` appears. That is not a mistake. The
filter `5` has not been installed yet, so `25` is still accepted at the stage
headed by `5`. A stage is not "the list of all primes." It is the list of
numbers that survive the filters installed so far.

In the full article, the accepted-value predicate is written as

```math
A_S(v)
\Longleftrightarrow
v \ge h
\text{ and no installed prime } q \text{ divides } v.
```

The sequence `l_0, l_1, l_2, ...` then means:

```math
\begin{aligned}
l_0 &= h,\\
l_{k+1} &= \text{the next accepted value after } l_k.
\end{aligned}
```

So for `h = 5`, we get:

```math
\begin{aligned}
l_0 &= 5,\\
l_1 &= 7,\\
l_2 &= 11,\\
l_3 &= 13.
\end{aligned}
```

This is verified in the source article through the `SpecSieveSequence`
contracts and the properties linked from
[`articles/chapter6/sieve-sequence.md`](sieve-sequence.md#3-linear-stage-semantics).

## 2. Why A Finite Cycle Can Describe An Infinite Stage

At a stage, multiply all installed filter primes together. Call that product
`M`.

For `h = 5`, the installed filters are `2` and `3`, so

```math
M = 2 \cdot 3 = 6.
```

Adding `6` to a number does not change whether it is divisible by `2` or `3`.
For example:

```text
5, 11, 17, 23, 29, ...
```

all have the same remainders modulo `2` and modulo `3`. Likewise:

```text
7, 13, 19, 25, 31, ...
```

all have the same remainders modulo `2` and modulo `3`.

That is the whole reason the stage repeats. In symbols:

```math
\begin{aligned}
q \mid M
&\Longrightarrow v+M \equiv v \pmod q,\\
v \text{ passes filter } q
&\Longleftrightarrow v+M \text{ passes filter } q,\\
v \text{ passes every installed filter}
&\Longleftrightarrow v+M \text{ passes every installed filter}.
\end{aligned}
```

The stage is infinite, but its pattern is periodic.

For `h = 5`, we have `M = 6`, so the canonical endpoint is

```text
h + M = 11.
```

The accepted values from the head up to that endpoint are

```text
5, 7, 11.
```

The gaps in that first canonical block are therefore

```text
7 - 5 = 2,
11 - 7 = 4.
```

So the cycle of gaps is `[2, 4]`, and its sum is

```math
2+4=6=M.
```

The verified model defines the canonical index `T` by the equation

```math
l_T = h + M.
```

For this example, `T = 2`, because `l_2 = 11`. The gap cycle is the list

```math
g_i = l_{i+1} - l_i
```

for `i = 0, ..., T-1`.

The key idea is:

```text
values repeat by adding M;
gaps repeat because subtracting neighboring repeated values gives the same gaps.
```

This is verified in the full article in
[Section 4](sieve-sequence.md#4-period-and-cycle-reconstruction).

## 3. Installing The Current Head As A New Filter

Now suppose the current head is `h`, and the old period contains `T` accepted
values. To move to the next stage, install `h` as a new filter.

The full article says the expanded block contains `hT` old survivors. Here is
why, slowly.

Start with one old period:

```text
T accepted values
```

To test the new filter `h`, repeat that old period `h` times:

```text
block 0: T accepted values
block 1: T accepted values
...
block h-1: T accepted values
```

So before applying the new filter:

```math
N_{\mathrm{old}} = hT.
```

Fix one position `r` inside the old period. The `h` lifted copies of that one
old value look like this:

```math
l_r,\quad l_r+M,\quad l_r+2M,\quad \ldots,\quad l_r+(h-1)M.
```

Because `h` is a new prime, it is not one of the old filters. Therefore `h`
does not divide the old product `M`. That means adding `M` repeatedly walks
through all residues modulo `h`.

For a small example, take `h = 5` and a step `M` that is not divisible by `5`.
If `M mod 5 = 2`, then the offsets add

```text
0, 2, 4, 6, 8
```

which are

```text
0, 2, 4, 1, 3   modulo 5.
```

That is every residue exactly once. So among the `h` lifted copies, exactly one
is divisible by `h` and gets removed.

There are `T` positions `r`, and each position loses exactly one copy:

```math
\begin{aligned}
N_{\mathrm{old}} &= hT,\\
N_{\mathrm{removed}} &= T,\\
N_{\mathrm{survive}} &= hT - T\\
&= T(h-1).
\end{aligned}
```

This is the exact survivor count, not a probability estimate. The full verified
property is linked in
[Section 5.1](sieve-sequence.md#51-exact-survivor-count).

## 4. Why A Real 2-Gap Loses Exactly Two Lifted Copies

A 2-gap is a pair of consecutive accepted values

```math
l_{k+1} - l_k = 2.
```

When the next filter is the odd prime `p`, the pair is copied `p` times:

```math
(l_k+jM,\ l_{k+1}+jM)
\quad\text{for}\quad
j=0,1,\ldots,p-1.
```

Think of `j` as the copy number.

There is exactly one copy number where the left endpoint is divisible by `p`.
Call it `j_L`.

There is exactly one copy number where the right endpoint is divisible by `p`.
Call it `j_R`.

The advanced-looking part is proving these two copy numbers are different. The
slow version is:

1. Suppose they were the same copy number, `j`.
2. Then `p` would divide the left lifted endpoint:

```math
p \mid (l_k+jM).
```

3. It would also divide the right lifted endpoint:

```math
p \mid (l_{k+1}+jM).
```

4. If a number divides two values, it divides their difference:

```math
p \mid \big((l_{k+1}+jM)-(l_k+jM)\big).
```

5. The `jM` parts cancel:

```math
(l_{k+1}+jM)-(l_k+jM)=l_{k+1}-l_k.
```

6. Because this is a 2-gap:

```math
l_{k+1}-l_k=2.
```

7. So we would have:

```math
p \mid 2.
```

8. But `p` is an odd prime, so `p > 2`, and an odd prime cannot divide `2`.

That contradiction proves

```math
j_L \ne j_R.
```

Therefore:

```math
\begin{aligned}
\text{one lifted copy dies from the left endpoint},\\
\text{one different lifted copy dies from the right endpoint},\\
\text{so exactly two lifted copies die}.
\end{aligned}
```

Since there were `p` lifted copies total, the number with both endpoints still
alive is

```math
p - 2.
```

This is verified in the full article in
[Section 5.2](sieve-sequence.md#52-exact-lifted-copy-law-for-a-real-2-gap).

## 5. Copy-Or-Merge Gap Dynamics

After installing a new filter, some old accepted values remain and some are
removed.

Take three old consecutive values:

```text
a, b, c
```

with old gaps:

```math
b-a,\quad c-b.
```

If `b` survives, then the gap from `a` to `b` is simply copied.

If `b` is removed but `a` and `c` survive, then the new neighboring values are
`a` and `c`, so the new gap is

```math
c-a.
```

Now expand that:

```math
\begin{aligned}
c-a
&=(c-b)+(b-a)\\
&=\text{second old gap}+\text{first old gap}.
\end{aligned}
```

So filtering does only two things to gaps:

- copy a gap when the next old value survives;
- merge neighboring gaps when one or more old values are removed.

That is the "copy-or-merge" rule. The full article links the verified copy and
merge properties in
[Section 5.3](sieve-sequence.md#53-copy-or-merge-gap-dynamics).

## 6. Why The Next Head Is Prime

This part has an explicit proof boundary.

The next head is the first accepted value after `h`. It is not divisible by any
installed smaller prime. To prove it is prime, we use this ordinary number
theory fact:

```text
If n is composite, then n has a prime divisor at most sqrt(n).
```

So if we know the next head is below `h^2`, any composite next head would have a
prime divisor below `h`. But all primes below `h` are already installed filters,
so that divisor would have removed it. Contradiction.

The missing ingredient is the bound that the next accepted value is below
`h^2`. The full article treats that bound as a mathematical input from
Bertrand-style reasoning, not as a fully internal Stainless proof.

The step-by-step logic is:

```math
\begin{aligned}
n &< h^2,\\
n \text{ composite}
&\Longrightarrow
\text{some prime } q \le \sqrt n,\\
n < h^2
&\Longrightarrow
\sqrt n < h,\\
\text{so } q &< h,\\
q < h
&\Longrightarrow q \text{ is an installed filter},\\
q \mid n
&\Longrightarrow n \text{ would not be accepted}.
\end{aligned}
```

Therefore the accepted value `n` must be prime.

The full article states this boundary in
[Section 6.1](sieve-sequence.md#61-square-bound-successor-primality) and
[Section 7](sieve-sequence.md#7-exact-proof-boundary).

## 7. What This Guide Does Not Claim

This guide is deliberately narrower than the full article.

It explains the main arithmetic steps:

- why a stage is periodic;
- why the expanded block has `hT` old survivors;
- why exactly `T` of them are removed by the new head;
- why a real 2-gap loses exactly two lifted copies;
- why filtering copies or merges gaps;
- why the next-head primality argument depends on a square bound.

It does not replace the complete verified source map, the full pipeline
agreement theorem, or the open proof-work discussion in the original article.
For those details, use the canonical article:
[Formal Verification of Sieve Sequence Stages and Their Transitions](sieve-sequence.md).
