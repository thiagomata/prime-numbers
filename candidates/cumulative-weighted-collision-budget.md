# Cumulative Weighted Collision Budget

**Candidate hypothesis:** Unproved and potentially false.

**Chain recurrence:** Mathematically proved.

**Conditional implication:** Mathematically proved.

**Empirical status:** NOT EVALUATED — this is the primary algebraic composition
framework, not the primary missing theorem. The next theorem is a weighted
aggregate bound for candidate #22's harmless-class energy, together with
candidate #13's endpoint-sampling and candidate #23's accepted-strike error
budgets. Extending the existing data is not the current step.

## Purpose

Pointwise candidates ask every incoming prime to sample the current 2-gap
population evenly. Hereditary survival only needs the total error accumulated
through the chain to stay below the multiplicative survival main term.

This candidate keeps the exact layer collision energies but combines them with
the weights forced by later filters. It allows individual layers to have large
residue bias when their contribution to the final population is sufficiently
attenuated.

## Setup

Fix a future prime head `Q` and let

```math
5\le r_0<r_1<\cdots<r_{m-1}<Q
```

be the missing primes installed in the conditioned chain. Let `S_i` be the
complete 2-gap starts in

```math
W_Q=[Q,Q^2)
```

immediately before filter `r_i`, and write

```math
N_i=|S_i|.
```

For the residue counts

```math
c_{i,a}
=
\#\{x\in S_i:x\equiv a\pmod{r_i}\},
```

define

```math
V_i
=
\sum_{a\bmod r_i}
\left(c_{i,a}-\frac{N_i}{r_i}\right)^2.
```

Set

```math
a_i=1-\frac2{r_i},
\qquad
A_{u,v}=\prod_{j=u}^{v-1}a_j,
\qquad
w_i=A_{i+1,m}.
```

## Candidate Hypothesis

For infinitely many future heads `Q`, suppose the complete conditioned chain
satisfies

```math
\boxed{
\sum_{i=0}^{m-1}
w_i\sqrt{2V_i}
<
N_0A_{0,m}.
}
```

This is the direct weighted collision budget.

A stronger second-moment form, convenient for an aggregate energy estimate,
is

```math
\boxed{
2
\left(\sum_{i=0}^{m-1}w_i\right)
\left(\sum_{i=0}^{m-1}w_iV_i\right)
<
\left(N_0A_{0,m}\right)^2.
}
```

Weighted Cauchy--Schwarz proves that the second displayed condition implies
the first.

## Why The Candidate Is Sufficient

At layer `i`, the exact harmful count and the two-class energy lemma give

```math
N_{i+1}
\ge
a_iN_i-\sqrt{2V_i}.
```

The proved chain induction unrolls these inequalities:

```math
N_m
\ge
N_0A_{0,m}
-
\sum_{i=0}^{m-1}
w_i\sqrt{2V_i}.
```

The direct candidate budget makes the right-hand side positive. Therefore

```math
N_m>0.
```

After every missing prime below `Q` has been installed, a complete 2-gap
remaining in `[Q,Q^2)` is square-safe and certifies a twin-prime pair.
Infinitely many heads satisfying the budget would give infinitely many such
certificates.

The recurrence and implication are proved in
[Weighted collision-energy chain survival](
../properties/sieve-sequence/weighted-collision-energy-chain-survival.md
).

## Fixed-Set Algebraic Form

Every changing population can be represented on the initial set `S_0` by

```math
f_i(x)
=
\prod_{j<i}
\mathbf 1_{r_j\nmid x(x+2)}.
```

The weighted energy in the second-moment candidate has the exact form

```math
\sum_iw_iV_i
=
\sum_{x,y\in S_0}
\sum_i
w_if_i(x)f_i(y)
\left(
\mathbf 1_{r_i\mid(x-y)}-\frac1{r_i}
\right).
```

Define `tau(x)` as the first layer that hits `x` or `x+2`, with `tau(x)=m`
for a final survivor, and define the energy stopping index

```math
s(x)=\min(\tau(x)+1,m).
```

A start hit at layer `tau(x)<m` is still present immediately before that
filter, so `f_i(x)=1` exactly when `i<s(x)`. For `d=x-y`, the pair sum stops at

```math
t(x,y)=\min(s(x),s(y)):
```

```math
\boxed{
\sum_{i<t(x,y)}
w_i
\left(
\mathbf 1_{r_i\mid d}-\frac1{r_i}
\right).
}
```

For `x!=y`, the positive primes in this kernel divide a nonzero difference
with

```math
|d|<Q^2-Q.
```

Their product is therefore smaller than `Q^2`. This is the candidate's
concrete arithmetic input.

The centering term has an exact telescope. With

```math
w_{-1}=A_{0,m},
```

the adjacent weights satisfy

```math
\frac{w_i}{r_i}
=
\frac{w_i-w_{i-1}}2.
```

Therefore the stopped kernel is exactly

```math
\boxed{
\sum_{\substack{i<t(x,y)\\r_i\mid d}}w_i
-
\frac{w_{t(x,y)-1}-A_{0,m}}2
}
```

when `t(x,y)>=1`, and is zero when `t(x,y)=0`. A pair difference with no
relevant prime divisor contributes nonpositively. The proof target should
retain this negative term rather than bounding only the positive divisor sum.

## First-Deletion Audit

Grouping ordered pairs by their corrected common energy stop gives an exact
layer decomposition. If `k_{i,0}` and `k_{i,-2}` are the two harmful class
sizes, then the terminal pair contribution at layer `i` is

```math
T_i
=
w_i
\left[
k_{i,0}^2+k_{i,-2}^2
-
\frac{N_i^2-N_{i+1}^2}{r_i}
\right].
```

The complete energy is

```math
\boxed{
\sum_iw_iV_i
=
\sum_iT_i
+
\sum_iw_iV_{r_i}(S_{i+1}).
}
```

The first sum has a negative balanced main term plus errors in total harmful
excess and left/right endpoint imbalance. The second sum is the same-prime
variance of the post-filter survivors among the `r_i-2` harmless classes.

This split identifies the missing asymmetric theorem, but three black-box
routes do not prove it:

- earlier pair histories telescope exactly to the displayed post-filter
  variances;
- harmful count and endpoint imbalance do not restrict concentration among
  harmless classes;
- applying the same sixfold class capacity to both harmful and harmless
  classes recombines to the direct bound

  ```math
  V_i
  \le
  B_iN_i-\frac{N_i^2}{r_i},
  \qquad
  B_i=\left\lfloor\frac{L}{6r_i}\right\rfloor+1.
  ```

Thus symmetric capacity loses the terminal cancellation.

## Practical Proof Program

The next proof should proceed through small lemmas:

1. **Endpoint asymmetry.** Use unsigned and signed endpoint observables to
   control total harmful excess `b_i` and endpoint imbalance `Delta_i`.
2. **Strike density.** Combine endpoint sampling with candidate #23; the exact
   bridge is

   ```math
   b_i=H_i\beta_i+2N_i\varepsilon_i.
   ```

3. **Harmless dispersion.** State an upper bound for
   `V_{r_i}(S_{i+1})` normalized by the actual survivor population. Check that
   it is not merely candidate #20 on the smaller harmless alphabet.
4. **Asymmetric composition.** Insert the endpoint and harmless bounds into
   the exact terminal decomposition without replacing both sides by the same
   class capacity.
5. **Constant audit.** Test the resulting weighted sum against the exact
   second-moment budget. Constants remain load-bearing.

This is a precise dispersion-style problem on a fixed finite set, not an
appeal to probabilistic independence.

## Relation To Other Candidates

- **#12:** controls each residue class at each layer. Candidate #21 needs only
  a weighted aggregate of second moments across the chain.
- **#19:** gives an unconditional absolute one-layer destruction cap but needs
  a large hereditary population floor. Candidate #21 replaces that floor with
  a cumulative correlation budget.
- **#20:** proposes the pointwise benchmark `V_i<=N_i`. Candidate #21 permits
  some layers to violate that scale if the complete weighted budget remains
  small.
- **#10:** controls a post-filter safe-window count discrepancy. It does not
  directly control `epsilon_i=H_i/A_i-1/r_i`; candidate #23 is the separate
  accepted-strike-density theorem.
- **#13:** the unsigned endpoint observable controls total destruction; adding
  the signed left-minus-right observable controls `Delta_i`. Together with
  candidate #23 it bounds both terminal errors, but not harmless-class
  dispersion.
- **#14:** supplies a different capacity mechanism once a suitable local
  cluster exists. Candidate #21 directly controls total conditioned survival
  and can be used independently of close-pair placement.
- **#2:** remains the terminal local-surplus target. Candidate #21 offers a
  possible structural explanation for why cumulative harmful shooting cannot
  exhaust the 2-gap population.

## Limitation

The weighted budget is unproved and is strong enough to imply final
square-window positivity. It may therefore retain the full parity difficulty.
Its value is not that the wall has disappeared, but that the missing theorem is
now an explicit aggregate bilinear estimate with exact weights and stopping
times.

The product bound on prime divisors controls one pair difference, not the sum
over all pairs. A worst-pair estimate multiplied by `N_0^2` is likely too
large. Success requires aggregate divisor incidence, cancellation from the
centered term, or an inequality that uses the nested deletion weights.

No current `.holds` lemma bounds this weighted energy. Existing verified
results provide complete-period counts, exact copy/filter frequency, and
copy-or-merge dynamics; a formal Scala lemma should be attempted only after
the mathematical aggregate bound is established.

## Established Inputs

- [Weighted collision-energy chain survival](
  ../properties/sieve-sequence/weighted-collision-energy-chain-survival.md
  )
- [Two-class survival from residue collision energy](
  ../properties/sieve-sequence/two-class-survival-from-collision-energy.md
  )
- [First-deletion pair terminal energy](
  ../properties/sieve-sequence/first-deletion-pair-terminal-energy.md
  )
- [Two endpoint observables separate harmful excess and imbalance](
  ../properties/sieve-sequence/two-endpoint-observables-separate-harmful-excess-and-imbalance.md
  )
- [Absence of 2-gaps is stable](
  ../properties/sieve-sequence/absence-of-two-gaps-is-stable.md
  )
- [Square-safe certification](
  ../properties/sieve-sequence/safe-window-two-gaps-certify-twin-primes.md
  )
