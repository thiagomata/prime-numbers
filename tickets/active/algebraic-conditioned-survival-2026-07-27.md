# Algebraic Conditioned Survival

## START HERE

Read the exact definitions in candidates #12, #13, and #14, then express the
smallest deterministic counting lemma that would make candidate #14 hereditary.
Do not run a new empirical sweep. The immediate task is to separate genuine
algebraic reductions from statements equivalent to the desired survivor.

## Goal

Develop and critically evaluate an algebraic proof program for forcing a
2-gap to survive every conditioned filter below a future square window. This
ticket is complete when the strongest defensible next theorem has an exact
statement, its dependencies on proved properties are explicit, circular or
twin-prime-equivalent formulations have been rejected, and the next formal
lemma is small enough to prove or falsify directly.

## Strategy

Treat candidate #14 as the consumer of a population-distribution theorem, not
as the theorem to attack directly. Audit three possible algebraic bridges:

1. a two-class discrepancy bound specialized to 2-gap starts (candidate #12);
2. an endpoint-observable sampling bound (candidate #13);
3. a recurrence or conserved quantity for conditioned local counts.

Prefer identities and inequalities derived from the exact copy/filter action.
Use the existing empirical results only to choose among statements; do not
collect more data. At every reduction, check whether the proposed premise is
strictly weaker than the final existence claim or merely restates it.

## Current State

- The project has strong finite support for candidates #12, #13, and #14.
- The spacing/capacity side of candidate #14 has a proved small-`k` foundation.
- The remaining obstacle is conditioned population control: bounding how many
  current 2-gaps land in the two harmful residue classes of the next prime.
- A new deterministic one-layer bound has been derived. If
  `L_Q=Q^2-Q-3`, then the harmful-hit count at incoming prime `r>=5` satisfies

  ```math
  K_r(W_Q)
  \le
  2\left(
  \left\lfloor\frac{L_Q}{6r}\right\rfloor+1
  \right).
  ```

  Consequently,

  ```math
  G_r(W_Q)
  \ge
  2\left\lfloor\frac{L_Q}{6r}\right\rfloor+3
  ```

  forces at least one 2-gap to survive that layer. This is not a discrepancy
  assumption: it follows because every post-3 start is `5 modulo 6`, while the
  incoming filter can destroy starts only in two classes modulo `r`.
- Exact multiplicative recurrence and constant additive-error approaches have
  already failed; neither should be retried without a new invariant.
- The current work is checking this bound carefully, comparing it with the
  existing order-only `k=2` threshold, and deciding how to promote the result
  as a proved property plus a narrower hereditary candidate.
- The result has now been promoted as
  `properties/sieve-sequence/harmful-residue-capacity-after-filter-three.md`
  and candidate #19,
  `candidates/sixfold-harmful-residue-capacity.md`.
- A second-moment refinement has been derived. If `c_a` counts current 2-gap
  starts in class `a modulo r`, `N=sum_a c_a`, and

  ```math
  V_r=\sum_{a\bmod r}\left(c_a-\frac Nr\right)^2,
  ```

  then the exact harmful count `K=c_0+c_{-2}` satisfies

  ```math
  K\le\frac{2N}{r}+\sqrt{2V_r}.
  ```

  Also,

  ```math
  V_r
  =
  \sum_{a\bmod r}c_a^2-\frac{N^2}{r},
  ```

  where `sum c_a^2` is the exact ordered-pair count for starts whose
  difference is divisible by `r`. This gives an alternative averaged
  algebraic target to candidate #12's worst-class discrepancy.
- The collision reduction is now promoted as
  `properties/sieve-sequence/two-class-survival-from-collision-energy.md`.
  For post-3 starts it has the exact autocorrelation form

  ```math
  C_r(S)
  =
  N+
  2\sum_{1\le h\le\lfloor L/(6r)\rfloor}
  A_S(6rh),
  ```

  where each `A_S(6rh)` counts the four-point endpoint pattern
  `{0,2,6rh,6rh+2}`.
- A concrete new candidate benchmark has emerged:

  ```math
  C_r(S)\le N+\frac{N^2}{r}.
  ```

  Together with the proved collision lemma, this forces survival whenever

  ```math
  N>\frac{2r^2}{(r-2)^2}.
  ```

  The exact integer floors are `N>=6` for `r=5`, `N>=4` for `r=7`, and
  `N>=3` for every prime `r>=11`.
- Candidate #20 has been created as
  `candidates/conditioned-residue-collision-energy.md`.
- The one-layer energy inequality unrolls exactly across a conditioned chain.
  For incoming primes `r_0<...<r_{m-1}`, define

  ```math
  a_i=1-\frac{2}{r_i},
  \qquad
  e_i=\sqrt{2V_i}.
  ```

  If `N_i` is the actual 2-gap population before layer `i`, then

  ```math
  N_{i+1}\ge a_iN_i-e_i
  ```

  and induction gives

  ```math
  N_m
  \ge
  N_0\prod_{j<m}a_j
  -
  \sum_{i<m}
  e_i
  \prod_{i<j<m}a_j.
  ```

  This exposes a cumulative weighted-energy theorem that could replace
  pointwise discrepancy at every layer.
- The chain recurrence is now promoted as
  `properties/sieve-sequence/weighted-collision-energy-chain-survival.md`.
  Every changing population has an exact fixed-initial-set representation:

  ```math
  f_i(x)=\prod_{j<i}\mathbf 1_{r_j\nmid x(x+2)},
  ```

  and

  ```math
  \sum_iw_iV_i
  =
  \sum_{x,y\in S_0}\sum_i
  w_if_i(x)f_i(y)
  \left(
  \mathbf 1_{r_i\mid(x-y)}-\frac1{r_i}
  \right).
  ```
- Define the deletion time `tau(x)` as the first layer that hits `x` or `x+2`,
  or `m` if no layer does, and define

  ```math
  s(x)=\min(\tau(x)+1,m).
  ```

  Since a start is still present immediately before its first hitting filter,

  ```math
  f_i(x)f_i(y)
  =
  \mathbf 1_{i<\min(s(x),s(y))}.
  ```

  For a pair difference `d=x-y`, the inner energy kernel is therefore a
  stopped weighted divisor sum over primes dividing `d`.
- Candidate #21 has been created as
  `candidates/cumulative-weighted-collision-budget.md` and is the primary
  algebraic target.
- The centering part of every stopped kernel telescopes exactly. With
  `w_{-1}=A_{0,m}`,

  ```math
  \frac{w_i}{r_i}=\frac{w_i-w_{i-1}}2,
  ```

  so the pair kernel stopped at `t>=1` is

  ```math
  \sum_{\substack{i<t\\r_i\mid d}}w_i
  -
  \frac{w_{t-1}-A_{0,m}}2.
  ```

  A difference with no relevant incoming prime divisor contributes
  nonpositively.
- There is an exact weighted deletion conservation law. Define the signed
  harmful excess

  ```math
  b_i=K_i-\frac{2N_i}{r_i}.
  ```

  Then

  ```math
  N_{i+1}=a_iN_i-b_i
  ```

  exactly, and

  ```math
  \boxed{
  \sum_{i=0}^{m-1}w_ib_i
  =
  N_0A_{0,m}-N_m.
  }
  ```

  At the individual-gap level, an initial gap killed at layer `t` contributes
  exactly `A_{0,m}` to the weighted signed sum, while a final survivor
  contributes `A_{0,m}-1`.
- The weighted collision energy now has an exact diagonal/off-diagonal
  decomposition. With

  ```math
  \kappa_d(t)
  =
  \sum_{i<t}
  w_i
  \left(
  \mathbf 1_{r_i\mid d}-\frac1{r_i}
  \right),
  ```

  and every start in `S_0` congruent to `5 modulo 6`,

  ```math
  \sum_iw_iV_i
  =
  \sum_{x\in S_0}\kappa_0(s(x))
  +
  2\sum_{h\ge1}
  \sum_{\substack{x,x+6h\in S_0}}
  \kappa_{6h}
  \left(
  \min(s(x),s(x+6h))
  \right).
  ```
- The first budget test is negative. The worst-difference estimate
  `kappa_d(t)<=omega(d)<=2 log(Q)/log(5)` yields only

  ```math
  \sum_iw_iV_i
  \le
  N_0m
  +
  \frac{2\log Q}{\log5}N_0(N_0-1).
  ```

  Candidate #21's second-moment allowance is at most `N_0^2/2`. For `Q>=5`
  and `N_0>=2`, the off-diagonal term in this crude upper bound already
  exceeds that maximum allowance. The method cannot certify #21.
- Swapping the difference and prime sums exactly gives:

  ```math
  \text{positive off-diagonal}
  =
  \sum_iw_i(C_i-N_i),
  ```

  ```math
  \text{negative off-diagonal}
  =
  -\sum_iw_i\frac{N_i(N_i-1)}{r_i},
  ```

  and

  ```math
  \text{diagonal}
  =
  \sum_iw_iN_i\left(1-\frac1{r_i}\right).
  ```

  Their sum simplifies back to `sum_i w_i V_i`. Reordering alone is a
  consistency identity, not a new estimate.
- A new exact structural input is available for two 2-gaps separated by `d`.
  Their endpoint offsets are `{0,2,d,d+2}`. For any prime `p>=5`, the number
  of distinct forbidden start residues is

  ```math
  \nu_p(d)
  =
  \begin{cases}
  2,&p\mid d,\\
  3,&p\mid d-2\text{ or }p\mid d+2,\\
  4,&\text{otherwise}.
  \end{cases}
  ```

  Therefore collision differences `r_i|d` are exactly those with an enhanced
  four-point local factor `r_i-2` instead of the generic `r_i-4`.
- The local-factor classification and CRT product are now promoted as
  `properties/sieve-sequence/two-gap-pair-local-factor-by-separation.md`.
- The complete-period average of the paired correlation can be proved exactly.
  Write the post-3 modulus as `M=6M'`, encode each cyclic 2-gap start as
  `x=5+6u`, and let `U` be the corresponding set of indices modulo `M'`.
  With

  ```math
  A(h)=\#\{u\in U:u+h\in U\},
  ```

  ordered-pair double counting gives

  ```math
  \sum_{h\bmod M'}A(h)=|U|^2.
  ```

  For a new prime `r` coprime to `M'`, multiplication by `r` permutes the
  difference classes, so

  ```math
  \sum_{h\bmod M'}A(rh)=|U|^2.
  ```
- The complete-period average is now promoted as
  `properties/sieve-sequence/complete-period-two-gap-pair-correlation-average.md`.
- The quotient correlation has an exact CRT-Fourier factorization. For the
  indicator `f=1_U` on `Z/M'Z`,

  ```math
  A(h)
  =
  \frac1{M'}
  \sum_\chi
  |\widehat f(\chi)|^2\chi(h).
  ```

  At a local prime `p>=5`, the trivial Fourier coefficient is `p-2`, while a
  nontrivial coefficient is the negative sum of the phases at the two
  forbidden classes and has magnitude at most `2`.
- The exact local nontrivial fourth-moment sum is

  ```math
  \sum_{\chi_p\ne1}
  |\widehat f_p(\chi_p)|^4
  =
  6p-16.
  ```

  Therefore, with `G=|U|`,

  ```math
  \sum_{\chi\ne1}
  |\widehat f(\chi)|^4
  =
  G^4
  \left[
  \prod_{p\mid M'}
  \left(
  1+\frac{6p-16}{(p-2)^4}
  \right)-1
  \right].
  ```
- For `0<=H<=M'`, Fourier inversion and Cauchy--Schwarz give

  ```math
  |\mathcal E(H;r)|
  \le
  G^2
  \sqrt{
  R_P
  \frac{H}{M'}
  \left(1-\frac{H}{M'}\right)
  },
  ```

  where

  ```math
  R_P
  =
  \prod_{p\mid M'}
  \left(
  1+\frac{6p-16}{(p-2)^4}
  \right)-1.
  ```
- Conductor localization gives two further exact structures. For

  ```math
  a(q)=\prod_{p\mid q}\frac2{p-2},
  ```

  the normalized weights `a(q)/(M'/G)` form a product measure on divisors of
  `M'` in which each prime `p` is included independently with probability
  exactly `2/p`.
- Applying Cauchy--Schwarz separately at each exact conductor yields the
  hybrid bound

  ```math
  |\mathcal E(H;r)|
  \le
  \frac{G^2\sqrt H}{M'}
  \left[
  \prod_{p\mid M'}
  \left(
  1+
  \frac{\sqrt{p(6p-16)}}{(p-2)^2}
  \right)-1
  \right].
  ```

  This uses the exact conductor-fourth mass together with the fact that a
  conductor-`q` character has prefix second moment at most
  `q min(H,q)`.
- The actual square-window pair count is a localized rectangle. If `I` is the
  quotient-coordinate origin interval and

  ```math
  g(u)=\mathbf 1_I(u)\mathbf 1_U(u),
  ```

  then

  ```math
  \mathcal R(I,H;r)
  =
  \sum_u g(u)
  \sum_{1\le h\le H}g(u+rh)
  =
  \frac1{M'}
  \sum_\chi
  |\widehat g(\chi)|^2D_H(\chi;r).
  ```

  Localization changes the spectrum by convolution:

  ```math
  \widehat g
  =
  \frac1{M'}
  \widehat{\mathbf 1_U}
  *
  \widehat{\mathbf 1_I}.
  ```

  The first factor has the proved CRT product spectrum; the interval factor
  spreads it across frequencies.
- The rectangle identities are now promoted as
  `properties/sieve-sequence/localized-two-gap-correlation-fourier-boundary.md`.
- The first generic convolution audit is complete. If `L=|I|`, the interval
  spectrum satisfies

  ```math
  \|\widehat{\mathbf 1_I}\|_1
  \ll
  M'\log(2L)
  ```

  and

  ```math
  \|\widehat{\mathbf 1_I}\|_{4/3}
  \ll
  (M')^{3/4}L^{1/4}.
  ```

  Young `L4*L1` gives

  ```math
  \|\widehat g\|_4
  \ll
  G\,C_4^{1/4}\log(2L),
  ```

  while Young `L2*L(4/3)` gives

  ```math
  \|\widehat g\|_4
  \ll
  (M')^{1/4}G^{1/2}L^{1/4}.
  ```

  The latter yields the rectangle discrepancy scale

  ```math
  |\mathcal E_I(H;r)|
  \ll
  G\sqrt{LH}.
  ```
- The interval-norm calculation and both generic Young bounds are now
  promoted in
  `properties/sieve-sequence/localized-two-gap-correlation-fourier-boundary.md`.
  That note explicitly marks the retained global factor `G` as the reason the
  bounds do not solve origin localization.
- Conductor-block localization has an exact obstruction. Split
  `M'=p m`, let `g` be the localized indicator with `J=sum g`, and let
  `F(y)` count selected points in the fiber over `y modulo m`. Parseval gives

  ```math
  \sum_{\substack{\chi_p\ne1\\\chi_m}}
  |\widehat g(\chi_p,\chi_m)|^2
  =
  M'J
  -
  \frac{M'}p
  \sum_yF(y)^2.
  ```

  If the origin interval has length `L<=M'/p`, every fiber contains at most
  one localized point, so this becomes exactly

  ```math
  M'J\left(1-\frac1p\right).
  ```

  For the complete CRT set, the corresponding fraction of total energy is
  only `2/p`. Short localization therefore creates, rather than preserves,
  nontrivial-at-`p` spectral mass.
- This projection theorem is now promoted as
  `properties/sieve-sequence/short-interval-localization-destroys-prime-conductor-decay.md`.
- The optimistic fixed-set large-sieve route also fails the candidate #21
  constant audit. For the full chain beginning at `r_0=5`, the coefficients

  ```math
  \lambda_i=\frac{w_i}{r_i}
  ```

  are nonincreasing and

  ```math
  \lambda_0=\frac{A_{0,m}}3.
  ```

  Granting the standard bound

  ```math
  \sum_i r_iV_i\le(L+Q^2)N
  ```

  would therefore give only

  ```math
  \sum_iw_iV_i
  \le
  \frac{A_{0,m}}3(L+Q^2)N.
  ```

  For this upper bound to imply #21 would require

  ```math
  2W(L+Q^2)<3NA_{0,m},
  \qquad
  W=\sum_iw_i.
  ```

  But `W>=1`, `A_{0,m}<=1`, and post-3 phase capacity gives
  `N<=floor(L/6)+1`, making the inequality impossible for
  `L=Q^2-Q-3` and `Q>=7`.
- This quantitative obstruction is now promoted as
  `properties/sieve-sequence/black-box-large-sieve-does-not-fit-weighted-collision-budget.md`.
- A stopping-time audit found an off-by-one defect in the weighted-energy
  notes. Since

  ```math
  f_i(x)
  =
  \prod_{j<i}
  \mathbf 1_{r_j\nmid x(x+2)},
  ```

  a start first hit at layer `t` is still present before that filter and
  satisfies `f_t(x)=1`. The existing statement
  `f_i(x)=1_{i<tau(x)}` with `tau(x)=t` incorrectly omitted the deleting
  layer from `V_t`. The correct energy stopping index is

  ```math
  s(x)
  =
  \min(\tau(x)+1,m)
  ```

  for first-hit time `tau`, with `s(x)=m` for a final survivor, so that
  `f_i(x)=1_{i<s(x)}`.
- The authoritative weighted collision-energy property and candidate #21 now
  use the corrected energy stopping index `s`. The deletion-conservation law
  continues to use first-hit layer `tau`, where its separate formula
  `f_i=1` for `i<=tau` was already correct.
- Grouping ordered pairs by their common energy stop gives a new exact
  terminal-layer identity. If `k_{t,0}` and `k_{t,-2}` are the two harmful
  class sizes at layer `t`, the terminal block contains
  `N_t^2-N_{t+1}^2` ordered pairs, of which exactly
  `k_{t,0}^2+k_{t,-2}^2` have `r_t|(x-y)`. Hence

  ```math
  T_t
  =
  w_t
  \left[
  k_{t,0}^2+k_{t,-2}^2
  -
  \frac{N_t^2-N_{t+1}^2}{r_t}
  \right].
  ```

  With `K_t=k_{t,0}+k_{t,-2}`,
  `Delta_t=k_{t,0}-k_{t,-2}`, and
  `b_t=K_t-2N_t/r_t`, this becomes

  ```math
  \frac{T_t}{w_t}
  =
  -
  \frac{2(r_t-2)}{r_t^3}N_t^2
  +
  \frac{4}{r_t^2}N_tb_t
  +
  \frac{r_t+2}{2r_t}b_t^2
  +
  \frac12\Delta_t^2.
  ```

  The balanced terminal contribution is negative; its positive errors are
  isolated into total harmful excess and endpoint-class imbalance.
- This identity is now promoted as
  `properties/sieve-sequence/first-deletion-pair-terminal-energy.md`.
- The earlier histories of the terminal pair blocks also telescope exactly.
  If

  ```math
  V_{r_i}(A)
  =
  \#\{(x,y)\in A^2:r_i\mid x-y\}
  -
  \frac{|A|^2}{r_i},
  ```

  then

  ```math
  H_t
  =
  \sum_{i<t}
  w_i
  \left(
  V_{r_i}(S_t)-V_{r_i}(S_{t+1})
  \right).
  ```

  Including the final-survivor pair block gives

  ```math
  \sum_iw_iV_i
  =
  \sum_iT_i
  +
  \sum_iw_iV_{r_i}(S_{i+1}).
  ```

  Equivalently,

  ```math
  V_{r_i}(S_i)
  =
  \frac{T_i}{w_i}
  +
  V_{r_i}(S_{i+1}).
  ```

  The remainder is the same-prime variance of the post-filter survivors and
  is nonnegative.
- Let `M=N_{i+1}`, `h=r_i-2`, and write `M=qh+s` with `0<=s<h`.
  The harmless-class variance has the sharp unconstrained envelope

  ```math
  hq^2+2sq+s-\frac{M^2}{r_i}
  \le
  V_{r_i}(S_{i+1})
  \le
  M^2\left(1-\frac1{r_i}\right).
  ```

  Thus fixed `K_i`, `b_i`, and `Delta_i` do not prevent every survivor from
  occupying one harmless class.
- With a common harmless-class capacity `B` and
  `M=q_BB+u`, `0<=u<B`, convexity gives the sharp refinement

  ```math
  V_{r_i}(S_{i+1})
  \le
  q_BB^2+u^2-\frac{M^2}{r_i}
  \le
  BM-\frac{M^2}{r_i}.
  ```

  The existing post-3 phase theorem supplies
  `B=floor(L/(6r_i))+1`.
- Candidate #13 has an exact two-observable translation into the terminal
  variables. The unsigned endpoint indicator has full sum `2G` and hit sum
  `K`; the signed left-minus-right endpoint observable has full sum `0` and
  hit sum `Delta`. If both sampling errors are at most `eta`, then

  ```math
  \left|\frac KH-\frac{2G}{A}\right|\le\eta,
  \qquad
  |\Delta|\le H\eta,
  ```

  where `A` is the accepted-anchor population and `H` is the number of
  accepted anchors hit.
- With endpoint bias

  ```math
  \beta=\frac KH-\frac{2G}{A}
  ```

  and strike-density discrepancy

  ```math
  \varepsilon=\frac HA-\frac1r,
  ```

  the harmful excess has the exact decomposition

  ```math
  b
  =
  H\beta+2G\varepsilon.
  ```

  Thus #13 controls both endpoint sampling errors only after adding the signed
  observable. A separate accepted-strike density theorem is still needed for
  `epsilon`; candidate #10's post-filter count discrepancy does not directly
  provide it.
- This bridge is promoted as
  `properties/sieve-sequence/two-endpoint-observables-separate-harmful-excess-and-imbalance.md`.
- The complete residue energy has an exact orthogonal decomposition. Let

  ```math
  U_i
  =
  \sum_{a\notin\{0,-2\}}
  \left(
  c_{i,a}-\frac{N_{i+1}}{r_i-2}
  \right)^2.
  ```

  Then

  ```math
  \boxed{
  V_i
  =
  U_i
  +
  \frac{r_i}{2(r_i-2)}b_i^2
  +
  \frac12\Delta_i^2.
  }
  ```

  The `N_i^2` and `N_ib_i` terms cancel exactly. Under perfect total harmful
  balance and left/right balance, `V_i=U_i`.
- This result is promoted as
  `properties/sieve-sequence/orthogonal-residue-energy-decomposition-after-two-class-filter.md`.
- The natural remaining benchmark

  ```math
  U_i\le N_{i+1}
  ```

  is equivalent to the harmless-class collision bound

  ```math
  \sum_{a\notin\{0,-2\}}c_{i,a}^2
  \le
  N_{i+1}
  +
  \frac{N_{i+1}^2}{r_i-2}.
  ```
- This benchmark is now candidate #22,
  `candidates/conditioned-harmless-class-collision-energy.md`. Candidate #21
  and both catalogs have been updated to expose the dependency chain and the
  completed failed-path audits. The property catalog now includes all notes
  through the orthogonal decomposition as entry #34.
- The user requested a complete consistency pass after the latest reduction.
  The stale-claim inventory includes the #19-#21 escape-wall ticket, the
  candidate taxonomy and dependency diagram, candidate #13's unsigned-only
  endpoint discussion, candidate #20's pre-#22 comparison, the route ranking
  in this ticket, and the internal capacity learnings summary. Published
  Chapter 6 articles contain no #19-#22 claims requiring synchronization.
- The consistency edits are now complete across the #19-#22 escape-wall
  ticket, candidate #10, #13, #19, #20, #21, and #22 notes, both catalogs,
  the #14 cross-scope note, the future research landscape, the two-endpoint
  property, and the internal capacity learnings summary.
- the Terminal Harmful-Excess Energy property is the later controlling result. Restricted #12, or the
  fallback #13+#23 representation, targets a harmful scalar theorem that is
  already terminal at candidate #21's global allowance. Candidate #22 remains
  an independently noncircular harmless-distribution problem but is not an
  additional survival obligation after scalar feasibility. Candidate #10 is
  not the strike-density theorem.

## Expected State

- One exact primary theorem and, if useful, one weaker fallback are written in
  algebraic form.
- Every term is grounded in the existing sieve-sequence definitions.
- A dependency chain shows precisely how the theorem would imply candidate
  #14 and then local survival.
- Known proof barriers and falsifiers are recorded.
- The first formalizable lemma is identified without claiming the open theorem
  has been proved.

## Similar Tickets

- [Prove hereditary shot spacing](prove-hereditary-shot-spacing-2026-07-23.md)
  contains the detailed boundary analysis for candidate #14.
- [Exact Q sweep for top candidates](../done/exact-q-sweep-top-candidates-2026-07-27.md)
  records the completed finite evidence and explains why more of the same is
  not the present bottleneck.

## Alternatives Considered

- **More empirical sampling:** rejected for this ticket because it cannot
  establish the required all-level statement and the existing footprint is
  already sufficient for prioritization.
- **Attack candidate #2 directly:** deferred because its local-surplus
  inequality hides the same harmful-hit distribution problem.
- **Prove more shot-spacing constants:** deprioritized because candidate #14's
  current obstruction is the supply and distribution of useful 2-gaps, not
  the geometry of a fixed finite cluster.
- **Use a probabilistic independence heuristic:** rejected as a proof unless
  converted into a deterministic finite-group or character-sum statement.

## Assumptions And Hypotheses

- **Assumption:** after filter `3`, distinct 2-gaps have disjoint endpoints.
  Validate against the proved isolation property.
- **Assumption:** a filter by prime `r > 2` destroys a 2-gap exactly when its
  start lies in one of two harmful residue classes modulo `r`.
  Validate from the filter definition and endpoint arithmetic.
- **Hypothesis:** the useful bridge can be stated as one-sided discrepancy for
  these two residue classes, rather than uniformity over every residue class.
  Validate by deriving the survivor inequality exactly.
- **Hypothesis:** a square-root-scale error is sufficient at every conditioned
  layer when combined with the existing local-count/capacity inequality.
  Validate symbolically; do not infer it from samples.
- **Risk:** a discrepancy bound strong enough at the last layer may be
  equivalent in difficulty to the twin-prime conclusion. Test logical strength
  before promoting it as progress.

## Validation

- Check definitions against candidate files and proved property notes.
- Derive every implication symbolically with named quantities and explicit
  inequalities.
- Search existing `.holds` lemmas before proposing any new Scala lemma.
- For any proposed recurrence, test it algebraically against the exact
  copy/filter decomposition already documented; existing data may be used only
  as a known counterexample source, not extended.
- Markdown-only changes require link and formatting checks, not Stainless.
- Final integrity pass for this loop: `git diff --check` is clean; every
  required persistent-memory heading is present; every new candidate/property
  catalog target exists; and no stale `i<tau` energy kernel remains. The
  existing verification log remains green at `30 valid, 0 invalid, 0 unknown`.
  Stainless was not rerun because all changes are Markdown-only. The unrelated
  staged giant CSV was preserved untouched.
- Final consistency-pass validation is also clean: no stale current-state
  phrase or stopping-index formula matched; both active tickets contain every
  required persistent-memory section; and every relative Markdown link under
  `candidates/`, `properties/`, `tickets/`, and `articles/` resolves. The audit
  also repaired one future-to-active ticket path and two duplicated draft
  article paths that were already broken before this pass.

## What is Learned

- Candidate #14 should be viewed as a deterministic capacity consumer.
- The prospective missing theorem concerns conditioned distribution into two
  harmful residue classes, not raw 2-gap density alone.
- A proof must exploit more structure than the average over residue classes:
  the next filter selects a particular pair of classes.
- Candidate #12 is stronger than necessary because it controls every residue
  class. For direct 2-gap survival, only the sum of the `0` and `-2` start
  classes matters.
- The installed filters `2` and `3` supply useful phase rigidity. Every 2-gap
  start is `5 modulo 6`; within any one residue class modulo a new odd prime
  `r`, two starts differ by a multiple of `6r`. Hence a start interval of
  diameter `L_Q` contains at most `floor(L_Q/(6r))+1` starts in that class.
- Summing the capacities of the two harmful classes gives a non-probabilistic
  destruction bound and the sufficient population threshold
  `2 floor(L_Q/(6r))+3`.
- The new threshold is asymptotically `L_Q/(3r)`, compared with the existing
  order-only close-pair threshold `L_Q/(2r)`. It directly forces one-layer
  survival but does not necessarily produce candidate #14's close pair.
- Cauchy--Schwarz converts the two-class harmful excess into the `L2` residue
  variance `V_r`. Parseval-by-counting rewrites that variance as the excess
  number of same-residue ordered pairs. This may be more tractable than
  pointwise equidistribution because it asks for a count of divisible
  differences, not control of every class.
- The collision criterion and the sixfold capacity theorem are not uniformly
  ordered. If `m=max_a c_a`, then `sum c_a^2<=mN`, but this implies the
  collision criterion only under the stronger count condition

  ```math
  N>
  \frac{m}{
  \frac12-\frac1r+\frac{2}{r^2}
  }.
  ```

  Candidate #19 needs only `N>2m` when the two harmful classes each have
  capacity `m`. For small `r`, the global energy condition can be worse because
  it charges variance in harmless classes. Collision energy is useful only if
  the exact difference structure yields a substantially sharper bound than
  `sum c_a^2<=mN`.
- The relative collision benchmark replaces candidate #19's order-`Q`
  population requirement at late layers by a constant population requirement.
  The price is a four-point correlation upper bound normalized by the actual
  conditioned population `N`, not by the complete-period main term.
- The threshold simplification is exact:

  ```math
  \left(
  \frac12-\frac1r+\frac{2}{r^2}
  \right)-\frac1r
  =
  \frac{(r-2)^2}{2r^2}.
  ```
- A pointwise collision benchmark `V_i<=N_i` gives
  `e_i<=sqrt(2N_i)`. Iterating that worst-case error is a constant-sensitive
  route: heuristic main-term and accumulated-error scales can both be of order
  `Q^2/log^2 Q`. Therefore the coefficient cannot be discarded as lower order.
- The unrolled formula suggests a genuinely different target: control the
  weighted sum of the actual `V_i` across the chain, possibly by a large-sieve
  or dispersion inequality, instead of bounding every selected harmful phase
  separately.
- The fixed-set bilinear identity resolves the changing-domain objection but
  not the changing-coefficient objection. The deletion-time form compresses
  those coefficients into one stopping index per start.
- Because `|x-y|<Q^2`, the positive prime-divisor terms in each off-diagonal
  stopped kernel satisfy a product constraint. Large incoming prime divisors
  cannot occur arbitrarily many times in one difference. The negative
  centering sum `-sum w_i/r_i` is part of the same exact kernel and should not
  be discarded.
- The multiplicative survival weights were chosen by the recurrence, and their
  centering terms are discrete derivatives. This is the first exact
  cancellation mechanism found in the algebraic pass.
- The signed weighted discrepancy is a conservation law, not an independent
  estimate. Proving

  ```math
  \sum_iw_ib_i<N_0A_{0,m}
  ```

  is algebraically identical to proving `N_m>0`. Any viable cumulative proof
  must dominate the signed excess by a genuinely stronger quadratic or
  structural quantity and then bound that quantity independently.
- Product control on the prime divisors of one difference is quantitatively
  insufficient when maximized independently over all `N_0(N_0-1)` ordered
  off-diagonal pairs. The next estimate must sum divisor incidence across
  differences before taking maxima and must retain the centered negative term.
- Grouping divisor incidence by layer without using a new correlation estimate
  merely reconstructs the original per-layer variance. The extra usable
  information must enter through the distribution of the four-point local
  factors over differences.
- The complete difference-period mean is exactly uniform; no probabilistic
  hypothesis is needed for that average. The remaining question is
  transference from the complete `M'`-period to the much shorter range of
  separations present in `[Q,Q^2)`.
- The CRT product set has an explicitly factorized spectrum. Fourth moments
  give rigorous prefix cancellation near a complete quotient period without
  any random assumption.
- In the late regime `H<<M'`, the fourth-moment bound has scale
  `G^2 sqrt(H/M')`, while the elementary bound has scale `HG`. Depending on
  `G/H`, the spectral estimate can be worse. Global fourth-moment control
  alone does not resolve very short prefixes of a primorial period.
- The conductor-fourth hybrid replaces the global `1/sqrt(M')` spectral scale
  by `1/M'` times an explicit Euler product. It is a genuine improvement for
  complete-origin correlation prefixes.
- The correlation `A(h)` still sums the origin `u` over the entire cyclic set
  `U`. A square-window collision count restricts both the origin and the
  difference. Therefore even a strong one-dimensional prefix bound does not
  by itself control candidate #21; the remaining object is a two-dimensional
  rectangle discrepancy.
- The origin restriction is precisely a convolution-norm problem in Fourier
  space. Any successful transference theorem must preserve enough of the
  conductor decay of `hat(1_U)` after convolution with the interval Dirichlet
  kernel.
- Generic Young bounds retain the complete-period population `G`, not the
  localized population `J=|U intersect I|`. When `M'>>L`, `G` can be much
  larger than `J`, so these estimates can exceed the trivial local rectangle
  bound. Origin transference requires a localized or conductor-aware norm,
  not a global convolution inequality.
- The corrected energy stop makes the deleting layer visible. At that layer,
  collision is equivalent to same-harmful-class simultaneous deletion. The
  terminal block consequently has a negative balanced quadratic main term,
  the first sign-definite cancellation found after localization.
- Terminal cancellation is incomplete because every pair also carries its
  centered collision history from earlier layers. The next theorem must
  compare that history with the terminal term without simply reconstructing
  the original weighted variance.
- The terminal observables contain no information about concentration among
  the `r_i-2` harmless classes. Their sharp post-filter upper envelope remains
  quadratic until an independent capacity or distribution theorem is used.
- The sixfold class capacity converts that remainder from quadratic `M^2` to
  at most `BM`. This is a concrete algebraic composition of #19 and #21, but
  its cumulative constants have not yet passed the survival budget.
- The endpoint observable framework is more useful than the original unsigned
  formulation suggested: a signed orientation observable directly controls
  `Delta_i`, the new error exposed by terminal pair energy.
- Total harmful excess `b_i` factors into two distinct discrepancies:
  endpoint sampling bias and accepted-strike density. Candidate #13 addresses
  the first; the second remains a separate open theorem and is not candidate
  #10 as currently stated.
- Even perfect control of both terminal errors leaves the post-filter
  harmless-class variance algebraically open. The Terminal Harmful-Excess Energy property later proves that
  this harmless variance is not an additional survival obligation once the
  assembled harmful scalar energy is below candidate #21's global allowance.
- The orthogonal identity removes the earlier terminal-history complexity:
  full energy is exactly harmless dispersion plus two scalar squared errors.
  There are no hidden linear terms.
- The two #13 endpoint observables address endpoint bias and `Delta_i`; a
  separate accepted-strike density theorem completes the bound for `b_i`.
  A smaller-alphabet collision theorem for `U_i` is an independently
  noncircular distributional component, not the remaining survival theorem
  after scalar feasibility.
- The benchmark `U_i<=N_{i+1}` is not automatically easier than candidate
  #20; it is candidate #20's relative-collision scale restricted to the
  harmless survivors. Its advantage is precision: it does not charge
  endpoint imbalance twice and composes orthogonally with endpoint sampling
  and accepted-strike density.
- Applying the same capacity to the two harmful classes removes that apparent
  gain. The terminal identity plus the harmless remainder bound simplifies to

  ```math
  V_i
  \le
  B_iN_i-\frac{N_i^2}{r_i},
  ```

  exactly the direct whole-histogram estimate
  `sum_a c_{i,a}^2<=B_iN_i`. The negative terminal term survives only if the
  harmful and harmless sides receive asymmetric information.
- Corrected algebraic route classification after the Terminal Harmful-Excess Energy property:
  1. **Restricted #12 weighted harmful norm:** the cleanest scalar
     representation, but already a terminal conditioned-chain theorem at
     candidate #21's global allowance.
  2. **#13 endpoint sampling plus #23 accepted-strike density:** a fallback
     representation whose individual components are noncircular; their
     assembled scalar theorem is terminal.
  3. **#21 cumulative weighted energy:** a valid terminal composition
     framework. Further algebraic rearrangement does not make its required
     arithmetic estimate preparatory.
  4. **#22 weighted harmless-class energy:** an independently noncircular
     distribution diagnostic, but redundant for survival after scalar
     feasibility in the separated composition.
  5. **#19/#20:** useful one-layer capacity and relative-collision testbeds;
     their existing open population or normalization steps remain.
  6. **#14:** a distinct capacity consumer whose close-pair existence theorem
     remains open.

## Failed Paths

- **Exact multiplicative recurrence for the local 2-gap count.** It fails
  because square-window boundaries and conditioning introduce non-multiplicative
  boundary terms. Retry only if an augmented state closes exactly under the
  copy/filter action.
- **Uniform constant additive correction.** Existing counterexamples rule out
  the tested constant bound. Retry only if the correction is allowed to scale
  with a proved boundary statistic.
- **Treating average residue occupancy as occupancy of the harmful classes.**
  The average does not control the particular classes chosen by the next
  filter. Retry only with a structural symmetry or discrepancy theorem that
  identifies those classes.
- **Additional finite sweeps as proof progress.** They can falsify but cannot
  supply the universal algebraic step. Reconsider only to test a genuinely new,
  sharply stated algebraic identity.
- **Summing the absolute one-layer harmful capacities through the chain.**
  Starting from a post-3 population of order `L_Q/6`, the cumulative bound
  subtracts a main term proportional to
  `(L_Q/3) sum_{r<Q} 1/r`. The reciprocal-prime sum is unbounded, so this
  bookkeeping eventually loses the entire initial population even before
  floor errors. It also double-counts gaps harmful to several primes. Retry
  only with an overlap-aware batch count or a potential that credits repeated
  coverage.
- **Using the cumulative signed harmful excess as the missing theorem.** The
  exact identity
  `sum_i w_i b_i=N_0 A_{0,m}-N_m` shows that the desired strict bound is
  equivalent to final survival. It merely rewrites the target. Retry only if
  the signed sum is controlled by an independently bounded quadratic,
  higher-moment, or structural quantity; candidate #21's collision energy is
  one such proposed majorant.
- **Worst-difference divisor bound for candidate #21.** Bounding every stopped
  kernel by `omega(d)<=2 log(Q)/log(5)` and then multiplying by the number of
  pairs gives an energy upper bound already larger than the maximum available
  second-moment budget. It discards both the frequency distribution of
  differences and the negative centering. Retry only after grouping divisor
  incidence across all differences or proving a substantially sharper
  average-kernel estimate.
- **Pure sum swapping in the difference-grouped energy.** Interchanging the
  prime and difference sums yields the exact positive collision count,
  centered off-diagonal count, and diagonal count, which simplify back to
  `sum_i w_i V_i`. No inequality is gained. Retry only with an independent
  average bound for the four-point pattern counts or their singular factors.
- **Using only the global Fourier fourth moment for late short prefixes.** The
  exact factorization proves a bound effective near a full quotient period,
  but for `H<<M'` it may exceed the trivial `HG` estimate. Retry only after
  exploiting conductor/frequency localization, additional averaging, or a
  spectrum norm adapted to short intervals.
- **Treating complete-origin correlation-prefix control as the square-window
  collision bound.** The former averages `u` over all of `U`; the latter
  restricts `u` and `u+h` to one short absolute window. Retry only after a
  rectangle-discrepancy or origin-transference theorem is proved.
- **Generic Young convolution bounds for origin localization.** `L4*L1`
  introduces an interval logarithm and retains `G^2`; `L2*L(4/3)` improves the
  scale to `G sqrt(LH)` but still uses the complete-period population instead
  of `J`. In the primorial-dominant regime these can be worse than the trivial
  local count. Retry only with conductor-block convolution, a localized large
  sieve, or an independent relation between `G` and `J` that does not assume
  short-window positivity.
- **Transferring complete-set conductor weights through localization.** For
  every prime with `L<=M'/p`, the localized nontrivial-at-`p` `L2` energy
  fraction is exactly `1-1/p`, not the complete-set fraction `2/p`.
  Localization destroys the proposed conductor decay before any blockwise
  triangle or Cauchy estimate is applied. Retry only if the proof couples the
  new high-conductor mass directly to cancellation in `D_H`; do not reuse the
  complete-set conductor distribution as a localized majorant.
- **Black-box localized large sieve.** Even if all layer variances are
  optimistically replaced by those of one fixed localized set, the standard
  `(L+Q^2)N` scale cannot fit candidate #21 after the exact survival weights
  are inserted. The required inequality contradicts the elementary post-3
  population capacity. Retry only with a structural gain over the standard
  large-sieve scale; fixing the changing-population bookkeeping alone is not
  enough.
- **Iterating first-deletion history telescoping.** The earlier histories of
  terminal pair blocks telescope to
  `sum_i w_i V_{r_i}(S_{i+1})`, giving exactly the layerwise partition of
  pre-filter variance into terminal and survivor-pair pieces. This is new
  structural bookkeeping but no upper bound. Retry only with an independent
  estimate for the post-filter variance or a relation tying it to the
  terminal observables `b_i` and `Delta_i`.
- **Symmetric reuse of the sixfold class capacity.** Bounding both harmful
  class squares and harmless survivor squares by the same capacity `B_i`
  recombines exactly to `V_i<=B_iN_i-N_i^2/r_i`, the direct class-capacity
  inequality already available before the first-deletion split. Retry only
  with asymmetric information: a stronger endpoint-class imbalance bound, a
  stronger harmless-dispersion bound, or a cross-layer covariance joining
  them.
- **Treating #22 as the primary missing survival theorem.** the Terminal Harmful-Excess Energy property
  proves that the harmful-excess square alone being below candidate #21's
  global allowance already forces `N_m>0`. Retry #22 for independent
  distributional value or only after a new composition gives it a
  nonredundant role.
- **Attributing accepted-strike density to candidate #10.** Candidate #10
  controls post-filter safe-window count discrepancy, not
  `epsilon_i=H_i/A_i-1/r_i`. Similar discrepancy language caused the mistaken
  dependency. Do not retry this bridge without an explicit theorem deriving
  accepted-anchor hit density from `E_q`.

## Open Concerns

- The precise normalization used by candidates #12 and #13 may obscure a
  simpler integer inequality.
- The square-root premise may be sufficient but still too strong to prove from
  current properties.
- Boundary contributions from copies entering and leaving `[Q,Q^2)` may need a
  separate deterministic lemma before any discrepancy argument can close.
- It is not yet known whether endpoint observables give strictly more algebraic
  leverage than direct counts of 2-gap starts.
- The new harmful-class capacity still requires a conditioned population lower
  bound of order `Q^2/r`; at late layers this is order `Q`. Establishing that
  bound for all relevant future heads may still encounter the parity barrier.
- Iterating the per-layer absolute capacities by a union bound is expected to
  be too lossy; the divergent reciprocal-prime factor confirms this
  algebraically.
- A collision-energy bound strong enough at the final layer may still encode
  the parity problem. Its logical strength must be audited before it is treated
  as a route around the known discrepancy wall.
- Standard upper-bound sieve estimates naturally bound four-point counts in
  terms of window length and local densities, whereas the proposed benchmark
  is relative to the unknown actual `N`. Converting an absolute upper bound
  into `N+N^2/r` without already having a strong lower bound for `N` may
  reintroduce the parity problem.
- The conditioned sets `S_i` change with `i`, so a classical large-sieve
  inequality for one fixed set does not apply verbatim. A viable cumulative
  theorem must either embed all `S_i` into one fixed weighted population or
  prove a monotone comparison that survives conditioning.
- A per-pair upper bound for the stopped divisor kernel may be too coarse when
  summed over `S_0^2`. Any proposed divisor-budget lemma must be checked at the
  aggregate scale required by the weighted-energy survival inequality.
- The stopping-time off-by-one has been corrected in the property, candidate,
  and ticket. Any future energy decomposition must use energy stop
  `s=min(tau+1,m)`, not first-hit layer `tau`.

## Next Action

Stop checkpoint. The Terminal Harmful-Excess Energy property classifies the current scalar route as terminal
and removes #22 as an additional survival obligation after scalar feasibility.

Resume this ticket only with one of two genuinely new inputs:

1. a terminal arithmetic estimate for restricted #12's weighted harmful norm,
   explicitly accepted as strong enough to prove final survival; or
2. a different composition framework that uses new signed or cross-layer
   arithmetic not already exhausted by the exact conservation law.

Do not resume generic #22/#23 algebra, do not return to local-ellipse
composition, and do not collect additional empirical evidence.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-07-27 | Finite evidence has served candidate selection; the proof bottleneck is conditioned two-class distribution. | Opened an algebra-only proof-program ticket and excluded new sweeps from its strategy. |
| 2026-07-27 | Post-3 phase rigidity bounds each harmful residue class by `floor((Q^2-Q-3)/(6r))+1`; two classes give a new one-layer survival threshold asymptotic to `Q^2/(3r)`. | Recorded the exact derivation, its improvement over the `k=2` order threshold, and the remaining population/parity concern. |
| 2026-07-27 | Promoted the sixfold capacity theorem and candidate #19. A sharper Cauchy--Schwarz route replaces worst-class discrepancy by same-residue collision energy. Naive cumulative subtraction fails algebraically because it introduces the divergent reciprocal-prime sum and loses overlap. | Made collision energy the next theorem and recorded cumulative absolute capacity as a failed path. |
| 2026-07-27 | Correction: the global collision-energy criterion does not automatically recover candidate #19 from the per-class cap. It can be stronger at small `r` because harmless-class variance contributes to the energy. | Reclassified collision energy as an alternative route whose value depends on a sharper divisible-difference count. |
| 2026-07-27 | Same-residue collisions equal a diagonal plus four-point autocorrelations at shifts `6rh`. The benchmark `C<=N+N^2/r` would reduce the needed population to 6 gaps at `r=5`, 4 at `r=7`, and 3 at every `r>=11`. | Promoted the exact identity as a property and selected a relative-collision candidate for formal comparison with #12 and #19. |
| 2026-07-27 | The one-layer energy loss unrolls into a multiplicative main term minus a weighted sum of actual layer energies. This meets the earlier failed chain route's retry condition because it seeks cumulative structural control rather than a pointwise square-root assumption. | Made the weighted cumulative-energy theorem the primary next algebraic target, with changing conditioned sets recorded as the central obstacle. |
| 2026-07-27 | Nested conditioned populations embed exactly into one initial set. Deletion times turn the cumulative energy kernel into a stopped, centered prime-divisor sum for each pair difference `|d|<Q^2`. | Ranked cumulative energy first and selected an aggregate divisor-kernel bound as the next concrete lemma. |
| 2026-07-27 | The centering weights telescope: `w_i/r_i=(w_i-w_{i-1})/2`. Hence only differences with relevant incoming prime divisors can contribute positively to the off-diagonal cumulative kernel. | Created candidate #21, promoted the chain and stopping-time identities, and narrowed the next proof loop to an aggregate divisor-incidence bound with an immediate budget check. |
| 2026-07-27 | Per-gap first-hit telescoping gives the exact conservation law `sum_i w_i b_i=N_0 A_{0,m}-N_m`. A strict signed cumulative bound is therefore equivalent to final survival and is not independent progress. | Recorded the signed-discrepancy route as a failed restatement. Kept #21 only through its stronger quadratic collision-energy majorant. |
| 2026-07-27 | The quadratic energy splits exactly by differences `6h`. A worst-pair bound using only `omega(d)` produces an upper bound larger than #21's entire available budget, so it cannot prove the candidate. | Recorded worst-difference maximization as failed and moved the next step to aggregate divisor incidence with the centered term retained. |
| 2026-07-27 | Swapping the aggregate divisor-incidence sums closes back to the original weighted variance, so bookkeeping alone does not help. The four-point offsets `{0,2,d,d+2}` have exact local factor `p-2`, `p-3`, or `p-4` according as `p|d`, `p|d±2`, or neither. | Recorded the pure sum swap as failed and selected an averaged four-point local-factor theorem as the next structural input. |
| 2026-07-27 | The four-point CRT factor is proved. Over a complete quotient difference period, its autocorrelation has exact mean `|U|^2/M'`, and multiplying differences by a new prime only permutes that period. | Narrowed the missing theorem to prefix discrepancy of the correlation sequence, retaining the short-window boundary explicitly. |
| 2026-07-27 | The quotient start set has a factorized Fourier spectrum; the exact fourth moment gives a rigorous correlation-prefix bound near full periods. It is too coarse in the late `H<<M'` regime. | Recorded global fourth moment as an insufficient late-prefix route and selected conductor-sensitive spectral localization as the next algebraic refinement. |
| 2026-07-27 | Exact conductor masses give a product measure with prime inclusion probability `2/p`. Combining conductor fourth moments with period-sensitive prefix norms produces a stronger explicit hybrid bound. It still averages origins over the full cyclic set. | Narrowed the remaining analytic object to two-dimensional origin/difference rectangle discrepancy. |
| 2026-07-27 | Localizing origins to the square window replaces the factorized spectrum by the convolution `hat(1_U)*hat(1_I)/M'`. The required pair count is the difference-prefix autocorrelation of this localized indicator. | Identified convolution-norm control as the exact origin-transference theorem and set explicit Young/interpolation bounds as the next falsifiers. |
| 2026-07-27 | Generic `L4*L1` and `L2*L(4/3)` Young bounds are rigorous but retain the global population `G`; the latter gives only `G sqrt(LH)`. They do not transfer to the localized mass `J`. | Recorded generic Young localization as failed and narrowed the next route to conductor-block or localized large-sieve control. |
| 2026-07-27 | The proved interval Dirichlet-kernel norms and the resulting Young estimates are now part of the localized Fourier boundary note, with their normalization and failure scale explicit. | Closed the generic-convolution documentation loop; conductor-block mixing is now the sole immediate algebraic test. |
| 2026-07-27 | Prime-projection Parseval shows that a window of length `L<=M'/p` puts exactly the fraction `1-1/p` of localized spectral energy in characters nontrivial at `p`, whereas the complete CRT set puts only `2/p` there. | Promoted the exact obstruction, rejected inheritance of complete-set conductor weights, and moved the next audit to a local-population large-sieve inequality. |
| 2026-07-27 | After exact survival weights are inserted, even the optimistic fixed-set large-sieve bound would need `2W(L+Q^2)<3NA`, contradicting the post-3 capacity `N<=floor(L/6)+1`. | Promoted the constant obstruction, rejected the black-box large sieve, and selected a first-deleting-prime pair decomposition as the next exact algebraic test. |
| 2026-07-27 | The stopping-time formula was off by one: a gap first hit at layer `t` contributes to the pre-filter energy `V_t`, because `f_t=1`. The earlier `i<tau` kernel omitted that layer. | Paused the new decomposition and made correction to the energy-stop index `s=min(tau+1,m)` the immediate consistency repair. |
| 2026-07-27 | The weighted-energy property, candidate #21, and the ticket now distinguish first-hit layer `tau` from energy stop `s=min(tau+1,m)`. | Restored the deleting layer to every stopped energy kernel; next run a stale-formula search before resuming new algebra. |
| 2026-07-27 | Pairs first lost after layer `t` have terminal contribution `w_t[k_0^2+k_{-2}^2-(N_t^2-N_{t+1}^2)/r_t]`; its centered form has a negative `N_t^2` main term and errors only in harmful excess `b_t` and endpoint imbalance `Delta_t`. | Promoted the first-deletion terminal identity and selected its earlier-history covariance as the next exact algebraic object. |
| 2026-07-27 | Earlier histories telescope exactly to the post-filter same-prime variances, so first-deletion grouping yields `V(S_i)=T_i/w_i+V(S_{i+1})` rather than a new upper bound. | Recorded the history route as a closed bookkeeping loop and reduced the next test to sharp envelopes for the harmless-class survivor variance. |
| 2026-07-27 | With only `N_i,K_i,Delta_i` fixed, post-filter variance can reach `N_{i+1}^2(1-1/r_i)`; the terminal observables do not control harmless-class concentration. A class cap `B_i` gives the sharp refinement `qB_i^2+u^2-N_{i+1}^2/r_i <= B_iN_{i+1}-N_{i+1}^2/r_i`. | Added the convex envelope and selected an exact weighted constant audit combining #19's capacity with #21's terminal decomposition. |
| 2026-07-27 | Using the same class cap on the harmful and harmless sides collapses exactly to the old whole-histogram bound `V_i<=B_iN_i-N_i^2/r_i`; symmetric capacity loses the terminal cancellation. | Recorded the #19/#21 black-box composition as a no-gain loop and selected candidate #13's endpoint observable as the next source of asymmetric information. |
| 2026-07-27 | Unsigned and signed endpoint observables give separate controls of total destruction `K` and orientation imbalance `Delta`; harmful excess decomposes exactly as `b=H beta+2G epsilon`, joining #13 sampling bias with #10 strike-density discrepancy. | Promoted the two-observable bridge and isolated harmless-class survivor dispersion as the remaining asymmetric theorem. |
| 2026-07-27 | Full residue energy decomposes orthogonally as `V_i=U_i+r_i b_i^2/(2(r_i-2))+Delta_i^2/2`; all baseline and linear terms cancel. | Promoted the decomposition and reduced the remaining distribution theorem to the smaller-alphabet collision benchmark `U_i<=N_{i+1}`. |
| 2026-07-27 | Candidate #22 now states the harmless-class benchmark explicitly; candidate #21 and the candidate/property indexes expose the exact #10/#13/#22 -> #21 chain. | Completed discoverability updates and selected the weakest weighted aggregate `U_i` budget as the next algebraic refinement. |
| 2026-07-27 | Markdown, ticket-structure, target-existence, and stopping-index consistency checks all pass; the prior Stainless baseline remains `30/0/0`. | Closed this work loop with the unrelated staged CSV untouched and a precise weighted-`U_i` next action. |
| 2026-07-27 | Correction: candidate #10 is a post-filter safe-window count discrepancy and does not directly control accepted-anchor strike density `H/A-1/r`. | Removed #10 from the scalar-error dependency chain. The current chain is #13 endpoint sampling plus a separate accepted-strike density theorem, together with #22 harmless dispersion, feeding #21. |
| 2026-07-27 | Completed the user-requested consistency pass across all current #19-#22 candidates, catalogs, properties, active strategy tickets, the future landscape, and the internal learnings summary. The escape-wall audit now includes #22 and distinguishes noncircular components from terminal consumers. | Recorded the mistaken #10 attribution as a failed path and moved the immediate action to repository-wide integrity validation before resuming weighted harmless-energy algebra. |
| 2026-07-27 | Repository-wide stale-claim, stopping-index, ticket-section, relative-link, and Markdown checks pass. Two unrelated legacy link patterns found by the audit were repaired; the staged giant CSV remains untouched. | Closed the understanding-sync pass. The next mathematical action is again the exact weighted `U_i` allowance, using #13 endpoint errors plus a separate accepted-strike density theorem. |
| 2026-07-29 | the Terminal Harmful-Excess Energy property proves `E_b >= (T-N_m)^2/(2W_-)` with `W_-<W`; hence the harmful-excess square below candidate #21's allowance already forces `N_m>0`. | Reclassified restricted #12 and the assembled #13+#23 scalar theorem as terminal, demoted #22 to an independent diagnostic, and stopped the exhausted algebraic decomposition route. |
