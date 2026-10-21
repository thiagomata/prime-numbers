# Continuous complex curves for sieve stages — research notes

Date: 2026-10-20

## START HERE

Current micro-goal (2026-10-21): add the explicit recurrence-to-infinite-sum
derivation in the sine-wave notation, then commit/push the two documentation
files to existing draft PR64 on feature/imaginay_function. Mathematical proofs
are the priority; Stainless formalization is not a requirement.

Preserve the discussion of Fourier cycle integrals and a continuous complex
curve whose real-axis contacts encode sieve survivors. These are mathematical
research notes, not a publication-ready article. None of the new analytic
constructions or proofs below has been verified in Stainless. No Scala changes
are proposed in this save.

## Goal

Record an exact continuous representation of successive sieve filters, explain
its infinite limit, and distinguish representing survivors from enumerating
them. Further development is mathematical; formalization is optional and is
not a prerequisite for this research.

## Strategy

Use roots-of-unity sums to detect divisibility at integer inputs. Add a
nonnegative imaginary penalty for rejected integers and a separate penalty
for noninteger inputs. Activate each prime's filter only after that prime,
preserving the prime itself. Compare this value-coordinate representation with
the Fourier representation in survivor-index coordinates.

## Current State

Recurrence follow-up: section1.2 now derives the finite sum by telescoping,
states the infinite sum with W_m, gives the12.5/12 activation examples and
proves local eventual equality on bounded intervals. Twin-contact formula
and the shifted endpoint range are explicit. Only this ticket and the math
note change; no code or runtime instructions change. Whitespace checks pass.

Latest follow-up: sine-ratio wave and finite cosine-sum equivalents are saved
in uniform-continuous-divisor-sieve.md section1.1, including continuous
extension, exact integer-selective changes and the filter4 example. This is
documentation-only; whitespace checks pass and no runtime gates apply.
Existing commits4912f037,4ac732ab and828ee3da are pushed. Draft PR64 exists at
https://github.com/thiagomata/prime-numbers/pull/64 and is attached to this chat.
GitHub comparison against master also includes inherited article
commit932fcbbc and merge05bdcc71. Preserve that history and disclose it in a
draft PR rather than claiming this documentation update revalidated articles.

Discussion saved with definitions and mathematical arguments. No runtime gates
are applicable to this Markdown-only note. Stainless verification and any
publication are pending; no arXiv counterpart is created or changed.
The bibliography below records the mathematical references cited during the
discussion and the proposed ManimGL visualization tool.
Candidate-save follow-up complete: the standalone research-direction note
and discovery link are saved. No numbered hypothesis was added. Critic and
Monitor reviews passed; Markdown whitespace checks passed. No runtime gates
apply, since executable instructions and source code were not changed.
Uniform function saved with proofs in
properties/sieve-sequence/uniform-continuous-divisor-sieve.md and linked from
the candidate research directions. Independent Critic/Monitor review passed.
Branch feature/imaginay_function has been created; the initial index was
empty. Both standalone animation numerical checks pass as the Python baseline.
No source changes are planned. The local commit contains only 14 selected
session files: the candidate README and research directions, uniform property
note, eight files in presentations/continuous-complex-sieve/, two animation
tickets and this research ticket. Existing unrelated modifications remain
outside the commit. Mathematical note and commit scope passed review.

Existing context consulted: `LEARNINGS.md` section 18.6 warns that Fourier work
already exists in the repository. Related work includes
[algebraic conditioned survival](../active/algebraic-conditioned-survival-2026-07-27.md)
and [the sieve property landscape](sieve-property-landscape.md).
These are context links, not claims that those tickets establish this construction.

## What is Learned

### 1. Fourier representation of a fixed cycle integral

This uses classical finite Fourier inversion and geometric summation, rather
than a newly discovered general integration formula. Rein van den Boomgaard's
DTFS exposition and Raya and Eberl's formalization are cited below.

For a repeating real gap list g_0,...,g_(N-1), define a starting value before
accumulation and its sequence by

```math
\begin{aligned}
x_n &= x_0+\sum_{j=0}^{n-1}g_j,\\
c_k &= \frac1N\sum_{r=0}^{N-1}g_r e^{-2\pi i kr/N},\\
\mu &= c_0=\frac1N\sum_{r=0}^{N-1}g_r.
\end{aligned}
```

Finite Fourier inversion and a geometric sum give the exact expression

```math
x_n=x_0+\mu n+
\sum_{k=1}^{N-1}c_k
\frac{1-e^{2\pi i kn/N}}{1-e^{2\pi i k/N}}.
```

The integral is linear growth plus a periodic correction. Complex conjugate
terms make the result real. This indexing convention must be reconciled with
the article's inclusive partial-sum convention before any article conversion.

Filtering in this representation needs survivor reindexing: if w_n is the
zero-or-one survival mask, define

```math
A(n)=\sum_{j=0}^{n}w_j,\qquad
n_m=\min\{n\ge0:A(n)=m+1\},\qquad y_m=x_{n_m}.
```

Multiplication by w_n leaves zero placeholders. Packing survivors changes
the index, turning an old wave exp(i omega n) into exp(i omega n_m), generally
mixing frequencies. Merely putting rejected entries on the imaginary axis
also retains their old positions.

### 2. A continuous divisibility detector

The squared detector is a normalized **Fejér kernel**, named for Lipót Fejér.
His original1900 paper and a modern normalization reference are listed below.
Classical roots-of-unity orthogonality supplies its divisibility samples.

For a prime p and real input t, define

```math
D_p(t)=\frac1p\sum_{\ell=0}^{p-1}e^{2\pi i\ell t/p}.
```

At an integer n, the ratio in this geometric sum is a p-th root of unity.
When p divides n every term equals one. Otherwise the geometric sum vanishes:

```math
|D_p(n)|^2=
\begin{cases}
1,&p\mid n,\\
0,&p\nmid n.
\end{cases}
```

For every real t, the triangle inequality gives |D_p(t)| <= 1. Its squared
modulus is a real, nonnegative, continuous trigonometric polynomial. It is
important to use squared modulus, rather than a complex square, to prevent
cancellation between imaginary penalties.

### 3. Preserve a prime by activating its filter only afterwards

The user's correction is essential: a global divisibility filter removes p
itself. Instead use

```math
a_p(t)=
\begin{cases}
0,&t\le p,\\
t-p,&p<t<p+1,\\
1,&t\ge p+1.
\end{cases}
```

This is continuous and lies between zero and one. At integer inputs it
preserves p and all earlier integers, while enabling rejection of later
multiples. This particular activation is piecewise linear; no general
smoothness claim is made.

### 4. Recursive stage construction

Let p_0=2 and start with Z_0(t)=t+i sin^2(pi t). At stage k use

```math
\begin{aligned}
\beta_k&=2^{-(k+1)},\\
Z_{k+1}(t)&=Z_k(t)+i\beta_k a_{p_k}(t)|D_{p_k}(t)|^2,\\
p_{k+1}&=\min\{n\in\mathbb Z:n>p_k,
                   \operatorname{Im}Z_{k+1}(n)=0\}.
\end{aligned}
```

The next head is sought strictly above the previous head, since previous
primes deliberately remain contacts. The rule is recursive and does not
require a precomputed list of all primes.

The next contact exists: if M is the product of the filters applied so far,
then M+1 exceeds the current head and is divisible by none of those filters.
Hence the set in the minimum is nonempty.

Inductively, the next head is prime. A composite proposed next head would
have a prime divisor smaller than itself. Since all primes up to the current
head have been selected, either that divisor is already a filter (a
contradiction), or it is itself a surviving integer strictly between the
current head and the proposed next head (also a contradiction). Thus the
recursive heads are exactly the successive primes.

For each finite stage, contacts above its current head agree with that
stage's surviving integers. Earlier prime contacts are retained as history.
The real coordinate here is the candidate value t, not its survivor rank.

### 5. Continuous infinite limit and exact prime contacts

Expanding the recursion gives

```math
Z_\infty(t)=t+i\left[
\sin^2(\pi t)+
\sum_{k=0}^{\infty}\beta_k a_{p_k}(t)|D_{p_k}(t)|^2
\right].
```

Each summand is continuous and bounded by beta_k. The geometric tail bound
is independent of t, giving uniform convergence and hence continuity.
This matters because pointwise convergence alone does not preserve
continuity, and an arbitrary infinite sum may not even converge.

There is a stronger observation specific to the activation: on any bounded
interval, filters with p_k at or above its upper endpoint vanish identically.
The sum is therefore locally finite. Continuity consequently also holds
with all beta_k=1. Geometric weights provide global uniform convergence of
the correction series but are not necessary for continuity or the contact set.

For real t >= 2, the contacts are exactly the primes:

```math
Z_\infty(t)\in\mathbb R
\quad\Longleftrightarrow\quad t\text{ is a prime integer}.
```

Proof: every imaginary summand is nonnegative. A noninteger has positive
sin^2(pi t). At a prime integer q, earlier prime detectors vanish and the
filters for q and later primes are inactive. At a composite integer n, a
prime divisor p<n has activation one and detector squared modulus one,
so its positive-weight contribution excludes contact. Restricting to t>=2
avoids the additional contacts at smaller integers outside the intended domain.

### 6. Benefits and limitations

| Representation | Benefit | Limitation |
|---|---|---|
| Cycle list and discrete integral | Exact integer arithmetic; consecutive values and gaps are explicit | Finite cycle sizes grow with sieve stages |
| Fourier gap representation | Exact frequency description of each fixed stage | Packing after filtering changes indices and mixes frequencies |
| Discrete complex markers | Encodes survival while preserving old positions | Does not enumerate survivors without selection |
| Continuous contact curve | Simple additive stage rule; limit retains prime contacts | Finding or counting contacts remains a separate problem |

The construction describes a complex-valued function of a real variable,
not a holomorphic function of a complex variable. The imaginary part is
nonnegative, so contacts are not sign crossings. Numerical near-zero values
are not certificates of exact contact. No computational speedup, new prime
distribution estimate, or simplification of existing Stainless proofs has
been established. The activated curve is not purely a finite sum of sine
and cosine waves: activation introduces an additional piecewise function.

## Bibliography

These sources distinguish classical ingredients from the specific activated
interpolation presented here. Its historical priority has not been determined;
an independent derivation is not evidence of novelty. External formal
verification does not imply Stainless verification of this construction.

1. Rein van den Boomgaard, University of Amsterdam, *Signal Processing*,
   [3.4. Discrete Time Fourier Series](https://staff.fnwi.uva.nl/r.vandenboomgaard/SignalProcessing/FrequencyDomain/DTP.html).
   Reference for expressing a finite-period sequence as a finite sum of
   complex exponentials and recovering it by Fourier inversion.
2. Rodrigo Raya and Manuel Eberl (2019), Archive of Formal Proofs,
   [Gauss Sums and the Polya–Vinogradov Inequality](https://www.isa-afp.org/browser_info/current/AFP/Gauss_Sums/document.pdf).
   Formal reference for geometric sums of roots of unity, including the
   unity-root-sum identity underlying the integer divisibility detector.
3. 3Blue1Brown,
   [ManimGL — animation engine for explanatory math videos](https://github.com/3b1b/manim).
   Proposed tool for plotting the complex curve and animating successive
   filters. This is a software reference, not a source for the mathematical
   claims. The linked repository is ManimGL, distinct from Manim Community.
4. L. Fejér (1900),
   [*Sur les fonctions bornées et intégrables*](https://history-of-approximation-theory.com/fpapers/fej1OCR.pdf),
   *Comptes rendus de l'Académie des sciences*,131,984–987.
   Original historical source for Fejér's Fourier-averaging work. The normalized
   kernel used here is described by a modern convention in
   [MIT18.102, Lecture16, Proposition173](https://ocw.mit.edu/courses/18-102-introduction-to-functional-analysis-spring-2021/eb44436072623f60f8f416875d4b2c11_MIT18_102s21_lec16.pdf).
5. NIST DLMF, [section27.18](https://dlmf.nist.gov/27.18) and
   [section27.3](https://dlmf.nist.gov/27.3).
   Modern references for the sieve of Eratosthenes, square-root certification,
   and classical divisor identities used in the later all-integer version.

The [claim-level attribution inventory](../../properties/sieve-sequence/research/continuous-sieve-attribution.md)
also records earlier Holt–Rudd gap-cycle research and unresolved priority
questions. These source roles replace any implication that “derived here”
means “first discovered here.”

## Failed Paths

- Sine-wave follow-up: two patch attempts used unmatched wrapped-line context
  (one ticket hunk, one property hunk) and failed atomically. Corrected only
  those same files using exact existing paragraph/heading anchors. No failed
  mathematical strategy or runtime validation occurred.
- 2026-10-21: first ticket-update patch had an unmatched context line; patch
  application failed atomically without changing the file. Retried only the
  same ticket with exact existing context. No mathematical approach failed.
- A second ticket prose patch repeated an inexact whole-line context and
  failed atomically. Read the exact surrounding lines before retrying; the
  corrected same-file patch succeeded. Do not reuse that unmatched context.
- Unactivated filters preserve primes only as stage history: each prime is
  eventually rejected by its own detector. Valid for that alternative goal,
  but fails the goal of retaining prime contacts in the limit. Activation
  after p resolves this issue.
- Real-part projection of discrete complex markers produces zero placeholders,
  not a packed survivor sequence. It remains suitable when positions are
  intentionally retained; use survivor selection when enumeration is needed.
- Inferring continuity solely from continuous summands is insufficient.
  Uniform convergence or local finiteness supplies the missing condition here.

## Open Concerns

- All analytic formulas and arguments remain Stainless-unverified; no Scala
  implementation or supporting analytic library has been selected.
- Before publication, audit relevant existing Fourier properties, formalize
  the induction on stage heads, and supply the required article representations.
- Efficient contact enumeration and any quantitative advantage remain open.
- The piecewise activation guarantees continuity; stronger regularity would
  require an explicitly chosen activation and a separate argument.

## Next Action

Review section1.2, commit only the property note and this ticket, and push
feature/imaginay_function normally to update existing PR64. No new PR, merge
or force push; preserve unrelated working changes and inherited-scope disclosure.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-10-20 | Continuous real-axis contacts avoid survivor reindexing when representing the accepted set. | Saved the value-coordinate construction and its tradeoffs. |
| 2026-10-20 | Filters must activate after their own primes to retain primes in the limit. | Recorded activation, recursive heads, and the contact proof. |
| 2026-10-20 | Activation makes the infinite series locally finite; positive geometric weights additionally give uniform convergence. | Recorded both continuity arguments and verification limits. |
| 2026-10-20 | Supporting references should accompany the saved discussion without attributing the specific activated construction to them; its priority was not established. | Added the cited Fourier, roots-of-unity, and ManimGL references with their respective roles. |
| 2026-10-20 | User requested preservation of four proposed research directions. | Began documentation-only candidate save; separate derived identities from open quantitative targets. |
| 2026-10-20 | Height and pair-height identities provide interfaces, while damped counts need independent lower bounds. | Saved candidates/continuous-contact-research-directions.md, linked its four directions from the candidate README, and completed mathematical/status review; no new failed approach. |
| 2026-10-21 | User prefers math-only development and requested saving/committing the all-integer variant. | Branch name corrected by user to feature/imaginay_function; existing scene checks pass; begin exact-scope documentation and commit. |
| 2026-10-21 | Uniform recurrence has divisor-count heights and prime-step contact changes; local finiteness supplies continuity. | Saved complete mathematical proofs and candidate link; review passed; isolated branch/commit next. |
| 2026-10-21 | User's team branch convention takes precedence over the default prefix. | Created feature/imaginay_function; reviewed exact 14-file commit scope, excluding unrelated work. |
| 2026-10-21 | User clarified a wave-first construction: each step leaves nonmultiple integer values unchanged. | Saved sine-ratio and finite-cosine formulas, continuous extension and equivalence to the existing detector; prepare documentation commit and draft PR with inherited scope disclosed. |
| 2026-10-21 | Additive recurrence telescopes to one locally finite infinite sum; no global uniform-convergence assumption is needed. | Added section1.2 with finite/infinite forms, compact-limit proof and twin-contact formula; update existing PR64 via two-file documentation commit. |
| 2026-10-21 | User requested credit for previously discovered properties. Proof and historical priority are separate. | Named Fejer and the modern expositors/formalizers, added classical sieve/divisor references, and linked the claim-level attribution audit. Exact interpolation priority remains unresolved. |
