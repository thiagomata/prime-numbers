# Attribution for the continuous sieve notes

**Status:** Source audit, 2026-10-21. This records established ingredients and
verified earlier work, not a completed search for every first discovery.
An independent proof, new notation or a new visualization does not establish
that a mathematical property is new.

## Scope

This pass covers the [uniform divisor-sieve note](../uniform-continuous-divisor-sieve.md),
[four contact directions](../../../candidates/continuous-contact-research-directions.md),
[five wave directions](../../../candidates/continuous-wave-twin-research.md),
[wave analysis](continuous-wave-twin-analysis.md), original construction notes,
and the [animation explanations](../../../presentations/continuous-complex-sieve/README.md).
The wider article inventory below remains a separate review obligation.

## The wave already has a classical name

Using a common convention for the Fejér kernel,

```math
\mathcal F_m(\theta)
=\frac1m\left|\sum_{r=0}^{m-1}e^{ir\theta}\right|^2,
\qquad
W_m(t)=\frac1m\mathcal F_m(2\pi t/m).
```

Thus the squared sine quotient and triangular Fourier coefficients in these
notes are normalized Fejér-kernel formulas. Credit **Lipót Fejér**, whose
1900 paper is listed in [F1]. The modern formula in [F2], Proposition173,
uses another normalization: its kernel satisfies
W_m(t)=(2 pi/m)K_(m-1)(2 pi t/m). We use [F2] to check the convention;
we do not attribute the kernel's discovery to the modern lecturer.

Fejér's Fourier summability theorem is not a theorem about this activated
sieve. The activation and prime/twin contact interpretation need their own
arguments, supplied in the notes.

## Claim-by-claim inventory

| Ingredient or statement | Classification and credit | Source and remaining historical question |
|---|---|---|
| Finite Fourier expansion of a periodic cycle; geometric sums selecting divisibility | Classical finite Fourier analysis and roots-of-unity orthogonality | [F3], [F4], especially [F4] sections4–5. These are modern expositions/formalizations, not evidence of first discovery. Do not infer attribution to Gauss merely from the title of [F4]. |
| Sine quotient, positivity and triangular coefficients of W_m | Normalized Fejér kernel | Fejér [F1]; convention checked in [F2]. These ingredients are not new wave identities of this project. |
| Sum of translated W_(km) waves equals W_m | Direct consequence of the classical finite Fourier coefficients and roots-of-unity sum | Proof in the wave analysis. A first source for this exact displayed folding identity has not been located; an independently written proof is not a novelty claim. |
| h(n)=tau(n)-2; factorization formula, low-height cases, square parity and coprime multiplication | Rewriting classical divisor-function facts in height notation | [N1], equations27.3.1 and27.3.5. Parity follows by pairing divisors, or from the product formula. No original discoverer is assigned by this audit; Apostol is cited by NIST as an exposition, not established here as originator. |
| Prime-filter height counts distinct proper prime divisors | Truncated version of a classical arithmetic function | [N2] defines the distinct-prime-divisor count (there called nu). At completion the unweighted activated height is omega(n)-1_(n prime), not omega(n) at primes. Weighted variants are weighted sums. |
| Composite filters remove no new integer contacts; first new rejection at p squared; square-root certification | Elementary sieve-of-Eratosthenes consequences | Traditional attribution to Eratosthenes; modern reference [N3]. The contact language is a reformulation. No surviving original ancient source was inspected. |
| Product of complementary zero-one rejection indicators | Elementary sieve indicator; expansion is inclusion-exclusion | [S1], Chapter6, section3.1, Theorem6.1, is a modern exposition. No first-discoverer claim for inclusion-exclusion is made. This product is not identified as Selberg's sieve. |
| Twin endpoints other than (3,5) are 6k-1 and6k+1 | Elementary congruence restriction: exclude divisibility by2 and3 | Derived in the candidate note's setting; no specific original discoverer verified. This necessary restriction does not assert primality of both endpoints. |
| Sum of two nonnegative heights vanishes exactly when both vanish; local finite stabilization; finite-window exponential count limit | Elementary consequences of the definitions and elementary analysis | Proofs in the corresponding notes. These are not presented as newly discovered general theorems. The short-window estimates proposed afterwards remain open. |
| Expanding a primorial gap cycle and closing gaps; complete-period 2-gap recurrence N_next=(q-2)N | Verified earlier sieve-gap research by Fred B. Holt and Helgi Rudd | [S2], section2/Lemma2.1 (printed p.5); proof of Corollary6.3 (printed pp.25–26); product count also printed p.28. Their wheel is equivalent up to indexing/rotation for these counts. This is earlier work, not a verified claim that they were the first discoverers. |
| Specific activation a_m, complex curve t+i h, bounded pair amplitude and activation-defect bookkeeping | Interpolation and presentation investigated here, built from the preceding ingredients | Historical priority of these exact combinations has not been established. No authorship or novelty claim follows from their being derived in this project. |

The Holt–Rudd counts concern complete sieve cycles. They do not assert that
every endpoint in a cycle is prime or prove a surviving pair in every short
square-certified interval. Nor does this citation identify every project
separator/histogram lemma with a theorem in their paper.

## Sources and what kind of credit they support

- **[F1] Original historical paper:** L. Fejér (1900),
  [*Sur les fonctions bornées et intégrables*](https://history-of-approximation-theory.com/fpapers/fej1OCR.pdf),
  *Comptes rendus de l'Académie des sciences*,131,984–987.
- **[F2] Modern kernel exposition:** MIT OpenCourseWare (2021),
  [18.102, Lecture16: Fejér's theorem and convergence of Fourier series](https://ocw.mit.edu/courses/18-102-introduction-to-functional-analysis-spring-2021/eb44436072623f60f8f416875d4b2c11_MIT18_102s21_lec16.pdf),
  Proposition173, printed p.83. Citation is for the displayed kernel formula.
- **[F3] Modern finite Fourier exposition:** Rein van den Boomgaard,
  [*Signal Processing*, section3.4, Discrete Time Fourier Series](https://staff.fnwi.uva.nl/r.vandenboomgaard/SignalProcessing/FrequencyDomain/DTP.html),
  University of Amsterdam. The notes acknowledge contributions by Jose
  Lagerberg, Taco Walstra and Maxim van den Berg.
- **[F4] Modern formal development:** Rodrigo Raya and Manuel Eberl (2019),
  [*Gauss Sums and the Pólya–Vinogradov Inequality*](https://isa-afp.org/entries/Gauss_Sums.html),
  Archive of Formal Proofs; [development PDF](https://isa-afp.org/browser_info/current/AFP/Gauss_Sums/document.pdf),
  sections4–5, including `unity-root-sum`. This gives Isabelle proofs of
  classical ingredients, not Stainless verification of these curves.
- **[N1] Modern divisor reference:** NIST Digital Library of Mathematical
  Functions, [section27.3](https://dlmf.nist.gov/27.3), especially
  [27.3.1](https://dlmf.nist.gov/27.3.E1) and
  [27.3.5](https://dlmf.nist.gov/27.3.E5). Its notes cite T. M. Apostol (1976),
  *Introduction to Analytic Number Theory*, pp.27–50.
- **[N2] Modern arithmetic-function reference:** NIST DLMF,
  [section27.2(i)](https://dlmf.nist.gov/27.2.i).
- **[N3] Modern sieve reference:** NIST DLMF,
  [section27.18](https://dlmf.nist.gov/27.18), which references R. Crandall and
  C. Pomerance (2005), *Prime Numbers: A Computational Perspective*, section3.2,
  for the sieve of Eratosthenes and states the square-root divisor test.
- **[S1] Modern inclusion-exclusion exposition:** Paul Pollack (2009),
  [*Not Always Buried Deep: A Second Course in Elementary Number Theory*](https://www.pollack-math.net/NABDofficial.pdf),
  American Mathematical Society, Chapter6, section3.1, printed p.170.
- **[S2] Earlier research directly relevant to the cycle lists:** Fred B. Holt
  and Helgi Rudd (2014),
  [*Eratosthenes sieve and the gaps between primes*](https://arxiv.org/abs/1408.6002).
  Source locations above refer to arXiv v1. Their related earlier preprint is
  [*On small gaps among primes*](https://arxiv.org/abs/1312.7569)
  (first submitted2013; revised2014).

## Wider article review still required

The current notes are only one part of the project. The following inventory
records concrete places to review, not findings that all these articles lack
citations:

| Article | Next attribution check |
|---|---|
| [Sieve Sequence](../../../articles/chapter6/sieve-sequence.md) | Existing Hardy–Wright and Pritchard references are present. Compare the cycle construction with Holt–Rudd and earlier wheel-sieve work; locate citations at the corresponding claims. |
| [Gap Dynamics](../../../articles/chapter6/gap-dynamics.md) | Its reference list currently contains the project foundation article only. Review the complete-period count/recursion against [S2] and source the named external asymptotic inputs explicitly. |
| [Survival Frontiers](../../../articles/chapter7/survival-frontiers.md) | Kochen–Stone and Hardy–Wright are already cited. Check elementary/classical machinery and distinguish new companion assumptions from prior theorems. |
| [Relaxed Almost-Prime](../../../articles/chapter6/relaxed-almost-prime.md) | Chen and modern sieve books are already cited. Verify point-of-use mapping rather than treating bibliography presence as a complete audit. |

Article edits must carry the same corrections into any accompanying arXiv
edition and rebuild it. No publication or arXiv source was changed in this pass.

## Attribution practice for subsequent results

Name established objects when introducing them. Cite an original paper when
verified and a modern source when it helps readers check the convention or
proof. Say which role each source serves. Mark a result as a consequence of
classical inputs when that is what the proof shows. For an unfamiliar exact
construction, write “priority not established” until a literature comparison
supports a stronger statement. Keep an open research question distinct from
a new theorem, and include credit in narration as well as technical notes.
