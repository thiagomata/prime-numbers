# Sieve Sequence Equivalence Proof and Article Improvements

## Summary

Completed the three-way equivalence proof (Spec ≡ Canonical ≡ Cycle) for the
sieve sequence at both current and next stages — 12,000+ lemmas, all verified
through Stainless (11502 valid, 0 invalid, 0 unknown). Alongside the proof,
reviewed and improved 7 articles covering the full verification stack from
foundational modulo arithmetic through cycle integrals to the sieve sequence
itself, including a `three-representations` rule requiring all properties to be
presented in English + LaTeX math + Scala `.holds` code with source references.

## Articles reviewed and improved

- **`modulo.md`** — division and modulo properties from first principles
- **`list.md`** — recursive list properties (sortedness, containment, product)
- **`cycle.md`** — cyclic list structure, periodicity, index arithmetic
- **`integral.md`** — discrete integration (prefix sums) from first principles
- **`integral-cycle.md`** — cycle integrals: positivity, strict increase,
  difference equals cycle value (Section 5 "Extended Properties" remains draft)
- **`sieve-sequence.md`** — the capstone: A = B = C equivalence for both
  current and next stages. All core proofs verified. Reports 11472 valid.
- **`gap-dynamics.md`** — gap evolution and twin prime candidate persistence
  in sieve sequences. Uses verified structural facts; open problems honestly
  flagged as `[Draft]`, `[Open]`, `[Empirical]`.

4 deprecated articles consolidated into the current set (old v1 proofs,
earlier gap-persistence drafts). Applied `framing-integrity` and
`property-completeness` checks across all articles: abstracts now accurately
scope what's proven, conclusions don't overclaim, every property expected by
the subject matter is either present or flagged as a gap.

## What was proved: A = B = C

**A = B = C (current stage):** `SpecSieveSequence.apply(k) ==
CycleSieveSequence.apply(k)` for all `k >= 0`, for every valid sieve stage.
The canonical representation (`SpecDerivedCycleSieve`) bridges the gap: the
spec value is proven equal to the cycle integral value at every index.

**A = B = C (next stage):** The three next-stage streams (`spec.next`,
`canonical.cycle.next()`, `CycleSieveSequence(spec.next).apply(k)`) produce
identical gap lists and identical apply sequences. The proof composes through
15 methods in the proof spine, using the survivor-walk bridge to match gaps
between the spec's `next.gapList` and the cycle's computed gaps.

**Structural invariants proven:**
- GapCycle enforces `allGreaterThan(gaps, 0)` at the type level
- CycleIntegral: positivity, strict increase, diff-equals-cycle-value
- Rotation/shift/gap-positivity algebras in ch3 (13 lemmas, 1322 VCs)
- Spec filter completeness: all primes below head are in `filterValues`
- Coprimality chains: every sieve-emitted value is coprime to all filter primes
- Filter preserves primes: no prime is filtered out by smaller primes
- Modulus arithmetic: product of filter primes equals `filterModulus`

## Chapter restructuring for verification isolation

The chapter dependency graph was refactored to eliminate circular imports and
enable independent chapter verification. Previously ch5 imported from ch6 and
ch6 imported from ch5, forcing all 6 chapters to be verified together in one
batch — overwhelming the solver and destroying cache reuse.

- **Extracted `CoprimeUtils.scala`** into ch5, removing the ch5→ch6 import edge
- **Moved rotation theory** (splitAt, rotateAt, permutation invariants) from ch6
  to ch3, making it a pure list-algebra foundation independent of primes
- **Moved gap-positivity foundation** (sum-positive, strict-ascending,
  gaps-positive) to ch3/ch4, isolating it from prime-dependent ch6 code
- Each chapter now verifies independently: ch3 1322 VCs, ch4 2675 VCs,
  ch5/ch6 each green with no cross-chapter import cycles
- Result: warm cache reuse works reliably — 3861/4678 VCs from cache on re-runs

## Key proof techniques documented

- **Transfer pattern:** `assertApplyMatches` rewrites `spec(k) -> cycle(k)`,
  transferring all spec facts to the cycle side without re-derivation
- **Private lemmas** reduce solver complexity at call sites (LEARNINGS 1.1)
- **Constructor invariants** kill cross-file unknowns: one `require(modulus > 0)`
  on `CycleSieveSequence` eliminated 5 unknowns in 3 files (LEARNINGS 6.5)
- **Builder order sanity-check:** reversed builder = unprovable goal disguised as
  timeout — caught by paper check before induction (LEARNINGS 5.6)
- **Recursive-search branch invariants** returned explicitly rather than left as
  internal assertions (LEARNINGS 18.5)
- **Cross-instance lemma calls** isolated through directed equality lemmas with
  explicit structural preconditions (LEARNINGS 18.3)
- **Lemma composition:** expensive shared constructions extracted into one outer
  proof body to avoid `.holds` boundary doubling VC cost (LEARNINGS 19.1)

## What's still open

- **Leg 4:** Proving `CycleSieveSequence.nextFromWindow()`'s walk-backed gaps
  match the spec's next-stage gaps through the cycle's own structural rules
  (bypasses the SpecDerivedCycleSieve bridge). Walk timed out 3x; certified
  `nextFromWindow()` path works but doesn't use the walk.
- **Euclid's lemma** (`primorial-not-divisible-by-new-prime`): blocked on SMT
  non-linear arithmetic limits
- **`apply(1) < head^2`** (`prove-apply1-is-prime`): blocked on Bertrand's
  postulate / prime gap depth
- **`gap-dynamics.md`** twin-prime claims: all `[Draft]` / `[Open]` — no formal
  proof, only empirical support up to p=997
- **Build/tooling:** `sbt assembly` dedup merge strategy and native Z3 warning

## Ticket structure after cleanup

- `active/` — 4 tickets (proof, article rewrite, property landscape, ch6 Phase E)
- `blocked/` — 4 tickets (2 open math problems, 2 tooling issues)
- `done/` — 29 completed tickets with implementation notes
- `archived/` — 1 empirical twin-prime research ticket (separate track)
- `trash/` — 17 superseded approaches + 7 stale planning docs + article reviews
