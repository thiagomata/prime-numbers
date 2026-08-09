# Reviewer Notes — August 2026 Batch

**Status as of final pass:** all actionable items resolved. Items 1–3 were
fixed by the authors after the first round; item 4 was intentionally
declined (Appendix B retained as the complete 86-property audit record);
items 5–6 were fixed in this final pass. No item altered a proof or a
constant. See the per-item **Resolution** lines.

Review of the August 2026 candidate/property/article batch:

- `articles/chapter6/gap-dynamics-v2.md` (new review draft)
- `articles/draft/draft-relaxed-almost-prime-sieve-sequence.md` (new review draft)
- `candidates/INVESTIGATION_STATUS.md` (new closure matrix)
- 13 new property notes: `properties/sieve-sequence/` #74–#86
- 2 new refuted statements: `candidates/refuted/`
  `bounded-cyclic-destruction-run-two.md`,
  `relaxed-weight-scalar-density-type-ii.md`
- `articles/learnings/learnings-capacity-argument.md` §22–§23 (new)
- `candidates/bounded-consecutive-destruction.md` (revised after run-three refutation)

## Overall Verdict

This is the most disciplined output the candidate/property program has
produced. The honest-scope machinery is doing real work: no theorem is
overclaimed, no refutation overreaches its quantifier, and the proof/claim
boundary is drawn more carefully than is typical.

Every spot of mathematics was re-derived independently and is correct:

- Property #82 (filter-7): the 21-weight sequence, cumulative sums
  (min −8, max 10), the bound 18/7, the attaining interval (residues 47–161,
  weight sum 18), and the energy consequence `(49P_m/30)·(18/7)² = 54P_m/5`.
- Property #83 (copy-block bridge): `B_j = d_{t_j}+d_{t_j-2}`,
  zero-sum, `ΣB_j² ≤ 4V_r`, and the filter-7 consistency check
  (ΣB²=20/7 ≤ 4V₇=48/7).
- Property #85 / scalar-density refutation: the χ₃ counterexample on
  W=30, Z=6 (8 reduced residues split 4-and-4 mod 3, 32 allowed ordered
  pairs, correlation −32, scalar comparison 0 → ratio exactly 1).
- Bounded cyclic run-two: Q=101, r=23, M=9,699,690, three consecutive
  starts with residues 21, 0, 21 mod 23, all destroyed.

Cross-reference integrity is fully intact: all 86 numbered property links
resolve, all new files carry headings and Status lines. Three-representations
(math form) and no-ticket-references rules are satisfied in both articles.

After this initial pass, a second round re-derived the capacity-exhaustion
chain #74–#81 by hand and checked the article math against each property's
canonical note for drift. That round found two more items (5 and 6 below),
bringing the total to six. None affects any proved result; they are
correctness-adjacent (items 1, 5, 6), framing consistency (items 2, 3), and
presentation (item 4).

## Item 1 — `D` is undefined inside Property #82

**Severity:** correctness-adjacent / easy fix.
**Resolution:** Fixed by the authors after round 1.
**Location:** `properties/sieve-sequence/filter-seven-harmful-excess-is-boundary-sized.md`,
"Exact Energy Consequence" section, lines 225 and 228.

The note writes

```text
\frac{11664}{D^2}
```

and refers to "the `D^2` filter-7 obstruction," but `D` is never defined
anywhere in that file. Its definition lives in another property:

```text
properties/sieve-sequence/capacity-stability-gap-cannot-rescue-capacity-envelope.md:46
    D = Q^2 - Q - 3
```

That is the source of the `P_mD^2/1080` charge the ratio is comparing
against. A reader of the #82 note in isolation cannot tell what `D` is
without leaving the file.

**Suggested fix.** Add one line to the "Exact Energy Consequence" section of
the #82 note, before the ratio:

```text
where D = Q^2 - Q - 3 is the eligible-window population proxy
from property #81.
```

No math changes; this only makes the note self-contained.

## Item 2 — "one exact twin-prime frontier" understates the open field

**Severity:** framing / strategic posture.
**Resolution:** Fixed by the authors after round 1.
**Location:** `candidates/INVESTIGATION_STATUS.md:23`.

The Handoff Verdict opens with:

> The broad field has reduced to one exact twin-prime frontier.

But the matrix's own rows classify 19 candidate-routes as still open
(Supporting open route / Intentionally deferred / Independent diagnostic /
Distinct next program), plus candidate #4's main hypothesis. The one-line
prose summary is more closed-sounding than the matrix it summarizes. The
matrix is the honest artifact; the summary oversells closure.

**Suggested fix.** Soften the opening to match the row-level nuance, e.g.:

> The broad field has reduced to one *primary* twin-prime frontier, with the
> supporting routes classified below by what each would require to re-enter.

This is wording only; the matrix rows are already correct.

## Item 3 — Candidate #25 carries two different status vocabularies

**Severity:** organizational / cosmetic.
**Resolution:** Fixed by the authors after round 1.
**Location:** `candidates/README.md` vs `candidates/INVESTIGATION_STATUS.md`.

Candidate #25 is described with two non-matching label schemes:

- `candidates/README.md` row:
  `[EXISTENCE EXTERNALLY KNOWN; LOCAL FACTORS AND OBSTRUCTIONS PROVED; WEIGHT POSITIVITY OPEN]`
- `INVESTIGATION_STATUS.md` matrix column: `Distinct next analytic program`
- `INVESTIGATION_STATUS.md` "Closure Labels" glossary: `Distinct next program`

Same meaning, three surfaces, two vocabularies. A reader cross-walking the
README and the matrix has to mentally map "Externally known / positivity
open" ↔ "Distinct next program." This is exactly the kind of small thing
that erodes trust in a handoff document over time.

**Suggested fix.** Pick one vocabulary. The cleanest is probably to keep the
README's descriptive tag (it is more informative) and align the matrix
column + glossary to reference it, e.g. label #25 as
"Externally known; method-specific proof open" in both the matrix and the
glossary. Alternatively, add a one-line glossary entry mapping the two.

## Item 4 — `gap-dynamics-v2.md` Appendix B is visually heavy

**Severity:** presentation only / optional.
**Resolution:** Intentionally declined. Appendix B is retained as the
complete 86-property audit record; the coverage table is the point, not
noise.
**Location:** `articles/chapter6/gap-dynamics-v2.md:1642` (Appendix B).

Appendix B is an 86-row coverage table. 54 of those rows say
"Canonical note only; no full article section" — i.e., they confirm a
negative (the property is *not* given a full article section). The table is
accurate and useful as an audit artifact, but it is a lot of real estate to
communicate "these properties live in their notes, not here." A reader
scanning the appendix for signal has to filter past 54 identical rows.

**Suggested fix (optional).** Collapse the 54 "canonical note only" rows
into a single sentence ("Properties #9–#11, #14–#24, #26–#65, #67–#81 are
treated only in their canonical notes; the rows below record the properties
that receive non-trivial article treatment"), and keep only the rows with
non-trivial treatment (Full proof / Collectively summarized / Refuted).
This loses no information and improves readability.

If the full table is valued as an audit record, an alternative is to move
it to a collapsible `<details>` block so the default view shows only the
non-trivial rows.

## Item 5 — Property #86 open-target inequality drift (`\le` vs `\ll`)

**Severity:** correctness-adjacent.
**Resolution:** Fixed. The canonical note's `\le`
(`relaxed-cofactor-divisor-sum-is-prime-progression-discrepancy.md:194`)
changed to `\ll`, matching the article (`:463`). `\ll` is the appropriate
consistent notation for a Type-I sieve estimate.
**Location:** canonical note
`properties/sieve-sequence/relaxed-cofactor-divisor-sum-is-prime-progression-discrepancy.md:194`
vs article `articles/draft/draft-relaxed-almost-prime-sieve-sequence.md:463`.

This was found in the second round by comparing each article section against
its canonical note. The two presentations state the open Type-I target with
different inequality operators:

- Canonical note (line 194):
  `\sum_{d} \tau_B(d) \max_I |\pi(I;d,-2)-\pi(I)/\varphi(d)|` **`\le`**
  `Q^2/(\log Q)^A`
- Article (line 463): the same left-hand side **`\ll`** `Q^2/(\log Q)^A`

These are different mathematical statements. `\le` asserts the sum is *at
most* `Q^2/(\log Q)^A`; `\ll` asserts it is `O(Q^2/(\log Q)^A)` (bounded by
an *implied constant multiple*). For a sieve Type-I target the `\ll` form
is the standard convention, and the constant hidden in `\ll` is exactly what
makes such estimates usable. Both files correctly flag the line as an open
target rather than a theorem, so no proved claim is affected. But the
*stated target* should be the same in both places.

**Suggested fix.** Pick one operator consistently. `\ll` is the right choice
for a Type-I target (it matches the prime-AP / large-sieve literature and
does not pretend an exact equality-constant is known). Change the canonical
note's `\le` at line 194 to `\ll`. No math changes downstream since the line
is an open target, not a proved bound.

## Item 6 — Property #81 uses `M_1` where Property #75 (its cited source) uses `X_1`

**Severity:** correctness-adjacent / notation collision.
**Resolution:** Fixed. Both occurrences in #81
(`capacity-stability-gap-cannot-rescue-capacity-envelope.md:274, :313`)
changed from `M_1` to `X_1`. Notation history, for context: Property #70
originally names the capacity maximum `M_i`; Properties #72 onward
deliberately rename it `X_i` to avoid collision with the native modulus
`M_k`. Since #81 directly invokes #75's `X_1 \ge B_1^2`, its two occurrences
must be `X_1`. Neither the proof nor any constant changes.
**Location:** `properties/sieve-sequence/capacity-stability-gap-cannot-rescue-capacity-envelope.md:274` and `:313`.

This was found in the second round by re-deriving the capacity chain. The
file states

```text
Property #75 then gives the sharp coordinate envelope
    M_1 >= B_1^2
```

and later `U_cap >= α_1 M_1` (line 313). But Property #75's actual boxed
result (`seven-layer-density-floor-maximizes-capacity-width.md:181`) is

```text
X >= B^2
```

i.e. it uses `X` (per-layer `X_i`), not `M`. Every other property in the
chain (#74, #75, #76, #78) uses `X_i` for the per-layer
squared-harmful-excess envelope. The `M_1` in #81 is a mis-naming of `X_1`.

This is also a notation collision: `M_k` is used as the *native modulus*
elsewhere in the capacity family, so a reader scanning #81 has to pause to
decide which `M` is meant.

The arithmetic is unaffected. The derivation `α_1·X_1` with
`X_1 ≥ B_1² ≥ (D/42)²` is what produces `P_mD²/1080` correctly; only the
symbol is wrong.

**Suggested fix.** Replace `M_1` with `X_1` at lines 274 and 313 of #81.
This aligns #81 with its cited source #75 and with the rest of the chain,
and removes the collision with `M_k`. No arithmetic changes.

## Second-Round Summary (capacity chain #74–#81 and article drift)

Recorded for the authors' confidence in the rest of the batch, and so these
are not re-litigated.

**Capacity chain #74–#81 — mathematically sound.** Every README-stated
constant was re-derived from each file's intermediate values:

- #74: `X>=min(N,2B,rB-N)^2/4`; envelope vanishes iff `N∈{0,rB}`. ✓
- #76: `q_(1,2)=210·(1/10)·(2/7)·(5/7)=30/7`; `e_2>=1` for `Q>=36`
  (`D(36)=1257`, `B=floor(1257/42)+1=30`, `7·30²/30=210>209≥s`); gain
  `>=42 d_m e_2`. ✓
- #77: `α_2=847/486`; `m=37` clears by exact integer check
  `29403·275²=2,223,601,875 < 37·847·269²=2,267,721,379`. ✓
- #78: `m>P_k(r_k-2)^2(1+6/D)^2` failure; necessary
  `r_k>=2+sqrt(7m/3)/(1+6/D)` (recovers #77's `29403/847` at `k=2`). ✓
- #79: `m<(3/7)(1+6/D)^2(2 log H/c-2)^2`. ✓
- #80: `sum<=3kD^2r_k^2/(25M_kP_k(r_k-2))` (`X_i<=D^2/25`,
  `q>=M_kP_k(r_k-2)/(3r_k^2)`). ✓
- #81: `1080=30·42²/49=30·36`; `(49/30)·(1/42²)=1/1080` exactly. ✓

The chain dependency is sound: each of #76→#77→#78→#79→#80→#81 correctly
cites its predecessor's named result as a premise, and #78 recovers #77's
constant `29403/847=(3/7)·9²` as its `k=2` specialization.

**External-theorem honesty — clean.** #79, #80, and #81 each use
PNT / Bertrand / prime-Mertens as explicit external dependencies, and each
file fences them off: a Status-header disclosure, a dedicated "Prime-Number-
Theorem Scale" / "Prime-Number-Theorem Corollary" section, and an explicit
"this is not a Stainless theorem" note. No file uses an external theorem
while claiming it as Stainless-verified.

**Article-vs-canonical drift — clean except item 5.** All five properties
(#82, #83, #84, #85, #86) were compared pairwise between their article
sections and their canonical notes. Constants, formulas, quantifier scope,
and sharpness claims are identical everywhere except the one `\le`/`\ll`
discrepancy in #86 (item 5). Notably:

- Property #84's five-row local-factor table is byte-for-byte identical in
  both files.
- Properties #82 and #83's weight sequences, cumulative sums, and boxed
  bounds are character-for-character identical.

The articles omit some of the canonical notes' finite consistency checks
(e.g. #83's filter-7 histogram check, #84's finite-wheel checks) and the
canonical notes' ratio comparisons. These are omissions for editorial
concision, not contradictions.

## What Was Checked and Found Clean

Recorded so these are not re-litigated:

- **All mathematics** listed in the Overall Verdict — re-derived by hand.
- **Cross-reference integrity** — all 86 property links resolve; all new
  files have headings and Status lines; no orphaned targets.
- **`bounded-consecutive-destruction.md` revision** — correctly propagates
  the run-three refutation: main hypothesis stays open, auxiliary `R=2`
  flagged as refuted, refuted statement cross-linked.
- **`learnings-capacity-argument.md` §22** — accurately reflects #82/#83
  and the precise three-part obstruction; math matches the property notes.
- **Three-representations (math form)** and **no-ticket-references** —
  both satisfied in both articles.
- **Appendix B learnings anchor links** (`#222-separate-capacity-envelopes-
  are-exhausted`) — verified to resolve under GitHub-flavored Markdown
  anchor generation (the dot in `22.2` is stripped, yielding `222`).
- **Capacity chain #74–#81 constants** — every README-stated constant
  re-derived from each file's intermediate values; all recomputed correctly.
- **Capacity chain dependency edges** (#76→#77→#78→#79→#80→#81) — each cites
  its predecessor correctly; no predecessor result over-claimed.
- **External-theorem honesty** (#79/#80/#81 use PNT/Bertrand/Mertens) — each
  fences external theorems off explicitly; no false Stainless claims.
- **Article-vs-canonical math drift** (#82, #83, #84, #85) — constants,
  formulas, quantifiers, and the #84 five-row table are identical in both
  presentations.

## Scope Boundary

This review covers correctness, framing, organization, and presentation of
the markdown deliverables only. The Stainless (Scala form-3) representation
gap for the new properties is real but tracked separately in
`tickets/active/add-draft-scala-three-representations-2026-08-03.md` and is
out of scope for this document.
