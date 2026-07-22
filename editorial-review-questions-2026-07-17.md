# Questions from the Editorial Review (2026-07-17)

1. **`deprecated-sieve-sequence.md`'s stale header** references a `draft-sieve-foundation.md`
   file and a ticket `article-consolidation.md`, neither of which exist in the repo today.
   Was `draft-sieve-foundation.md` an early name for what's now `deprecated-sieve-foundation.md`,
   or a genuinely separate file that got deleted? If it's just stale, the top banner (lines 1-7)
   looks safe to delete outright, since the correct/current banner is already sitting right below
   it (lines 11-13).

2. **Broken deprecated-folder links** (`../sieve-sequence.md` → should be `../chapter6/sieve-sequence.md`,
   same for `gap-dynamics.md`) — want me to fix these five links directly? It's a markdown-only
   change (no `.scala` touched), so per the green-to-green rule it wouldn't require `just verify`.

3. **Inline GitHub URLs vs. relative paths** in `cycle.md`, `integral.md`, `integral-cycle.md`,
   `euclid-theorem.md` — is this an intentional style difference (older articles predate the
   relative-path convention CONTRIBUTING.md now documents), or should these be brought in line
   with `sieve-sequence.md`'s approach? Given how many call sites this touches, I'd want your
   go-ahead before batch-editing four articles.

4. **`SpecDerivedEquivalence`, `SpecDerivedExtendedWindowProperties`, `SpecDerivedRebuiltCycleProperties`
   in OBJECTS.md's chapter-6 catalog** — none of these appear in `sieve-sequence.md`. Are these
   internal plumbing that the article intentionally doesn't surface, or genuine article-worthy
   properties that got left out? I flagged this as a spot-check finding rather than asserting a
   gap, since a full property-completeness audit against `OBJECTS.md` was out of scope for this pass.

5. **Should this review itself become a ticket entry** under `tickets/active/` going forward
   (I created `scientific-review-articles-2026-07-17.md` there), or would you rather these kinds of
   editorial passes live somewhere else, given `tickets/trash/README.md` notes that past "article
   reviews" were moved to trash as non-canonical?
