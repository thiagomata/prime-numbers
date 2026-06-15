# Review: articles/cycle.md

## Source

- Article: `articles/cycle.md`
- Current role: Foundational article

## Verdict

Promising foundation article, but needs editorial tightening before magazine publication.

## Must Fix

- Add explicit source-reference blocks after every major verified property, following the current `PROOF_GUIDE.md` format.
- Cross-check every cited lemma name against `OBJECTS.md` and `src/main/scala/` so the article does not rely on renamed or stale proof functions.
- Make the title more precise. "Unbound Lists" is awkward and should become something like "Formal Verification of Cyclic Lists".
- Ensure each property has all three required forms: English overview with `Intuition:` and `Why This Matters:`, mathematical proof, and Scala verification code.

## Should Fix

- Treat the repetition in the long equivalence section as an editorial choice, not an automatic flaw. The self-contained proof blocks are useful, especially for readers entering from one side of the equivalence. Recommended fix: add a short roadmap before the proof explaining that some repetition is intentional, and only remove repeated text where it does not improve local readability.
- Split long code listings from proof explanation so readers can scan the argument.
- Add a short scope note clarifying that the article proves cycle access, equivalence, and periodicity properties; applications to sieve sequences are handled in later articles.

## Validation

- Run `just verify` or confirm the latest `verify.log` still reports all VCs valid.
- Search for every function cited by the article in `src/main/scala/`.
- Compare the article property list against the Cycles section of `OBJECTS.md`.
