# Remove ModIdentity.longProof Dead Code

## START HERE

Micro-goal: remove `ModIdentity.longProof` if it is not used by production
proof code or an article excerpt.

## Goal

The modulo article no longer embeds the long identity derivation because it has
low signal/noise for the article. Under the project standard, source code should
not keep pedagogical-only verified methods. If a method is not used by articles
and not called by the verification/proof surface, it is dead code.

## Current State

`rg -n 'longProof' .` currently finds:

- `src/main/scala/v1/chapter2/div/properties/ModIdentity.scala`
- `src/test/scala/v1/div/properties/ModIdentityTest.scala`
- `src/test/scala/v1/chapter2/div/properties/ModIdentityTest.scala`
- `OBJECTS.md`
- `articles/chapter2/modulo.md`

The article currently links to `ModIdentity::longProof`, but does not use the
long proof as an excerpt. If the method is removed, that article reference must
also be removed or replaced with a reference to `ModIdentity::modIdentity`.

## Expected State

- `ModIdentity.longProof` removed if no production proof depends on it.
- Dedicated tests for `longProof` removed.
- `OBJECTS.md` no longer lists `longProof`.
- `articles/chapter2/modulo.md` does not reference `longProof`.
- `ModIdentity::modIdentity` remains as the verified identity property.

## Search Plan

- Search all `src/main/scala` callers of `longProof`.
- Search tests and docs for references.
- Confirm `modIdentity` proves both:

```math
n \text{ mod } n = 0,\quad n \text{ div } n = 1
```

## Risks

- Removing Scala code requires verification. Do not perform this as part of a
  markdown-only article pass.
- There appear to be duplicate test trees under `src/test/scala/v1/...` and
  `src/test/scala/v1/chapter2/...`; update both if removing the tested method.
- Do not remove nearby identity lemmas or helper imports unless they become
  unused and the compiler confirms it.

## Validation

- Run tests after code/test changes.
- Run `just verify-ch 2`.
- Run `rg -n 'longProof' .` and confirm no stale references remain.
- Run `git diff --check`.

## Article Note

After removal, the Identity section of `articles/chapter2/modulo.md` should
state the mathematical normalization argument and cite only
`ModIdentity::modIdentity`.
