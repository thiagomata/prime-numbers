# Releasing Articles

This document describes how and when this repository cuts a GitHub Release,
and what each release is expected to mean.

## Strategy: One Release Per Article

A release is an immutable snapshot in time. Requiring every article to be
publication-ready before the first release forces fixing all of them at
once, which does not match how this project actually works — articles are
brought up to `CONTRIBUTING.md`'s Article Quality Checklist one at a time,
starting with the earliest chapters.

Instead, each release marks the point where one additional article has
reached publication-ready status. The release itself is still a snapshot of
the **whole repository** at that commit — Zenodo and Software Heritage
archive the full repository, not a single file — but the release notes scope
the claim to the specific article(s) that changed.

This also matches Zenodo's own versioning model: each GitHub Release gets
its own DOI, and Zenodo separately maintains a "concept DOI" that always
resolves to the latest release, so a release-per-article sequence is exactly
the versioning story Zenodo is designed for, not a workaround.

## Versioning Scheme

Tags follow `vMAJOR.MINOR.0`:

- **v1.0.0** — first release, marking the first article publication-ready.
- **v1.x.0** — each subsequent article reaching publication-ready status
  bumps the minor version. This is purely additive: the newly released
  article is complete and citable, and nothing about a previously released
  article's content or claims changes.
- **v2.0.0** (reserved) — a structurally bigger milestone, such as "all
  currently planned chapters published" or a reorganization that changes how
  earlier articles are cited (e.g. renumbering that breaks external links).

Starting at `v1.0.0` rather than `v0.1.0` is deliberate. Semver's `0.x`
convention signals "the API may change without warning" — appropriate for
software under active development, but the wrong signal for a citable,
checklist-verified article: `modulo.md`'s math is proven and Stainless-
verified, and the article itself does not become less complete because
`list.md` isn't done yet. What's incomplete is the *collection*, not the
*content already released*. `v1.0.0` communicates "this release meets its
own quality bar and won't be silently reinterpreted," which is the message a
citer needs.

Patch versions (`v1.0.1`) are not used under this scheme: a release is
immutable, so a correction to already-released content becomes a new minor
release, not a patch to the old one.

## Mechanics

1. **Cut releases from `master` only.** A release must follow a merged PR,
   never a feature branch — Zenodo archives the exact tagged commit, and
   that commit should be a coherent, working state of the whole repository.
2. **Update `CITATION.cff` first.** Bump the `version:` field to match the
   new tag and update `date-released` to the release date. (If `version:`
   is not yet present, add it starting at the first release.)
3. **Scope the release notes.** State plainly which article(s) reached
   publication-ready status in this release and that the rest of the
   repository remains in progress. Do not imply the whole project is
   finished.
4. **Tag and create the GitHub Release** (`git tag vX.Y.0 && git push --tags`,
   then `gh release create`), only after explicit sign-off — a
   Zenodo-linked release mints a permanent DOI, which is not something to
   create speculatively.
5. **Zenodo archival is a one-time, separate setup step** (linking the
   Zenodo GitHub App to this repository) done once by the repository owner;
   after that, each new GitHub Release triggers an automatic archive and DOI
   mint. Software Heritage already archives all public GitHub repositories
   automatically, independent of any release.

## Per-Release Checklist

Before tagging a release for article `N`:

- [ ] Article `N` passes `CONTRIBUTING.md`'s Article Quality Checklist
      (structure, notation, conclusion completeness, OBJECTS.md parity, no
      forward references, etc.).
- [ ] Every other article that cites article `N` uses its current title and
      any anchors it links into article `N` still resolve (check after any
      subsection renumbering).
- [ ] `CITATION.cff` `version` and `date-released` updated.
- [ ] Release notes name the specific article(s) now publication-ready and
      state that the rest of the repository is still in progress.
