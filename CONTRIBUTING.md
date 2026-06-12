# Contributing Guidelines

This document describes the conventions for articles, proofs, and code in this repository.

## Article Structure

### Formal Articles (Finished)

Formal articles follow a consistent structure:

1. **Title**: Descriptive title starting with "Formal Verification of..."
2. **Author Info**: Name, affiliation, email, GitHub
3. **Abstract**: Wrapped in `<div align="justify"><p style="text-align: justify">`
4. **Numbered Sections**: 1. Introduction, 2. Preliminaries, 3. Main Content, etc.
5. **Mathematical Proofs**: LaTeX notation with step-by-step derivations
6. **Stainless Code**: Formal verification code alongside the math
7. **References**: HTML anchors with links to companion articles

### Draft Articles

- Prefix filename with `draft-` (e.g., `draft-sieve-foundation.md`)
- Same structure as formal articles
- Remove prefix when article is finalized

### Example Structure

```markdown
# Formal Verification of [Topic] from First Principles

**Author:** Mata, T. H.
Independent Researcher  
**Email:** [email](mailto:email)  
**GitHub:** [@thiagomata](https://github.com/thiagomata)

## Abstract

<div align="justify">
<p style="text-align: justify">
...
</p>
</div>

## 1. Introduction

## 2. Preliminaries

## 3. [Main Content]

## 4. Conclusion

## 5. Future Work

## References

<a name="ref1" id="ref1" href="#ref1">[1]</a>
...
```

## Cross-Referencing Rules

### Direction

- **Only reference prerequisites** (articles you build on)
- **Never reference dependents** (articles that build on you)

This follows standard academic convention where citations flow forward in time.

### Format

- Use formal citations in References section for prerequisites
- Use informal "companion article" language for forward mentions (optional)

### Future Work Section

- Mention research areas generally
- Do not cite specific upcoming articles

**Correct:**
> Applications to prime sieving remain valuable research directions.

**Incorrect:**
> See the companion article [5] for sieve foundations.

## README Updates

### When to Add

- After a new lemma is formally verified
- When it represents a "best of the best" result

### Format

Follow the existing section structure:

```markdown
### [Category] Properties

The article [Title](./articles/file.md) establishes...

```math
\begin{aligned}
...definitions...
\end{aligned}
```

From these definitions, it mathematically proves and formally verifies the following properties:

```math
\begin{aligned}
...properties with labels...
\end{aligned}
```
```

## Creating Verifiable Proofs

For detailed guidance on writing mathematical proofs with Stainless verification, 
see [PROOF_GUIDE.md](./PROOF_GUIDE.md).
