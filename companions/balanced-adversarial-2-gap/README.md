# Balanced Adversarial 2-Gap Companion

The balanced adversarial companion keeps the real sieve's exact `r-2`
descendant law but, wherever the exact-two-deletion rule allows it, spends
both deletions on a chosen target region whenever possible. It is the
pessimistic mirror of
[the balanced good (protective parent) companion](../balanced-good-2-gap/README.md):
where that companion preserves the target child whenever possible, this one
destroys it whenever possible. Its purpose, full setup, and comparison with
the other balanced companions are in [`model.md`](model.md).

Its role is to make one point sharp and unconditional: unbounded global
2-gap growth alone cannot force head 2-gaps. An adversary free to choose,
independently for every parent, which two copies die can drive a chosen
target region's local population to exactly zero forever, while the global
population keeps growing without bound.

## Short-Name Registry

| Short Name | File |
|---|---|
| Targeted Head Suppression | [properties/targeted-head-suppression.md](properties/targeted-head-suppression.md) |

## Shared Premises

Unconditional for the head (a single point can never receive more than one
child per parent). For a general target window, conditional on the window
being shorter than the current modulus -- already established as holding
for every stage past the first few (`p >= 11`); see
[Targeted Head Suppression](properties/targeted-head-suppression.md) for
the citation. This is a premise about a constructed model, not a fact about
the real sieve; see the [parent README](../README.md#scope-contract).
