# Higher derivations on algebras — a Lean 4 formalization

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24015054.svg)](https://doi.org/10.5281/zenodo.24015054)
[![Lean Action CI](https://github.com/mirzavaziri/higher-derivations/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/mirzavaziri/higher-derivations/actions/workflows/lean_action_ci.yml)

This repository contains a complete formal verification, in [Lean 4](https://lean-lang.org)
with [Mathlib](https://github.com/leanprover-community/mathlib4), of the characterization of
higher derivations proved in

> M. Mirzavaziri, *Characterization of higher derivations on algebras*,
> Communications in Algebra **38** (2010), no. 3, 981–987.

## The result

Let `A` be an algebra (not necessarily commutative) over a field `𝕜`. A **higher derivation**
on `A` is a sequence of linear maps `d₀, d₁, d₂, …` with `d₀ = id` and

    dₙ(ab) = Σ_{i+j=n} dᵢ(a) dⱼ(b).

* **`HigherDerivation.exists_derivations`** — every higher derivation arises from a sequence of
  derivations `δ₁, δ₂, …` through the recursion

      (n+1) dₙ₊₁ = Σ_{k=0}^{n} δₖ₊₁ ∘ dₙ₋ₖ.

  This direction holds **in every characteristic**.
* **`HigherDerivation.leibniz_of_recursion`** — conversely, if `𝕜` has characteristic zero,
  every sequence built from derivations by this recursion is a higher derivation.

Both theorems are proved completely: the file contains no `sorry`, and the proofs rely only on
Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Files

* [`HigherDerivations/Basic.lean`](HigherDerivations/Basic.lean) — definitions and proofs.

You can also [open the file in the Lean web editor](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fmirzavaziri%2Fhigher-derivations%2Fmain%2FHigherDerivations%2FBasic.lean) and check it in your browser,
without installing anything.

## Building

The Lean and Mathlib versions are pinned (`lean-toolchain`, `lake-manifest.json`), so the
project builds the same way at any time:

```
lake exe cache get
lake build
```

## How to cite

If you use this formalization, please cite it together with the original paper:

```bibtex
@software{mirzavaziri_higher_derivations_lean,
  author    = {Mirzavaziri, Madjid},
  title     = {Higher derivations on algebras: a {Lean} 4 formalization},
  version   = {v1.0.0},
  year      = {2026},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.24015054},
  url       = {https://doi.org/10.5281/zenodo.24015054}
}

@article{mirzavaziri_2010_higher_derivations,
  author  = {Mirzavaziri, Madjid},
  title   = {Characterization of higher derivations on algebras},
  journal = {Communications in Algebra},
  volume  = {38},
  number  = {3},
  pages   = {981--987},
  year    = {2010}
}
```

## Acknowledgement

The formalization was written with the assistance of Claude (Anthropic) and checked by the
Lean kernel.
