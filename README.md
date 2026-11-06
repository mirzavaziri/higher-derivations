# Higher derivations on algebras — a Lean 4 formalization

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

## Building

The Lean and Mathlib versions are pinned (`lean-toolchain`, `lake-manifest.json`), so the
project builds the same way at any time:

```
lake exe cache get
lake build
```

## Acknowledgement

The formalization was written with the assistance of Claude (Anthropic) and checked by the
Lean kernel.
