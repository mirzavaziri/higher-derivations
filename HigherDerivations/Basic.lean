/-
Copyright (c) 2026 Madjid Mirzavaziri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madjid Mirzavaziri
-/
import Mathlib

/-!
# Higher derivations on algebras

A *higher derivation* on a `𝕜`-algebra `A` is a sequence `d 0, d 1, d 2, …` of linear maps
with `d 0 = id` and `d n (a * b) = ∑_{i + j = n} d i a * d j b`.

## Main results

* `HigherDerivation.exists_derivations`: every higher derivation is determined by a sequence
  of derivations `δ` through `(n + 1) d (n+1) = ∑_{k=0}^{n} δ (k+1) ∘ d (n-k)`.
  No assumption on the characteristic of `𝕜` is needed.
* `HigherDerivation.leibniz_of_recursion`: conversely, in characteristic zero, any sequence
  built from derivations by this recursion is a higher derivation.

The algebra `A` need not be commutative. Since Mathlib's `Derivation` requires a commutative
algebra, we use our own structure `NCDerivation`.

## References

* M. Mirzavaziri, *Characterization of higher derivations on algebras*,
  Comm. Algebra 38 (2010), 981–987.
-/

open Finset

/-- A derivation on a (not necessarily commutative) algebra `A`. -/
structure NCDerivation (𝕜 A : Type*) [Field 𝕜] [Ring A] [Algebra 𝕜 A] where
  toLinearMap : A →ₗ[𝕜] A
  leibniz : ∀ a b : A, toLinearMap (a * b) = toLinearMap a * b + a * toLinearMap b

/-- A higher derivation: a sequence `d n` of linear maps with `d 0 = id`
satisfying `d n (a * b) = ∑_{i + j = n} d i a * d j b`. -/
structure HigherDerivation (𝕜 A : Type*) [Field 𝕜] [Ring A] [Algebra 𝕜 A] where
  d : ℕ → A →ₗ[𝕜] A
  d_zero : d 0 = LinearMap.id
  leibniz : ∀ (n : ℕ) (a b : A), d n (a * b) = ∑ p ∈ antidiagonal n, d p.1 a * d p.2 b

namespace HigherDerivation

/-! ### Two reindexing lemmas for triple sums -/

/-- `∑_{i+j=n} ∑_{k ≤ i} F(k, i-k, j) = ∑_{k ≤ n} ∑_{l+j=n-k} F(k, l, j)`. -/
theorem sum_antidiagonal_range_fst {M : Type*} [AddCommMonoid M] (n : ℕ)
    (F : ℕ → ℕ → ℕ → M) :
    ∑ p ∈ antidiagonal n, ∑ k ∈ range (p.1 + 1), F k (p.1 - k) p.2 =
      ∑ k ∈ range (n + 1), ∑ q ∈ antidiagonal (n - k), F k q.1 q.2 := by
  rw [sum_comm' (t' := range (n + 1)) (s' := fun k => {p ∈ antidiagonal n | k ≤ p.1})]
  · refine sum_congr rfl fun k hk => ?_
    rw [Nat.antidiagonal_filter_le_fst_of_le (Nat.lt_succ_iff.mp (mem_range.mp hk)),
      sum_map]
    refine sum_congr rfl fun q _ => ?_
    show F k (q.1 + k - k) q.2 = F k q.1 q.2
    rw [Nat.add_sub_cancel]
  · intro p k
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨hp, hk⟩
      have h := mem_antidiagonal.mp hp
      exact ⟨⟨hp, by omega⟩, by omega⟩
    · rintro ⟨⟨hp, hk⟩, -⟩
      exact ⟨hp, by omega⟩

/-- `∑_{i+j=n} ∑_{k ≤ j} F(k, i, j-k) = ∑_{k ≤ n} ∑_{i+l=n-k} F(k, i, l)`. -/
theorem sum_antidiagonal_range_snd {M : Type*} [AddCommMonoid M] (n : ℕ)
    (F : ℕ → ℕ → ℕ → M) :
    ∑ p ∈ antidiagonal n, ∑ k ∈ range (p.2 + 1), F k p.1 (p.2 - k) =
      ∑ k ∈ range (n + 1), ∑ q ∈ antidiagonal (n - k), F k q.1 q.2 := by
  rw [sum_comm' (t' := range (n + 1)) (s' := fun k => {p ∈ antidiagonal n | k ≤ p.2})]
  · refine sum_congr rfl fun k hk => ?_
    rw [Nat.antidiagonal_filter_le_snd_of_le (Nat.lt_succ_iff.mp (mem_range.mp hk)),
      sum_map]
    refine sum_congr rfl fun q _ => ?_
    show F k q.1 (q.2 + k - k) = F k q.1 q.2
    rw [Nat.add_sub_cancel]
  · intro p k
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨hp, hk⟩
      have h := mem_antidiagonal.mp hp
      exact ⟨⟨hp, by omega⟩, by omega⟩
    · rintro ⟨⟨hp, hk⟩, -⟩
      exact ⟨hp, by omega⟩

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

/-- The first term `d 1` of a higher derivation is a derivation. -/
theorem d_one_leibniz (D : HigherDerivation 𝕜 A) (a b : A) :
    D.d 1 (a * b) = D.d 1 a * b + a * D.d 1 b := by
  have h : antidiagonal 1 = {(0, 1), (1, 0)} := by rfl
  rw [D.leibniz, h]
  simp [D.d_zero, add_comm]

/-! ### Step 1: the sequence `δ` -/

/-- The derivations attached to a higher derivation:
`δ 0 = 0` and `δ (n+1) = (n+1) d (n+1) - ∑_{k<n} δ (k+1) ∘ d (n-k)`. -/
def δ (D : HigherDerivation 𝕜 A) : ℕ → A →ₗ[𝕜] A
  | 0 => 0
  | n + 1 => ((n : 𝕜) + 1) • D.d (n + 1) - ∑ k : Fin n, D.δ (k + 1) ∘ₗ D.d (n - k)

theorem δ_zero (D : HigherDerivation 𝕜 A) : D.δ 0 = 0 := by
  rw [δ]

theorem δ_succ (D : HigherDerivation 𝕜 A) (n : ℕ) :
    D.δ (n + 1) = ((n : 𝕜) + 1) • D.d (n + 1) - ∑ k : Fin n, D.δ (k + 1) ∘ₗ D.d (n - k) := by
  rw [δ]

/-! ### Step 3: the recursion `(n+1) d (n+1) = ∑_{k ≤ n} δ (k+1) ∘ d (n-k)` -/

theorem d_succ_eq_sum (D : HigherDerivation 𝕜 A) (n : ℕ) :
    ((n : 𝕜) + 1) • D.d (n + 1) = ∑ k ∈ range (n + 1), D.δ (k + 1) ∘ₗ D.d (n - k) := by
  have h := Fin.sum_univ_eq_sum_range (fun k => D.δ (k + 1) ∘ₗ D.d (n - k)) n
  rw [sum_range_succ, Nat.sub_self, D.d_zero, LinearMap.comp_id, D.δ_succ n, h]
  abel

/-! ### Step 2: each `δ n` is a derivation -/

/-! ### The key computation, shared by both directions

If `d` and `δ` satisfy the recursion `(m+1) d (m+1) = ∑_{k ≤ m} δ (k+1) ∘ d (m-k)`, then
`∑_{i+j=n+1} (i + j) d i a * d j b` can be expanded in terms of the `δ`'s. -/

theorem sum_weighted_eq (δ d : ℕ → A →ₗ[𝕜] A)
    (hrec : ∀ m : ℕ, ((m : 𝕜) + 1) • d (m + 1) =
      ∑ k ∈ range (m + 1), δ (k + 1) ∘ₗ d (m - k))
    (n : ℕ) (a b : A) :
    ∑ p ∈ antidiagonal (n + 1),
        ((p.1 : 𝕜) • (d p.1 a * d p.2 b) + (p.2 : 𝕜) • (d p.1 a * d p.2 b)) =
      ∑ k ∈ range (n + 1), ∑ q ∈ antidiagonal (n - k),
        (δ (k + 1) (d q.1 a) * d q.2 b + d q.1 a * δ (k + 1) (d q.2 b)) := by
  have H1 : ∑ p ∈ antidiagonal n, ((p.1 + 1 : ℕ) : 𝕜) • (d (p.1 + 1) a * d p.2 b) =
      ∑ k ∈ range (n + 1), ∑ q ∈ antidiagonal (n - k), δ (k + 1) (d q.1 a) * d q.2 b := by
    rw [← sum_antidiagonal_range_fst n (fun k l j => δ (k + 1) (d l a) * d j b)]
    refine sum_congr rfl fun p _ => ?_
    rw [← smul_mul_assoc, ← sum_mul]
    congr 1
    push_cast
    rw [← LinearMap.smul_apply, hrec p.1, LinearMap.sum_apply]
    rfl
  have H2 : ∑ p ∈ antidiagonal n, ((p.2 + 1 : ℕ) : 𝕜) • (d p.1 a * d (p.2 + 1) b) =
      ∑ k ∈ range (n + 1), ∑ q ∈ antidiagonal (n - k), d q.1 a * δ (k + 1) (d q.2 b) := by
    rw [← sum_antidiagonal_range_snd n (fun k i l => d i a * δ (k + 1) (d l b))]
    refine sum_congr rfl fun p _ => ?_
    rw [← mul_smul_comm, ← mul_sum]
    congr 1
    push_cast
    rw [← LinearMap.smul_apply, hrec p.2, LinearMap.sum_apply]
    rfl
  rw [sum_add_distrib, Nat.sum_antidiagonal_succ, Nat.sum_antidiagonal_succ', H1, H2]
  simp only [Nat.cast_zero, zero_smul, zero_add, ← sum_add_distrib]

/-- On `antidiagonal (n+1)` the weight `i + j` is just `n + 1`. -/
theorem sum_weighted_eq_smul (d : ℕ → A →ₗ[𝕜] A) (n : ℕ) (a b : A) :
    ∑ p ∈ antidiagonal (n + 1),
        ((p.1 : 𝕜) • (d p.1 a * d p.2 b) + (p.2 : 𝕜) • (d p.1 a * d p.2 b)) =
      ((n : 𝕜) + 1) • ∑ p ∈ antidiagonal (n + 1), d p.1 a * d p.2 b := by
  rw [smul_sum]
  refine sum_congr rfl fun p hp => ?_
  rw [← add_smul]
  have h := congrArg (Nat.cast : ℕ → 𝕜) (mem_antidiagonal.mp hp)
  push_cast at h
  rw [h]

/-! ### Step 2: each `δ n` is a derivation -/

theorem δ_succ_leibniz (D : HigherDerivation 𝕜 A) (n : ℕ) (a b : A) :
    D.δ (n + 1) (a * b) = D.δ (n + 1) a * b + a * D.δ (n + 1) b := by
  induction n using Nat.strong_induction_on generalizing a b with
  | _ n ih =>
  -- First expression for `(n+1) d (n+1) (a b)`: weight the Leibniz rule by `n + 1 = i + j`.
  have E1 : (((n : 𝕜) + 1) • D.d (n + 1)) (a * b) =
      ∑ k ∈ range (n + 1), ∑ q ∈ antidiagonal (n - k),
        (D.δ (k + 1) (D.d q.1 a) * D.d q.2 b + D.d q.1 a * D.δ (k + 1) (D.d q.2 b)) := by
    rw [LinearMap.smul_apply, D.leibniz, ← sum_weighted_eq_smul,
      sum_weighted_eq D.δ D.d D.d_succ_eq_sum]
  -- Second expression, from the recursion.
  have E2 : (((n : 𝕜) + 1) • D.d (n + 1)) (a * b) =
      ∑ k ∈ range (n + 1), D.δ (k + 1) (∑ q ∈ antidiagonal (n - k), D.d q.1 a * D.d q.2 b) := by
    rw [D.d_succ_eq_sum n, LinearMap.sum_apply]
    refine sum_congr rfl fun k _ => ?_
    rw [LinearMap.comp_apply, D.leibniz]
  have E := E2.symm.trans E1
  -- The terms with `k < n` agree by the induction hypothesis.
  have H : ∑ k ∈ range n, D.δ (k + 1) (∑ q ∈ antidiagonal (n - k), D.d q.1 a * D.d q.2 b) =
      ∑ k ∈ range n, ∑ q ∈ antidiagonal (n - k),
        (D.δ (k + 1) (D.d q.1 a) * D.d q.2 b + D.d q.1 a * D.δ (k + 1) (D.d q.2 b)) := by
    refine sum_congr rfl fun k hk => ?_
    rw [map_sum]
    exact sum_congr rfl fun q _ => ih k (mem_range.mp hk) _ _
  rw [sum_range_succ, sum_range_succ, H, Nat.sub_self, Nat.antidiagonal_zero, sum_singleton,
    sum_singleton, D.d_zero, LinearMap.id_apply, LinearMap.id_apply] at E
  exact add_left_cancel E

theorem δ_leibniz (D : HigherDerivation 𝕜 A) :
    ∀ (n : ℕ) (a b : A), D.δ n (a * b) = D.δ n a * b + a * D.δ n b
  | 0, a, b => by
    simp only [D.δ_zero, LinearMap.zero_apply, zero_mul, mul_zero, add_zero]
  | n + 1, a, b => D.δ_succ_leibniz n a b

/-! ### The characterization -/

/-- Every higher derivation comes from a sequence of derivations `δ` via
`(n + 1) d_{n+1} = ∑_{k=0}^{n} δ_{k+1} ∘ d_{n-k}`. No assumption on the characteristic
is needed. -/
theorem exists_derivations (D : HigherDerivation 𝕜 A) :
    ∃ δ : ℕ → NCDerivation 𝕜 A, ∀ n : ℕ,
      ((n : 𝕜) + 1) • D.d (n + 1) =
        ∑ k ∈ range (n + 1), (δ (k + 1)).toLinearMap ∘ₗ D.d (n - k) :=
  ⟨fun m => ⟨D.δ m, D.δ_leibniz m⟩, D.d_succ_eq_sum⟩

/-- Conversely, any sequence `d` built from derivations `δ` by the same recursion
is a higher derivation. -/
theorem leibniz_of_recursion [CharZero 𝕜]
    (δ : ℕ → NCDerivation 𝕜 A) (d : ℕ → A →ₗ[𝕜] A)
    (h0 : d 0 = LinearMap.id)
    (hrec : ∀ n : ℕ, ((n : 𝕜) + 1) • d (n + 1) =
      ∑ k ∈ range (n + 1), (δ (k + 1)).toLinearMap ∘ₗ d (n - k)) :
    ∀ (n : ℕ) (a b : A), d n (a * b) = ∑ p ∈ antidiagonal n, d p.1 a * d p.2 b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b
  cases n with
  | zero => simp only [Nat.antidiagonal_zero, sum_singleton, h0, LinearMap.id_apply]
  | succ n =>
  -- Here we divide by `n + 1`, which is where characteristic zero is used.
  have hc : ((n : 𝕜) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  suffices h : ((n : 𝕜) + 1) • d (n + 1) (a * b) =
      ((n : 𝕜) + 1) • ∑ p ∈ antidiagonal (n + 1), d p.1 a * d p.2 b by
    have h' := congrArg (((n : 𝕜) + 1)⁻¹ • ·) h
    simpa only [inv_smul_smul₀ hc] using h'
  rw [← LinearMap.smul_apply, hrec n, LinearMap.sum_apply, ← sum_weighted_eq_smul,
    sum_weighted_eq (fun m => (δ m).toLinearMap) d hrec]
  refine sum_congr rfl fun k _ => ?_
  rw [LinearMap.comp_apply, ih (n - k) (by omega), map_sum]
  exact sum_congr rfl fun q _ => (δ (k + 1)).leibniz _ _

end HigherDerivation
