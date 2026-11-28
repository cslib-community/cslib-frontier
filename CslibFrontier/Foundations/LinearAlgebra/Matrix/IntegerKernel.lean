/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/LinearAlgebra/Matrix/IntegerKernel.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.BasicSolution
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bounded integer kernel vectors

An integer matrix `A : Matrix m n ℤ` with fewer rows than columns (`card m < card n`) admits a
nonzero integer kernel vector whose entries satisfy an explicit Siegel-style determinant bound
inherited from `Matrix.exists_int_nonneg_mulVec_eq`. Rationally dependent tall matrices also
have bounded integer kernel vectors, with a separate parameter bounding the column count.

## Main results

* `Matrix.exists_int_mulVec_eq_zero_of_not_injective`: bounded integer dependencies for any shape.
* `Matrix.exists_int_mulVec_eq_zero_of_card_lt`: existence of a bounded nonzero integer solution to
  `A *ᵥ c = 0` whenever `Fintype.card m < Fintype.card n`.
-/

public section

namespace Matrix

/-- Explicit entry bound on a nonzero integer kernel vector for an integer matrix with `r` rows
and entry bound `B`. -/
@[expose] def kernelVecBound (r B : ℕ) : ℕ :=
  r.factorial * (r * ((r + 1) * B) ^ 2 + 1) ^ r

private lemma sum_ne_eq_sum_erase {n α : Type*} [Fintype n] [DecidableEq n] [AddCommMonoid α]
    (j₀ : n) (f : n → α) :
    ∑ j : { j : n // j ≠ j₀ }, f j.val = ∑ j ∈ Finset.univ.erase j₀, f j :=
  (Finset.sum_subtype _ (fun _ => by simp) f).symm

/-- A rationally dependent family of integer columns has a bounded nonzero integer kernel
vector. The parameter `r` bounds the number of columns minus one, independently of the number
of rows; this also applies to dependent tall matrices. -/
theorem exists_int_mulVec_eq_zero_of_not_injective {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℤ) {B r : ℕ} (hA : ∀ i j, |A i j| ≤ B)
    (hcard : Fintype.card n ≤ r + 1)
    (hnot_inj : ¬ Function.Injective (A.map (Int.cast : ℤ → ℚ)).mulVecLin) :
    ∃ c : n → ℤ, c ≠ 0 ∧ A *ᵥ c = 0 ∧
      ∀ j, |c j| ≤ (r.factorial * (Fintype.card m * ((r + 1) * B) ^ 2 + 1) ^ r : ℕ) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot'] at hnot_inj
  push Not at hnot_inj
  obtain ⟨v, hv_eq, hv0⟩ := hnot_inj
  obtain ⟨j, -⟩ := Function.ne_iff.1 hv0
  have : Nonempty n := ⟨j⟩
  obtain ⟨j₀, hj₀⟩ := Finite.exists_max fun j => |v j|
  have hvj₀ : v j₀ ≠ 0 := fun h => hv0 (funext fun j => by simpa [h] using hj₀ j)
  let w : n → ℚ := (v j₀)⁻¹ • v
  have hw_mul : (A.map (Int.cast : ℤ → ℚ)) *ᵥ w = 0 := by
    change (A.map (Int.cast : ℤ → ℚ)).mulVec ((v j₀)⁻¹ • v) = 0
    rw [Matrix.mulVec_smul, show (A.map (Int.cast : ℤ → ℚ)) *ᵥ v = 0 from hv_eq, smul_zero]
  have hw_j₀ : w j₀ = 1 := by simp [w, hvj₀]
  have hw_abs : ∀ j, |w j| ≤ 1 := fun j => by
    rw [show w j = (v j₀)⁻¹ * v j by rfl, abs_mul, abs_inv, inv_mul_le_iff₀ (abs_pos.2 hvj₀),
      mul_one]
    exact hj₀ j
  let n' := { j : n // j ≠ j₀ }
  let A' : Matrix m n' ℤ := fun i j => A i j.val
  let b' : m → ℤ := fun i => -A i j₀ + ∑ j : n', A i j.val
  let x' : n' → ℚ := fun j => w j.val + 1
  have hx'_nonneg : 0 ≤ x' := fun j =>
    show (0 : ℚ) ≤ w j.val + 1 by linarith [(abs_le.1 (hw_abs j.val)).1]
  have hAx' : (A'.map Int.cast) *ᵥ x' = fun i => (b' i : ℚ) := by
    ext i
    have hrow : ∑ j : n, ((A i j : ℤ) : ℚ) * w j = 0 := congrFun hw_mul i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀), hw_j₀, ← sum_ne_eq_sum_erase] at hrow
    change ∑ j : n', ((A i j.val : ℤ) : ℚ) * (w j.val + 1) =
      ((-A i j₀ + ∑ j : n', A i j.val : ℤ) : ℚ)
    simp only [Int.cast_add, Int.cast_neg, Int.cast_sum, mul_add, mul_one, Finset.sum_add_distrib]
    linarith
  let B' : ℕ := (r + 1) * B
  have hn' : Fintype.card n' ≤ r := by
    rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ]
    omega
  have hA'_bd : ∀ i (j : n'), |A' i j| ≤ B' := fun i j =>
    (hA i j.val).trans (by exact_mod_cast Nat.le_mul_of_pos_left B (Nat.succ_pos _))
  have hb'_bd : ∀ i, |b' i| ≤ B' := fun i => by
    have hsum_bd : |∑ j : n', A i j.val| ≤ Fintype.card n' * B :=
      ((Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun (j : n') _ => hA i j.val)).trans_eq (by simp)
    have : (Fintype.card n' : ℤ) ≤ r := by exact_mod_cast hn'
    calc |b' i| ≤ |-A i j₀| + |∑ j : n', A i j.val| := abs_add_le _ _
      _ ≤ B + Fintype.card n' * B := add_le_add (by simpa [abs_neg] using hA i j₀) hsum_bd
      _ ≤ (B' : ℤ) := by dsimp only [B']; push_cast; nlinarith [Int.natCast_nonneg B]
  obtain ⟨d, p', hd_pos, hp'_nonneg, hAp', hd_le, hp'_le⟩ :=
    Matrix.exists_int_nonneg_mulVec_eq hA'_bd hb'_bd hx'_nonneg hAx'
  have hbound : (Fintype.card n').factorial *
      (Fintype.card m * B' ^ 2 + 1) ^ Fintype.card n' ≤
      r.factorial * (Fintype.card m * B' ^ 2 + 1) ^ r :=
    Nat.mul_le_mul (Nat.factorial_le hn')
      (Nat.pow_le_pow_right (by omega) hn')
  have hd_bound := hd_le.trans (Int.ofNat_le.mpr hbound)
  have hp_bound := fun j => (hp'_le j).trans (Int.ofNat_le.mpr hbound)
  let c : n → ℤ := fun j => if h : j = j₀ then d else p' ⟨j, h⟩ - d
  refine ⟨c, ?_, ?_, ?_⟩
  · intro hc0
    have h0 := congrFun hc0 j₀
    simp only [c, dite_eq_left rfl, Pi.zero_apply] at h0
    omega
  · ext i
    have hAp_i : ∑ j : n', A' i j * p' j = d * b' i := congrFun hAp' i
    change ∑ j : n, A i j * c j = 0
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀), ← sum_ne_eq_sum_erase,
      show c j₀ = d from dite_eq_left rfl,
      Finset.sum_congr rfl fun (j : n') _ => show A i j * c j = A' i j * p' j - d * A i j by
        simp only [c, dite_eq_right j.property, A']; ring,
      Finset.sum_sub_distrib, hAp_i, ← Finset.mul_sum]
    simp only [b']
    ring
  · intro j
    by_cases hj : j = j₀
    · subst hj
      simpa only [c, dite_eq_left rfl, abs_of_pos hd_pos] using hd_bound
    · have : 0 ≤ p' ⟨j, hj⟩ := hp'_nonneg ⟨j, hj⟩
      have := hp_bound ⟨j, hj⟩
      simp only [c, dite_eq_right hj, abs_le]
      constructor <;> linarith

private lemma exists_int_mulVec_eq_zero_of_succ {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℤ) {B : ℕ} (hA : ∀ i j, |A i j| ≤ B)
    (hcard : Fintype.card n = Fintype.card m + 1) :
    ∃ c : n → ℤ, c ≠ 0 ∧ A *ᵥ c = 0 ∧ ∀ j, |c j| ≤ kernelVecBound (Fintype.card m) B := by
  apply exists_int_mulVec_eq_zero_of_not_injective A hA hcard.le
  intro hinj
  have hrank := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at hrank
  omega

/-- An integer matrix `A : Matrix m n ℤ` with `Fintype.card m < Fintype.card n` and entry bound `B`
admits a nonzero integer kernel vector bounded in magnitude by `kernelVecBound (card m) B`. -/
theorem exists_int_mulVec_eq_zero_of_card_lt {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℤ) {B : ℕ} (hA : ∀ i j, |A i j| ≤ B)
    (hcard : Fintype.card m < Fintype.card n) :
    ∃ c : n → ℤ, c ≠ 0 ∧ A *ᵥ c = 0 ∧ ∀ j, |c j| ≤ kernelVecBound (Fintype.card m) B := by
  classical
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset n)) hcard
  have hS_card : Fintype.card S = Fintype.card m + 1 := by simp [Fintype.card_coe, hS]
  let AS : Matrix m S ℤ := A.submatrix id Subtype.val
  obtain ⟨cS, hcS0, hAS, hcS_bd⟩ := exists_int_mulVec_eq_zero_of_succ AS
    (fun i j => hA i j.val) hS_card
  let c : n → ℤ := fun j => if hj : j ∈ S then cS ⟨j, hj⟩ else 0
  refine ⟨c, ?_, ?_, ?_⟩
  · exact fun hc0 => hcS0 (funext fun j => by simpa [c, j.property] using congrFun hc0 j.val)
  · ext i
    change ∑ j : n, A i j * c j = 0
    rw [← Finset.sum_subset (Finset.subset_univ S) fun j _ hj => by simp [c, hj],
      ← Finset.sum_coe_sort S (fun j => A i j * c j)]
    simpa [c, AS, mulVec, dotProduct] using congrFun hAS i
  · intro j
    by_cases hj : j ∈ S
    · simpa [c, hj] using hcS_bd ⟨j, hj⟩
    · simp [c, hj]

end Matrix
