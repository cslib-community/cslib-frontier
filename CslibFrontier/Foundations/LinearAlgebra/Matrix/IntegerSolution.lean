/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, beside `Mathlib/LinearAlgebra/Matrix/Farkas.lean`)

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.IntegerKernel
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.NonnegativeForm
public import CslibFrontier.Foundations.Data.Nat.BinarySize
import CslibFrontier.Foundations.Data.Int.Radix
import Mathlib.Order.WellFounded
import Mathlib.Tactic.Positivity

/-!
# Small integer solutions of equality and inequality systems

If an integer equality system has a nonnegative integer solution, it has one of explicitly
bounded size. Split variables and slack variables give the corresponding bound for inequalities.
This is a mathematical step toward NP membership of integer programming, not the
NP-completeness statements of Arora–Barak or Goldreich.

The proof minimizes a positive radix-weighted objective over integer solutions. Columns at
large coordinates must be independent: a bounded integer dependence would permit both signs
of a feasible move, contradicting minimality and uniqueness of bounded radix expansions.
The remaining coordinates contribute a bounded right-hand side; the existing rational
basic-solution bound then bounds the independent coordinates as well. This gives an original,
loose explicit bound with polynomial binary length, rather than the sharper classical constants.

## Main results

* `Matrix.exists_nonneg_int_mulVec_eq_le`: bounded integer solutions of `Ax = b`, `x ≥ 0`.
* `Matrix.exists_int_mulVec_le_abs_le`: bounded integer solutions of `Ax ≤ b`.
* `Matrix.size_nonnegIntSolutionBound_le`: the bound has polynomial binary length.
-/

public section

open Finset

namespace Matrix

private lemma exists_nonneg_int_solution_independent_large {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℤ} {b : Fin m → ℤ} {B : ℕ}
    (hA : ∀ i j, |A i j| ≤ B) {x₀ : Fin n → ℤ} (hx₀ : 0 ≤ x₀) (hAx₀ : A *ᵥ x₀ = b) :
    ∃ x : Fin n → ℤ, 0 ≤ x ∧ A *ᵥ x = b ∧
      Function.Injective
        ((A.submatrix id (fun j : {j //
          (n.factorial * (m * ((n + 1) * B) ^ 2 + 1) ^ n : ℕ) ≤ x j} => j.val)).map
          (Int.cast : ℤ → ℚ)).mulVecLin := by
  classical
  let K := n.factorial * (m * ((n + 1) * B) ^ 2 + 1) ^ n
  let cost (x : Fin n → ℤ) : ℤ := ∑ j, x j * (K + 1 : ℤ) ^ j.val
  let S : Set (Fin n → ℤ) := {x | 0 ≤ x ∧ A *ᵥ x = b}
  have hS : S.Nonempty := ⟨x₀, hx₀, hAx₀⟩
  let x := Function.argminOn (fun x => (cost x).toNat) S hS
  have hxS : x ∈ S := Function.argminOn_mem _ S hS
  obtain ⟨hx, hAx⟩ := hxS
  have hcost : ∀ y : Fin n → ℤ, 0 ≤ y → 0 ≤ cost y := fun y hy =>
    Finset.sum_nonneg fun j _ => mul_nonneg (hy j) (by positivity)
  have hmin : ∀ y, 0 ≤ y → A *ᵥ y = b → cost x ≤ cost y := fun y hy hAy => by
    have h : (cost x).toNat ≤ (cost y).toNat :=
      Function.argminOn_le (fun x => (cost x).toNat) S ⟨hy, hAy⟩
    have := hcost x hx
    have := hcost y hy
    omega
  refine ⟨x, hx, hAx, ?_⟩
  by_contra hinj
  let J := {j : Fin n // (K : ℤ) ≤ x j}
  let AJ : Matrix (Fin m) J ℤ := A.submatrix id Subtype.val
  obtain ⟨cJ, hcJ, hAcJ, hcJB⟩ := exists_int_mulVec_eq_zero_of_not_injective AJ
    (fun i j => hA i j.val) (r := n) (by
      calc Fintype.card J ≤ Fintype.card (Fin n) := Fintype.card_subtype_le _
        _ ≤ n + 1 := by simp) hinj
  let c : Fin n → ℤ := fun j => if hj : (K : ℤ) ≤ x j then cJ ⟨j, hj⟩ else 0
  have hcB (j : Fin n) : |c j| ≤ x j ∧ |c j| ≤ K := by
    by_cases hj : (K : ℤ) ≤ x j
    · have h : |cJ ⟨j, hj⟩| ≤ K := by simpa only [Fintype.card_fin] using hcJB ⟨j, hj⟩
      simpa only [c, dite_eq_left hj] using ⟨h.trans hj, h⟩
    · simpa [c, hj] using hx j
  have hAc : A *ᵥ c = 0 := by
    ext i
    change ∑ j, A i j * c j = 0
    rw [← Fintype.sum_subtype_add_sum_subtype (fun j => (K : ℤ) ≤ x j)]
    have hzero : ∑ j : {j : Fin n // ¬(K : ℤ) ≤ x j}, A i j.val * c j.val = 0 :=
      Finset.sum_eq_zero fun j _ => by simp [c, j.property]
    rw [hzero, add_zero]
    have heq : ∀ j : J, c j.val = cJ j := fun j => by simp [c, j.property]
    simpa only [AJ, mulVec, dotProduct, submatrix_apply, id_eq, heq, Pi.zero_apply]
      using congrFun hAcJ i
  have hplus : 0 ≤ x + c := fun j => by
    change 0 ≤ x j + c j
    linarith [(abs_le.mp (hcB j).1).1]
  have hminus : 0 ≤ x - c := fun j => sub_nonneg.mpr (le_abs_self _ |>.trans (hcB j).1)
  have h1 := hmin (x + c) hplus (by rw [mulVec_add, hAx, hAc, add_zero])
  have h2 := hmin (x - c) hminus (by rw [mulVec_sub, hAx, hAc, sub_zero])
  have hcost_add : cost (x + c) = cost x + cost c := by
    simp [cost, add_mul, Finset.sum_add_distrib]
  have hcost_sub : cost (x - c) = cost x - cost c := by
    simp [cost, sub_mul, Finset.sum_sub_distrib]
  have hc0 : cost c = 0 := by linarith
  have hc_eq : c = 0 := by
    let a : ℕ → ℤ := fun j => if hj : j < n then c ⟨j, hj⟩ else 0
    have hsum : ∑ j ∈ Finset.range n, a j * (K + 1 : ℤ) ^ j = 0 := by
      rw [← Fin.sum_univ_eq_sum_range]
      simpa [a, cost] using hc0
    have h := Int.eq_zero_of_sum_mul_pow_eq_zero (a := a)
      (fun j hj => by simpa [a, hj] using Int.lt_add_one_iff.mpr (hcB ⟨j, hj⟩).2) hsum
    funext j
    simpa [a, j.isLt] using h j j.isLt
  exact hcJ (funext fun j => by simpa [c, j.property] using congrFun hc_eq j.val)

/-- An explicit bound for nonnegative integer solutions of an `m × n` integer equality system
with coefficients and right-hand side bounded by `B`. Its logarithm is polynomial in
`m`, `n` and `log₂ B`. -/
@[expose] def nonnegIntSolutionBound (m n B : ℕ) : ℕ :=
  let K := n.factorial * (m * ((n + 1) * B) ^ 2 + 1) ^ n
  let C := B + n * B * K
  max K (n.factorial * (m * C ^ 2 + 1) ^ n)

/-- **Small nonnegative integer solutions.** This is a step toward integer programming in NP,
not the NP-completeness theorem: every integer-feasible `Ax = b`, `x ≥ 0` has an integer
solution bounded by `nonnegIntSolutionBound`. Unlike `exists_int_nonneg_mulVec_eq`, there is
no denominator and the right-hand side is unchanged. -/
private theorem exists_nonneg_int_mulVec_eq_le_fin {m n B : ℕ}
    {A : Matrix (Fin m) (Fin n) ℤ} {b : Fin m → ℤ}
    (hA : ∀ i j, |A i j| ≤ B) (hb : ∀ i, |b i| ≤ B)
    {x₀ : Fin n → ℤ} (hx₀ : 0 ≤ x₀) (hAx₀ : A *ᵥ x₀ = b) :
    ∃ x : Fin n → ℤ, 0 ≤ x ∧ A *ᵥ x = b ∧
      ∀ j, x j ≤ (nonnegIntSolutionBound m n B : ℕ) := by
  classical
  let K := n.factorial * (m * ((n + 1) * B) ^ 2 + 1) ^ n
  let C := B + n * B * K
  obtain ⟨x, hx, hAx, hinj⟩ := exists_nonneg_int_solution_independent_large hA hx₀ hAx₀
  let J := {j : Fin n // (K : ℤ) ≤ x j}
  let AJ : Matrix (Fin m) J ℤ := A.submatrix id Subtype.val
  let z : Fin n → ℤ := fun j => if (K : ℤ) ≤ x j then 0 else x j
  let b' : Fin m → ℤ := b - A *ᵥ z
  have hz (j : Fin n) : |z j| ≤ K := by
    by_cases hj : (K : ℤ) ≤ x j
    · simp [z, hj]
    · simpa [z, hj, abs_of_nonneg (hx j)] using (not_le.1 hj).le
  have hb' : ∀ i, |b' i| ≤ C := by
    intro i
    calc |b' i| ≤ |b i| + |(A *ᵥ z) i| := abs_sub _ _
      _ ≤ B + ∑ _j : Fin n, (B : ℤ) * K := by
        apply add_le_add (hb i)
        change |∑ j, A i j * z j| ≤ _
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => by
          rw [abs_mul]
          exact mul_le_mul (hA i j) (hz j) (abs_nonneg _) (by positivity))
      _ = (C : ℤ) := by simp [C]; ring
  have hAC : ∀ i j, |AJ i j| ≤ C := fun i j =>
    (hA i j.val).trans (Int.ofNat_le.mpr (Nat.le_add_right B _))
  have hAJx : AJ *ᵥ (fun j : J => x j.val) = b' := by
    ext i
    have h := Fintype.sum_subtype_add_sum_subtype (fun j : Fin n => (K : ℤ) ≤ x j)
      (fun j => A i j * (x j - z j))
    have hJ (j : J) : x j.val - z j.val = x j.val := by simp [z, j.property]
    have hJc (j : {j : Fin n // ¬(K : ℤ) ≤ x j}) : x j.val - z j.val = 0 := by simp [z, j.property]
    simp only [hJ, hJc, mul_zero, sum_const_zero, add_zero, mul_sub, sum_sub_distrib] at h
    simpa only [AJ, b', mulVec, dotProduct, ← hAx, Pi.sub_apply, submatrix_apply, id_eq] using h
  have hAJxQ : AJ.map (Int.cast : ℤ → ℚ) *ᵥ (fun j : J => (x j.val : ℚ)) =
      fun i => (b' i : ℚ) := funext fun i =>
    ((Int.castRingHom ℚ).map_mulVec AJ (fun j : J => x j.val) i).symm.trans
      (congrArg (Int.castRingHom ℚ) (congrFun hAJx i))
  obtain ⟨d, p, hd, hp, hAp, _, hpB⟩ := exists_int_nonneg_mulVec_eq hAC hb'
    (show (0 : J → ℚ) ≤ fun j => (x j.val : ℚ) from fun j => Int.cast_nonneg (hx j.val)) hAJxQ
  have hpx : p = d • (fun j : J => x j.val) := by
    have hEq : (fun j => (p j : ℚ)) = (fun j : J => ((d * x j.val : ℤ) : ℚ)) := by
      apply hinj
      change AJ.map (Int.cast : ℤ → ℚ) *ᵥ _ = AJ.map (Int.cast : ℤ → ℚ) *ᵥ _
      have hcast := (Int.castRingHom ℚ).map_mulVec AJ p
      have hcast' := (Int.castRingHom ℚ).map_mulVec AJ (d • (fun j : J => x j.val))
      rw [mulVec_smul, hAJx] at hcast'
      ext i
      exact (hcast i).symm.trans (by rw [hAp]; exact hcast' i)
    ext j
    exact_mod_cast congrFun hEq j
  have hcard : Fintype.card J ≤ n := (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin n)
  have hbound : (Fintype.card J).factorial * (m * C ^ 2 + 1) ^ Fintype.card J ≤
      n.factorial * (m * C ^ 2 + 1) ^ n :=
    Nat.mul_le_mul (Nat.factorial_le hcard) (Nat.pow_le_pow_right (by omega) hcard)
  refine ⟨x, hx, hAx, fun j => ?_⟩
  by_cases hj : (K : ℤ) ≤ x j
  · have h := hpB ⟨j, hj⟩
    simp only [hpx, Pi.smul_apply, smul_eq_mul, Fintype.card_fin] at h
    have hdx : x j ≤ d * x j := by nlinarith [hx j]
    exact (hdx.trans h |>.trans (Int.ofNat_le.mpr hbound)).trans
      (Int.ofNat_le.mpr (le_max_right _ _))
  · exact (le_of_lt (lt_of_not_ge hj)).trans (Int.ofNat_le.mpr (le_max_left _ _))

/-- **Small nonnegative integer solutions**, with arbitrary finite row and column types.
This is the equality-form small-solution step toward integer programming in NP, not a
complexity-class membership assertion. The solution is integral and has the original right-hand
side, with no scaling factor. -/
theorem exists_nonneg_int_mulVec_eq_le {m n : Type*} [Fintype m] [Fintype n]
    {A : Matrix m n ℤ} {b : m → ℤ} {B : ℕ}
    (hA : ∀ i j, |A i j| ≤ B) (hb : ∀ i, |b i| ≤ B)
    {x₀ : n → ℤ} (hx₀ : 0 ≤ x₀) (hAx₀ : A *ᵥ x₀ = b) :
    ∃ x : n → ℤ, 0 ≤ x ∧ A *ᵥ x = b ∧
      ∀ j, x j ≤ (nonnegIntSolutionBound (Fintype.card m) (Fintype.card n) B : ℕ) := by
  classical
  let e := (Fintype.equivFin m).symm
  let f := (Fintype.equivFin n).symm
  have hAx : A.submatrix e f *ᵥ (x₀ ∘ f) = b ∘ e := by
    ext i
    change (∑ j, A (e i) (f j) * x₀ (f j)) = b (e i)
    rw [f.sum_comp (fun j => A (e i) j * x₀ j)]
    exact congrFun hAx₀ (e i)
  obtain ⟨x, hx, hAx, hB⟩ := exists_nonneg_int_mulVec_eq_le_fin
    (fun i j => hA (e i) (f j)) (fun i => hb (e i)) (fun j => hx₀ (f j)) hAx
  refine ⟨x ∘ f.symm, fun j => hx (f.symm j), ?_, fun j => hB (f.symm j)⟩
  ext i
  have h := congrFun hAx (e.symm i)
  simp only [mulVec, dotProduct, Equiv.apply_symm_apply] at h
  change (∑ j, A i j * x (f.symm j)) = b i
  rw [← f.sum_comp]
  simpa only [Equiv.symm_apply_apply] using h

/-- Polynomial upper bound for the binary length of `nonnegIntSolutionBound m n B`, where
`L = B.size`. Set `k = n² + 2 + n(m + 2(n + L + 1) + 3)`; the bound is
`k + n² + 2 + n(m + 2(2L + n + k + 1) + 3)`. -/
@[expose] def nonnegIntSolutionBits (m n L : ℕ) : ℕ :=
  let k := n * n + 2 + n * (m + 2 * (n + L + 1) + 3)
  k + n * n + 2 + n * (m + 2 * (2 * L + n + k + 1) + 3)

/-- The equality-form integer small-solution bound has polynomial binary length, including
zero rows, zero columns and zero coefficient bound. -/
theorem size_nonnegIntSolutionBound_le (m n B : ℕ) :
    (nonnegIntSolutionBound m n B).size ≤ nonnegIntSolutionBits m n B.size := by
  let K := n.factorial * (m * ((n + 1) * B) ^ 2 + 1) ^ n
  let k := n * n + 2 + n * (m + 2 * (n + B.size + 1) + 3)
  have hm := Nat.size_le_self m
  have hn := Nat.size_le_self n
  have hn1 := Nat.size_le_self (n + 1)
  have hfac := Nat.size_factorial_le n
  have hKB : K.size ≤ k := by
    have h1 := Nat.size_mul_le (n + 1) B
    have h2 := Nat.size_pow_le ((n + 1) * B) 2
    have h3 := Nat.size_mul_le m (((n + 1) * B) ^ 2)
    have h4 := Nat.size_add_le (m * ((n + 1) * B) ^ 2) 1
    have h5 := Nat.size_pow_le (m * ((n + 1) * B) ^ 2 + 1) n
    have h6 := Nat.size_mul_le n.factorial ((m * ((n + 1) * B) ^ 2 + 1) ^ n)
    dsimp only [k]
    norm_num only [Nat.size_one] at h4
    nlinarith
  let C := B + n * B * K
  have hC : C.size ≤ 2 * B.size + n + k + 1 := by
    have h1 := Nat.size_mul_le n B
    have h2 := Nat.size_mul_le (n * B) K
    have h3 := Nat.size_add_le B (n * B * K)
    dsimp only [C]
    omega
  have hD : (n.factorial * (m * C ^ 2 + 1) ^ n).size ≤
      n * n + 2 + n * (m + 2 * (2 * B.size + n + k + 1) + 3) := by
    have h1 := Nat.size_pow_le C 2
    have h2 := Nat.size_mul_le m (C ^ 2)
    have h3 := Nat.size_add_le (m * C ^ 2) 1
    have h4 := Nat.size_pow_le (m * C ^ 2 + 1) n
    have h5 := Nat.size_mul_le n.factorial ((m * C ^ 2 + 1) ^ n)
    norm_num only [Nat.size_one] at h3
    nlinarith
  change (max K (n.factorial * (m * C ^ 2 + 1) ^ n)).size ≤
    k + n * n + 2 + n * (m + 2 * (2 * B.size + n + k + 1) + 3)
  rw [Monotone.map_max fun _ _ => Nat.size_le_size]
  omega

/-- **Small integer solutions of inequalities.** This is the integer small-solution step toward
NP membership, not an NP membership assertion. A feasible integer system has a solution whose
absolute coordinates are bounded by the nonnegative equality bound after splitting variables
and introducing slacks. -/
theorem exists_int_mulVec_le_abs_le {m n : Type*} [Fintype m] [Fintype n]
    {A : Matrix m n ℤ} {b : m → ℤ} {B : ℕ}
    (hA : ∀ i j, |A i j| ≤ B) (hb : ∀ i, |b i| ≤ B)
    {x₀ : n → ℤ} (hx₀ : A *ᵥ x₀ ≤ b) :
    ∃ x : n → ℤ, A *ᵥ x ≤ b ∧ ∀ j, |x j| ≤
      (nonnegIntSolutionBound (Fintype.card m)
        (2 * Fintype.card n + Fintype.card m) (B + 1) : ℕ) := by
  classical
  have hM := abs_nonnegForm_le hA
  obtain ⟨z, hz, hMz⟩ := nonnegForm_solution hx₀
  obtain ⟨p, hp, hMp, hpB⟩ := exists_nonneg_int_mulVec_eq_le hM
    (fun i => (hb i).trans (by simp)) hz hMz
  have hcard : Fintype.card (n ⊕ n ⊕ m) = 2 * Fintype.card n + Fintype.card m := by
    simp only [Fintype.card_sum]
    omega
  rw [hcard] at hpB
  refine ⟨fun j => p (.inl j) - p (.inr (.inl j)), ?_, fun j => ?_⟩
  · rw [nonnegForm_mulVec] at hMp
    intro i
    have h := congrFun hMp i
    have hslack := hp (.inr (.inr i))
    simp only [Pi.add_apply, Pi.zero_apply] at h hslack
    linarith
  · exact abs_sub_le_of_nonneg_of_le (hp _) (hpB _) (hp _) (hpB _)

end Matrix
