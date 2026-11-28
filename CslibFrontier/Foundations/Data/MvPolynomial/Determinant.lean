/-
Copyright (c) 2026 Samuel Schlesinger, lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Algebra/MvPolynomial/Determinant`)

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring

/-!
# Determinants of multivariate polynomials

A determinant with entries of total degree at most `d` has total degree at most the matrix
size times `d` (`totalDegree_det_le`). Perturbing each entry only below degree `d` preserves
all coefficients at or above that maximal determinant degree
(`coeff_det_eq_of_totalDegree_sub_lt`), over every commutative coefficient ring.

The coefficient stability argument is adapted from
[lean-canny](https://github.com/edemaine/lean-canny/blob/970f28a5ecefc1327402ade16c068aa4b1b2c183/LeanCanny/CountingHierarchy/DeterminantTopDegree.lean).
-/

public section

namespace MvPolynomial

open Finset Fintype
open scoped BigOperators

/-- A determinant of polynomials of total degree at most `d` has total degree at most
`|ι| * d`. -/
theorem totalDegree_det_le {R σ ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (MvPolynomial σ R)) (d : ℕ) (hA : ∀ i j, (A i j).totalDegree ≤ d) :
    A.det.totalDegree ≤ card ι * d := by
  rw [Matrix.det_apply]
  refine totalDegree_finsetSum_le fun σ _ => (totalDegree_smul_le _ _).trans ?_
  calc (∏ i : ι, A (σ i) i).totalDegree
      ≤ ∑ i : ι, (A (σ i) i).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ _i : ι, d := sum_le_sum fun _ _ => hA _ _
    _ = card ι * d := by simp

variable {A σ κ : Type*} [CommRing A]

/-- Perturbing each factor below degree `d` changes a nonempty product
 only below its maximal possible degree. -/
private theorem product_difference_degree_lt (s : Finset κ) (hs : s.Nonempty)
    (f g : κ → MvPolynomial σ A) (d : ℕ)
    (hf : ∀ i ∈ s, (f i).totalDegree ≤ d)
    (hg : ∀ i ∈ s, (g i).totalDegree ≤ d)
    (hd : ∀ i ∈ s, (f i - g i).totalDegree < d) :
    ((∏ i ∈ s, f i) - ∏ i ∈ s, g i).totalDegree < s.card * d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a s ha ih =>
    have hda := hd a (Finset.mem_insert_self _ _)
    by_cases hs0 : s = ∅
    · subst s
      simpa using hda
    · have hf' : ∀ i ∈ s, (f i).totalDegree ≤ d := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hsub := ih (Finset.ne_empty_iff_nonempty.mp hs0) hf'
        (fun i hi => hg i (Finset.mem_insert_of_mem hi))
        fun i hi => hd i (Finset.mem_insert_of_mem hi)
      have heq : f a * (∏ i ∈ s, f i) - g a * (∏ i ∈ s, g i) =
          (f a - g a) * (∏ i ∈ s, f i) + g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) := by ring
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha,
        Nat.add_mul, one_mul, heq]
      have hp : (∏ i ∈ s, f i).totalDegree ≤ s.card * d :=
        (totalDegree_finsetProd _ _).trans ((Finset.sum_le_sum hf').trans_eq (by simp))
      have hm1 := totalDegree_mul (f a - g a) (∏ i ∈ s, f i)
      have hm2 := totalDegree_mul (g a) ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)
      have hga := hg a (Finset.mem_insert_self _ _)
      exact (totalDegree_add _ _).trans_lt (max_lt_iff.mpr ⟨by omega, by omega⟩)

/-- Lower-degree changes to matrix entries preserve all coefficients at
 the maximal determinant degree. -/
theorem coeff_det_eq_of_totalDegree_sub_lt {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) (MvPolynomial σ A))
    (d : ℕ) (hM : ∀ i j, (M i j).totalDegree ≤ d)
    (hN : ∀ i j, (N i j).totalDegree ≤ d)
    (hd : ∀ i j, (M i j - N i j).totalDegree < d)
    (e : σ →₀ ℕ) (he : n * d ≤ e.degree) : M.det.coeff e = N.det.coeff e := by
  classical
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hpos : 0 < n * d := Nat.mul_pos (by omega)
      (lt_of_le_of_lt (Nat.zero_le _) (hd ⟨0, by omega⟩ ⟨0, by omega⟩))
    have hdeg : (M.det - N.det).totalDegree < n * d := by
      rw [Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
      refine (totalDegree_finsetSum_le (d := n * d - 1) fun π _ => ?_).trans_lt (by omega)
      rw [← smul_sub]
      refine (totalDegree_smul_le _ _).trans ?_
      have hb := product_difference_degree_lt Finset.univ
        ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ (fun j => M (π j) j) (fun j => N (π j) j) d
        (fun j _ => hM (π j) j) (fun j _ => hN (π j) j) (fun j _ => hd (π j) j)
      simp only [Finset.card_univ, Fintype.card_fin] at hb; omega
    simpa only [AddMonoidAlgebra.coeff_sub_apply, sub_eq_zero] using
      coeff_eq_zero_of_totalDegree_lt (hdeg.trans_le he)

end MvPolynomial
