/-
Copyright (c) 2026 Samuel Schlesinger, Shengye Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Shengye Tao
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.MvPolynomial.ConsecutiveLayers
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset

/-!
# A low-rank matrix agreeing with Walsh signs on an overlap band

Index a Boolean vector by its support. Each degree-j squarefree monomial separates
into a row indicator and a column indicator. This gives the finite rank application
of interpolation on consecutive Hamming layers.

## Main results

* `Cslib.exists_low_rank_eq_walsh_on_band` constructs a matrix over any field, expresses it as
  a product through small supports, and bounds its rank by the number of such supports.

## References

* [Alman and Williams, *Probabilistic Rank and Matrix Rigidity*, Lemmas 3.1–3.2][AlmanWilliams2017]
-/

public section

namespace Cslib

open Finset

/-- The j-subsets contributing a given coefficient are precisely the j-subsets of z. -/
private theorem sum_subset_coeff {K : Type*} [Field K] {n : ℕ}
    (z : Finset (Fin n)) (j : ℕ) (c : K) :
    (∑ s : {s : Finset (Fin n) // s.card = j}, if s.val ⊆ z then c else 0) =
      c * (z.card.choose j : K) := by
  rw [← sum_subtype (univ.powersetCard j) (fun _ => mem_powersetCard_univ)
    (fun s => if s ⊆ z then c else 0), ← Finset.sum_filter]
  have h : ((univ : Finset (Fin n)).powersetCard j).filter (· ⊆ z) = z.powersetCard j := by
    ext s; simp [and_comm]
  simp [h, nsmul_eq_mul, mul_comm]

/-- Finite interpolation step toward [Alman and Williams, Lemma 3.1][AlmanWilliams2017].
Over every field, the Walsh–Hadamard signs on `t` consecutive overlap sizes agree with
a matrix of rank at most the number of squarefree monomials of degree below `t`. -/
theorem exists_low_rank_eq_walsh_on_band (K : Type*) [Field K] (n k t : ℕ) :
    ∃ A : Matrix (Finset (Fin n)) (Finset (Fin n)) K,
      A.rank ≤ ∑ j : Fin t, n.choose j ∧ ∀ x y, k ≤ (x ∩ y).card →
        (x ∩ y).card < k + t → A x y = (-1 : K) ^ (x ∩ y).card := by
  classical
  obtain ⟨a, ha⟩ := exists_choose_interpolant k t (fun w => (-1 : ℤ) ^ w)
  let I := (j : Fin t) × {s : Finset (Fin n) // s.card = j.val}
  let L : Matrix (Finset (Fin n)) I K := fun x ⟨j, s⟩ => if s.val ⊆ x then (a j : K) else 0
  let R : Matrix I (Finset (Fin n)) K := fun ⟨_, s⟩ y => if s.val ⊆ y then 1 else 0
  refine ⟨L * R, ?_, ?_⟩
  · apply (Matrix.rank_mul_le_left L R).trans
    apply L.rank_le_card_width.trans
    simp [I, Fintype.card_sigma]
  · intro x y lo hi
    rw [Matrix.mul_apply, Fintype.sum_sigma]
    have product (j : Fin t) (s : {s : Finset (Fin n) // s.card = j.val}) :
        L x ⟨j, s⟩ * R ⟨j, s⟩ y = if s.val ⊆ x ∩ y then (a j : K) else 0 := by
      by_cases hx : s.val ⊆ x <;> by_cases hy : s.val ⊆ y <;>
        simp [L, R, hx, hy, subset_inter_iff]
    simp_rw [product, sum_subset_coeff]
    exact_mod_cast congrArg (Int.cast : ℤ → K) (ha (x ∩ y).card lo hi)

end Cslib
