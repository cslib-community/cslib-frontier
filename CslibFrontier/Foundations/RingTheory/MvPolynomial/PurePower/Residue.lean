/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate (Mathlib, pure-power polynomial quotients)

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Fintype.Pi
import Lean.Elab.Tactic.Omega

/-!
# Finite residues for pure-power polynomial relations

For relations `X i ^ ell - r i` with `totalDegree (r i) < ell`, a finite sum of
polynomial coefficients defines the formal Laurent residue. The degree bound proves
`truncated_stable`: increasing a sufficiently large truncation bound does not change the sum.
Consequently `linear` is an actual linear functional, and `residue_low_degree` identifies it
with the top-box coefficient at low degree. The coefficient ring is any commutative ring.

This is an algebraic step toward real-arithmetic counting bounds, ported from
`LeanCanny.CountingHierarchy.PurePowerResidue` at lean-canny commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`. No resource bound is asserted here.
-/

public section

namespace MvPolynomial.PurePower

open MvPolynomial
open scoped BigOperators

variable {S : Type*} [CommRing S] {n : ℕ}

/-- A rectangular finite set of geometric-series indices. -/
@[expose] noncomputable def indices (n B : ℕ) : Finset (Fin n → ℕ) :=
  Fintype.piFinset (fun _ => Finset.range (B + 1))

@[simp] theorem mem_indices {B : ℕ} {j : Fin n → ℕ} :
    j ∈ indices n B ↔ ∀ i, j i ≤ B := by
  simp only [indices, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff]

private theorem indices_mono {B C : ℕ} (h : B ≤ C) : indices n B ⊆ indices n C := by
  intro j hj
  exact mem_indices.mpr (fun i => (mem_indices.mp hj i).trans h)

/-- The target exponent `tau + ell*j`. -/
@[expose] noncomputable def target (ell : ℕ) (j : Fin n → ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => ell - 1 + ell * j i)

private theorem target_degree (ell : ℕ) (j : Fin n → ℕ) :
    (target ell j).sum (fun _ e => e) = n * (ell - 1) + ell * (∑ i, j i) := by
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp only [target, Finsupp.coe_equivFunOnFinite_symm, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum]

/-- One summand in the finite Laurent coefficient formula. -/
@[expose] noncomputable def term (ell : ℕ) (r : Fin n → MvPolynomial (Fin n) S)
    (v : MvPolynomial (Fin n) S) (j : Fin n → ℕ) : S :=
  (v * ∏ i, r i ^ j i).coeff (target ell j)

/-- The geometric-series numerator grows by at most `ell - 1` per index increment. -/
theorem numerator_degree {ell : ℕ} (r : Fin n → MvPolynomial (Fin n) S)
    (hr : ∀ i, (r i).totalDegree < ell) (v : MvPolynomial (Fin n) S) (j : Fin n → ℕ) :
    (v * ∏ i, r i ^ j i).totalDegree ≤ v.totalDegree + (ell - 1) * (∑ i, j i) := by
  have hprod : (∏ i, r i ^ j i).totalDegree ≤ ∑ i, j i * (ell - 1) := by
    apply (MvPolynomial.totalDegree_finsetProd Finset.univ (fun i => r i ^ j i)).trans
    apply Finset.sum_le_sum
    intro i _
    exact (MvPolynomial.totalDegree_pow (r i) (j i)).trans
      (Nat.mul_le_mul_left (j i) (by have := hr i; omega))
  calc
    _ ≤ v.totalDegree + (∏ i, r i ^ j i).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ ≤ v.totalDegree + ∑ i, j i * (ell - 1) := Nat.add_le_add_left hprod _
    _ = _ := by rw [← Finset.sum_mul]; congr 1; exact Nat.mul_comm _ _

/-- The total-degree decrease bounds every contributing geometric-series index. -/
theorem term_eq_zero_of_degree_lt {ell : ℕ} (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (v : MvPolynomial (Fin n) S) (j : Fin n → ℕ)
    (h : v.totalDegree < n * (ell - 1) + (∑ i, j i)) : term ell r v j = 0 := by
  classical
  by_contra hne
  have hc := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hne)
  rw [target_degree] at hc
  have hd := numerator_degree r hr v j
  have hmul : ell * (∑ i, j i) = (ell - 1) * (∑ i, j i) + (∑ i, j i) := by
    calc
      _ = (ell - 1 + 1) * (∑ i, j i) := by congr 1; omega
      _ = _ := by rw [add_mul, one_mul]
  rw [hmul] at hc
  omega

/-- A fixed rectangular truncation is a linear map in its numerator. -/
@[expose] noncomputable def truncated (ell : ℕ) (r : Fin n → MvPolynomial (Fin n) S)
    (B : ℕ) : MvPolynomial (Fin n) S →ₗ[S] S where
  toFun v := ∑ j ∈ indices n B, term ell r v j
  map_add' v w := by
    simp only [term, add_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [term, smul_mul_assoc, MvPolynomial.coeff_smul, RingHom.id_apply,
      smul_eq_mul, Finset.mul_sum]

/-- All truncations above the numerator's degree give the same finite sum. -/
theorem truncated_stable {ell B C : ℕ} (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (v : MvPolynomial (Fin n) S) (hB : v.totalDegree ≤ B) (hBC : B ≤ C) :
    truncated ell r B v = truncated ell r C v := by
  apply Finset.sum_subset (indices_mono hBC)
  intro j _ hj
  have hnot : ¬∀ i, j i ≤ B := by simpa only [mem_indices] using hj
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  have hji : j i ≤ (∑ i, j i) :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  exact term_eq_zero_of_degree_lt hell r hr v j (by omega)

/-- The truncation at the numerator degree gives the canonical residue functional. -/
@[expose] noncomputable def residue (ell : ℕ) (r : Fin n → MvPolynomial (Fin n) S)
    (v : MvPolynomial (Fin n) S) : S := truncated ell r v.totalDegree v

theorem residue_eq_truncated {ell B : ℕ} (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (v : MvPolynomial (Fin n) S) (hB : v.totalDegree ≤ B) :
    residue ell r v = truncated ell r B v :=
  truncated_stable hell r hr v (Nat.le_refl _) hB

theorem residue_add {ell : ℕ} (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (v w : MvPolynomial (Fin n) S) : residue ell r (v + w) = residue ell r v + residue ell r w := by
  let B := v.totalDegree + w.totalDegree
  have hv : v.totalDegree ≤ B := by dsimp [B]; omega
  have hw : w.totalDegree ≤ B := by dsimp [B]; omega
  have ha : (v + w).totalDegree ≤ B :=
    (MvPolynomial.totalDegree_add v w).trans (max_le hv hw)
  rw [residue_eq_truncated hell r hr (v + w) ha,
    residue_eq_truncated hell r hr v hv, residue_eq_truncated hell r hr w hw, map_add]

theorem residue_smul {ell : ℕ} (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (c : S) (v : MvPolynomial (Fin n) S) : residue ell r (c • v) = c • residue ell r v := by
  rw [residue_eq_truncated hell r hr (c • v) (MvPolynomial.totalDegree_smul_le c v),
    residue_eq_truncated hell r hr v (Nat.le_refl _), map_smul]

/-- The canonical residue, with linearity derived from finite degree bounds. -/
@[expose] noncomputable def linear {ell : ℕ} (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell) :
    MvPolynomial (Fin n) S →ₗ[S] S where
  toFun := residue ell r
  map_add' := residue_add hell r hr
  map_smul' c v := residue_smul hell r hr c v

@[simp] theorem linear_apply {ell : ℕ} (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (v : MvPolynomial (Fin n) S) : linear hell r hr v = residue ell r v := rfl

/-- At low degree the residue is simply the top-box coefficient. -/
theorem residue_low_degree {ell : ℕ} (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (v : MvPolynomial (Fin n) S) (hv : v.totalDegree ≤ n * (ell - 1)) :
    residue ell r v = v.coeff (Finsupp.equivFunOnFinite.symm (fun _ => ell - 1)) := by
  classical
  change (∑ j ∈ indices n v.totalDegree, term ell r v j) = _
  rw [Finset.sum_eq_single (0 : Fin n → ℕ)]
  · simp [term, target]
  · intro j _ hj
    have hex : ∃ i, j i ≠ 0 := by
      by_contra h
      have hall : ∀ i, j i = 0 := by simpa only [not_exists, not_not] using h
      exact hj (funext hall)
    obtain ⟨i, hi⟩ := hex
    have hji : j i ≤ (∑ i, j i) :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    exact term_eq_zero_of_degree_lt hell r hr v j (by omega)
  · intro h
    exact False.elim (h (mem_indices.mpr (fun _ => Nat.zero_le _)))

end MvPolynomial.PurePower
