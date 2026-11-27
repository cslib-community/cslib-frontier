/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate (Mathlib, pure-power polynomial residues and traces)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.MvPolynomial.Degrees
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.Residue

/-!
# Coefficient specialization of finite pure-power residues

The finite residue commutes with any coefficient-ring homomorphism. The degree decrease under
specialization ensures that both canonical truncations compute the same sum. Expanding a
specialized kernel by coefficients then reduces its pairing to residues over the source ring;
`residue_kernel_expansion` supplies the reproducing identity used by the quotient trace proof.
No injectivity, nonsingularity, or squarefreeness assumption is required.

This is an algebraic step toward real-arithmetic counting bounds, ported from
`LeanCanny.CountingHierarchy.PurePowerResidueMap` and `PurePowerResidueExpansion` at commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183` of lean-canny.
-/

public section

namespace MvPolynomial

namespace PurePower

open MvPolynomial
open scoped BigOperators

variable {S T : Type*} [CommRing S] [CommRing T] {n : ℕ}

/-- Applying a coefficient homomorphism commutes with every fixed truncation. -/
theorem truncated_map (φ : S →+* T) (ell B : ℕ)
    (r : Fin n → MvPolynomial (Fin n) S) (v : MvPolynomial (Fin n) S) :
    φ (truncated ell r B v) = truncated ell (fun i => (r i).map φ) B (v.map φ) := by
  change φ (∑ j ∈ indices n B, term ell r v j) =
    ∑ j ∈ indices n B, term ell (fun i => (r i).map φ) (v.map φ) j
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold term
  rw [← MvPolynomial.coeff_map φ]
  congr 1
  simp only [map_mul, map_prod, map_pow]

/-- Specialization needs no nonsingularity or squarefreeness hypothesis. -/
theorem residue_map (φ : S →+* T) {ell : ℕ} (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (v : MvPolynomial (Fin n) S) :
    φ (residue ell r v) = residue ell (fun i => (r i).map φ) (v.map φ) := by
  have hr' (i : Fin n) : ((r i).map φ).totalDegree < ell :=
    (totalDegree_map_le φ (r i)).trans_lt (hr i)
  calc
    _ = truncated ell (fun i => (r i).map φ) v.totalDegree (v.map φ) :=
      truncated_map φ ell v.totalDegree r v
    _ = _ := (residue_eq_truncated hell (fun i => (r i).map φ) hr'
      (v.map φ) (totalDegree_map_le φ v)).symm

/-- Expand a specialized residue pairing through the finite coefficients of its kernel. -/
theorem residue_kernel_expansion (φ : S →+* T) {ell : ℕ} (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (K : MvPolynomial (Fin n) T) (q : MvPolynomial (Fin n) S) :
    residue ell (fun i => (r i).map φ) (K * q.map φ) =
      ∑ e ∈ K.support, K.coeff e * φ (residue ell r (monomial e 1 * q)) := by
  have hr' (i : Fin n) : ((r i).map φ).totalDegree < ell :=
    (totalDegree_map_le φ (r i)).trans_lt (hr i)
  conv_lhs => rw [K.as_sum]
  rw [Finset.sum_mul, ← linear_apply hell _ hr', map_sum]
  apply Finset.sum_congr rfl
  intro e _
  have heq : monomial e (K.coeff e) * q.map φ =
      K.coeff e • (monomial e (1 : S) * q).map φ := by
    simp only [map_mul, map_monomial, map_one]
    rw [← smul_mul_assoc]
    simp only [smul_monomial, smul_eq_mul, mul_one]
  rw [heq, map_smul, linear_apply, ← residue_map φ hell r hr, smul_eq_mul]

end PurePower
end MvPolynomial
