/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, polynomial resultants)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.RingTheory.Polynomial.ResultantCoeffNorm
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# An integer polynomial for the values at algebraic roots

The resultant of `p(X)` and `Y - g(X)` eliminates the source variable `X`. It has
a root at `g(a)` for each root `a` of `p`. Factoring over a splitting field accounts
for multiplicities and gives the exact degree in `Y`. The coefficient norm bound
uses the Sylvester determinant.

Adapted from `PolynomialValueResultant` and `PolynomialValueResultantBounds` in
lean-canny at commit `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Polynomial

/-- The resultant eliminating the source variable from `p(X)` and `Y - g(X)`. -/
noncomputable def valueResultant (p g : ℤ[X]) : ℤ[X] :=
  (p.map C).resultant (C X - g.map C)

private theorem map_valueResultant_eq_prod {K : Type*} [Field K] [CharZero K]
    (p g : ℤ[X]) (hs : (p.map (Int.castRingHom K)).Splits) :
    (p.valueResultant g).map (Int.castRingHom K) =
      C ((p.map (Int.castRingHom K)).leadingCoeff ^
        (C X - g.map C).natDegree) *
        ((p.map (Int.castRingHom K)).roots.map
          (fun a => X - C ((g.map (Int.castRingHom K)).eval a))).prod := by
  let φ := Int.castRingHom K
  let ψ := mapRingHom φ
  let q := C X - g.map C
  have hφ : Function.Injective φ := Int.cast_injective
  have hmap (r : ℤ[X]) : (r.map C).map ψ = (r.map φ).map C := by
    rw [map_map, map_map]
    exact congrArg (fun f => r.map f) (mapRingHom_comp_C φ)
  have hpdeg : (p.map C).natDegree = ((p.map φ).map C).natDegree := by
    simp only [natDegree_map_eq_of_injective C_injective,
      natDegree_map_eq_of_injective hφ]
  change ψ ((p.map C).resultant q) = _
  rw [← resultant_map_map, hmap, hpdeg,
    resultant_eq_prod_eval _ _ _ natDegree_map_le (hs.map C),
    leadingCoeff_map_of_injective C_injective, ← map_pow,
    hs.roots_map_of_injective C_injective, Multiset.map_map]
  apply congrArg (fun m : Multiset K[X] => C _ * m.prod)
  apply Multiset.map_congr rfl
  intro a _
  change (q.map ψ).eval (C a) = X - C ((g.map φ).eval a)
  simp only [q, Polynomial.map_sub, map_C, hmap, eval_sub, eval_C, eval_map_apply,
    ψ, coe_mapRingHom, map_X]

/-- If the source polynomial is nonzero, its value resultant is nonzero and has
the same natural degree, including for repeated roots and constant test polynomials. -/
theorem valueResultant_ne_zero_and_natDegree {p : ℤ[X]} (hp : p ≠ 0) (g : ℤ[X]) :
    p.valueResultant g ≠ 0 ∧ (p.valueResultant g).natDegree = p.natDegree := by
  let φ := Int.castRingHom (AlgebraicClosure ℚ)
  have hφ : Function.Injective φ := Int.cast_injective
  have hpφ : p.map φ ≠ 0 := (Polynomial.map_ne_zero_iff hφ).mpr hp
  have hs : (p.map φ).Splits := IsAlgClosed.splits _
  have hlead : (p.map φ).leadingCoeff ^ (C X - g.map C).natDegree ≠ 0 :=
    pow_ne_zero _ (leadingCoeff_ne_zero.mpr hpφ)
  have hprod :
      (((p.map φ).roots.map (fun a => X - C ((g.map φ).eval a))).prod).Monic :=
    monic_multiset_prod_of_monic _ _ fun _ _ => monic_X_sub_C _
  have h := map_valueResultant_eq_prod p g hs
  constructor
  · intro hz
    rw [hz, Polynomial.map_zero] at h
    exact (mul_ne_zero (C_ne_zero.mpr hlead) hprod.ne_zero) h.symm
  · rw [← natDegree_map_eq_of_injective hφ (p.valueResultant g),
      h, natDegree_C_mul hlead]
    simpa only [Multiset.map_map, Function.comp_def, Multiset.card_map,
      ← hs.natDegree_eq_card_roots, natDegree_map_eq_of_injective hφ] using
      natDegree_multiset_prod_X_sub_C_eq_card
        ((p.map φ).roots.map fun a => (g.map φ).eval a)

/-- Evaluating the test polynomial at any root of the source gives a root of the
value resultant, after casting coefficients to the ambient field. -/
theorem isRoot_valueResultant {K : Type*} [Field K] [CharZero K]
    {p : ℤ[X]} (hp : p ≠ 0) (g : ℤ[X]) {a : K}
    (ha : (p.map (Int.castRingHom K)).IsRoot a) :
    ((p.valueResultant g).map (Int.castRingHom K)).IsRoot
      ((g.map (Int.castRingHom K)).eval a) := by
  let ι := algebraMap K (AlgebraicClosure K)
  let φ := Int.castRingHom (AlgebraicClosure K)
  have hφ : Function.Injective φ := Int.cast_injective
  have hcomp : ι.comp (Int.castRingHom K) = φ := Subsingleton.elim _ _
  have hmap (r : ℤ[X]) : (r.map (Int.castRingHom K)).map ι = r.map φ := by
    rw [map_map, hcomp]
  have ha' := ha.map ι
  rw [hmap] at ha'
  apply IsRoot.of_map (f := ι) _ (algebraMap K (AlgebraicClosure K)).injective
  rw [hmap, ← eval_map_apply, hmap]
  rw [IsRoot.def, map_valueResultant_eq_prod p g (IsAlgClosed.splits _), eval_mul]
  apply mul_eq_zero_of_right
  rw [eval_multiset_prod]
  apply Multiset.prod_eq_zero
  simp only [Multiset.map_map]
  refine Multiset.mem_map.mpr ⟨ι a, (mem_roots ((Polynomial.map_ne_zero_iff hφ).mpr hp)).mpr
    ha', ?_⟩
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C, φ, sub_self]

/-- The value resultant has a Sylvester determinant norm bound in the source
and test degrees and the larger of their coefficient norms. -/
theorem coeffNorm1_valueResultant_le (p g : ℤ[X]) :
    (p.valueResultant g).coeffNorm1 ≤ (p.natDegree + g.natDegree).factorial *
      (max p.coeffNorm1 (1 + g.coeffNorm1)) ^ (p.natDegree + g.natDegree) := by
  let f := p.map C
  let q := C X - g.map C
  let A := max p.coeffNorm1 (1 + g.coeffNorm1)
  have hf (k : ℕ) : (f.coeff k).coeffNorm1 ≤ A := by
    rw [coeff_map, coeffNorm1_C]
    exact (natAbs_coeff_le_coeffNorm1 p k).trans (le_max_left _ _)
  have hq (k : ℕ) : (q.coeff k).coeffNorm1 ≤ A := by
    rw [coeff_sub, coeff_map]
    have hX : (X : ℤ[X]).coeffNorm1 = 1 := by
      rw [← mul_one (X : ℤ[X]), coeffNorm1_X_mul, coeffNorm1_one]
    have hC : ((C X : ℤ[X][X]).coeff k).coeffNorm1 ≤ 1 := by
      by_cases hk : k = 0 <;> simp [coeff_C, hk, hX, coeffNorm1_zero]
    have hg : (C (g.coeff k)).coeffNorm1 ≤ g.coeffNorm1 := by
      rw [coeffNorm1_C]
      exact natAbs_coeff_le_coeffNorm1 g k
    exact (coeffNorm1_sub_le _ _).trans ((Nat.add_le_add hC hg).trans (le_max_right _ _))
  have hqdeg : q.natDegree ≤ g.natDegree :=
    (natDegree_sub_le _ _).trans (max_le (by rw [natDegree_C]; exact Nat.zero_le _)
      natDegree_map_le)
  have hN : f.natDegree + q.natDegree ≤ p.natDegree + g.natDegree := by
    rw [natDegree_map_eq_of_injective C_injective]
    exact Nat.add_le_add_left hqdeg _
  exact (coeffNorm1_resultant_le f q hf hq).trans (Nat.mul_le_mul (Nat.factorial_le hN)
    (Nat.pow_le_pow_right (le_trans (Nat.le_add_right _ _) (le_max_right _ _)) hN))

end Polynomial
