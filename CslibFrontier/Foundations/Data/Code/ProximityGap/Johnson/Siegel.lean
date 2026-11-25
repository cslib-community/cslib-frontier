/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson.Bounds
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson.DegZ
import CslibFrontier.Foundations.Data.Code.GuruswamiSudan
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Step 1: Zero-Denominator Siegel Interpolation Along Parameterized Curves

Constructs a nonzero trivariate polynomial `Q(Z, X, Y) ∈ F[Z][X][Y]` interpolating a degree-`r`
curve of words with multiplicity `m` at every evaluation point `α i`, bounding both its
`(1, d)`-weighted `(X, Y)`-degree and its `Z`-degree `siegelZDeg`.

## Main results

* `Cslib.Code.ProximityGap.exists_siegel_interpolant`: zero-denominator Siegel interpolation lemma.
-/

public section

namespace Cslib.Code.ProximityGap

open Cslib.Code Cslib.Code.GuruswamiSudan Finset Polynomial Polynomial.Bivariate

variable {F : Type*} [Field F]

/-- Polynomial `Q_c ∈ F[Z][X][Y]` constructed from coefficient table `c : (M × Fin (B + 1)) → F`. -/
private noncomputable def polyOfTable (M : Finset (ℕ × ℕ)) (B : ℕ)
    (c : (M × Fin (B + 1)) → F) : F[X][X][X] :=
  ∑ p ∈ M.attach,
    C (C (∑ t : Fin (B + 1), C (c (p, t)) * X ^ (t : ℕ)) * X ^ p.1.1) * X ^ p.1.2

private theorem coeff_coeff_coeff_polyOfTable (M : Finset (ℕ × ℕ)) (B : ℕ)
    (c : (M × Fin (B + 1)) → F) (a b t : ℕ) :
    (((polyOfTable M B c).coeff b).coeff a).coeff t =
      if h : (a, b) ∈ M then
        if ht : t < B + 1 then c (⟨(a, b), h⟩, ⟨t, ht⟩) else 0
      else 0 := by
  rw [polyOfTable, finsetSum_coeff, finsetSum_coeff, finsetSum_coeff]
  have hterm (p : M) :
      (((C (C (∑ u : Fin (B + 1), C (c (p, u)) * X ^ (u : ℕ)) * X ^ p.1.1) *
          X ^ p.1.2).coeff b).coeff a).coeff t =
        if p.1 = (a, b) then if ht : t < B + 1 then c (p, ⟨t, ht⟩) else 0 else 0 := by
    by_cases hpe : p.1 = (a, b)
    · simp only [hpe, ↓reduceIte, coeff_C_mul_X_pow, finsetSum_coeff]
      by_cases ht : t < B + 1
      · rw [dite_eq_left ht, Finset.sum_eq_single ⟨t, ht⟩
          (fun u _ hne => ite_eq_right fun h => hne (Fin.ext h.symm))
          (absurd (mem_univ _)), ite_eq_left rfl]
      · rw [dite_eq_right ht]
        exact Finset.sum_eq_zero fun u _ => ite_eq_right (by omega)
    · rw [ite_eq_right hpe, coeff_C_mul_X_pow]
      split_ifs with hpb
      · rw [coeff_C_mul_X_pow, ite_eq_right fun hpa => hpe (Prod.ext hpa.symm hpb.symm),
          coeff_zero]
      · exact coeff_zero _
  simp_rw [hterm]
  by_cases hab : (a, b) ∈ M
  · rw [dite_eq_left hab, Finset.sum_eq_single ⟨(a, b), hab⟩
      (fun _ _ hne => ite_eq_right fun h => hne (Subtype.ext h)) (absurd (mem_attach M _))]
    simp
  · rw [dite_eq_right hab]
    exact Finset.sum_eq_zero fun p _ => ite_eq_right fun h : p.1 = (a, b) => hab (h ▸ p.2)

private theorem polyOfTable_eq_zero_iff (M : Finset (ℕ × ℕ)) (B : ℕ)
    (c : (M × Fin (B + 1)) → F) :
    polyOfTable M B c = 0 ↔ c = 0 := by
  refine ⟨fun h0 => funext fun ⟨⟨⟨a, b⟩, hab⟩, ⟨t, ht⟩⟩ => ?_, ?_⟩
  · simpa [coeff_coeff_coeff_polyOfTable, hab, ht] using
      congrArg (fun Q : F[X][X][X] => ((Q.coeff b).coeff a).coeff t) h0
  · rintro rfl
    ext b a t
    rw [coeff_coeff_coeff_polyOfTable]
    split_ifs <;> simp

private theorem weightedDegree_polyOfTable_le (d D B : ℕ)
    (c : (Sudan.monomials d D × Fin (B + 1)) → F) :
    weightedDegree d (polyOfTable (Sudan.monomials d D) B c) ≤ D := by
  refine weightedDegree_le_iff.2 fun a b hab => by_contra fun hlt => hab ?_
  ext t
  rw [coeff_coeff_coeff_polyOfTable, coeff_zero, dite_eq_right fun hmem => ?_]
  have hle := (Sudan.mem_monomials.1 hmem).2.2
  dsimp only at hle; omega

private theorem natDegree_polyOfTable_le (d D B : ℕ)
    (c : (Sudan.monomials d D × Fin (B + 1)) → F) :
    (polyOfTable (Sudan.monomials d D) B c).natDegree ≤ maxYDeg d D := by
  refine natDegree_le_iff_coeff_eq_zero.2 fun b hb => ?_
  ext a t
  rw [coeff_coeff_coeff_polyOfTable, coeff_zero, coeff_zero, dite_eq_right fun hmem => ?_]
  exact hb.not_ge (Finset.le_sup (f := Prod.snd) hmem)

private theorem degZ_polyOfTable_le (M : Finset (ℕ × ℕ)) (B : ℕ)
    (c : (M × Fin (B + 1)) → F) :
    degZ (polyOfTable M B c) ≤ B := by
  refine degZ_le_iff.2 fun a b => natDegree_le_iff_coeff_eq_zero.2 fun t ht => ?_
  rw [coeff_coeff_coeff_polyOfTable]
  split_ifs <;> first | rfl | omega

private theorem natDegree_coeff_shift_polyOfTable_le {d D B r : ℕ}
    (c : (Sudan.monomials d D × Fin (B + 1)) → F) (x : F) (w : F[X]) (hw : w.natDegree ≤ r)
    (u v : ℕ) :
    (((shift (C x) w (polyOfTable (Sudan.monomials d D) B c)).coeff v).coeff u).natDegree ≤
      B + r * maxYDeg d D := by
  rw [polyOfTable, map_sum, finsetSum_coeff, finsetSum_coeff]
  refine (natDegree_sum_le _ _).trans (Finset.sup_le fun p _ => ?_)
  set cz : F[X] := ∑ t : Fin (B + 1), C (c (p, t)) * X ^ (t : ℕ)
  have hcz_deg : cz.natDegree ≤ B := (natDegree_sum_le _ _).trans (Finset.sup_le fun t _ =>
    (natDegree_C_mul_X_pow_le _ _).trans (by omega))
  change ((((shift (C x) w (C (C cz * X ^ p.1.1) * X ^ p.1.2)).coeff v).coeff u).natDegree) ≤ _
  rw [C_mul_X_pow_eq_monomial, C_mul_X_pow_eq_monomial, coeff_coeff_shift_monomial]
  refine natDegree_mul_le.trans (Nat.add_le_add ?_ (natDegree_pow_le.trans ?_))
  · have hre : (p.1.1.choose u : F[X]) * (p.1.2.choose v : F[X]) * cz * (C x) ^ (p.1.1 - u) =
        C ((p.1.1.choose u : F) * (p.1.2.choose v : F) * x ^ (p.1.1 - u)) * cz := by
      simp only [map_mul, map_pow, map_natCast]
      ring
    exact hre ▸ (natDegree_C_mul_le _ _).trans hcz_deg
  · calc (p.1.2 - v) * w.natDegree ≤ p.1.2 * r := Nat.mul_le_mul (Nat.sub_le _ _) hw
      _ ≤ r * maxYDeg d D :=
        mul_comm _ r ▸ Nat.mul_le_mul_right r (Finset.le_sup (f := Prod.snd) p.2)

/-- Step 1 (Siegel interpolation in `F[Z][X][Y]`): zero-denominator multiplicity-`m` interpolant
with explicit `Z`-degree bound `siegelZDeg n m d D r`. -/
theorem exists_siegel_interpolant [DecidableEq F] {ι : Type*} [Fintype ι] (α : ι → F)
    {r m d D : ℕ} (u : Fin (r + 1) → (ι → F))
    (hinterp : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials d D)) :
    ∃ Q : F[X][X][X],
      Q ≠ 0 ∧
      weightedDegree d Q ≤ D ∧
      Q.natDegree ≤ maxYDeg d D ∧
      degZ Q ≤ siegelZDeg (Fintype.card ι) m d D r ∧
      ∀ i : ι, VanishesToOrder m (C (α i)) (curveWord u i) Q := by
  classical
  set M := Sudan.monomials d D
  set B := siegelZDeg (Fintype.card ι) m d D r
  set D_Y := maxYDeg d D
  set R_eq := Fintype.card ι * (m * (m + 1) / 2)
  let entry : (M × Fin (B + 1)) → (ι × multPairs m × Fin (B + r * D_Y + 1)) → F := fun pt eq =>
    (((shift (C (α eq.1)) (curveWord u eq.1)
        (C (C (X ^ (pt.2 : ℕ)) * X ^ pt.1.1.1) * X ^ pt.1.1.2)).coeff eq.2.1.1.2).coeff
      eq.2.1.1.1).coeff (eq.2.2 : ℕ)
  let Φ : ((M × Fin (B + 1)) → F) →ₗ[F] ((ι × multPairs m × Fin (B + r * D_Y + 1)) → F) :=
    { toFun := fun c eq => ∑ pt : M × Fin (B + 1), c pt * entry pt eq
      map_add' := fun _ _ => funext fun _ => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun _ _ => funext fun _ => by simp [smul_eq_mul, mul_assoc, Finset.mul_sum] }
  have hΦ_eq : ∀ c eq, Φ c eq =
      (((shift (C (α eq.1)) (curveWord u eq.1) (polyOfTable M B c)).coeff eq.2.1.1.2).coeff
        eq.2.1.1.1).coeff (eq.2.2 : ℕ) := fun c eq => by
    change ∑ pt : M × Fin (B + 1), c pt * entry pt eq = _
    rw [polyOfTable, map_sum, finsetSum_coeff, finsetSum_coeff, finsetSum_coeff,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hsplit :
        C (C (∑ t : Fin (B + 1), C (c (p, t)) * X ^ (t : ℕ)) * X ^ p.1.1) * X ^ p.1.2 =
        ∑ t : Fin (B + 1),
          C (C (C (c (p, t)))) * (C (C (X ^ (t : ℕ)) * X ^ p.1.1) * X ^ p.1.2) := by
      simp only [map_sum, Finset.sum_mul, map_mul, mul_assoc]
    rw [hsplit, map_sum, finsetSum_coeff, finsetSum_coeff, finsetSum_coeff]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hshiftC : shift (C (α eq.1)) (curveWord u eq.1) (C (C (C (c (p, t))))) =
        C (C (C (c (p, t)))) := by
      rw [shift_apply, map_C, taylor_C]
      change C (taylor (C (α eq.1)) (C (C _))) = _
      rw [taylor_C]
    rw [map_mul, hshiftC, coeff_C_mul, coeff_C_mul, coeff_C_mul]
  have hsiegel : R_eq * r * D_Y < (#M - R_eq) * (B + 1) := by
    simpa [B, siegelZDeg, R_eq, D_Y] using
      Nat.lt_mul_div_succ (R_eq * r * D_Y) (Nat.sub_pos_of_lt hinterp)
  have hcard_lt : Fintype.card (ι × multPairs m × Fin (B + r * D_Y + 1)) <
      Fintype.card (M × Fin (B + 1)) := by
    simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin, card_multPairs]
    have h1 : Fintype.card ι * (m * (m + 1) / 2 * (B + r * D_Y + 1)) =
        R_eq * (B + 1) + R_eq * r * D_Y := by dsimp only [R_eq]; ring
    have h2 : #M * (B + 1) = R_eq * (B + 1) + (#M - R_eq) * (B + 1) := by
      rw [← add_mul, Nat.add_sub_of_le hinterp.le]
    omega
  obtain ⟨c, hc_mem, hc_ne⟩ := (Submodule.ne_bot_iff _).1 <|
    LinearMap.ker_ne_bot_of_finrank_lt (f := Φ) (by
      simpa only [Module.finrank_fintype_fun_eq_card] using hcard_lt)
  refine ⟨polyOfTable M B c, (not_iff_not.2 (polyOfTable_eq_zero_iff M B c)).2 hc_ne,
    weightedDegree_polyOfTable_le d D B c, natDegree_polyOfTable_le d D B c,
    degZ_polyOfTable_le M B c, fun i u₀ v₀ huv => ?_⟩
  ext t; rw [coeff_zero]
  by_cases ht : t < B + r * D_Y + 1
  · exact (hΦ_eq c (i, ⟨(u₀, v₀), mem_multPairs.2 huv⟩, ⟨t, ht⟩)).symm.trans
      (congrFun (LinearMap.mem_ker.1 hc_mem) _)
  · have hdeg := natDegree_coeff_shift_polyOfTable_le c (α i) (curveWord u i)
      (Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (Nat.succ_pos r) _)) u₀ v₀
    exact coeff_eq_zero_of_natDegree_lt (by dsimp only [M, B, D_Y] at *; omega)

end Cslib.Code.ProximityGap
