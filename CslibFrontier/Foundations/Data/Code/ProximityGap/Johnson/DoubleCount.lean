/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson.DegZ
public import CslibFrontier.Foundations.Data.Code.ReedSolomon
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Lagrange

/-!
# Step 7: Weighted Double Counting and Lagrange Interpolation

Converts the algebraic-closure lifted polynomial and surviving scalar set `T''` into
correlated Reed–Solomon codewords `v : Fin (r + 1) → (ι → F)` agreeing on a common heavy set
`D'` via weighted double counting and Lagrange interpolation.

## Main results

* `Cslib.Code.ProximityGap.exists_correlatedAgreement_of_lifted_poly`: extracts the final
  correlated-agreement subset and codeword tuple.
-/

public section

namespace Cslib.Code.ProximityGap

open Cslib.Code Finset Polynomial Polynomial.Bivariate

variable {F : Type*} [Field F]

private theorem weighted_double_count_le {ι α : Type*} [Fintype ι]
    {W : ι → ℕ} {W_tot B_W bad : ℕ} (T : Finset α) (Istar : Finset ι)
    (agree : α → ι → Prop) [∀ z i, Decidable (agree z i)]
    (hW_sum : ∑ i, W i ≤ W_tot) (hT : W_tot * bad < #T)
    (hlo : ∀ z ∈ T, B_W ≤ ∑ i ∈ Finset.univ.filter (agree z), W i)
    (hbad : ∀ i ∉ Istar, #(T.filter fun z => agree z i) ≤ bad) :
    B_W ≤ ∑ i ∈ Istar, W i := by
  classical
  have hswap : ∑ z ∈ T, ∑ i ∈ Finset.univ.filter (agree z), W i =
      ∑ i : ι, #(T.filter fun z => agree z i) * W i := by
    calc _ = ∑ z ∈ T, ∑ i : ι, if agree z i then W i else 0 :=
            Finset.sum_congr rfl fun z _ => Finset.sum_filter _ _
      _ = ∑ i : ι, ∑ z ∈ T, if agree z i then W i else 0 := Finset.sum_comm
      _ = ∑ i : ι, #(T.filter fun z => agree z i) * W i := Finset.sum_congr rfl fun i _ => by
            rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  have hlo' : #T * B_W ≤ ∑ i : ι, #(T.filter fun z => agree z i) * W i :=
    (by rw [Finset.sum_const, smul_eq_mul] : ∑ _z ∈ T, B_W = #T * B_W) ▸
      (Finset.sum_le_sum hlo).trans_eq hswap
  have hpart_in : ∑ i ∈ Istar, #(T.filter fun z => agree z i) * W i ≤ #T * ∑ i ∈ Istar, W i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ (card_filter_le _ _)
  have hpart_out : ∑ i ∈ Finset.univ \ Istar, #(T.filter fun z => agree z i) * W i ≤
      W_tot * bad :=
    (Finset.sum_le_sum fun i hi =>
      Nat.mul_le_mul_right (W i) (hbad i (mem_sdiff.1 hi).2)).trans <| by
      rw [← Finset.mul_sum, mul_comm bad]
      exact Nat.mul_le_mul_right bad
        ((Finset.sum_le_sum_of_subset (subset_univ _)).trans hW_sum)
  have hsplit : ∑ i : ι, #(T.filter fun z => agree z i) * W i =
      (∑ i ∈ Finset.univ \ Istar, #(T.filter fun z => agree z i) * W i) +
        ∑ i ∈ Istar, #(T.filter fun z => agree z i) * W i :=
    (Finset.sum_sdiff (subset_univ Istar)).symm
  have hlt : #T * B_W < #T * ((∑ i ∈ Istar, W i) + 1) := by
    calc #T * B_W ≤ #T * ∑ i ∈ Istar, W i + W_tot * bad := by omega
      _ < #T * ∑ i ∈ Istar, W i + #T := Nat.add_lt_add_left hT _
      _ = #T * ((∑ i ∈ Istar, W i) + 1) := by ring
  exact Nat.lt_succ_iff.1 (Nat.lt_of_mul_lt_mul_left hlt)

/-- Step 7: Weighted double-counting shows `B_W ≤ ∑ i ∈ Istar, W i`, giving `k ≤ #Istar`, and
Lagrange interpolation on a `k`-element subset `J ⊆ Istar` pulls `Pstar ∈ L[X]` down to `r + 1`
Reed–Solomon codewords `v : Fin (r + 1) → (ι → F)` agreeing with `u` on `Istar`. -/
theorem exists_correlatedAgreement_of_lifted_poly {ι : Type*} [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α)
    {k r d D B_Z D_Y M W_tot B_W μ : ℕ}
    (hk : 1 ≤ k) (hd : d = k - 1) (hM : 0 < M)
    {W : ι → ℕ} (hW_le : ∀ i, W i ≤ M) (hW_sum : ∑ i, W i ≤ W_tot)
    (hk_le_t : k ≤ (B_W + M - 1) / M)
    {u : Fin (r + 1) → (ι → F)}
    {S : F[X][X][X]} {Fstar : F[X][X]} {x₀ : F} {T'' : Finset F}
    (hT''_card : W_tot * D_Y * (4 * D * B_Z + r * D_Y) < #T'')
    (hT''_mem : ∀ z ∈ T'',
      ∃ P : F[X], P.natDegree ≤ d ∧
        (evZ₂ z S).eval (P ^ μ) = 0 ∧
        (Fstar.map (evZ z)).eval ((P ^ μ).eval x₀) = 0 ∧
        ((S.map (Polynomial.evalRingHom (C x₀))).derivative.map (evZ z)).eval
          ((P ^ μ).eval x₀) ≠ 0 ∧
        B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => P.eval (α i) = (curveWord u i).eval z), W i)
    (Pstar : (AlgebraicClosure (FractionRing F[X]))[X])
    (Istar : Finset ι)
    (hPstar_deg : Pstar.natDegree ≤ d)
    (hIstar_agree : ∀ i ∈ Istar,
      Pstar.eval (((algebraMap (FractionRing F[X]) (AlgebraicClosure (FractionRing F[X]))).comp
        (algebraMap F[X] (FractionRing F[X]))) (C (α i))) =
      ((algebraMap (FractionRing F[X]) (AlgebraicClosure (FractionRing F[X]))).comp
        (algebraMap F[X] (FractionRing F[X]))) (curveWord u i))
    (hIstar_bad : ∀ i ∉ Istar, ∃ res : F[X], res ≠ 0 ∧
      res.natDegree ≤ 4 * D * D_Y * B_Z + r * D_Y ^ 2 ∧
      ∀ z ∈ T'', ∀ P : F[X], P.natDegree ≤ d →
        (evZ₂ z S).eval (P ^ μ) = 0 →
        (Fstar.map (evZ z)).eval ((P ^ μ).eval x₀) = 0 →
        ((S.map (Polynomial.evalRingHom (C x₀))).derivative.map (evZ z)).eval
          ((P ^ μ).eval x₀) ≠ 0 →
        P.eval (α i) = (curveWord u i).eval z → res.eval z = 0) :
    ∃ D' : Finset ι, B_W ≤ ∑ i ∈ D', W i ∧
      ∃ v : Fin (r + 1) → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', ∀ j, u j i = v j i := by
  classical
  let K := FractionRing F[X]; let L := AlgebraicClosure K
  let j_L : F[X] →+* L := (algebraMap K L).comp (algebraMap F[X] K)
  have hj_L_inj : Function.Injective j_L :=
    (RingHom.injective (algebraMap K L)).comp (IsFractionRing.injective F[X] K)
  choose P_of hP_deg hS_ev hF_ev hγ_ev hW_agree using fun z : T'' => hT''_mem z.1 z.2
  let agree : F → ι → Prop := fun z i =>
    (if hz : z ∈ T'' then P_of ⟨z, hz⟩ else 0).eval (α i) = (curveWord u i).eval z
  have hW_Istar : B_W ≤ ∑ i ∈ Istar, W i :=
    weighted_double_count_le T'' Istar agree hW_sum (by rwa [← mul_assoc])
      (fun z hz => by simpa only [agree, hz, ↓reduceDIte] using hW_agree ⟨z, hz⟩)
      fun i hi_not => by
        obtain ⟨res, hres_ne, hres_deg, hres_van⟩ := hIstar_bad i hi_not
        have hle := card_filter_eval_eq_zero_le hres_ne (T''.filter fun z => agree z i)
        rw [Finset.filter_true_of_mem fun z hz => by
          obtain ⟨hzT, hag⟩ := mem_filter.1 hz
          exact hres_van z hzT _ (hP_deg ⟨z, hzT⟩) (hS_ev ⟨z, hzT⟩) (hF_ev ⟨z, hzT⟩)
            (hγ_ev ⟨z, hzT⟩) (by simpa only [agree, hzT, ↓reduceDIte] using hag)] at hle
        exact hle.trans (hres_deg.trans_eq (by ring))
  obtain ⟨J, hJ_sub, hJ_card⟩ := Finset.exists_subset_card_eq
    (hk_le_t.trans (ceil_div_le_card_of_sum_le hM hW_le hW_Istar))
  let Pj : Fin (r + 1) → F[X] := fun j => Lagrange.interpolate J α (u j)
  let v : Fin (r + 1) → (ι → F) := fun j i => (Pj j).eval (α i)
  have hPj_deg (j) : (Pj j).degree < k := hJ_card ▸ Lagrange.degree_interpolate_lt _ hα.injOn
  let P_FZ : F[X][X] := ∑ j : Fin (r + 1), (Pj j).map C * C (X ^ (j : ℕ))
  let P_L : L[X] := P_FZ.map j_L
  have hP_L_eval (i : ι) : P_L.eval (j_L (C (α i))) = j_L (curveWord v i) := by
    have hFZ : P_FZ.eval (C (α i)) = curveWord v i := by
      rw [curveWord, Polynomial.ofFn_eq_sum_monomial]
      simp only [P_FZ, eval_finsetSum, eval_mul, eval_C, v]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hhom := (Polynomial.hom_eval₂ (Pj j) (RingHom.id F) Polynomial.C (α i)).symm
      rw [RingHom.comp_id, Polynomial.eval₂_id] at hhom
      rw [Polynomial.eval_map, hhom, Polynomial.C_mul_X_pow_eq_monomial]
    have hhom := (Polynomial.hom_eval₂ P_FZ (RingHom.id F[X]) j_L (C (α i))).symm
    rw [RingHom.comp_id, Polynomial.eval₂_id] at hhom
    rw [Polynomial.eval_map, hhom, hFZ]
  have hP_L_deg_lt : P_L.degree < k := Polynomial.degree_map_le.trans_lt <|
    (degree_sum_le _ _).trans_lt <| (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun j _ =>
      (degree_mul_le _ _).trans_lt <|
        (add_le_add Polynomial.degree_map_le degree_C_le).trans_lt (by simpa using hPj_deg j)
  have hPstar_deg_lt : Pstar.degree < k := by
    rcases eq_or_ne Pstar 0 with rfl | h0
    · exact WithBot.bot_lt_coe k
    · rw [Polynomial.degree_eq_natDegree h0]; exact Nat.cast_lt.2 (by omega)
  have hPstar_eq : Pstar = P_L := sub_eq_zero.1 <| by_contra fun hne => by
    have hdeg := (Polynomial.natDegree_lt_iff_degree_lt hne).2
      ((degree_sub_le _ _).trans_lt (max_lt hPstar_deg_lt hP_L_deg_lt))
    let f_pts : ι → L := fun i => j_L (C (α i))
    have hcard := card_filter_eval_eq_zero_le hne (J.image f_pts)
    have hvan : ∀ x ∈ J.image f_pts, (Pstar - P_L).eval x = 0 := fun x hx => by
      obtain ⟨i, hiJ, rfl⟩ := mem_image.1 hx
      have hcw : curveWord u i = curveWord v i := congrArg (Polynomial.ofFn (r + 1)) <|
        funext fun j => (Lagrange.eval_interpolate_at_node _ hα.injOn hiJ).symm
      rw [eval_sub, hIstar_agree i (hJ_sub hiJ), hP_L_eval i, hcw, sub_self]
    have hf_inj : Function.Injective f_pts := hj_L_inj.comp (Polynomial.C_injective.comp hα)
    rw [Finset.filter_true_of_mem hvan, card_image_of_injective J hf_inj, hJ_card] at hcard
    omega
  refine ⟨Istar, hW_Istar, v, fun j => mem_reedSolomon.2 ⟨Pj j, hPj_deg j, rfl⟩, fun i hi j => ?_⟩
  have hcw : curveWord v i = curveWord u i :=
    hj_L_inj (by rw [← hP_L_eval i, ← hPstar_eq, hIstar_agree i hi])
  simpa only [curveWord, Polynomial.ofFn_coeff_eq_val_of_lt _ j.2] using
    (congrArg (fun p : F[X] => p.coeff (j : ℕ)) hcw).symm

end Cslib.Code.ProximityGap
