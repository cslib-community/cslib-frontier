/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
-- `import all`: reads private `capAt` from `Coefficient`, planar ray-crossing helpers from
-- `PlanarGeometry`, Gaussian sample symmetries from `SampleSpace`, `edgeVec2` / `blockColor`
-- helpers from `QuotientColoring`, and `badCount` / `four_mul_badCount_le` from
-- `BadCountPointwise`.
import all CslibFrontier.Computability.Circuit.Frontier.TensorRank.ThreeWayCut.Coefficient
import all CslibFrontier.Computability.Circuit.Frontier.TensorRank.ThreeWayCut.PlanarGeometry
import all CslibFrontier.Computability.Circuit.Frontier.TensorRank.ThreeWayCut.SampleSpace
import all CslibFrontier.Computability.Circuit.Frontier.TensorRank.ThreeWayCut.QuotientColoring
import all CslibFrontier.Computability.Circuit.Frontier.TensorRank.ThreeWayCut.BadCountPointwise
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.Straddle
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Arccos
import CslibFrontier.Foundations.Geometry.Euclidean.Angle.Cap
import CslibFrontier.Foundations.MeasureTheory.Constructions.BorelSpace.Order
import CslibFrontier.Foundations.Probability.Gaussian.ConvexCap
import CslibFrontier.Foundations.Probability.Gaussian.OffMedian
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Expected degree-`3` half-edge mismatch bound via `rayCross` and `ConvexCap`

Bounds the ray-crossing probability `measureReal_rayCross_le` via Sheppard's arc-cosine inequality
and combines spherical-cap inner-product concavity with `measureReal_pi_prod_convex_zero_le` to
establish `integral_badCount_le_capAt`.
-/

-- This proof-only companion is intentionally private; sibling ThreeWayCut modules use import all.
set_option linter.privateModule false

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace Interval

namespace Cslib.Circuits.Frontier.TensorRank

open Cslib.Circuits.Frontier.Gaussian Cslib.Circuits.Frontier.Multigraph

attribute [local instance]
  instIsProbabilityMeasure_gauss2
  instIsProbabilityMeasure_gaussTie
  instIsProbabilityMeasure_blockMeasure

section DegreeThreeCap

variable {W F : Type*} [Fintype W] [Finite F]

omit [Finite F] in
private theorem measurableSet_rayCross_edgeVec2 (Q : Multigraph W F) (q : ℝ) (R : ℕ)
    (c : Fin 3) (e₁ e₂ : F) :
    MeasurableSet {ω : W → BlockSample |
      rayCross c (edgeVec2 Q q R ω e₁) (edgeVec2 Q q R ω e₂)} := by
  have hm_dot (e : F) : Measurable fun ω : W → BlockSample =>
      dot2 (normVec c) (edgeVec2 Q q R ω e) :=
    (by unfold dot2; fun_prop : Measurable (dot2 (normVec c))).comp (measurable_edgeVec2 Q q R e)
  have hm_det : Measurable fun ω : W → BlockSample =>
      det2 (edgeVec2 Q q R ω e₁) (edgeVec2 Q q R ω e₂) :=
    (by unfold det2; fun_prop : Measurable fun p : (ℝ × ℝ) × (ℝ × ℝ) => det2 p.1 p.2).comp
      ((measurable_edgeVec2 Q q R e₁).prodMk (measurable_edgeVec2 Q q R e₂))
  exact ((measurableSet_lt (hm_dot e₁) measurable_const).inter
      ((measurableSet_lt measurable_const (hm_dot e₂)).inter
        (measurableSet_lt measurable_const hm_det))).union
    ((measurableSet_lt (hm_dot e₂) measurable_const).inter
      ((measurableSet_lt measurable_const (hm_dot e₁)).inter
        (measurableSet_lt hm_det measurable_const)))

/-- Probability of `rayCross c` on any ordered pair `(e₁, e₂)` is at most
`arccos ⟪edgeVector e₁, edgeVector e₂⟫ / (2π)`. -/
private theorem measureReal_rayCross_le {Q : Multigraph W F} (hloop : Q.Loopless)
    (hdeg : Q.MaxDegreeLE 3) {q : ℝ} (hq : 0 ≤ q) {R : ℕ} {ρ₀ : ℝ} (hρ₀ : -1 < ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) (c : Fin 3) (e₁ e₂ : F) :
    (Measure.pi fun _ : W => blockMeasure).real
      {ω | rayCross c (edgeVec2 Q q R ω e₁) (edgeVec2 Q q R ω e₂)} ≤
        arccos ⟪edgeVector Q q R e₁, edgeVector Q q R e₂⟫ / (2 * π) := by
  set P := Measure.pi fun _ : W => blockMeasure
  set A : Set (W → BlockSample) :=
    {ω | rayCross c (edgeVec2 Q q R ω e₁) (edgeVec2 Q q R ω e₂)}
  set Aneg : Set (W → BlockSample) := (fun ω : W → BlockSample => fun B => negSample (ω B)) ⁻¹' A
  have hAm : MeasurableSet A := measurableSet_rayCross_edgeVec2 Q q R c e₁ e₂
  have hmp_neg : MeasurePreserving (fun ω : W → BlockSample => fun B => negSample (ω B)) P P :=
    measurePreserving_pi _ _ fun _ => measurePreserving_negSample
  have hdisj : Disjoint A Aneg := disjoint_left.mpr fun ω h1 h2 =>
    rayCross_disjoint_neg2 c _ _
      ⟨h1, by simpa only [A, Aneg, mem_preimage, mem_ofPred_eq, edgeVec2_negSample] using h2⟩
  let proj_n (ω : W → BlockSample) : W → ℝ := fun B => dot2 (normVec c) (ω B).1
  have hmp_n : MeasurePreserving proj_n P (Measure.pi fun _ : W => gaussianReal 0 1) :=
    measurePreserving_pi _ _ fun _ =>
      (measurePreserving_dot2_unit (normVec_sq c)).comp
        (MeasureTheory.measurePreserving_fst (μ := gauss2) (ν := gaussTie))
  set U := {g : W → ℝ | (0 : ℝ) ∈ Ι (edgeScore Q q R g e₁) (edgeScore Q q R g e₂)}
  have hUm : MeasurableSet U :=
    measurableSet_setOf_mem_uIoc (measurable_edgeScore q R e₁) (measurable_edgeScore q R e₂) 0
  have hsub : A ∪ Aneg ⊆ proj_n ⁻¹' U := fun ω hω => by
    simp only [mem_union, A, Aneg, mem_preimage, mem_ofPred_eq, edgeVec2_negSample] at hω
    simpa only [mem_preimage, U, mem_ofPred_eq, proj_n, ← dot2_edgeVec2] using
      rayCross_or_neg2_imp_mem_uIoc c _ _ hω
  have hunit (e : F) : ‖edgeVector Q q R e‖ = 1 := norm_edgeVector hloop hdeg hq hρ₀ hρ e
  have h2A : 2 * P.real A ≤ arccos ⟪edgeVector Q q R e₁, edgeVector Q q R e₂⟫ / π := by
    calc 2 * P.real A = P.real A + P.real Aneg := by
          rw [hmp_neg.measureReal_preimage hAm.nullMeasurableSet]; ring
      _ = P.real (A ∪ Aneg) := (measureReal_union hdisj (hAm.preimage hmp_neg.measurable)).symm
      _ ≤ P.real (proj_n ⁻¹' U) :=
          ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
      _ = (Measure.pi fun _ : W => gaussianReal 0 1).real U :=
          hmp_n.measureReal_preimage hUm.nullMeasurableSet
      _ ≤ arccos ⟪edgeVector Q q R e₁, edgeVector Q q R e₂⟫ / π := by
          rw [← InnerProductGeometry.angle_eq_arccos_inner_of_norm_eq_one (hunit e₁) (hunit e₂)]
          exact measureReal_mem_uIoc_le ((hunit e₁).trans (hunit e₂).symm) 0
  rw [le_div_iff₀ (by positivity)]
  linarith [(le_div_iff₀ pi_pos).mp h2A]

/-- **Expected `badCount` at a degree-`3` block.** At any block `B` with
`(Q.incidenceSet B).ncard = 3`, `E[badCount Q q R · B] ≤ capAt ρ₀`. -/
private theorem integral_badCount_le_capAt {Q : Multigraph W F} (hloop : Q.Loopless)
    (hdeg : Q.MaxDegreeLE 3) {q : ℝ} (hq : 0 ≤ q) {R : ℕ} {ρ₀ : ℝ}
    (hρ₀ : 0 ≤ ρ₀) (hρ_lt : ρ₀ < 1)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R)
    {B : W} (h3 : (Q.incidenceSet B).ncard = 3) :
    ∫ ω, (badCount Q q R ω B : ℝ) ∂(Measure.pi fun _ : W => blockMeasure) ≤ capAt ρ₀ := by
  classical
  have := Fintype.ofFinite F
  set P := Measure.pi fun _ : W => blockMeasure
  obtain ⟨e₀, e₁, e₂, h01, h02, h12, hinc_set⟩ := ncard_eq_three.mp h3
  set s : Finset F := {e₀, e₁, e₂}
  have hs_inc : (s : Set F) = Q.incidenceSet B := by simp [s, hinc_set]
  have hs_toFin : s = (Q.incidenceSet B).toFinset := by ext e; simp [← hs_inc]
  have hs_card : s.card = 3 := Finset.card_eq_three.2 ⟨_, _, _, h01, h02, h12, rfl⟩
  have hoff_card : (s.offDiag.card : ℝ) = 6 := by simp [Finset.offDiag_card, hs_card]
  have hunit (e : F) : ‖edgeVector Q q R e‖ = 1 :=
    norm_edgeVector hloop hdeg hq (by linarith) hρ e
  have hcap_vec (e : F) (he : e ∈ s) :
      √((1 + ρ₀) / 2) ≤ ⟪edgeVector Q q R e, unitKernelRow Q.toSimpleGraph q R B⟫ :=
    le_inner_edgeVector hloop hdeg hq hρ₀ hρ (by rw [← hs_inc]; exact he)
  have hpair_mem (p : F × F) (hp : p ∈ s.offDiag) :
      ⟪edgeVector Q q R p.1, edgeVector Q q R p.2⟫ ∈ Icc 0 1 := by
    obtain ⟨h1, h2, -⟩ := Finset.mem_offDiag.mp hp
    refine ⟨?_, (real_inner_le_norm _ _).trans_eq (by rw [hunit, hunit, one_mul])⟩
    have := InnerProductGeometry.two_mul_sq_sub_one_le_inner (norm_unitKernelRow q R B)
      (hunit p.1) (hunit p.2) (sqrt_nonneg _) (hcap_vec _ h1) (hcap_vec _ h2)
    rw [sq_sqrt (by linarith)] at this
    linarith
  let proj2 (ω : W → BlockSample) : (W → ℝ) × (W → ℝ) :=
    (fun B' => (ω B').1.1, fun B' => (ω B').1.2)
  have hmp_proj2 : MeasurePreserving proj2 P
      ((Measure.pi fun _ : W => gaussianReal 0 1).prod
        (Measure.pi fun _ : W => gaussianReal 0 1)) :=
    (measurePreserving_arrowProdEquivProdArrow ℝ ℝ W (fun _ => gaussianReal 0 1)
      (fun _ => gaussianReal 0 1)).comp (measurePreserving_pi _ _ fun _ =>
        MeasureTheory.measurePreserving_fst (μ := gauss2) (ν := gaussTie))
  set NullTie : Set (W → BlockSample) := {ω | ¬Function.Injective (ω B).2}
  set NullRay : Set (W → BlockSample) :=
    ⋃ e ∈ s, ⋃ c : Fin 3, {ω | dot2 (normVec c) (edgeVec2 Q q R ω e) = 0}
  set NullDet : Set (W → BlockSample) :=
    ⋃ p ∈ s.offDiag.filter (fun p => edgeVector Q q R p.1 ≠ edgeVector Q q R p.2),
      {ω | det2 (edgeVec2 Q q R ω p.1) (edgeVec2 Q q R ω p.2) = 0}
  set NullB := NullTie ∪ (NullRay ∪ NullDet)
  have hNullB_null : P NullB = 0 := by
    refine measure_union_null
      ((measureReal_eq_zero_iff (measure_ne_top _ _)).mp (measureReal_not_injective_tie_zero B))
      (measure_union_null ((measure_biUnion_null_iff s.countable_toSet).mpr fun e _ =>
        measure_iUnion_null fun c => measure_dot2_edgeVec2_eq_zero (hunit e) c)
      ((measure_biUnion_null_iff (Finset.countable_toSet _)).mpr fun p hp => ?_))
    obtain ⟨hp_off, hne_vec⟩ := Finset.mem_filter.mp hp
    set Sd : Set ((W → ℝ) × (W → ℝ)) :=
      {g | det2 (⟪edgeVector Q q R p.1, WithLp.toLp 2 g.1⟫,
                  ⟪edgeVector Q q R p.1, WithLp.toLp 2 g.2⟫)
                (⟪edgeVector Q q R p.2, WithLp.toLp 2 g.1⟫,
                  ⟪edgeVector Q q R p.2, WithLp.toLp 2 g.2⟫) = 0}
    have hSm : MeasurableSet Sd :=
      (isClosed_eq (by unfold det2; fun_prop) continuous_const).measurableSet
    refine (measureReal_eq_zero_iff (measure_ne_top _ _)).mp ?_
    change P.real (proj2 ⁻¹' Sd) = 0
    rw [hmp_proj2.measureReal_preimage hSm.nullMeasurableSet]
    exact measureReal_pi_prod_det2_eq_zero (hunit p.1) (hunit p.2)
      (by linarith [(hpair_mem p hp_off).1]) hne_vec
  let RC (p : F × F) (c : Fin 3) : Set (W → BlockSample) :=
    {ω | rayCross c (edgeVec2 Q q R ω p.1) (edgeVec2 Q q R ω p.2)}
  set Sconv : Set ((W → ℝ) × (W → ℝ)) :=
    {g | ∃ w₀ w₁ w₂ : ℝ, 0 ≤ w₀ ∧ 0 ≤ w₁ ∧ 0 ≤ w₂ ∧ w₀ + w₁ + w₂ = 1 ∧
      w₀ * ⟪edgeVector Q q R e₀, WithLp.toLp 2 g.1⟫ +
        w₁ * ⟪edgeVector Q q R e₁, WithLp.toLp 2 g.1⟫ +
        w₂ * ⟪edgeVector Q q R e₂, WithLp.toLp 2 g.1⟫ = 0 ∧
      w₀ * ⟪edgeVector Q q R e₀, WithLp.toLp 2 g.2⟫ +
        w₁ * ⟪edgeVector Q q R e₁, WithLp.toLp 2 g.2⟫ +
        w₂ * ⟪edgeVector Q q R e₂, WithLp.toLp 2 g.2⟫ = 0}
  set Conv : Set (W → BlockSample) := proj2 ⁻¹' Sconv
  have hRC_m (p : F × F) (c : Fin 3) : MeasurableSet (RC p c) :=
    measurableSet_rayCross_edgeVec2 Q q R c p.1 p.2
  have hSconv_m : MeasurableSet Sconv := by
    have hcg (e : F) : Continuous fun g : (W → ℝ) × (W → ℝ) =>
        (⟪edgeVector Q q R e, WithLp.toLp 2 g.1⟫, ⟪edgeVector Q q R e, WithLp.toLp 2 g.2⟫) := by
      fun_prop
    exact measurableSet_convex_zero_three (hcg e₀) (hcg e₁) (hcg e₂)
  have hConv_m : MeasurableSet Conv := hSconv_m.preimage hmp_proj2.measurable
  have hint_bad : Integrable (fun ω => (badCount Q q R ω B : ℝ)) P :=
    integrable_badCount hdeg q R B
  have hint1 {S : Set (W → BlockSample)} (hSm : MeasurableSet S) :
      Integrable (S.indicator (1 : (W → BlockSample) → ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator hSm
  let rhsFn (ω : W → BlockSample) : ℝ :=
    (∑ p ∈ s.offDiag, ∑ c : Fin 3, (RC p c).indicator (1 : (W → BlockSample) → ℝ) ω) +
      2 * Conv.indicator (1 : (W → BlockSample) → ℝ) ω
  have hint_sum : Integrable (fun ω => ∑ p ∈ s.offDiag, ∑ c : Fin 3,
      (RC p c).indicator (1 : (W → BlockSample) → ℝ) ω) P :=
    integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun c _ => hint1 (hRC_m p c)
  have hint_rhs : Integrable rhsFn P := hint_sum.add ((hint1 hConv_m).const_mul 2)
  have hae_le : (fun ω => 4 * (badCount Q q R ω B : ℝ)) ≤ᵐ[P] rhsFn := by
    filter_upwards [compl_mem_ae_iff.mpr hNullB_null] with ω hω
    simp only [NullB, NullTie, NullRay, NullDet, mem_compl_iff, mem_union, mem_iUnion,
      mem_ofPred_eq, not_or, not_exists, not_not] at hω
    obtain ⟨hinj, hray_ω, hdet_ω⟩ := hω
    have hdet_sec : ∀ a ∈ s, ∀ b ∈ s, ∀ c₁ c₂ : Fin 3,
        inOpenSector c₁ (edgeVec2 Q q R ω a) → inOpenSector c₂ (edgeVec2 Q q R ω b) →
        c₁ ≠ c₂ → det2 (edgeVec2 Q q R ω a) (edgeVec2 Q q R ω b) ≠ 0 :=
      fun a ha b hb _ _ hc₁ hc₂ hne_c => by
        have hab : a ≠ b := by rintro rfl; exact hne_c (inOpenSector_unique hc₁ hc₂)
        have hvec_ne : edgeVector Q q R a ≠ edgeVector Q q R b := fun heq =>
          hne_c (inOpenSector_unique (by simpa only [edgeVec2, edgeScore, heq] using hc₁) hc₂)
        exact hdet_ω (a, b) (Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩, hvec_ne⟩)
    have hreal := Nat.cast_le (α := ℝ).mpr
      (four_mul_badCount_le h01 h12 h02 hs_toFin hinj hray_ω hdet_sec)
    push_cast [rhsFn, indicator_apply, RC, mem_ofPred_eq] at hreal
    exact hreal
  have hint_ineq : 4 * ∫ ω, (badCount Q q R ω B : ℝ) ∂P ≤ ∫ ω, rhsFn ω ∂P := by
    rw [← integral_const_mul]; exact integral_mono_ae (hint_bad.const_mul 4) hint_rhs hae_le
  have hint_rhs_eq : ∫ ω, rhsFn ω ∂P =
      (∑ p ∈ s.offDiag, ∑ c : Fin 3, P.real (RC p c)) + 2 * P.real Conv := by
    dsimp [rhsFn]
    rw [integral_add hint_sum ((hint1 hConv_m).const_mul 2), integral_const_mul,
      integral_indicator_one hConv_m,
      integral_finsetSum _ fun p _ => integrable_finsetSum _ fun c _ => hint1 (hRC_m p c)]
    congr 1
    exact Finset.sum_congr rfl fun p _ =>
      (integral_finsetSum _ fun c _ => hint1 (hRC_m p c)).trans
        (Finset.sum_congr rfl fun c _ => integral_indicator_one (hRC_m p c))
  have hpart1 : (∑ p ∈ s.offDiag, ∑ c : Fin 3, P.real (RC p c)) ≤ 6 * straddleBound ρ₀ := by
    have hinner_sum : 6 * ((1 + 3 * ρ₀) / 4) ≤
        ∑ p ∈ s.offDiag, ⟪edgeVector Q q R p.1, edgeVector Q q R p.2⟫ := by
      have h := InnerProductGeometry.le_sum_offDiag_inner (norm_unitKernelRow q R B)
        (s := s) (y := edgeVector Q q R) (fun e _ => hunit e) (sqrt_nonneg _) hcap_vec
      rw [hs_card, sq_sqrt (by linarith)] at h
      linarith
    have hjensen := Real.sum_arccos_le_card_mul_arccos s.offDiag hpair_mem
      (by rw [hoff_card]; exact hinner_sum)
    rw [hoff_card] at hjensen
    calc (∑ p ∈ s.offDiag, ∑ c : Fin 3, P.real (RC p c))
        ≤ ∑ p ∈ s.offDiag, ∑ _c : Fin 3,
            arccos ⟪edgeVector Q q R p.1, edgeVector Q q R p.2⟫ / (2 * π) :=
          Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun c _ =>
            measureReal_rayCross_le hloop hdeg hq (by linarith) hρ c p.1 p.2
      _ = 3 / (2 * π) * ∑ p ∈ s.offDiag, arccos ⟪edgeVector Q q R p.1, edgeVector Q q R p.2⟫ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun p _ => by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ 3 / (2 * π) * (6 * arccos ((1 + 3 * ρ₀) / 4)) := by gcongr
      _ = 6 * straddleBound ρ₀ := by unfold straddleBound; ring
  have hpart2 : P.real Conv ≤ 1 - √((1 + ρ₀) / 2) := by
    rw [hmp_proj2.measureReal_preimage hSconv_m.nullMeasurableSet]
    exact measureReal_pi_prod_convex_zero_le (norm_unitKernelRow q R B)
      (sqrt_pos.mpr (by linarith)) (sqrt_le_one.mpr (by linarith))
      (hcap_vec e₀ (by simp [s])) (hcap_vec e₁ (by simp [s])) (hcap_vec e₂ (by simp [s]))
      (hunit e₀).le (hunit e₁).le (hunit e₂).le
  rw [hint_rhs_eq] at hint_ineq
  unfold capAt
  linarith only [hint_ineq, hpart1, hpart2]

end DegreeThreeCap

end Cslib.Circuits.Frontier.TensorRank
