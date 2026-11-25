/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.GameTheory.Mechanism.Approximation.LaviSwamy
public import CslibFrontier.GameTheory.Mechanism.Approximation.RelatedScheduling
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Checked Witnesses for Truthful Approximation Mechanisms (NRTV Ch. 12)

Concrete non-vacuous witnesses exercising:

1. **Lavi–Swamy LP convex decomposition** (`LaviSwamy`):
   * The `3`-item pairwise-conflict (triangle) packing polytope `P` with fractional optimum
     `x* = (1/2, 1/2, 1/2)` and exact integrality gap `α = 3/2`.
   * Explicit convex decomposition of `(2/3) • x* = (1/3, 1/3, 1/3)` with exact expectation
     identity `E[v(ω)] = (1 / α) * (v ⬝ᵥ x*)`, plus convex-hull membership via
     `scaled_mem_convexHull_of_integralityGap`.
   * Non-vacuous instantiation of `exists_laviSwamyExPost_of_isCompact` on `P`.
2. **Archer–Tardos & related-machine scheduling** (`RelatedScheduling`):
   * Explicit threshold work rule `q(c) = if c ≤ 2 then 1 else 0` whose Archer–Tardos payment at
     `c = 1` equals the critical threshold `2`.
   * Concrete `2`-machine, `2`-job related-machine instance instantiating `lexOptMechanism_isDSIC`,
     `lexOptMechanism_isIR`, and exact makespan `optRelatedMakespan = 2`.
-/

namespace CslibFrontierTests.MechanismApproximationNRTV

open Finset Matrix
open Cslib.GameTheory.Mechanism

private theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr rfl

/-! ### 1. Lavi–Swamy Triangle Packing Polytope Witness (`α = 3/2`) -/

section LaviSwamyWitness

open LaviSwamy

/-- The triangle pairwise-conflict packing polytope in `ℝ³`:
`0 ≤ x`, `x₀ + x₁ ≤ 1`, `x₁ + x₂ ≤ 1`, `x₂ + x₀ ≤ 1`. -/
@[expose] public def trianglePolytope : Set (Fin 3 → ℝ) :=
  {x | (∀ k, 0 ≤ x k) ∧ x 0 + x 1 ≤ 1 ∧ x 1 + x 2 ≤ 1 ∧ x 2 + x 0 ≤ 1}

/-- The four integral packings in `trianglePolytope`: `none ↦ 0` and `some k ↦ e_k`. -/
@[expose] public def triangleEmbed : Option (Fin 3) → Fin 3 → ℝ
  | none => 0
  | some k => Pi.single k 1

private theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- The fractional vertex `x* = (1/2, 1/2, 1/2)` belongs to `trianglePolytope`, and `(2/3) • x*`
equals the uniform convex combination `(1/3, 1/3, 1/3)` of the three singleton packings, giving
the exact expectation identity `E[v ⬝ᵥ embed ω] = (1 / (3/2)) * (v ⬝ᵥ x*)`. -/
public theorem triangle_explicit_decomposition (v : Fin 3 → ℝ) :
    let xStar : Fin 3 → ℝ := fun _ => 1 / 2
    xStar ∈ trianglePolytope ∧
      ∃ p : PMF (Option (Fin 3)),
        (∑ ω, (p ω).toReal • triangleEmbed ω) = (1 / (3 / 2 : ℝ)) • xStar ∧
        expectedVal p (fun ω => v ⬝ᵥ triangleEmbed ω) = (1 / (3 / 2 : ℝ)) * (v ⬝ᵥ xStar) := by
  intro xStar
  have hx : xStar ∈ trianglePolytope := by
    refine ⟨fun _ => by norm_num [xStar], ?_, ?_, ?_⟩ <;> norm_num [xStar]
  let μ : Option (Fin 3) → ℝ
    | none => 0
    | some _ => 1 / 3
  have hμ_nonneg : ∀ ω, 0 ≤ μ ω := fun ω => by cases ω <;> norm_num [μ]
  have hμ_sum : ∑ ω : Option (Fin 3), μ ω = 1 := by
    rw [Fintype.sum_option, Fin.sum_univ_three]
    norm_num [μ]
  let p := pmfOfRealWeights μ hμ_nonneg hμ_sum
  have hdecomp : ∑ ω : Option (Fin 3), (p ω).toReal • triangleEmbed ω =
      (1 / (3 / 2 : ℝ)) • xStar := by
    funext k
    simp only [p, pmfOfRealWeights_toReal, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Fintype.sum_option, Fin.sum_univ_three]
    rcases fin3_cases k with rfl | rfl | rfl <;>
      simp [μ, triangleEmbed, xStar] <;> norm_num
  refine ⟨hx, p, hdecomp, ?_⟩
  rw [expectedVal_dotProduct, hdecomp, dotProduct_smul, smul_eq_mul]

/-- The triangle polytope satisfies `VerifiesIntegralityGap trianglePolytope triangleEmbed (3/2)`
and yields a non-vacuous instance of `exists_laviSwamyExPost_of_isCompact`. -/
public theorem triangle_laviSwamy_nonvacuous :
    VerifiesIntegralityGap trianglePolytope triangleEmbed (3 / 2) ∧
      ∃ M : RandomizedLinearMechanism (Fin 3) (Option (Fin 3)) (Fin 3),
        M.IsTruthfulInExpectationOn triangleEmbed nonnegValProfiles ∧
        M.IsExPostIROn triangleEmbed nonnegValProfiles ∧
        M.IsExPostNPTOn nonnegValProfiles ∧
        ∀ b : Fin 3 → Fin 3 → ℝ, ∀ ω : Option (Fin 3),
          (1 / (3 / 2 : ℝ)) * (∑ i : Fin 3, b i ⬝ᵥ triangleEmbed ω) ≤
            M.expectedWelfare triangleEmbed b := by
  have hdown : ∀ (ω : Option (Fin 3)) (S : Finset (Fin 3)), ∃ ω' : Option (Fin 3),
      ∀ k : Fin 3, triangleEmbed ω' k = if k ∈ S then triangleEmbed ω k else 0 := by
    intro ω S
    cases ω with
    | none =>
      refine ⟨none, fun k => ?_⟩
      simp only [triangleEmbed, Pi.zero_apply, ite_self]
    | some j =>
      by_cases hj : j ∈ S
      · refine ⟨some j, fun k => ?_⟩
        by_cases hkj : k = j
        · subst hkj; simp only [hj, ↓reduceIte]
        · simp only [triangleEmbed, Pi.single_eq_of_ne hkj, ite_self]
      · refine ⟨none, fun k => ?_⟩
        by_cases hkj : k = j
        · subst hkj; simp only [hj, ↓reduceIte, triangleEmbed, Pi.zero_apply]
        · simp only [triangleEmbed, Pi.zero_apply, Pi.single_eq_of_ne hkj, ite_self]
  have hgap : VerifiesIntegralityGap trianglePolytope triangleEmbed (3 / 2) := by
    intro w x hx
    refine integralityGap_of_nonneg_approx (by norm_num) hx.1 hdown (fun u hu => ?_) w
    have hsum_le : x 0 + x 1 + x 2 ≤ 3 / 2 := by linarith [hx.2.1, hx.2.2.1, hx.2.2.2]
    obtain ⟨k0, -, hk0⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 3)) u
      Finset.univ_nonempty
    refine ⟨some k0, ?_⟩
    have hdot_embed : u ⬝ᵥ triangleEmbed (some k0) = u k0 := by
      simp only [dotProduct, triangleEmbed, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [hdot_embed]
    have hdot_le : u ⬝ᵥ x ≤ u k0 * (x 0 + x 1 + x 2) := by
      simp only [dotProduct, Fin.sum_univ_three]
      have h0 : u 0 * x 0 ≤ u k0 * x 0 :=
        mul_le_mul_of_nonneg_right (hk0 0 (Finset.mem_univ 0)) (hx.1 0)
      have h1 : u 1 * x 1 ≤ u k0 * x 1 :=
        mul_le_mul_of_nonneg_right (hk0 1 (Finset.mem_univ 1)) (hx.1 1)
      have h2 : u 2 * x 2 ≤ u k0 * x 2 :=
        mul_le_mul_of_nonneg_right (hk0 2 (Finset.mem_univ 2)) (hx.1 2)
      linarith
    have huk0_nonneg : 0 ≤ u k0 := hu k0
    nlinarith
  have hP_closed : IsClosed trianglePolytope := by
    have h0 : IsClosed {x : Fin 3 → ℝ | ∀ k, 0 ≤ x k} := by
      rw [Set.ofPred_forall]
      exact isClosed_iInter fun k => isClosed_le continuous_const (continuous_apply k)
    have h1 : IsClosed {x : Fin 3 → ℝ | x 0 + x 1 ≤ 1} :=
      isClosed_le ((continuous_apply 0).add (continuous_apply 1)) continuous_const
    have h2 : IsClosed {x : Fin 3 → ℝ | x 1 + x 2 ≤ 1} :=
      isClosed_le ((continuous_apply 1).add (continuous_apply 2)) continuous_const
    have h3 : IsClosed {x : Fin 3 → ℝ | x 2 + x 0 ≤ 1} :=
      isClosed_le ((continuous_apply 2).add (continuous_apply 0)) continuous_const
    exact h0.inter (h1.inter (h2.inter h3))
  have hP_sub : trianglePolytope ⊆ Set.pi Set.univ fun _ : Fin 3 => Set.Icc (0 : ℝ) 1 := by
    intro x hx k _
    refine ⟨hx.1 k, ?_⟩
    rcases fin3_cases k with rfl | rfl | rfl
    · linarith [hx.1 1, hx.2.1]
    · linarith [hx.1 0, hx.2.1]
    · linarith [hx.1 1, hx.2.2.1]
  have hP_compact : IsCompact trianglePolytope :=
    (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hP_closed hP_sub
  have hembed : ∀ ω, triangleEmbed ω ∈ trianglePolytope := fun ω => by
    cases ω with
    | none => refine ⟨fun _ => le_rfl, ?_, ?_, ?_⟩ <;> norm_num [triangleEmbed]
    | some j =>
      rcases fin3_cases j with rfl | rfl | rfl <;> refine ⟨fun k => ?_, ?_, ?_, ?_⟩
      all_goals try (rcases fin3_cases k with rfl | rfl | rfl <;> simp [triangleEmbed])
      all_goals simp [triangleEmbed]
  obtain ⟨M, hTIE, hIR, hNPT, -, hApprox⟩ :=
    exists_laviSwamyExPost_of_isCompact (ι := Fin 3) (by norm_num) hP_compact
      ⟨0, hembed none⟩ (fun x hx => hx.1) hembed hgap
  exact ⟨hgap, M, hTIE, hIR, hNPT, hApprox⟩

/-- Exercise `scaled_mem_convexHull_of_integralityGap` on the triangle packing vertex
`x* = (1/2, 1/2, 1/2)` with integrality gap `α = 3/2`. -/
public theorem triangle_scaled_mem_convexHull :
    (1 / (3 / 2 : ℝ)) • (fun _ : Fin 3 => (1 / 2 : ℝ)) ∈
      convexHull ℝ (Set.range triangleEmbed) := by
  have hx : (fun _ : Fin 3 => (1 / 2 : ℝ)) ∈ trianglePolytope := by
    refine ⟨fun _ => by norm_num, ?_, ?_, ?_⟩ <;> norm_num
  exact scaled_mem_convexHull_of_integralityGap triangleEmbed
    (fun w => triangle_laviSwamy_nonvacuous.1 w _ hx)

end LaviSwamyWitness

/-! ### 2. Archer–Tardos and Related-Machine Scheduling Witnesses -/

section RelatedWitnesses

open RelatedScheduling MeasureTheory

/-- Threshold work rule on one agent: gets `1` unit of work iff reported unit cost is `≤ 2`.
Its Archer–Tardos payment at cost `1` is `1 * 1 + ∫_{1}^{2} 1 = 2`, the critical threshold. -/
@[expose] public noncomputable def thresholdWork : (Unit → ℝ) → Unit → ℝ :=
  fun c _ => if c () ≤ 2 then 1 else 0

public theorem thresholdWork_archerTardos_payment :
    archerTardosPayment thresholdWork (fun _ => 1) () = 2 := by
  have hint_eq : (∫ x in Set.Ioi (1 : ℝ), thresholdWork (Function.update (fun _ => 1) () x) ()) =
      1 := by
    have hunion : Set.Ioi (1 : ℝ) = Set.Ioc 1 2 ∪ Set.Ioi 2 :=
      (Set.Ioc_union_Ioi_eq_Ioi (by norm_num)).symm
    have hf1 : IntegrableOn (fun x : ℝ => if x ≤ 2 then (1 : ℝ) else 0) (Set.Ioc 1 2) volume := by
      have hmeas : volume (Set.Ioc (1 : ℝ) 2) ≠ ⊤ := by
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top
      refine (integrableOn_const (C := (1 : ℝ)) (hs := hmeas)).congr_fun
        (fun x hx => ?_) measurableSet_Ioc
      simp only [hx.2, ↓reduceIte]
    have hf2 : IntegrableOn (fun x : ℝ => if x ≤ 2 then (1 : ℝ) else 0) (Set.Ioi 2) volume := by
      refine (integrableOn_zero (μ := volume) (s := Set.Ioi 2)).congr_fun
        (fun x hx => ?_) measurableSet_Ioi
      have hgt : ¬x ≤ 2 := not_le.2 (Set.mem_Ioi.1 hx)
      simp only [hgt, ↓reduceIte]
    have hfun : (fun x : ℝ => thresholdWork (Function.update (fun _ => 1) () x) ()) =
        fun x : ℝ => if x ≤ 2 then 1 else 0 := by
      funext x
      simp only [thresholdWork, Function.update_self]
    rw [hfun, hunion, setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hf1 hf2]
    have hIoc : ∫ x in Set.Ioc (1 : ℝ) 2, (if x ≤ 2 then (1 : ℝ) else 0) = 1 := by
      have hcongr : Set.EqOn (fun x : ℝ => if x ≤ 2 then (1 : ℝ) else 0) (fun _ => (1 : ℝ))
          (Set.Ioc 1 2) := fun x hx => by simp only [hx.2, ↓reduceIte]
      rw [setIntegral_congr_fun measurableSet_Ioc hcongr, setIntegral_const, Measure.real,
        Real.volume_Ioc]
      norm_num
    have hIoi : ∫ x in Set.Ioi (2 : ℝ), (if x ≤ 2 then (1 : ℝ) else 0) = 0 := by
      have hcongr : Set.EqOn (fun x : ℝ => if x ≤ 2 then (1 : ℝ) else 0) (fun _ => (0 : ℝ))
          (Set.Ioi 2) := fun x hx => by
            have hgt : ¬x ≤ 2 := not_le.2 (Set.mem_Ioi.1 hx)
            simp only [hgt, ↓reduceIte]
      rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_zero]
    rw [hIoc, hIoi, add_zero]
  rw [archerTardosPayment, hint_eq]
  norm_num [thresholdWork]

/-- Non-vacuous `2`-machine, `2`-job related-machine witness (`w = ![1, 2]`, `c = ![1, 2]`):
`lexOptMechanism` is DSIC and IR, and achieves exact `optRelatedMakespan = 2`. -/
public theorem related_two_machines_witness :
    letI : LinearOrder (Fin 2 → Fin 2) := LinearOrder.lift' (Fintype.equivFin (Fin 2 → Fin 2))
      (Fintype.equivFin (Fin 2 → Fin 2)).injective
    let w : Fin 2 → ℝ := ![1, 2]
    let c : Fin 2 → ℝ := ![1, 2]
    (lexOptMechanism (M := Fin 2) (J := Fin 2) w).IsDSIC ∧
      (lexOptMechanism (M := Fin 2) (J := Fin 2) w).IsIR ∧
      optRelatedMakespan w c = 2 := by
  let : LinearOrder (Fin 2 → Fin 2) := LinearOrder.lift' (Fintype.equivFin (Fin 2 → Fin 2))
    (Fintype.equivFin (Fin 2 → Fin 2)).injective
  let w : Fin 2 → ℝ := ![1, 2]
  let c : Fin 2 → ℝ := ![1, 2]
  have hw : ∀ j : Fin 2, 0 ≤ w j := fun j => by fin_cases j <;> norm_num [w]
  have hc : c ∈ posCosts := fun i => by fin_cases i <;> norm_num [c]
  refine ⟨lexOptMechanism_isDSIC hw, lexOptMechanism_isIR hw, ?_⟩
  apply le_antisymm
  · let aStar : Fin 2 → Fin 2 := ![1, 0]
    refine (optRelatedMakespan_le w c aStar).trans
      ((relatedMakespan_le_iff w c aStar).2 fun i => ?_)
    rcases fin2_cases i with rfl | rfl
    · have hf : (Finset.univ.filter fun j : Fin 2 => aStar j = 0) = {1} := by decide
      rw [work, hf, Finset.sum_singleton]; norm_num [w, c]
    · have hf : (Finset.univ.filter fun j : Fin 2 => aStar j = 1) = {0} := by decide
      rw [work, hf, Finset.sum_singleton]; norm_num [w, c]
  · have hvol := sum_weight_le_optRelatedMakespan_mul_sum_inv (w := w) hc
    simp only [Fin.sum_univ_two, w, c] at hvol
    norm_num at hvol
    linarith

end RelatedWitnesses

end CslibFrontierTests.MechanismApproximationNRTV
