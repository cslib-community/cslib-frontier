/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Basic
public import CslibFrontier.Computability.Circuit.Frontier.TensorRank.ThreeWayCut.Coefficient
-- `import all`: reads private `capAt` helpers from `Coefficient`, planar ray normals from
-- `PlanarGeometry`, `BlockSample` / `blockMeasure` from `SampleSpace`, quotient coloring / cut
-- marginals from `QuotientColoring`, `badCount` / `sum_cutAny_le_sum_badCount` from
-- `BadCountPointwise`, and `integral_badCount_le_capAt` from `DegreeThreeCap`.
import all CslibFrontier.Computability.Circuit.Frontier.TensorRank.ThreeWayCut.Coefficient
import all CslibFrontier.Computability.Circuit.Frontier.TensorRank.ThreeWayCut.PlanarGeometry
import all CslibFrontier.Computability.Circuit.Frontier.TensorRank.ThreeWayCut.SampleSpace
import all CslibFrontier.Computability.Circuit.Frontier.TensorRank.ThreeWayCut.QuotientColoring
import all CslibFrontier.Computability.Circuit.Frontier.TensorRank.ThreeWayCut.BadCountPointwise
import all CslibFrontier.Computability.Circuit.Frontier.TensorRank.ThreeWayCut.DegreeThreeCap
import CslibFrontier.Computability.Circuit.Frontier.Layouts.CappedCompression
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.Straddle
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Arccos
import CslibFrontier.Foundations.Probability.UnionBound
import CslibFrontier.Foundations.Probability.WeightedSecondMoment
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Global balanced `3`-way cut of connected loopless subcubic multigraphs

Combines weight-capped multigraph compression (`CappedCompression`), the `Z₃`-symmetric planar
Gaussian quotient coloring, and local Chebyshev concentration (`WeightedSecondMoment`) to prove
`exists_balanced_threeWayCut`.

## Main results

* `Cslib.Circuits.Frontier.TensorRank.exists_balanced_threeWayCut`: simultaneous `1 / 3`-balance on
  `A ⊆ V` and `(2 / 3) · threeWayCapCoefficient · β₁(G)` bound on all three pairwise edge cuts.
-/

public section

open MeasureTheory ProbabilityTheory Real Set

namespace Cslib.Circuits.Frontier.TensorRank

open Cslib.Circuits.Frontier.Gaussian Cslib.Circuits.Frontier.Multigraph

attribute [local instance]
  instIsProbabilityMeasure_gauss2
  instIsProbabilityMeasure_gaussTie
  instIsProbabilityMeasure_blockMeasure

/-! ### Parameter selection and the global balanced `3`-way cut theorem -/

private theorem exists_threeWay_params {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ (q : ℝ) (R : ℕ) (ρ₀ η : ℝ) (M : ℕ),
      0 ≤ q ∧ 0 ≤ ρ₀ ∧ ρ₀ < 1 ∧
      ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R ∧
      0 < η ∧ 2 ≤ M ∧
      capAt ρ₀ ≤ threeWayCapCoefficient + ξ / 4 ∧
      16 / (M : ℝ) + η ≤ ξ / 4 := by
  set g : ℝ := 2 * √2 / 3 with hg
  have hsqrt_lo : (7 : ℝ) / 5 < √2 := (lt_sqrt (by norm_num)).mpr (by norm_num)
  have hsqrt_hi : √2 < (3 : ℝ) / 2 := (sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hcont_cap : Continuous fun ρ : ℝ => capAt ρ := by
    unfold capAt straddleBound
    fun_prop
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp (hcont_cap.continuousAt (x := g))
    (ξ / 4) (by positivity)
  set ρ₀ := g - min δ (1 / 4) / 2
  have hmin : 0 < min δ (1 / 4) := lt_min hδ (by norm_num)
  have hρ₀_lt_g : ρ₀ < g := by dsimp [ρ₀]; linarith
  have hρ₀_nonneg : 0 ≤ ρ₀ := by
    dsimp [ρ₀, g]; linarith [min_le_right δ (1 / 4)]
  have hρ₀_lt_one : ρ₀ < 1 := by
    dsimp [ρ₀, g]; linarith
  have hcap_le : capAt ρ₀ ≤ threeWayCapCoefficient + ξ / 4 := by
    have hdist : dist ρ₀ g < δ := by
      rw [Real.dist_eq, show ρ₀ - g = -(min δ (1 / 4) / 2) by dsimp [ρ₀]; ring, abs_neg,
        abs_of_pos (by positivity)]
      linarith [min_le_left δ (1 / 4)]
    have hd := hclose hdist
    rw [Real.dist_eq, capAt_limit] at hd
    linarith [le_abs_self (capAt ρ₀ - threeWayCapCoefficient), hd]
  have hv3 : vertexCorrelation 3 = g := by norm_num [vertexCorrelation, g]
  obtain ⟨q, R, hq, hρ_raw⟩ := exists_decay_radius_degree (by norm_num : 2 ≤ 3)
    (ρ := ρ₀) (by rw [hv3]; exact hρ₀_lt_g)
  have hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R := by
    norm_num at hρ_raw; exact hρ_raw
  set η := ξ / 8
  have hη : 0 < η := by positivity
  set M : ℕ := ⌈128 / ξ⌉₊ + 2
  have hM2 : 2 ≤ M := by dsimp [M]; omega
  have hM_pos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hM_ge : 128 / ξ ≤ (M : ℝ) := by
    dsimp [M]; push_cast; linarith [Nat.le_ceil (128 / ξ)]
  have h16M : 16 / (M : ℝ) ≤ ξ / 8 := by
    rw [div_le_iff₀ hM_pos]
    have hmul := mul_le_mul_of_nonneg_left hM_ge hξ.le
    rw [mul_div_cancel₀ _ hξ.ne'] at hmul
    linarith only [hmul]
  exact ⟨q, R, ρ₀, η, M, hq, hρ₀_nonneg, hρ₀_lt_one, hρ, hη, hM2, hcap_le,
    by dsimp [η]; linarith only [h16M]⟩

/-- **Balanced `3`-way cut of a connected loopless subcubic multigraph.** For every `ξ > 0` there is
a constant `C₀ : ℕ` such that every finite connected loopless multigraph `G` of maximum degree at
most `3` and every subset `A ⊆ V` admit a vertex `3`-coloring `col : V → Fin 3` balancing `A` up to
`ξ |V| + C₀` on all three parts while keeping all three pairwise edge cuts at most
`(2 / 3) · threeWayCapCoefficient · β₁(G) + ξ |V| + C₀`. -/
theorem exists_balanced_threeWayCut {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ C₀ : ℕ, ∀ {V E : Type*} [Finite V] [Finite E] (G : Multigraph V E),
      G.Loopless → G.toSimpleGraph.Connected → G.MaxDegreeLE 3 →
      ∀ A : Set V, ∃ col : V → Fin 3,
        (∀ c : Fin 3,
          |((A ∩ {v | col v = c}).ncard : ℝ) - 1 / 3 * (A.ncard : ℝ)| ≤
            ξ * Nat.card V + C₀) ∧
        (∀ c : Fin 3,
          ((G.edgeCut {v | col v = c} ∩ G.edgeCut {v | col v = c + 1}).ncard : ℝ) ≤
            2 / 3 * threeWayCapCoefficient * (G.cycleRank : ℝ) + ξ * Nat.card V + C₀) := by
  obtain ⟨q, R, ρ₀, η, M, hq, hρ₀, hρ_lt, hρ, hη, hM2, hcap_le, hslack⟩ :=
    exists_threeWay_params hξ
  set D_blk := vertexOverlap 3 R
  set D_edg := vertexOverlap 3 (R + 1)
  set C₀ : ℕ := max M (⌈12 * ((M : ℝ) ^ 2 * ((D_blk : ℝ) + D_edg)) / η ^ 2⌉₊ + 1)
  refine ⟨C₀, fun {V E} _ _ G hloop hconn hdeg A => ?_⟩
  classical
  have := Fintype.ofFinite V
  have := Fintype.ofFinite E
  by_cases hsmall : Nat.card V ≤ C₀
  · -- Small-graph regime `|V| ≤ C₀`: the constant coloring `fun _ => 0` has `0` cut edges!
    refine ⟨fun _ => 0, fun c => ?_, fun c => ?_⟩
    · have hA_le : (A.ncard : ℝ) ≤ (C₀ : ℝ) :=
        Nat.cast_le.mpr ((ncard_le_card A).trans hsmall)
      have hA_nonneg : (0 : ℝ) ≤ A.ncard := Nat.cast_nonneg _
      have hv_nonneg : (0 : ℝ) ≤ ξ * Nat.card V := by positivity
      rcases c with ⟨_ | _ | _ | _, hlt⟩
      · change |((A ∩ {v : V | (0 : Fin 3) = 0}).ncard : ℝ) - 1 / 3 * (A.ncard : ℝ)| ≤ _
        have heq : A ∩ {v : V | (0 : Fin 3) = 0} = A := by simp
        rw [heq]
        have habs : |(A.ncard : ℝ) - 1 / 3 * (A.ncard : ℝ)| = 2 / 3 * (A.ncard : ℝ) := by
          rw [show (A.ncard : ℝ) - 1 / 3 * (A.ncard : ℝ) = 2 / 3 * (A.ncard : ℝ) by ring,
            abs_of_nonneg (by positivity)]
        rw [habs]
        linarith only [hA_le, hA_nonneg, hv_nonneg]
      · change |((A ∩ {v : V | (0 : Fin 3) = 1}).ncard : ℝ) - 1 / 3 * (A.ncard : ℝ)| ≤ _
        have heq : A ∩ {v : V | (0 : Fin 3) = 1} = ∅ := by ext; simp
        rw [heq, ncard_empty, Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
        linarith only [hA_le, hA_nonneg, hv_nonneg]
      · change |((A ∩ {v : V | (0 : Fin 3) = 2}).ncard : ℝ) - 1 / 3 * (A.ncard : ℝ)| ≤ _
        have heq : A ∩ {v : V | (0 : Fin 3) = 2} = ∅ := by ext; simp
        rw [heq, ncard_empty, Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
        linarith only [hA_le, hA_nonneg, hv_nonneg]
      · omega
    · have hempty : G.edgeCut {v : V | (0 : Fin 3) = c} ∩
          G.edgeCut {v : V | (0 : Fin 3) = c + 1} = ∅ := by
        rcases c with ⟨_ | _ | _ | _, hlt⟩
        · ext e
          change e ∈ G.edgeCut {v | (0 : Fin 3) = 0} ∩ G.edgeCut {v | (0 : Fin 3) = 1} ↔ _
          simp
        · ext e
          change e ∈ G.edgeCut {v | (0 : Fin 3) = 1} ∩ G.edgeCut {v | (0 : Fin 3) = 2} ↔ _
          simp
        · ext e
          change e ∈ G.edgeCut {v | (0 : Fin 3) = 2} ∩ G.edgeCut {v | (0 : Fin 3) = 0} ↔ _
          simp
        · omega
      rw [hempty, ncard_empty, Nat.cast_zero]
      have hpos_cap := threeWayCapCoefficient_pos
      positivity
  · -- Large-graph regime `C₀ < |V|`: compress with unit vertex weight and run `Z₃` Gaussian cut.
    push Not at hsmall
    have hM_lt_V : M < Nat.card V := (le_max_left _ _).trans_lt hsmall
    obtain ⟨cmp, hsat⟩ := CappedCompression.exists_saturated (G := G) (w := fun _ => 1)
      (d := 3) (M := M) hdeg fun _ => by omega
    set Q := cmp.quotient
    have hQ_loop : Q.Loopless := cmp.quotient_loopless
    have hQ_deg : Q.MaxDegreeLE 3 := cmp.quotient_maxDegreeLE
    -- Since every block has size `≤ M < |V|`, there are at least two blocks.
    have htwo : 1 < Nat.card cmp.blocks := by
      by_contra! hle1
      have hsum := cmp.sum_blockWeight_univ
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
        ← Nat.card_eq_fintype_card] at hsum
      have hleM : ∑ B : cmp.blocks, cmp.blockWeight B ≤ Nat.card cmp.blocks * M := by
        calc ∑ B : cmp.blocks, cmp.blockWeight B ≤ ∑ _B : cmp.blocks, M :=
              Finset.sum_le_sum fun B _ => cmp.blockWeight_le B
          _ = Nat.card cmp.blocks * M := by
              simp [Nat.card_eq_fintype_card]
      have hV_le : Nat.card V ≤ M := by
        rw [← hsum]
        exact hleM.trans (by nlinarith only [hle1])
      omega
    -- Block counts: `#cmp.blocks ≤ |V|`, `#cmp.external ≤ 2 |V|`, `#Q_{1,2} ≤ 8 |V| / M`,
    -- `#Q₃ ≤ 2 β₁ + #Q₁`.
    have hblocks_le_V : cmp.blocks.card ≤ Nat.card V := cmp.card_blocks_le
    have hext_le : 2 * Nat.card cmp.external ≤ 3 * Nat.card V := by
      have hhand := Q.sum_ncard_incidenceSet hQ_loop
      have hdeg_sum : ∑ B : cmp.blocks, (Q.incidenceSet B).ncard ≤ 3 * cmp.blocks.card := by
        calc ∑ B : cmp.blocks, (Q.incidenceSet B).ncard ≤ ∑ _B : cmp.blocks, 3 :=
              Finset.sum_le_sum fun B _ => hQ_deg B
          _ = 3 * cmp.blocks.card := by simp [Nat.mul_comm]
      omega
    have hG_edges_le : 2 * Nat.card E ≤ 3 * Nat.card V := by
      have hhand := G.sum_ncard_incidenceSet hloop
      have hdeg_sum : ∑ v : V, (G.incidenceSet v).ncard ≤ 3 * Nat.card V := by
        calc ∑ v : V, (G.incidenceSet v).ncard ≤ ∑ _v : V, 3 :=
              Finset.sum_le_sum fun v _ => hdeg v
          _ = 3 * Nat.card V := by simp [Nat.mul_comm, Nat.card_eq_fintype_card]
      omega
    have hbeta_le_V : G.cycleRank ≤ Nat.card V := by
      have hconnE := G.card_le_card_add_one_of_connected hconn
      unfold Multigraph.cycleRank
      omega
    set Q12 := Finset.univ.filter fun B : cmp.blocks =>
      1 ≤ (Q.incidenceSet B).ncard ∧ (Q.incidenceSet B).ncard ≤ 2
    set Q1 := Finset.univ.filter fun B : cmp.blocks => (Q.incidenceSet B).ncard = 1
    set Q3 := Finset.univ.filter fun B : cmp.blocks => (Q.incidenceSet B).ncard = 3
    have hQ12_real : (Q12.card : ℝ) ≤ 8 * (Nat.card V : ℝ) / (M : ℝ) := by
      have : M * Q12.card ≤ 8 * Nat.card V := by
        simpa [Q12, Nat.card_eq_fintype_card] using hsat.mul_card_deg_one_two_le
      rw [le_div_iff₀ (by positivity)]
      exact_mod_cast (by linarith : Q12.card * M ≤ 8 * Nat.card V)
    have hQ1_sub : Q1 ⊆ Q12 := fun B hB => by
      have h1 := (Finset.mem_filter.mp hB).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ B, by omega, by omega⟩
    have hQ1_le_Q12 : Q1.card ≤ Q12.card := Finset.card_le_card hQ1_sub
    have hQ3_le : Q3.card ≤ 2 * G.cycleRank + Q1.card :=
      cmp.card_deg_three_le_of_connected hloop hconn htwo
    -- Expected pairwise cut bound on `Q`:
    set P := Measure.pi fun _ : cmp.blocks => blockMeasure
    have hexp_cutAny :
        (∑ e : cmp.external, P.real (cutAnyEvent Q q R e)) ≤
          capAt ρ₀ * (Q3.card : ℝ) + 2 * (Q12.card : ℝ) := by
      -- Outside `NullAllRay`, `#{e | cutAnyEvent} ≤ ∑ B, badCount B`.
      set NullAllRay : Set (cmp.blocks → BlockSample) :=
        ⋃ e : cmp.external, ⋃ c : Fin 3, {ω | dot2 (normVec c) (edgeVec2 Q q R ω e) = 0}
      have hNullAllRay_null : P NullAllRay = 0 :=
        measure_iUnion_null fun e => measure_iUnion_null fun c =>
          measure_dot2_edgeVec2_eq_zero (norm_edgeVector hQ_loop hQ_deg hq (by linarith) hρ e) c
      have hcutAny_m (e : cmp.external) : MeasurableSet (cutAnyEvent Q q R e) :=
        measurableSet_cutAnyEvent Q q R e
      have hbad_int (B : cmp.blocks) :
          Integrable (fun ω => (badCount Q q R ω B : ℝ)) P :=
        integrable_badCount hQ_deg q R B
      let indCut (e : cmp.external) (ω : cmp.blocks → BlockSample) : ℝ :=
        (cutAnyEvent Q q R e).indicator (1 : (cmp.blocks → BlockSample) → ℝ) ω
      have hint_cut (e : cmp.external) : Integrable (indCut e) P :=
        (integrable_const (1 : ℝ)).indicator (hcutAny_m e)
      have hlhs_eq : (∑ e : cmp.external, P.real (cutAnyEvent Q q R e)) =
          ∫ ω, (∑ e : cmp.external, indCut e ω) ∂P := by
        rw [integral_finsetSum Finset.univ fun e _ => hint_cut e]
        exact (Finset.sum_congr rfl fun e _ => integral_indicator_one (hcutAny_m e)).symm
      have hae_cut_bad :
          (fun ω => ∑ e : cmp.external, indCut e ω) ≤ᵐ[P]
          (fun ω => ∑ B : cmp.blocks, (badCount Q q R ω B : ℝ)) := by
        filter_upwards [compl_mem_ae_iff.mpr hNullAllRay_null] with ω hω
        simp only [NullAllRay, mem_compl_iff, mem_iUnion, mem_ofPred_eq, not_exists] at hω
        have hnat := sum_cutAny_le_sum_badCount hQ_loop q R hω
        have hlhs_nat : (∑ e : cmp.external, indCut e ω) =
            ((Finset.univ.filter fun e : cmp.external => ω ∈ cutAnyEvent Q q R e).card : ℝ) := by
          rw [Finset.card_filter, Nat.cast_sum]
          refine Finset.sum_congr rfl fun e _ => ?_
          dsimp [indCut]
          by_cases h : ω ∈ cutAnyEvent Q q R e <;> simp [h]
        rw [hlhs_nat, ← Nat.cast_sum]
        exact_mod_cast hnat
      have hsum_bad : (∑ e : cmp.external, P.real (cutAnyEvent Q q R e)) ≤
          ∑ B : cmp.blocks, ∫ ω, (badCount Q q R ω B : ℝ) ∂P := by
        rw [hlhs_eq, ← integral_finsetSum _ fun B _ => hbad_int B]
        exact integral_mono_ae
          (integrable_finsetSum _ fun e _ => hint_cut e)
          (integrable_finsetSum _ fun B _ => hbad_int B) hae_cut_bad
      -- Bound `∫ badCount B` by `0` on deg `0`, `2` on `Q12`, and `capAt ρ₀` on `Q3`.
      have hB_bound (B : cmp.blocks) :
          ∫ ω, (badCount Q q R ω B : ℝ) ∂P ≤
            (if B ∈ Q3 then capAt ρ₀ else 0) + (if B ∈ Q12 then 2 else 0) := by
        have hd_le := hQ_deg B
        have hbad_le_deg (ω) : badCount Q q R ω B ≤ (Q.incidenceSet B).ncard := by
          unfold badCount
          rw [toFinset_eq_of_fintype (Q.incidenceSet B) _]
          exact (Finset.card_filter_le _ _).trans_eq (Set.ncard_eq_toFinset_card' _).symm
        interval_cases hdegB : (Q.incidenceSet B).ncard
        · have h0 (ω) : badCount Q q R ω B = 0 := Nat.eq_zero_of_le_zero (hbad_le_deg ω)
          have hn3 : B ∉ Q3 := by simp [Q3, hdegB]
          have hn12 : B ∉ Q12 := by simp [Q12, hdegB]
          simp [h0, hn3, hn12]
        · have hn3 : B ∉ Q3 := by simp [Q3, hdegB]
          have hm12 : B ∈ Q12 := by simp [Q12, hdegB]
          simp only [hn3, hm12, ↓reduceIte, zero_add]
          calc ∫ ω, (badCount Q q R ω B : ℝ) ∂P ≤ ∫ _, (2 : ℝ) ∂P :=
                integral_mono (hbad_int B) (integrable_const 2) fun ω => by
                  have h1 := hbad_le_deg ω
                  exact_mod_cast (by omega : badCount Q q R ω B ≤ 2)
            _ = 2 := by simp
        · have hn3 : B ∉ Q3 := by simp [Q3, hdegB]
          have hm12 : B ∈ Q12 := by simp [Q12, hdegB]
          simp only [hn3, hm12, ↓reduceIte, zero_add]
          calc ∫ ω, (badCount Q q R ω B : ℝ) ∂P ≤ ∫ _, (2 : ℝ) ∂P :=
                integral_mono (hbad_int B) (integrable_const 2) fun ω => by
                  exact_mod_cast hbad_le_deg ω
            _ = 2 := by simp
        · have hm3 : B ∈ Q3 := by simp [Q3, hdegB]
          have hn12 : B ∉ Q12 := by simp [Q12, hdegB]
          simp only [hm3, hn12, ↓reduceIte, add_zero]
          exact integral_badCount_le_capAt hQ_loop hQ_deg hq hρ₀ hρ_lt hρ hdegB
      calc (∑ e : cmp.external, P.real (cutAnyEvent Q q R e))
          ≤ ∑ B : cmp.blocks, ∫ ω, (badCount Q q R ω B : ℝ) ∂P := hsum_bad
        _ ≤ ∑ B : cmp.blocks, ((if B ∈ Q3 then capAt ρ₀ else 0) + (if B ∈ Q12 then 2 else 0)) :=
            Finset.sum_le_sum fun B _ => hB_bound B
        _ = capAt ρ₀ * (Q3.card : ℝ) + 2 * (Q12.card : ℝ) := by
            rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter,
              Finset.sum_const, nsmul_eq_mul, mul_comm (Q3.card : ℝ),
              Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
              mul_comm (Q12.card : ℝ)]
    -- Deduce the expected pairwise cut bound for each `c : Fin 3`.
    have hexp_cutPair (c : Fin 3) :
        (∑ e : cmp.external, (1 : ℝ) * P.real (cutPairEvent Q q R c e)) ≤
          2 / 3 * threeWayCapCoefficient * (G.cycleRank : ℝ) +
            (ξ / 2 + 16 / (M : ℝ)) * (Nat.card V : ℝ) := by
      have hthird : (∑ e : cmp.external, (1 : ℝ) * P.real (cutPairEvent Q q R c e)) =
          1 / 3 * ∑ e : cmp.external, P.real (cutAnyEvent Q q R e) := by
        have h3e (e : cmp.external) : P.real (cutPairEvent Q q R c e) =
            1 / 3 * P.real (cutAnyEvent Q q R e) :=
          measureReal_cutPairEvent_eq_third Q q R c e
        simp_rw [one_mul, h3e]
        rw [← Finset.mul_sum]
      have hcap3 : capAt ρ₀ ≤ 3 := capAt_le_three ρ₀
      have hcap_nonneg : 0 ≤ capAt ρ₀ := by
        have hstrad_pos : 0 ≤ straddleBound ρ₀ := by
          unfold straddleBound
          have ha : 0 ≤ arccos ((1 + 3 * ρ₀) / 4) := arccos_nonneg _
          positivity
        have hsqrt_le1 : √((1 + ρ₀) / 2) ≤ 1 := sqrt_le_one.mpr (by linarith)
        unfold capAt
        linarith only [hstrad_pos, hsqrt_le1]
      have hQ3_real : (Q3.card : ℝ) ≤ 2 * (G.cycleRank : ℝ) + (Q12.card : ℝ) := by
        exact_mod_cast hQ3_le.trans (Nat.add_le_add_left hQ1_le_Q12 _)
      have h1 : capAt ρ₀ * (Q3.card : ℝ) + 2 * (Q12.card : ℝ) ≤
          2 * capAt ρ₀ * (G.cycleRank : ℝ) + 5 * (Q12.card : ℝ) := by
        have hm1 := mul_le_mul_of_nonneg_left hQ3_real hcap_nonneg
        have hm2 : capAt ρ₀ * (Q12.card : ℝ) ≤ 3 * (Q12.card : ℝ) := by gcongr
        linarith only [hm1, hm2]
      have h2 : 2 * capAt ρ₀ * (G.cycleRank : ℝ) ≤
          2 * threeWayCapCoefficient * (G.cycleRank : ℝ) +
            ξ / 2 * (Nat.card V : ℝ) := by
        have hβ_real : (G.cycleRank : ℝ) ≤ (Nat.card V : ℝ) := Nat.cast_le.mpr hbeta_le_V
        have hm1 : 2 * capAt ρ₀ * (G.cycleRank : ℝ) ≤
            2 * (threeWayCapCoefficient + ξ / 4) * (G.cycleRank : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith only [hcap_le]) (Nat.cast_nonneg _)
        have hm2 : ξ / 2 * (G.cycleRank : ℝ) ≤ ξ / 2 * (Nat.card V : ℝ) := by gcongr
        linarith only [hm1, hm2]
      have h3 : 5 / 3 * (Q12.card : ℝ) ≤ 16 / (M : ℝ) * (Nat.card V : ℝ) := by
        calc 5 / 3 * (Q12.card : ℝ) ≤ 2 * (Q12.card : ℝ) := by
              have : (0 : ℝ) ≤ Q12.card := Nat.cast_nonneg _
              linarith only [this]
          _ ≤ 2 * (8 * (Nat.card V : ℝ) / (M : ℝ)) := by gcongr
          _ = 16 / (M : ℝ) * (Nat.card V : ℝ) := by ring
      have hξV : 0 ≤ ξ * (Nat.card V : ℝ) := by positivity
      rw [hthird, add_mul]
      linarith only [hexp_cutAny, h1, h2, h3, hξV]
    -- Apply `WeightedSecondMoment` to the `6` local block/edge sums!
    set h : ℝ := (Nat.card V : ℝ)
    have hh_pos : 0 < h := by
      dsimp [h]; exact_mod_cast (Nat.zero_lt_of_lt hM_lt_V)
    set thr : ℝ := η * h
    have hthr_pos : 0 < thr := by positivity
    let aWt (B : cmp.blocks) : ℝ := ((A ∩ {v : V | v ∈ B.1}).ncard : ℝ)
    have haWt_bounds (B : cmp.blocks) : 0 ≤ aWt B ∧ aWt B ≤ M := by
      refine ⟨Nat.cast_nonneg _, ?_⟩
      have hsub : A ∩ {v : V | v ∈ B.1} ⊆ {v : V | v ∈ B.1} := inter_subset_right
      have hle_len : (A ∩ {v : V | v ∈ B.1}).ncard ≤ cmp.blockWeight B := by
        refine (ncard_le_ncard hsub (toFinite _)).trans ?_
        rw [cmp.ncard_block_eq_length B, CappedCompression.blockWeight]
        simp
      exact Nat.cast_le.mpr (hle_len.trans (cmp.blockWeight_le B))
    have haWt_eq (B : cmp.blocks) :
        aWt B = (((Finset.univ.filter (· ∈ A)).filter fun v => cmp.blockOf v = B).card : ℝ) := by
      dsimp only [aWt]
      congr 1; rw [← ncard_coe_finset]; congr 1; ext v; simp [cmp.mem_iff_blockOf_eq]
    have haWt_sum_univ : ∑ B : cmp.blocks, aWt B = (A.ncard : ℝ) := by
      simp_rw [haWt_eq]
      rw [← Nat.cast_sum, Finset.sum_card_fiberwise_eq_card_filter, ← ncard_coe_finset]
      congr 2; ext v; simp
    let colEvent (c : Fin 3) (B : cmp.blocks) : Set (cmp.blocks → BlockSample) :=
      {ω | blockColor Q q R ω B = c}
    let devA (c : Fin 3) := weightedDeviation P Finset.univ aWt (colEvent c) thr
    let devCut (c : Fin 3) :=
      weightedDeviation P Finset.univ (fun _ => 1) (cutPairEvent Q q R c) thr
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
    have hdevA_le (c : Fin 3) : P.real (devA c) ≤ h * (M : ℝ) ^ 2 * D_blk / thr ^ 2 :=
      (measureReal_weightedDeviation_le _ (fun B _ => measurableSet_blockColor_eq Q q R B c)
        (fun B _ => (haWt_bounds B).1) (fun B _ => (haWt_bounds B).2) _
        (fun B _ ω₁ ω₂ h12 => by simp only [mem_ofPred_eq, dependsOn_blockColor Q q R B h12])
        (fun B _ => card_not_disjoint_closedBall_le hQ_deg (by norm_num) R B) hthr_pos).trans (by
          gcongr
          rw [Finset.card_univ, Fintype.card_coe, show h = Nat.card V from rfl]
          exact_mod_cast hblocks_le_V)
    have hdevCut_le (c : Fin 3) : P.real (devCut c) ≤ 2 * h * (M : ℝ) ^ 2 * D_edg / thr ^ 2 :=
      (measureReal_weightedDeviation_le _ (fun e _ => measurableSet_cutPairEvent Q q R c e)
        (fun _ _ => zero_le_one) (fun _ _ => hM1) _ (fun e _ => dependsOn_cutPairEvent Q q R c e)
        (fun e _ => card_not_disjoint_closedBall_src_le hQ_deg (R + 1) e) hthr_pos).trans (by
          gcongr
          rw [Finset.card_univ, ← Nat.card_eq_fintype_card, show h = Nat.card V from rfl]
          exact_mod_cast (by omega : Nat.card cmp.external ≤ 2 * Nat.card V))
    -- The `6` deviation events together have probability strictly below `1`.
    have ha : 6 * ((M : ℝ) ^ 2 * (D_blk + D_edg)) / η ^ 2 < h := by
      have hlt : ((⌈12 * ((M : ℝ) ^ 2 * (D_blk + D_edg)) / η ^ 2⌉₊ + 1 : ℕ) : ℝ) < h :=
        Nat.cast_lt.mpr ((le_max_right _ _).trans_lt hsmall)
      have := Nat.le_ceil (12 * ((M : ℝ) ^ 2 * (D_blk + D_edg)) / η ^ 2)
      have : 0 ≤ 6 * ((M : ℝ) ^ 2 * (D_blk + D_edg)) / η ^ 2 := by positivity
      push_cast at hlt
      linarith [show 12 * ((M : ℝ) ^ 2 * (D_blk + D_edg)) / η ^ 2 =
        2 * (6 * ((M : ℝ) ^ 2 * (D_blk + D_edg)) / η ^ 2) by ring]
    obtain ⟨ω, hω⟩ := exists_forall_notMem_of_sum_le (s := Finset.univ) (A := Sum.elim devA devCut)
      (b := Sum.elim (fun _ => h * (M : ℝ) ^ 2 * D_blk / thr ^ 2)
        (fun _ => 2 * h * (M : ℝ) ^ 2 * D_edg / thr ^ 2))
      (by rintro (c | c) -; exacts [hdevA_le c, hdevCut_le c]) (by
        simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have : 0 ≤ h * (M : ℝ) ^ 2 * D_blk / thr ^ 2 := by positivity
        calc _ ≤ 6 * ((M : ℝ) ^ 2 * (D_blk + D_edg)) * h / thr ^ 2 := by
              linarith [show 6 * ((M : ℝ) ^ 2 * (D_blk + D_edg)) * h / thr ^ 2 =
                6 * (h * M ^ 2 * D_blk / thr ^ 2) + 3 * (2 * h * M ^ 2 * D_edg / thr ^ 2) by ring]
          _ < 1 := mul_div_mul_sq_lt_one hη.ne' hh_pos ha)
    have hgoodA (c : Fin 3) : ω ∉ devA c := hω (.inl c) (Finset.mem_univ _)
    have hgoodC (c : Fin 3) : ω ∉ devCut c := hω (.inr c) (Finset.mem_univ _)
    -- Lift `blockColor Q q R ω` to `col : V → Fin 3` along `cmp.blockOf`.
    refine ⟨fun v => blockColor Q q R ω (cmp.blockOf v), fun c => ?_, fun c => ?_⟩
    · -- Balance of `A ∩ {v | col v = c}`:
      have hgood :=
        not_le.mp (by simpa only [devA, weightedDeviation, mem_ofPred_eq] using hgoodA c)
      have hval : ((A ∩ {v : V | blockColor Q q R ω (cmp.blockOf v) = c}).ncard : ℝ) =
          ∑ B : cmp.blocks, aWt B * (colEvent c B).indicator 1 ω := by
        have htot_card : (A ∩ {v : V | blockColor Q q R ω (cmp.blockOf v) = c}).ncard =
            ∑ B ∈ Finset.univ.filter (fun B => blockColor Q q R ω B = c),
              ((Finset.univ.filter (· ∈ A)).filter fun v => cmp.blockOf v = B).card := by
          rw [Finset.sum_card_fiberwise_eq_card_filter, ← ncard_coe_finset]
          congr 1; ext v; simp
        rw [htot_card, Nat.cast_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun B _ => ?_
        rw [haWt_eq]
        by_cases hB : blockColor Q q R ω B = c <;> simp [colEvent, hB]
      have hmean : (∑ B : cmp.blocks, aWt B * P.real (colEvent c B)) =
          1 / 3 * (A.ncard : ℝ) := by
        have h3b (B : cmp.blocks) : P.real (colEvent c B) = 1 / 3 :=
          measureReal_blockColor_eq_one_third Q q R B c
        simp_rw [h3b]
        rw [← Finset.sum_mul, haWt_sum_univ]
        ring
      rw [hval, ← hmean]
      have hη_le : η * h ≤ ξ * h + (C₀ : ℝ) := by
        have hη_lt_ξ : η ≤ ξ := by
          linarith only [hξ, hη, hslack, show 0 ≤ 16 / (M : ℝ) by positivity]
        have hm := mul_le_mul_of_nonneg_right hη_lt_ξ hh_pos.le
        have hc0 : (0 : ℝ) ≤ C₀ := Nat.cast_nonneg _
        linarith only [hm, hc0]
      exact hgood.le.trans hη_le
    · -- Pairwise edge-cut bound `E(V_c, V_{c + 1})`:
      have hgood :=
        not_le.mp (by simpa only [devCut, weightedDeviation, mem_ofPred_eq] using hgoodC c)
      set Sc : Set cmp.blocks := {B | blockColor Q q R ω B = c}
      set Sc1 : Set cmp.blocks := {B | blockColor Q q R ω B = c + 1}
      have hdisj_c : Disjoint Sc Sc1 :=
        disjoint_left.mpr fun B h1 h2 => by
          rw [mem_ofPred_eq] at h1 h2; rw [h1] at h2; fin_cases c <;> revert h2 <;> decide
      have hpre_eq : (G.edgeCut {v | blockColor Q q R ω (cmp.blockOf v) = c} ∩
          G.edgeCut {v | blockColor Q q R ω (cmp.blockOf v) = c + 1}).ncard =
          (Q.edgeCut Sc ∩ Q.edgeCut Sc1).ncard :=
        cmp.ncard_crossEdges_preimage hdisj_c
      have hQ_cut_sum : ((Q.edgeCut Sc ∩ Q.edgeCut Sc1).ncard : ℝ) =
          ∑ e : cmp.external, (1 : ℝ) * (cutPairEvent Q q R c e).indicator 1 ω := by
        have hset_eq : Q.edgeCut Sc ∩ Q.edgeCut Sc1 =
            {e : cmp.external | ω ∈ cutPairEvent Q q R c e} := by
          ext e
          simp only [mem_inter_iff, Multigraph.mem_edgeCut, Sc, Sc1, cutPairEvent, mem_ofPred_eq]
          generalize blockColor Q q R ω (Q.src e) = a
          generalize blockColor Q q R ω (Q.tgt e) = b
          fin_cases c <;> fin_cases a <;> fin_cases b <;> decide
        rw [hset_eq, show {e : cmp.external | ω ∈ cutPairEvent Q q R c e}.ncard =
            (Finset.univ.filter fun e : cmp.external => ω ∈ cutPairEvent Q q R c e).card by
          rw [← ncard_coe_finset]; congr 1; ext e; simp]
        rw [Finset.card_filter, Nat.cast_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        by_cases he : ω ∈ cutPairEvent Q q R c e <;> simp [he]
      rw [hpre_eq, hQ_cut_sum]
      have habs := le_of_abs_le hgood.le
      have hexp := hexp_cutPair c
      have hslack_h : (ξ / 2 + 16 / (M : ℝ)) * h + η * h ≤ ξ * h + (C₀ : ℝ) := by
        have hsum_coef : (ξ / 2 + 16 / (M : ℝ)) + η ≤ ξ := by linarith only [hslack, hξ]
        have hm := mul_le_mul_of_nonneg_right hsum_coef hh_pos.le
        have hc0 : (0 : ℝ) ≤ C₀ := Nat.cast_nonneg _
        linarith only [hm, hc0]
      dsimp [thr] at habs
      dsimp [h] at hslack_h ⊢
      linarith only [habs, hexp, hslack_h]


end Cslib.Circuits.Frontier.TensorRank
