/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Compiler.Hypergraph.Compiler
public import CslibFrontier.Computability.Circuit.Frontier.Compiler.Hypergraph.Gaussian.DualCert
import all CslibFrontier.Computability.Circuit.Frontier.Compiler.Hypergraph.Gaussian.EuclideanSheppard
import all CslibFrontier.Computability.Circuit.Frontier.Compiler.Hypergraph.Gaussian.WalkKernel
import all CslibFrontier.Computability.Circuit.Frontier.Compiler.Hypergraph.Gaussian.CorrelationBounds
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.Basic
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Arccos
import CslibFrontier.Foundations.Probability.Gaussian.Sheppard

/-!
# Uniform `(θ, S)` Parameter Selection for `HyperDualCert`

Private `hyperScore` definition and uniform `(θ, S)` selection across all hyperedge sizes
`2 ≤ k ≤ K₀` (`exists_uniform_theta_radius`), imported via `import all` by `Layout.lean`.
-/

-- Internal proof-only helpers; `Layout.lean` imports all.
set_option linter.privateModule false

public section

namespace Cslib.Circuits.Frontier.Hypergraph

open MeasureTheory ProbabilityTheory Real Set Filter Cslib.Circuits
open scoped RealInnerProductSpace Interval

section BipartiteKernel

variable {σ : Signature} {n : ℕ} (c : Circuit σ n 1) (K₀ : ℕ)

/-! ### Uniform `(θ, S)` parameter selection for `HyperDualCert` -/

private theorem twoStepCorr_pos {r k : ℕ} (hr : 2 ≤ r) (hk : 2 ≤ k) : 0 < twoStepCorr r k := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hm : 0 < (r : ℝ) * ((k : ℝ) - 1) := by nlinarith
  unfold twoStepCorr
  positivity

private theorem twoStepCorr_lt_one {r k : ℕ} (hr : 2 ≤ r) (hk : 2 ≤ k) : twoStepCorr r k < 1 := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hm : (2 : ℝ) ≤ (r : ℝ) * ((k : ℝ) - 1) := by nlinarith
  set q := 1 / √((r : ℝ) * ((k : ℝ) - 1))
  have hq_lt : q < 1 := by
    dsimp only [q]
    rw [div_lt_one (sqrt_pos.mpr (by linarith))]
    exact (lt_sqrt zero_le_one).mpr (by linarith)
  change 2 * q / (1 + q ^ 2) < 1
  rw [div_lt_one (by positivity)]
  nlinarith [sq_pos_of_pos (sub_pos.mpr hq_lt)]

/-- Gaussian vertex score induced by `hyperUnitRow c K₀ r θ S`. -/
private noncomputable def hyperScore (r : ℕ) (θ : ℝ) (S : ℕ) (ω : HyperNode c → ℝ)
    (v : HyperNode c) : ℝ :=
  ⟪hyperUnitRow c K₀ r θ S v, WithLp.toLp 2 ω⟫

end BipartiteKernel

section ParameterSelection

/-- Shared `(θ, S)` convergence selection for the two-step pairwise inner-product bound: for any
`r ≥ 2`, `k ≥ 2`, and `δ > 0`, choosing `θ` close to `1` and `S` large makes every pair of vertices
in any size-`k` pruned hyperedge have inner product at least `twoStepCorr r k - 3 * δ / 4`. -/
private theorem exists_theta_radius_twoStep_inner_ge {r k K₀ : ℕ} (hr : 2 ≤ r) (hk : 2 ≤ k)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ θ₀ ∈ Ioo (0 : ℝ) 1, ∀ θ ∈ Ioo θ₀ 1, ∃ S₀ : ℕ, 1 ≤ S₀ ∧ ∀ S ≥ S₀,
      ∀ {σ : Signature} {n : ℕ} (c : Circuit σ n 1), c.FanInAtMost r →
        ∀ (e : PrunedEdge c K₀), (hyperEdge c e.1).card = k →
          ∀ {u v : HyperNode c}, u ∈ hyperEdge c e.1 → v ∈ hyperEdge c e.1 →
            twoStepCorr r k - 3 * δ / 4 ≤
              ⟪hyperUnitRow c K₀ r θ S u, hyperUnitRow c K₀ r θ S v⟫ := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hm_pos : 0 < (r : ℝ) * ((k : ℝ) - 1) := by nlinarith
  set q₂ := 1 / √((r : ℝ) * ((k : ℝ) - 1))
  have hq₂_pos : 0 < q₂ := by positivity
  set D : ℝ := max ((r : ℝ) + 1) (K₀ : ℝ)
  have hD_pos : 0 < D := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  set ρ₀ := twoStepCorr r k
  let f : ℝ → ℝ := fun θ => 2 * (θ ^ 2 * q₂) / (1 + (θ ^ 2 * q₂) ^ 2)
  have hf_cont : ContinuousAt f 1 := by
    dsimp only [f]
    refine ((continuousAt_const.mul ((continuousAt_id.pow 2).mul continuousAt_const)).div
      (continuousAt_const.add (((continuousAt_id.pow 2).mul continuousAt_const).pow 2)) ?_)
    positivity
  have hf1 : f 1 = ρ₀ := by simp [f, ρ₀, twoStepCorr, q₂]
  obtain ⟨γ, hγ, hcont_f⟩ := Metric.continuousAt_iff.mp hf_cont (δ / 2) (half_pos hδ)
  set θ₀ := 1 - min γ (1 / 2) / 2
  have hθ₀_mem : θ₀ ∈ Ioo (0 : ℝ) 1 := by
    have hmin_pos : 0 < min γ (1 / 2) := lt_min hγ (by norm_num)
    have hmin_le : min γ (1 / 2) ≤ 1 / 2 := min_le_right _ _
    exact ⟨by dsimp only [θ₀]; linarith, by dsimp only [θ₀]; linarith⟩
  refine ⟨θ₀, hθ₀_mem, fun θ hθ => ?_⟩
  have hθ0 : 0 < θ := hθ₀_mem.1.trans hθ.1
  have hθ1 : θ < 1 := hθ.2
  have hdist_θ : dist θ 1 < γ := by
    rw [Real.dist_eq, abs_of_neg (by linarith)]
    have : min γ (1 / 2) ≤ γ := min_le_left _ _
    have : θ₀ < θ := hθ.1
    dsimp only [θ₀] at this
    linarith
  have hf_close : ρ₀ - δ / 2 < f θ := by
    have H := hcont_f hdist_θ
    rw [Real.dist_eq, hf1] at H
    linarith [neg_abs_le (f θ - ρ₀)]
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < δ / (16 * D)) hθ1
  refine ⟨max 1 (N + 1), le_max_left _ _, fun S hS σ n c hfan e hk_eq u v hu hv => ?_⟩
  have hS1 : 1 ≤ S := (le_max_left 1 (N + 1)).trans hS
  have hSN : N ≤ 4 * S - 2 := by
    have : N + 1 ≤ S := (le_max_right 1 (N + 1)).trans hS
    omega
  have herr : 4 * D * θ ^ (4 * S - 2) < δ / 4 := by
    have hpow : θ ^ (4 * S - 2) ≤ θ ^ N := pow_le_pow_of_le_one hθ0.le hθ1.le hSN
    have hlt := (mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 4 * D)).trans_lt
      (mul_lt_mul_of_pos_left hN (by positivity : 0 < 4 * D))
    have hsimp : 4 * D * (δ / (16 * D)) = δ / 4 := by field_simp; ring
    linarith
  have hcorr := twoStep_le_inner_hyperUnitRow c K₀ hr hfan hθ0 hθ1.le hS1 e hu hv
  have hq_eq : θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1)) = θ ^ 2 * q₂ := by
    rw [hk_eq]
    dsimp only [q₂]
    ring
  dsimp only at hcorr
  rw [hq_eq] at hcorr
  change 2 * (θ ^ 2 * q₂) / (1 + (θ ^ 2 * q₂) ^ 2) - 4 * D * θ ^ (4 * S - 2) ≤ _ at hcorr
  dsimp only [ρ₀, f] at hf_close ⊢
  linarith

private theorem measureReal_hyperedgeStraddles_le_of_sum_angle {r k K₀ S : ℕ} {θ ρ p η t : ℝ}
    (hk : 2 ≤ k) {σ : Signature} {n : ℕ} (c : Circuit σ n 1) (e : PrunedEdge c K₀)
    (hk_eq : (hyperEdge c e.1).card = k)
    (hsum : ∑ pq ∈ (hyperEdge c e.1).offDiag,
        InnerProductGeometry.angle (hyperUnitRow c K₀ r θ S pq.1)
          (hyperUnitRow c K₀ r θ S pq.2) ≤
      ((hyperEdge c e.1).card : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1) * arccos ρ)
    (harc : (k : ℝ) / (2 * π) * arccos ρ ≤ p + η) :
    (Measure.pi fun _ : HyperNode c => gaussianReal 0 1).real
      {ω | HyperedgeStraddles (hyperEdge c e.1)
        {v | hyperScore c K₀ r θ S ω v < t}} ≤ p + η := by
  have hprob := measureReal_straddlesOn_le_of_sum_angle (hk_eq ▸ hk)
    (fun v _ => norm_hyperUnitRow c K₀ r θ S v) hsum t
  have hev : {ω : HyperNode c → ℝ | HyperedgeStraddles (hyperEdge c e.1)
      {v | hyperScore c K₀ r θ S ω v < t}} =
      {ω | StraddlesOn (fun v => ⟪hyperUnitRow c K₀ r θ S v, WithLp.toLp 2 ω⟫) t
        ↑(hyperEdge c e.1)} := by
    ext ω
    exact hyperedgeStraddles_threshold_iff _ _ _
  rw [hev]
  rw [hk_eq] at hprob
  exact hprob.trans harc

private theorem exists_theta_radius_pairwise {r k K₀ : ℕ} (hr : 2 ≤ r) (hk : 2 ≤ k)
    {p η : ℝ} (hη : 0 < η) (hp : (k : ℝ) / (2 * π) * arccos (twoStepCorr r k) ≤ p) :
    ∃ θ₀ ∈ Ioo (0 : ℝ) 1, ∀ θ ∈ Ioo θ₀ 1, ∃ S₀ : ℕ, 1 ≤ S₀ ∧ ∀ S ≥ S₀,
      ∀ {σ : Signature} {n : ℕ} (c : Circuit σ n 1), c.FanInAtMost r →
        ∀ (e : PrunedEdge c K₀), (hyperEdge c e.1).card = k → ∀ t : ℝ,
          (Measure.pi fun _ : HyperNode c => gaussianReal 0 1).real
            {ω | HyperedgeStraddles (hyperEdge c e.1)
              {v | hyperScore c K₀ r θ S ω v < t}} ≤ p + η := by
  set ρ₀ := twoStepCorr r k
  obtain ⟨δ, hδ, hcont_arc⟩ := Metric.continuousAt_iff.mp
    (continuous_arccos.continuousAt (x := ρ₀)) (2 * π * η / k) (by positivity)
  obtain ⟨θ₀, hθ₀_mem, hθ_sel⟩ := exists_theta_radius_twoStep_inner_ge (K₀ := K₀) hr hk hδ
  set ρ := ρ₀ - 3 * δ / 4
  have hdist_ρ : dist ρ ρ₀ < δ := by
    rw [Real.dist_eq, show ρ - ρ₀ = -(3 * δ / 4) by dsimp only [ρ]; ring, abs_neg,
      abs_of_pos (by positivity)]
    linarith
  have harc_le : (k : ℝ) / (2 * π) * arccos ρ ≤ p + η := by
    have H := (le_abs_self _).trans (hcont_arc hdist_ρ).le
    rw [Real.dist_eq] at *
    have hmul := mul_le_mul_of_nonneg_left (show arccos ρ ≤ arccos ρ₀ + 2 * π * η / k by
      linarith [le_abs_self (arccos ρ - arccos ρ₀), (hcont_arc hdist_ρ).le])
      (by positivity : 0 ≤ (k : ℝ) / (2 * π))
    have hcancel : (k : ℝ) / (2 * π) * (2 * π * η / k) = η := by
      have hk_ne : (k : ℝ) ≠ 0 := by positivity
      field_simp
    linarith
  refine ⟨θ₀, hθ₀_mem, fun θ hθ => ?_⟩
  obtain ⟨S₀, hS₀, hS_sel⟩ := hθ_sel θ hθ
  refine ⟨S₀, hS₀, fun S hS σ n c hfan e hk_eq t => ?_⟩
  have hangle : ∑ pq ∈ (hyperEdge c e.1).offDiag,
      InnerProductGeometry.angle (hyperUnitRow c K₀ r θ S pq.1)
        (hyperUnitRow c K₀ r θ S pq.2) ≤
      ((hyperEdge c e.1).card : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1) * arccos ρ := by
    have hcard : ((hyperEdge c e.1).offDiag.card : ℝ) =
        ((hyperEdge c e.1).card : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1) := by
      rw [Finset.offDiag_card, Nat.cast_sub (Nat.le_mul_self _), Nat.cast_mul]
      ring
    rw [← hcard, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun pq hpq => ?_
    obtain ⟨h1, h2, -⟩ := Finset.mem_offDiag.mp hpq
    rw [InnerProductGeometry.angle_eq_arccos_inner_of_norm_eq_one
      (norm_hyperUnitRow c K₀ r θ S pq.1) (norm_hyperUnitRow c K₀ r θ S pq.2)]
    exact arccos_le_arccos (hS_sel S hS c hfan e hk_eq h1 h2)
  exact measureReal_hyperedgeStraddles_le_of_sum_angle hk c e hk_eq hangle harc_le

private theorem exists_theta_radius_slepian {r k K₀ : ℕ} (hr : 2 ≤ r) (hk : 2 ≤ k)
    {p η : ℝ} (hη : 0 < η) (hp : equicorrStraddle k (twoStepCorr r k) ≤ p) :
    ∃ θ₀ ∈ Ioo (0 : ℝ) 1, ∀ θ ∈ Ioo θ₀ 1, ∃ S₀ : ℕ, 1 ≤ S₀ ∧ ∀ S ≥ S₀,
      ∀ {σ : Signature} {n : ℕ} (c : Circuit σ n 1), c.FanInAtMost r →
        ∀ (e : PrunedEdge c K₀), (hyperEdge c e.1).card = k → ∀ t : ℝ,
          (Measure.pi fun _ : HyperNode c => gaussianReal 0 1).real
            {ω | HyperedgeStraddles (hyperEdge c e.1)
              {v | hyperScore c K₀ r θ S ω v < t}} ≤ p + η := by
  set ρ₀ := twoStepCorr r k
  have hρ₀_pos := twoStepCorr_pos hr hk
  have hρ₀_lt := twoStepCorr_lt_one hr hk
  obtain ⟨δ₀, hδ₀, hcont_sl⟩ := Metric.continuousAt_iff.mp
    (continuousAt_equicorrStraddle k hρ₀_pos hρ₀_lt) η hη
  set δ := min δ₀ (min ρ₀ (1 - ρ₀))
  have hδ : 0 < δ := lt_min hδ₀ (lt_min hρ₀_pos (sub_pos.mpr hρ₀_lt))
  obtain ⟨θ₀, hθ₀_mem, hθ_sel⟩ := exists_theta_radius_twoStep_inner_ge (K₀ := K₀) hr hk hδ
  set ρ := ρ₀ - 3 * δ / 4
  have hρ0 : 0 ≤ ρ := by
    have : δ ≤ ρ₀ := (min_le_right _ _).trans (min_le_left _ _)
    dsimp only [ρ]
    linarith
  have hρ1 : ρ < 1 := by
    dsimp only [ρ]
    linarith
  have hdist_ρ : dist ρ ρ₀ < δ₀ := by
    rw [Real.dist_eq, show ρ - ρ₀ = -(3 * δ / 4) by dsimp only [ρ]; ring, abs_neg,
      abs_of_pos (by positivity)]
    have : δ ≤ δ₀ := min_le_left _ _
    linarith
  have hsl_le : equicorrStraddle k ρ ≤ p + η := by
    have H := (le_abs_self (equicorrStraddle k ρ - equicorrStraddle k ρ₀)).trans
      (by simpa [Real.dist_eq] using (hcont_sl hdist_ρ).le)
    linarith
  refine ⟨θ₀, hθ₀_mem, fun θ hθ => ?_⟩
  obtain ⟨S₀, hS₀, hS_sel⟩ := hθ_sel θ hθ
  refine ⟨S₀, hS₀, fun S hS σ n c hfan e hk_eq t => ?_⟩
  have hprob := measureReal_straddlesOn_le_equicorr (s := hyperEdge c e.1) (hk_eq ▸ hk)
    (fun v _ => norm_hyperUnitRow c K₀ r θ S v) hρ0 hρ1
    (fun u hu v hv _ => hS_sel S hS c hfan e hk_eq hu hv) t
  have hev : {ω : HyperNode c → ℝ | HyperedgeStraddles (hyperEdge c e.1)
      {v | hyperScore c K₀ r θ S ω v < t}} =
      {ω | (∃ v ∈ hyperEdge c e.1, ⟪hyperUnitRow c K₀ r θ S v, WithLp.toLp 2 ω⟫ < t) ∧
        (∃ v ∈ hyperEdge c e.1, t ≤ ⟪hyperUnitRow c K₀ r θ S v, WithLp.toLp 2 ω⟫)} := by
    ext ω
    rw [mem_ofPred_eq, mem_ofPred_eq, hyperedgeStraddles_threshold_iff]
    simp only [StraddlesOn, Finset.mem_coe, hyperScore]
  rw [hev]
  rw [hk_eq] at hprob
  exact hprob.trans hsl_le

private theorem exists_theta_radius_cap {r k K₀ : ℕ} (hr : 2 ≤ r) (hk : 2 ≤ k)
    {p η : ℝ} (hη : 0 < η) (hcap : 1 / 2 < capSq r k)
    (hp : (k : ℝ) / (2 * π) * arccos (capCorr r k) ≤ p) :
    ∃ θ₀ ∈ Ioo (0 : ℝ) 1, ∀ θ ∈ Ioo θ₀ 1, ∃ S₀ : ℕ, 1 ≤ S₀ ∧ ∀ S ≥ S₀,
      ∀ {σ : Signature} {n : ℕ} (c : Circuit σ n 1), c.FanInAtMost r →
        ∀ (e : PrunedEdge c K₀), (hyperEdge c e.1).card = k → ∀ t : ℝ,
          (Measure.pi fun _ : HyperNode c => gaussianReal 0 1).real
            {ω | HyperedgeStraddles (hyperEdge c e.1)
              {v | hyperScore c K₀ r θ S ω v < t}} ≤ p + η := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hm_pos : 0 < (r : ℝ) * ((k : ℝ) - 1) := by nlinarith
  set D : ℝ := max ((r : ℝ) + 1) (K₀ : ℝ)
  have hD_pos : 0 < D := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  set q₁ := 1 / √(√((k : ℝ) - 1) * √(r : ℝ))
  have hq₁_pos : 0 < q₁ := by
    have : 0 < √((k : ℝ) - 1) * √(r : ℝ) :=
      mul_pos (sqrt_pos.mpr (by linarith)) (sqrt_pos.mpr (by linarith))
    exact div_pos one_pos (sqrt_pos.mpr this)
  have hq₁_sq : q₁ ^ 2 = 1 / √((r : ℝ) * ((k : ℝ) - 1)) := by
    dsimp only [q₁]
    rw [div_pow, one_pow, sq_sqrt (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)),
      mul_comm (√((k : ℝ) - 1)), ← sqrt_mul (by linarith)]
  set κ₀ := 2 * q₁ / (1 + q₁ ^ 2)
  have hκ₀_sq : κ₀ ^ 2 = capSq r k := by
    dsimp only [κ₀, capSq]
    rw [div_pow, mul_pow, hq₁_sq]
    set s := √((r : ℝ) * ((k : ℝ) - 1))
    have hs : 0 < s := sqrt_pos.mpr hm_pos
    field_simp
    ring
  have hκ₀_gt : √2 / 2 < κ₀ := by
    have hsq : (√2 / 2) ^ 2 < κ₀ ^ 2 := by
      rw [div_pow, sq_sqrt zero_le_two, hκ₀_sq]
      linarith
    have hκ₀_nn : 0 ≤ κ₀ := by positivity
    nlinarith [sqrt_nonneg 2]
  let Hcap : ℝ → ℝ := fun κ => ((k : ℝ) * κ ^ 2 - 1) / ((k : ℝ) - 1)
  have hHcap_eq : Hcap κ₀ = capCorr r k := by
    dsimp only [Hcap, capCorr]
    rw [hκ₀_sq]
  have hcomp_cont : ContinuousAt (fun κ => arccos (Hcap κ)) κ₀ := by
    refine continuous_arccos.continuousAt.comp ?_
    dsimp only [Hcap]
    exact ((continuousAt_const.mul (continuousAt_id.pow 2)).sub continuousAt_const).div_const _
  obtain ⟨δ₀, hδ₀, hcont_cap⟩ := Metric.continuousAt_iff.mp hcomp_cont
    (2 * π * η / k) (by positivity)
  set δ := min δ₀ (κ₀ - √2 / 2)
  have hδ : 0 < δ := lt_min hδ₀ (sub_pos.mpr hκ₀_gt)
  let g : ℝ → ℝ := fun θ => 2 * (θ * q₁) / (1 + (θ * q₁) ^ 2)
  have hg_cont : ContinuousAt g 1 := by
    dsimp only [g]
    refine ((continuousAt_const.mul (continuousAt_id.mul continuousAt_const)).div
      (continuousAt_const.add ((continuousAt_id.mul continuousAt_const).pow 2)) ?_)
    positivity
  have hg1 : g 1 = κ₀ := by simp [g, κ₀]
  obtain ⟨γ, hγ, hcont_g⟩ := Metric.continuousAt_iff.mp hg_cont (δ / 2) (half_pos hδ)
  set θ₀ := 1 - min γ (1 / 2) / 2
  have hθ₀_mem : θ₀ ∈ Ioo (0 : ℝ) 1 := by
    have hmin_pos : 0 < min γ (1 / 2) := lt_min hγ (by norm_num)
    have hmin_le : min γ (1 / 2) ≤ 1 / 2 := min_le_right _ _
    exact ⟨by dsimp only [θ₀]; linarith, by dsimp only [θ₀]; linarith⟩
  refine ⟨θ₀, hθ₀_mem, fun θ hθ => ?_⟩
  have hθ0 : 0 < θ := hθ₀_mem.1.trans hθ.1
  have hθ1 : θ < 1 := hθ.2
  have hdist_θ : dist θ 1 < γ := by
    rw [Real.dist_eq, abs_of_neg (by linarith)]
    have : min γ (1 / 2) ≤ γ := min_le_left _ _
    have : θ₀ < θ := hθ.1
    dsimp only [θ₀] at this
    linarith
  have hg_close : κ₀ - δ / 2 < g θ := by
    have H := hcont_g hdist_θ
    rw [Real.dist_eq, hg1] at H
    linarith [neg_abs_le (g θ - κ₀)]
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
    (by positivity : 0 < δ * (θ * q₁) / (8 * D)) hθ1
  refine ⟨max 1 N, le_max_left _ _, fun S hS σ n c hfan e hk_eq t => ?_⟩
  have hS1 : 1 ≤ S := (le_max_left 1 N).trans hS
  have hSN : N ≤ 4 * S := by
    have : N ≤ S := (le_max_right 1 N).trans hS
    omega
  have herr : 2 * D * θ ^ (4 * S) / (θ * q₁) < δ / 4 := by
    have hpow : θ ^ (4 * S) ≤ θ ^ N := pow_le_pow_of_le_one hθ0.le hθ1.le hSN
    have hq1_pos : 0 < θ * q₁ := mul_pos hθ0 hq₁_pos
    rw [div_lt_iff₀ hq1_pos]
    have hlt := (mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 2 * D)).trans_lt
      (mul_lt_mul_of_pos_left hN (by positivity : 0 < 2 * D))
    have hsimp : 2 * D * (δ * (θ * q₁) / (8 * D)) = δ / 4 * (θ * q₁) := by field_simp; ring
    linarith
  set κ := κ₀ - 3 * δ / 4
  have hκ_ge : √2 / 2 ≤ κ := by
    have : δ ≤ κ₀ - √2 / 2 := min_le_right _ _
    dsimp only [κ]
    linarith
  have hdist_κ : dist κ κ₀ < δ₀ := by
    rw [Real.dist_eq, show κ - κ₀ = -(3 * δ / 4) by dsimp only [κ]; ring, abs_neg,
      abs_of_pos (by positivity)]
    have : δ ≤ δ₀ := min_le_left _ _
    linarith
  have harc_le : (k : ℝ) / (2 * π) * arccos (Hcap κ) ≤ p + η := by
    have H := (le_abs_self (arccos (Hcap κ) - arccos (Hcap κ₀))).trans
      (by simpa [Real.dist_eq] using (hcont_cap hdist_κ).le)
    rw [hHcap_eq] at H
    have hmul := mul_le_mul_of_nonneg_left H (by positivity : 0 ≤ (k : ℝ) / (2 * π))
    have hcancel : (k : ℝ) / (2 * π) * (2 * π * η / k) = η := by
      have hk_ne : (k : ℝ) ≠ 0 := by positivity
      field_simp
    linarith
  obtain ⟨w_e, hw_e_norm, hw_e_inner⟩ :=
    oneStep_le_inner_hyperUnitRow_center c K₀ hr hfan hθ0 hθ1.le hS1 e
  have hsw_eq : stepWeight c K₀ r θ (.inr e)
      (.inl (Classical.choose (Finset.card_pos.mp (Nat.zero_lt_of_lt e.2.1)))) = θ * q₁ := by
    dsimp only [stepWeight, bipBranch, q₁]
    have hk1 : ((hyperEdge c e.1).card - 1 : ℕ) = (k : ℝ) - 1 := by
      rw [hk_eq, Nat.cast_sub (by omega), Nat.cast_one]
    rw [hk1]
    ring
  have hκ_inner (v : HyperNode c) (hv : v ∈ hyperEdge c e.1) :
      κ ≤ ⟪hyperUnitRow c K₀ r θ S v, w_e⟫ := by
    have hcorr := hw_e_inner v hv
    rw [hsw_eq] at hcorr
    dsimp only [κ, g] at hg_close ⊢
    linarith
  have hsum_ang := InnerProductGeometry.sum_offDiag_angle_le hw_e_norm
    (fun v _ => norm_hyperUnitRow c K₀ r θ S v) hκ_ge hκ_inner
  have hH_eq : (((hyperEdge c e.1).card : ℝ) * κ ^ 2 - 1) /
      (((hyperEdge c e.1).card : ℝ) - 1) = Hcap κ := by
    rw [hk_eq]
  rw [hH_eq] at hsum_ang
  exact measureReal_hyperedgeStraddles_le_of_sum_angle hk c e hk_eq hsum_ang harc_le

private theorem exists_theta_radius_starCone {r k K₀ : ℕ} (hr : 2 ≤ r) (hk : 2 ≤ k)
    {p η : ℝ} (hη : 0 < η) (hk3 : 3 ≤ k)
    (hlo : 1 / √((r : ℝ) * ((k : ℝ) - 1)) < coneMeanSq r k)
    (hhi : coneMeanSq r k - 1 / √((r : ℝ) * ((k : ℝ) - 1)) <
      2 * (1 / √((r : ℝ) * ((k : ℝ) - 1))) * √(coneMeanSq r k))
    (hp : (k : ℝ) / (2 * π) * arccos (coneCorr r k) ≤ p) :
    ∃ θ₀ ∈ Ioo (0 : ℝ) 1, ∀ θ ∈ Ioo θ₀ 1, ∃ S₀ : ℕ, 1 ≤ S₀ ∧ ∀ S ≥ S₀,
      ∀ {σ : Signature} {n : ℕ} (c : Circuit σ n 1), c.FanInAtMost r →
        ∀ (e : PrunedEdge c K₀), (hyperEdge c e.1).card = k → ∀ t : ℝ,
          (Measure.pi fun _ : HyperNode c => gaussianReal 0 1).real
            {ω | HyperedgeStraddles (hyperEdge c e.1)
              {v | hyperScore c K₀ r θ S ω v < t}} ≤ p + η := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hm_pos : 0 < (r : ℝ) * ((k : ℝ) - 1) := by nlinarith
  set q₂ := 1 / √((r : ℝ) * ((k : ℝ) - 1))
  have hq₂_pos : 0 < q₂ := by positivity
  set D : ℝ := max ((r : ℝ) + 1) (K₀ : ℝ)
  have hD_pos : 0 < D := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  set ρ₀ := coneCorr r k
  have hρ₀_pos : 0 < ρ₀ := by
    dsimp only [ρ₀, coneCorr]
    have hk2_nn : 0 ≤ (k : ℝ) - 2 := by
      have : (3 : ℝ) ≤ k := by exact_mod_cast hk3
      linarith
    have hk1_nn : 0 ≤ (k : ℝ) - 1 := by linarith
    positivity
  obtain ⟨δ₀, hδ₀, hcont_arc⟩ := Metric.continuousAt_iff.mp
    (continuous_arccos.continuousAt (x := ρ₀)) (2 * π * η / k) (by positivity)
  set δ := min δ₀ ρ₀
  have hδ : 0 < δ := lt_min hδ₀ hρ₀_pos
  let qf : ℝ → ℝ := fun θ => θ ^ 2 * q₂
  let Qf : ℝ → ℝ := fun θ => (1 + ((k : ℝ) - 1) * qf θ ^ 2) / k
  let cf : ℝ → ℝ := fun θ =>
    (2 * qf θ + ((k : ℝ) - 2) * qf θ ^ 2) / (1 + ((k : ℝ) - 1) * qf θ ^ 2)
  have hqf_cont : Continuous qf := (continuous_pow 2).mul continuous_const
  have hQf_cont : Continuous Qf :=
    (continuous_const.add (continuous_const.mul (hqf_cont.pow 2))).div_const _
  have hcf_cont : ContinuousAt cf 1 := by
    dsimp only [cf]
    refine ((continuous_const.mul hqf_cont |>.add
      (continuous_const.mul (hqf_cont.pow 2))).continuousAt).div
      (continuous_const.add (continuous_const.mul (hqf_cont.pow 2))).continuousAt ?_
    have : 0 ≤ (k : ℝ) - 1 := by linarith
    have : 0 ≤ qf 1 ^ 2 := sq_nonneg _
    positivity
  have hgap1_cont : ContinuousAt (fun θ => Qf θ - qf θ) 1 :=
    (hQf_cont.sub hqf_cont).continuousAt
  have hgap2_cont : ContinuousAt (fun θ => 2 * qf θ * √(Qf θ) - (Qf θ - qf θ)) 1 :=
    (((continuous_const.mul hqf_cont).mul
      (continuous_sqrt.comp hQf_cont)).sub (hQf_cont.sub hqf_cont)).continuousAt
  have hgap1_pos : 0 < Qf 1 - qf 1 := by
    simpa [Qf, qf, coneMeanSq, q₂] using sub_pos.mpr hlo
  have hgap2_pos : 0 < 2 * qf 1 * √(Qf 1) - (Qf 1 - qf 1) := by
    simpa [Qf, qf, coneMeanSq, q₂] using sub_pos.mpr hhi
  have hcf1 : cf 1 = ρ₀ := by simp [cf, qf, ρ₀, coneCorr, q₂]
  obtain ⟨γ₁, hγ₁, hc1⟩ := Metric.continuousAt_iff.mp hcf_cont (δ / 2) (half_pos hδ)
  obtain ⟨γ₂, hγ₂, hc2⟩ := Metric.continuousAt_iff.mp hgap1_cont ((Qf 1 - qf 1) / 2)
    (half_pos hgap1_pos)
  obtain ⟨γ₃, hγ₃, hc3⟩ := Metric.continuousAt_iff.mp hgap2_cont
    ((2 * qf 1 * √(Qf 1) - (Qf 1 - qf 1)) / 2) (half_pos hgap2_pos)
  set γ := min γ₁ (min γ₂ γ₃)
  have hγ : 0 < γ := lt_min hγ₁ (lt_min hγ₂ hγ₃)
  set θ₀ := 1 - min γ (1 / 2) / 2
  have hθ₀_mem : θ₀ ∈ Ioo (0 : ℝ) 1 := by
    have hmin_pos : 0 < min γ (1 / 2) := lt_min hγ (by norm_num)
    have hmin_le : min γ (1 / 2) ≤ 1 / 2 := min_le_right _ _
    exact ⟨by dsimp only [θ₀]; linarith, by dsimp only [θ₀]; linarith⟩
  refine ⟨θ₀, hθ₀_mem, fun θ hθ => ?_⟩
  have hθ0 : 0 < θ := hθ₀_mem.1.trans hθ.1
  have hθ1 : θ < 1 := hθ.2
  have hdist_θ : dist θ 1 < γ := by
    rw [Real.dist_eq, abs_of_neg (by linarith)]
    have : min γ (1 / 2) ≤ γ := min_le_left _ _
    have : θ₀ < θ := hθ.1
    dsimp only [θ₀] at this
    linarith
  have hcf_close : ρ₀ - δ / 2 < cf θ := by
    have H := hc1 (hdist_θ.trans_le (min_le_left _ _))
    rw [Real.dist_eq, hcf1] at H
    linarith [neg_abs_le (cf θ - ρ₀)]
  have htan_lo_θ : qf θ ≤ Qf θ := by
    have H := hc2 (hdist_θ.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    rw [Real.dist_eq] at H
    linarith [neg_abs_le ((Qf θ - qf θ) - (Qf 1 - qf 1))]
  have htan_hi_θ : Qf θ - qf θ ≤ 2 * qf θ * √(Qf θ) := by
    have H := hc3 (hdist_θ.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    rw [Real.dist_eq] at H
    linarith [neg_abs_le ((2 * qf θ * √(Qf θ) - (Qf θ - qf θ)) -
      (2 * qf 1 * √(Qf 1) - (Qf 1 - qf 1)))]
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < δ / (32 * √D)) hθ1
  refine ⟨max 1 (N + 1), le_max_left _ _, fun S hS σ n c hfan e hk_eq t => ?_⟩
  have hS1 : 1 ≤ S := (le_max_left 1 (N + 1)).trans hS
  have hSN : N ≤ 2 * S - 1 := by
    have : N + 1 ≤ S := (le_max_right 1 (N + 1)).trans hS
    omega
  have herr : 8 * √D * θ ^ (2 * S - 1) < δ / 4 := by
    have hpow : θ ^ (2 * S - 1) ≤ θ ^ N := pow_le_pow_of_le_one hθ0.le hθ1.le hSN
    have hlt := (mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 8 * √D)).trans_lt
      (mul_lt_mul_of_pos_left hN (by positivity : 0 < 8 * √D))
    have hsimp : 8 * √D * (δ / (32 * √D)) = δ / 4 := by
      have hsqD : √D ≠ 0 := (sqrt_pos.mpr hD_pos).ne'
      field_simp
      ring
    linarith
  set ρ := ρ₀ - 3 * δ / 4
  have hρ0 : 0 ≤ ρ := by
    have : δ ≤ ρ₀ := min_le_right _ _
    dsimp only [ρ]
    linarith
  have hdist_ρ : dist ρ ρ₀ < δ₀ := by
    rw [Real.dist_eq, show ρ - ρ₀ = -(3 * δ / 4) by dsimp only [ρ]; ring, abs_neg,
      abs_of_pos (by positivity)]
    have : δ ≤ δ₀ := min_le_left _ _
    linarith
  have harc_le : (k : ℝ) / (2 * π) * arccos ρ ≤ p + η := by
    have H := (le_abs_self (arccos ρ - arccos ρ₀)).trans
      (by simpa [Real.dist_eq] using (hcont_arc hdist_ρ).le)
    have hmul := mul_le_mul_of_nonneg_left H (by positivity : 0 ≤ (k : ℝ) / (2 * π))
    have hcancel : (k : ℝ) / (2 * π) * (2 * π * η / k) = η := by
      have hk_ne : (k : ℝ) ≠ 0 := by positivity
      field_simp
    linarith
  have hq_eq : θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1)) = qf θ := by
    rw [hk_eq]
    dsimp only [qf, q₂]
    ring
  have hlo_e : θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1)) ≤
      (1 + (((hyperEdge c e.1).card : ℝ) - 1) *
        (θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1))) ^ 2) /
        (hyperEdge c e.1).card := by
    rw [hq_eq, hk_eq]
    exact htan_lo_θ
  have hhi_e : (1 + (((hyperEdge c e.1).card : ℝ) - 1) *
      (θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1))) ^ 2) /
      (hyperEdge c e.1).card -
      θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1)) ≤
    2 * (θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1))) *
      √((1 + (((hyperEdge c e.1).card : ℝ) - 1) *
        (θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1))) ^ 2) /
        (hyperEdge c e.1).card) := by
    rw [hq_eq, hk_eq]
    exact htan_hi_θ
  have hcone_sum := starCone_le_sum_offDiag_inner_hyperUnitRow c K₀ hr hfan hθ0 hθ1.le hS1 e
    (hk_eq ▸ hk3) hlo_e hhi_e
  dsimp only at hcone_sum
  rw [hq_eq, hk_eq] at hcone_sum
  have hsum_ang : ∑ pq ∈ (hyperEdge c e.1).offDiag,
      InnerProductGeometry.angle (hyperUnitRow c K₀ r θ S pq.1)
        (hyperUnitRow c K₀ r θ S pq.2) ≤
      ((hyperEdge c e.1).card : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1) * arccos ρ := by
    have hcard : ((hyperEdge c e.1).offDiag.card : ℝ) =
        (k : ℝ) * ((k : ℝ) - 1) := by
      rw [Finset.offDiag_card, hk_eq, Nat.cast_sub (Nat.le_mul_self _), Nat.cast_mul]
      ring
    have hrew : ∑ pq ∈ (hyperEdge c e.1).offDiag,
        InnerProductGeometry.angle (hyperUnitRow c K₀ r θ S pq.1)
          (hyperUnitRow c K₀ r θ S pq.2) =
        ∑ pq ∈ (hyperEdge c e.1).offDiag,
          arccos ⟪hyperUnitRow c K₀ r θ S pq.1, hyperUnitRow c K₀ r θ S pq.2⟫ :=
      Finset.sum_congr rfl fun pq _ =>
        InnerProductGeometry.angle_eq_arccos_inner_of_norm_eq_one
          (norm_hyperUnitRow c K₀ r θ S pq.1) (norm_hyperUnitRow c K₀ r θ S pq.2)
    rw [hrew, hk_eq, ← hcard]
    refine Real.sum_arccos_le_card_mul_arccos _ (fun pq _ => ⟨?_, ?_⟩) ?_
    · exact inner_hyperUnitRow_nonneg c K₀ r hθ0.le S pq.1 pq.2
    · exact (real_inner_le_norm _ _).trans_eq
        (by rw [norm_hyperUnitRow, norm_hyperUnitRow, one_mul])
    · rw [hcard]
      have hk3R : (3 : ℝ) ≤ k := by exact_mod_cast hk3
      have hk_prod_nn : 0 ≤ (k : ℝ) * ((k : ℝ) - 1) := by nlinarith
      have hρ_le : ρ ≤ cf θ - 8 * √D * θ ^ (2 * S - 1) := by
        dsimp only [ρ]
        linarith
      exact (mul_le_mul_of_nonneg_left hρ_le hk_prod_nn).trans hcone_sum
  exact measureReal_hyperedgeStraddles_le_of_sum_angle hk c e hk_eq hsum_ang harc_le

/-- Analytic parameter selection for a single hyperedge size `k`: given `HyperEdgeBound r k p` and
`η > 0`, there is a decay threshold `θ₀ ∈ (0, 1)` such that for every `θ ∈ (θ₀, 1)` there is a
radius `S₀` above which every size-`k` pruned hyperedge in any fan-in-`r` circuit straddles any
threshold `t` with probability at most `p + η`. -/
private theorem exists_theta_radius_of_hyperEdgeBound {r k K₀ : ℕ} (hr : 2 ≤ r) (hk : 2 ≤ k)
    {p η : ℝ} (hη : 0 < η) (hb : HyperEdgeBound r k p) :
    ∃ θ₀ ∈ Ioo (0 : ℝ) 1, ∀ θ ∈ Ioo θ₀ 1, ∃ S₀ : ℕ, 1 ≤ S₀ ∧ ∀ S ≥ S₀,
      ∀ {σ : Signature} {n : ℕ} (c : Circuit σ n 1), c.FanInAtMost r →
        ∀ (e : PrunedEdge c K₀), (hyperEdge c e.1).card = k → ∀ t : ℝ,
          (Measure.pi fun _ : HyperNode c => gaussianReal 0 1).real
            {ω | HyperedgeStraddles (hyperEdge c e.1)
              {v | hyperScore c K₀ r θ S ω v < t}} ≤ p + η := by
  cases hb with
  | pairwise hp => exact exists_theta_radius_pairwise hr hk hη hp
  | slepian hp => exact exists_theta_radius_slepian hr hk hη hp
  | cap hcap hp => exact exists_theta_radius_cap hr hk hη hcap hp
  | starCone hk3 hlo hhi hp => exact exists_theta_radius_starCone hr hk hη hk3 hlo hhi hp

/-- Uniform `(θ, S)` across all `k ∈ [2, K₀]` for a `HyperDualCert r K₀ a b`. -/
private theorem exists_uniform_theta_radius {r K₀ : ℕ} {a b : ℚ}
    (hcert : HyperDualCert r K₀ a b) {η : ℝ} (hη : 0 < η) :
    ∃ θ ∈ Ioo (0 : ℝ) 1, ∃ S : ℕ, 1 ≤ S ∧
      ∀ {σ : Signature} {n : ℕ} (c : Circuit σ n 1), c.FanInAtMost r →
        ∀ (e : PrunedEdge c K₀) (t : ℝ),
          (Measure.pi fun _ : HyperNode c => gaussianReal 0 1).real
            {ω | HyperedgeStraddles (hyperEdge c e.1)
              {v | hyperScore c K₀ r θ S ω v < t}} ≤
            (a : ℝ) * (hyperEdge c e.1).card + b + η := by
  classical
  let I := Finset.Icc 2 K₀
  have hI_ne : I.Nonempty := Finset.nonempty_Icc.mpr hcert.hK₀
  have hex (k : I) := exists_theta_radius_of_hyperEdgeBound (K₀ := K₀) hcert.hr
    (Finset.mem_Icc.mp k.2).1 hη (hcert.hedge k.1 k.2)
  let θ_of (k : I) : ℝ := Classical.choose (hex k)
  have hθ_spec (k : I) := Classical.choose_spec (hex k)
  let θ_img : Finset ℝ := (Finset.univ : Finset I).image θ_of
  have hθ_img_ne : θ_img.Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨2, Finset.mem_Icc.mpr ⟨le_rfl, hcert.hK₀⟩⟩⟩ |>.image θ_of
  let θ_max : ℝ := θ_img.max' hθ_img_ne
  have hθ_max_lt : θ_max < 1 := by
    obtain ⟨k_star, _, hk_star_eq⟩ := Finset.mem_image.mp (Finset.max'_mem θ_img hθ_img_ne)
    dsimp only [θ_max]
    rw [← hk_star_eq]
    exact (hθ_spec k_star).1.2
  have hθ_max_pos : 0 < θ_max := by
    let k₂ : I := ⟨2, Finset.mem_Icc.mpr ⟨le_rfl, hcert.hK₀⟩⟩
    exact (hθ_spec k₂).1.1.trans_le
      (Finset.le_max' θ_img (θ_of k₂) (Finset.mem_image.mpr ⟨k₂, Finset.mem_univ k₂, rfl⟩))
  set θ := (θ_max + 1) / 2
  have hθ_mem : θ ∈ Ioo (0 : ℝ) 1 := ⟨by dsimp only [θ]; linarith, by dsimp only [θ]; linarith⟩
  have hθ_k (k : I) : θ ∈ Ioo (θ_of k) 1 := by
    have hle : θ_of k ≤ θ_max :=
      Finset.le_max' θ_img (θ_of k) (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩)
    exact ⟨by dsimp only [θ]; linarith, hθ_mem.2⟩
  let S_of (k : I) : ℕ := Classical.choose ((hθ_spec k).2 θ (hθ_k k))
  have hS_spec (k : I) := Classical.choose_spec ((hθ_spec k).2 θ (hθ_k k))
  set S : ℕ := max 1 ((Finset.univ : Finset I).sup S_of)
  refine ⟨θ, hθ_mem, S, le_max_left _ _, fun c hfan e t => ?_⟩
  let k_e : I := ⟨(hyperEdge c e.1).card, Finset.mem_Icc.mpr ⟨e.2.1, e.2.2⟩⟩
  have hS_ge : S_of k_e ≤ S :=
    (Finset.le_sup (f := S_of) (Finset.mem_univ k_e)).trans (le_max_right _ _)
  exact (hS_spec k_e).2 S hS_ge c hfan e rfl t

end ParameterSelection

end Cslib.Circuits.Frontier.Hypergraph
