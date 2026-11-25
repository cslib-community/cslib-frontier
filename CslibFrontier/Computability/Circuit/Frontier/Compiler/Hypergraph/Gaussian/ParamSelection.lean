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

/-- A property holding eventually near `1` holds on an interval `(θ₀, 1)` with `0 < θ₀`. -/
private theorem exists_Ioo_of_eventually_nhds_one {P : ℝ → Prop} (h : ∀ᶠ θ in nhds (1 : ℝ), P θ) :
    ∃ θ₀ ∈ Ioo (0 : ℝ) 1, ∀ θ ∈ Ioo θ₀ 1, P θ := by
  obtain ⟨γ, hγ, hP⟩ := Metric.eventually_nhds_iff.mp h
  refine ⟨max (1 - γ) (1 / 2), ⟨by positivity, max_lt (by linarith) (by norm_num)⟩,
    fun θ hθ => hP ?_⟩
  rw [Real.dist_eq, abs_of_neg (by linarith [hθ.2])]
  linarith [le_max_left (1 - γ) (1 / 2), hθ.1]

/-- For `θ ∈ (0, 1)`, the error term `C * θ ^ S'` is below `ε > 0` once `S' ≥ S ≥ S₀`. -/
private theorem exists_radius_mul_pow_lt {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (C : ℝ) {ε : ℝ}
    (hε : 0 < ε) : ∃ S₀ : ℕ, 1 ≤ S₀ ∧ ∀ S ≥ S₀, ∀ S' ≥ S, C * θ ^ S' < ε := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (((tendsto_pow_atTop_nhds_zero_of_lt_one hθ0.le hθ1).const_mul C).eventually_lt_const
      (by simpa using hε))
  exact ⟨max 1 N, le_max_left _ _,
    fun S hS S' hS' => hN S' ((le_max_right _ _).trans (hS.trans hS'))⟩

/-- Slack selection: if `F` is continuous at `x₀` with `F x₀ < v`, some `δ ∈ (0, c]` keeps
`F (x₀ - 3 * δ / 4) ≤ v`. -/
private theorem exists_slack {F : ℝ → ℝ} {x₀ v c : ℝ} (hF : ContinuousAt F x₀) (hv : F x₀ < v)
    (hc : 0 < c) : ∃ δ, 0 < δ ∧ δ ≤ c ∧ F (x₀ - 3 * δ / 4) ≤ v := by
  obtain ⟨δ₀, hδ₀, h⟩ := Metric.continuousAt_iff.mp hF (v - F x₀) (sub_pos.mpr hv)
  have hδ : 0 < min δ₀ c := lt_min hδ₀ hc
  have H := h (x := x₀ - 3 * (min δ₀ c / 2) / 4) (by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [min_le_left δ₀ c])
  rw [Real.dist_eq, abs_lt] at H
  exact ⟨min δ₀ c / 2, half_pos hδ, by linarith [min_le_right δ₀ c], by linarith [H.2]⟩

/-- Shared `(θ, S)` convergence selection for the two-step pairwise inner-product bound: for any
`r ≥ 2`, `k ≥ 2`, and `δ > 0`, choosing `θ` close to `1` and `S` large makes every pair of vertices
in any size-`k` pruned hyperedge have inner product at least `twoStepCorr r k - 3 * δ / 4`. -/
private theorem exists_theta_radius_twoStep_inner_ge {r k K₀ : ℕ} (hr : 2 ≤ r) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ θ₀ ∈ Ioo (0 : ℝ) 1, ∀ θ ∈ Ioo θ₀ 1, ∃ S₀ : ℕ, 1 ≤ S₀ ∧ ∀ S ≥ S₀,
      ∀ {σ : Signature} {n : ℕ} (c : Circuit σ n 1), c.FanInAtMost r →
        ∀ (e : PrunedEdge c K₀), (hyperEdge c e.1).card = k →
          ∀ {u v : HyperNode c}, u ∈ hyperEdge c e.1 → v ∈ hyperEdge c e.1 →
            twoStepCorr r k - 3 * δ / 4 ≤
              ⟪hyperUnitRow c K₀ r θ S u, hyperUnitRow c K₀ r θ S v⟫ := by
  set q₂ := 1 / √((r : ℝ) * ((k : ℝ) - 1))
  have hf_cont : ContinuousAt (fun θ : ℝ => 2 * (θ ^ 2 * q₂) / (1 + (θ ^ 2 * q₂) ^ 2)) 1 := by
    fun_prop (disch := positivity)
  obtain ⟨θ₀, hθ₀_mem, hθ_close⟩ := exists_Ioo_of_eventually_nhds_one
    (hf_cont.eventually_const_lt (u := twoStepCorr r k - δ / 2) (by simp [twoStepCorr, q₂, hδ]))
  refine ⟨θ₀, hθ₀_mem, fun θ hθ => ?_⟩
  have hθ0 : 0 < θ := hθ₀_mem.1.trans hθ.1
  obtain ⟨S₀, hS₀, herr⟩ := exists_radius_mul_pow_lt hθ0 hθ.2
    (4 * max ((r : ℝ) + 1) (K₀ : ℝ)) (by positivity : 0 < δ / 4)
  refine ⟨S₀, hS₀, fun S hS σ n c hfan e hk_eq u v hu hv => ?_⟩
  have hcorr := twoStep_le_inner_hyperUnitRow c K₀ hr hfan hθ0 hθ.2.le (hS₀.trans hS) e hu hv
  have hq_eq : θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1)) = θ ^ 2 * q₂ := by
    rw [hk_eq, mul_one_div]
  dsimp only at hcorr
  rw [hq_eq] at hcorr
  linarith [hθ_close θ hθ, herr S hS (4 * S - 2) (by omega)]

private theorem measureReal_hyperedgeStraddles_le_of_sum_angle {r k K₀ S : ℕ} {θ ρ p η t : ℝ}
    (hk : 2 ≤ k) {σ : Signature} {n : ℕ} (c : Circuit σ n 1) (e : PrunedEdge c K₀)
    (hk_eq : (hyperEdge c e.1).card = k)
    (hsum : ∑ pq ∈ (hyperEdge c e.1).offDiag,
        InnerProductGeometry.angle (hyperUnitRow c K₀ r θ S pq.1)
          (hyperUnitRow c K₀ r θ S pq.2) ≤ (k : ℝ) * ((k : ℝ) - 1) * arccos ρ)
    (harc : (k : ℝ) / (2 * π) * arccos ρ ≤ p + η) :
    (Measure.pi fun _ : HyperNode c => gaussianReal 0 1).real
      {ω | HyperedgeStraddles (hyperEdge c e.1)
        {v | hyperScore c K₀ r θ S ω v < t}} ≤ p + η := by
  subst hk_eq
  have hprob := measureReal_straddlesOn_le_of_sum_angle hk
    (fun v _ => norm_hyperUnitRow c K₀ r θ S v) hsum t
  have hev : {ω : HyperNode c → ℝ | HyperedgeStraddles (hyperEdge c e.1)
      {v | hyperScore c K₀ r θ S ω v < t}} =
      {ω | StraddlesOn (fun v => ⟪hyperUnitRow c K₀ r θ S v, WithLp.toLp 2 ω⟫) t
        ↑(hyperEdge c e.1)} := by
    ext ω
    exact hyperedgeStraddles_threshold_iff _ _ _
  rw [hev]
  exact hprob.trans harc

private theorem cast_card_offDiag {α : Type*} (s : Finset α) :
    (s.offDiag.card : ℝ) = s.card * (s.card - 1) := by
  classical
  rw [Finset.offDiag_card, Nat.cast_sub (Nat.le_mul_self _), Nat.cast_mul]
  ring

private theorem exists_theta_radius_pairwise {r k K₀ : ℕ} (hr : 2 ≤ r) (hk : 2 ≤ k)
    {p η : ℝ} (hη : 0 < η) (hp : (k : ℝ) / (2 * π) * arccos (twoStepCorr r k) ≤ p) :
    ∃ θ₀ ∈ Ioo (0 : ℝ) 1, ∀ θ ∈ Ioo θ₀ 1, ∃ S₀ : ℕ, 1 ≤ S₀ ∧ ∀ S ≥ S₀,
      ∀ {σ : Signature} {n : ℕ} (c : Circuit σ n 1), c.FanInAtMost r →
        ∀ (e : PrunedEdge c K₀), (hyperEdge c e.1).card = k → ∀ t : ℝ,
          (Measure.pi fun _ : HyperNode c => gaussianReal 0 1).real
            {ω | HyperedgeStraddles (hyperEdge c e.1)
              {v | hyperScore c K₀ r θ S ω v < t}} ≤ p + η := by
  obtain ⟨δ, hδ, -, harc_le⟩ := exists_slack (x₀ := twoStepCorr r k)
    (F := fun ρ => (k : ℝ) / (2 * π) * arccos ρ) (v := p + η) (by fun_prop) (by linarith) one_pos
  obtain ⟨θ₀, hθ₀_mem, hθ_sel⟩ := exists_theta_radius_twoStep_inner_ge (k := k) (K₀ := K₀) hr hδ
  refine ⟨θ₀, hθ₀_mem, fun θ hθ => ?_⟩
  obtain ⟨S₀, hS₀, hS_sel⟩ := hθ_sel θ hθ
  refine ⟨S₀, hS₀, fun S hS σ n c hfan e hk_eq t => ?_⟩
  refine measureReal_hyperedgeStraddles_le_of_sum_angle hk c e hk_eq ?_ harc_le
  have hcard : ((hyperEdge c e.1).offDiag.card : ℝ) = (k : ℝ) * ((k : ℝ) - 1) := by
    rw [cast_card_offDiag, hk_eq]
  rw [← hcard, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun pq hpq => ?_
  obtain ⟨h1, h2, -⟩ := Finset.mem_offDiag.mp hpq
  rw [InnerProductGeometry.angle_eq_arccos_inner_of_norm_eq_one
    (norm_hyperUnitRow c K₀ r θ S pq.1) (norm_hyperUnitRow c K₀ r θ S pq.2)]
  exact arccos_le_arccos (hS_sel S hS c hfan e hk_eq h1 h2)

private theorem exists_theta_radius_slepian {r k K₀ : ℕ} (hr : 2 ≤ r) (hk : 2 ≤ k)
    {p η : ℝ} (hη : 0 < η) (hp : equicorrStraddle k (twoStepCorr r k) ≤ p) :
    ∃ θ₀ ∈ Ioo (0 : ℝ) 1, ∀ θ ∈ Ioo θ₀ 1, ∃ S₀ : ℕ, 1 ≤ S₀ ∧ ∀ S ≥ S₀,
      ∀ {σ : Signature} {n : ℕ} (c : Circuit σ n 1), c.FanInAtMost r →
        ∀ (e : PrunedEdge c K₀), (hyperEdge c e.1).card = k → ∀ t : ℝ,
          (Measure.pi fun _ : HyperNode c => gaussianReal 0 1).real
            {ω | HyperedgeStraddles (hyperEdge c e.1)
              {v | hyperScore c K₀ r θ S ω v < t}} ≤ p + η := by
  have hρ₀_pos := twoStepCorr_pos hr hk
  have hρ₀_lt := twoStepCorr_lt_one hr hk
  obtain ⟨δ, hδ, hδρ, hsl_le⟩ := exists_slack (continuousAt_equicorrStraddle k hρ₀_pos hρ₀_lt)
    (v := p + η) (by linarith) hρ₀_pos
  obtain ⟨θ₀, hθ₀_mem, hθ_sel⟩ := exists_theta_radius_twoStep_inner_ge (k := k) (K₀ := K₀) hr hδ
  refine ⟨θ₀, hθ₀_mem, fun θ hθ => ?_⟩
  obtain ⟨S₀, hS₀, hS_sel⟩ := hθ_sel θ hθ
  refine ⟨S₀, hS₀, fun S hS σ n c hfan e hk_eq t => ?_⟩
  have hprob := measureReal_straddlesOn_le_equicorr (s := hyperEdge c e.1) (hk_eq ▸ hk)
    (fun v _ => norm_hyperUnitRow c K₀ r θ S v) (by linarith) (by linarith)
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
  obtain ⟨δ, hδ, hδκ, harc_le⟩ := exists_slack (x₀ := κ₀)
    (F := fun κ => (k : ℝ) / (2 * π) * arccos (((k : ℝ) * κ ^ 2 - 1) / ((k : ℝ) - 1)))
    (v := p + η) (by fun_prop) (by rw [hκ₀_sq]; unfold capCorr at hp; linarith)
    (sub_pos.mpr hκ₀_gt)
  have hg_cont : ContinuousAt (fun θ : ℝ => 2 * (θ * q₁) / (1 + (θ * q₁) ^ 2)) 1 := by
    fun_prop (disch := positivity)
  obtain ⟨θ₀, hθ₀_mem, hθ_close⟩ := exists_Ioo_of_eventually_nhds_one
    (hg_cont.eventually_const_lt (u := κ₀ - δ / 2) (by simp [κ₀, hδ]))
  refine ⟨θ₀, hθ₀_mem, fun θ hθ => ?_⟩
  have hθ0 : 0 < θ := hθ₀_mem.1.trans hθ.1
  obtain ⟨S₀, hS₀, herr⟩ := exists_radius_mul_pow_lt hθ0 hθ.2
    (2 * max ((r : ℝ) + 1) (K₀ : ℝ) / (θ * q₁)) (by positivity : 0 < δ / 4)
  refine ⟨S₀, hS₀, fun S hS σ n c hfan e hk_eq t => ?_⟩
  obtain ⟨w_e, hw_e_norm, hw_e_inner⟩ :=
    oneStep_le_inner_hyperUnitRow_center c K₀ hr hfan hθ0 hθ.2.le (hS₀.trans hS) e
  have hsw_eq : stepWeight c K₀ r θ (.inr e)
      (.inl (Classical.choose (Finset.card_pos.mp (Nat.zero_lt_of_lt e.2.1)))) = θ * q₁ := by
    dsimp only [stepWeight, bipBranch, q₁]
    rw [hk_eq, Nat.cast_sub (by omega), Nat.cast_one]
    ring
  have hκ_inner (v : HyperNode c) (hv : v ∈ hyperEdge c e.1) :
      κ₀ - 3 * δ / 4 ≤ ⟪hyperUnitRow c K₀ r θ S v, w_e⟫ := by
    have hcorr := hw_e_inner v hv
    have h := herr S hS (4 * S) (by omega)
    rw [hsw_eq] at hcorr
    rw [div_mul_eq_mul_div] at h
    linarith [hθ_close θ hθ]
  have hsum_ang := InnerProductGeometry.sum_offDiag_angle_le hw_e_norm
    (fun v _ => norm_hyperUnitRow c K₀ r θ S v) (by linarith) hκ_inner
  rw [hk_eq] at hsum_ang
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
  have hk3R : (3 : ℝ) ≤ k := by exact_mod_cast hk3
  have hm_pos : 0 < (r : ℝ) * ((k : ℝ) - 1) :=
    mul_pos (by exact_mod_cast (by omega : 0 < r)) (by linarith)
  set q₂ := 1 / √((r : ℝ) * ((k : ℝ) - 1))
  set ρ₀ := coneCorr r k
  have hρ₀_pos : 0 < ρ₀ := by
    dsimp only [ρ₀, coneCorr]
    have : 0 ≤ (k : ℝ) - 2 := by linarith
    have : 0 ≤ (k : ℝ) - 1 := by linarith
    positivity
  obtain ⟨δ, hδ, hδρ, harc_le⟩ := exists_slack (x₀ := ρ₀)
    (F := fun ρ => (k : ℝ) / (2 * π) * arccos ρ) (v := p + η) (by fun_prop) (by linarith) hρ₀_pos
  let qf : ℝ → ℝ := fun θ => θ ^ 2 * q₂
  let Qf : ℝ → ℝ := fun θ => (1 + ((k : ℝ) - 1) * qf θ ^ 2) / k
  let cf : ℝ → ℝ := fun θ =>
    (2 * qf θ + ((k : ℝ) - 2) * qf θ ^ 2) / (1 + ((k : ℝ) - 1) * qf θ ^ 2)
  have hqf_cont : Continuous qf := (continuous_pow 2).mul continuous_const
  have hQf_cont : Continuous Qf :=
    (continuous_const.add (continuous_const.mul (hqf_cont.pow 2))).div_const _
  have hcf_cont : ContinuousAt cf 1 := by
    refine ((continuous_const.mul hqf_cont |>.add
      (continuous_const.mul (hqf_cont.pow 2))).continuousAt).div
      (continuous_const.add (continuous_const.mul (hqf_cont.pow 2))).continuousAt ?_
    have : 0 ≤ (k : ℝ) - 1 := by linarith
    positivity
  have hgap1_cont : ContinuousAt (fun θ => Qf θ - qf θ) 1 :=
    (hQf_cont.sub hqf_cont).continuousAt
  have hgap2_cont : ContinuousAt (fun θ => 2 * qf θ * √(Qf θ) - (Qf θ - qf θ)) 1 :=
    (((continuous_const.mul hqf_cont).mul
      (continuous_sqrt.comp hQf_cont)).sub (hQf_cont.sub hqf_cont)).continuousAt
  obtain ⟨θ₀, hθ₀_mem, hθ_close⟩ := exists_Ioo_of_eventually_nhds_one
    ((hcf_cont.eventually_const_lt (u := ρ₀ - δ / 2) (by simp [cf, qf, ρ₀, coneCorr, q₂, hδ])).and
      ((hgap1_cont.eventually_const_lt (u := 0) (by simpa [Qf, qf, coneMeanSq, q₂] using hlo)).and
        (hgap2_cont.eventually_const_lt (u := 0) (by simpa [Qf, qf, coneMeanSq, q₂] using hhi))))
  refine ⟨θ₀, hθ₀_mem, fun θ hθ => ?_⟩
  obtain ⟨hcf_close, htan_lo, htan_hi⟩ := hθ_close θ hθ
  have hθ0 : 0 < θ := hθ₀_mem.1.trans hθ.1
  obtain ⟨S₀, hS₀, herr⟩ := exists_radius_mul_pow_lt hθ0 hθ.2
    (8 * √(max ((r : ℝ) + 1) (K₀ : ℝ))) (by positivity : 0 < δ / 4)
  refine ⟨S₀, hS₀, fun S hS σ n c hfan e hk_eq t => ?_⟩
  have hq_eq : θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1)) = qf θ := by
    rw [hk_eq]
    exact (mul_one_div _ _).symm
  have hcone_sum := starCone_le_sum_offDiag_inner_hyperUnitRow c K₀ hr hfan hθ0 hθ.2.le
    (hS₀.trans hS) e (hk_eq ▸ hk3) (by rw [hq_eq, hk_eq]; linarith)
    (by rw [hq_eq, hk_eq]; linarith)
  dsimp only at hcone_sum
  rw [hq_eq, hk_eq] at hcone_sum
  refine measureReal_hyperedgeStraddles_le_of_sum_angle hk c e hk_eq ?_ harc_le
  have hcard : ((hyperEdge c e.1).offDiag.card : ℝ) = (k : ℝ) * ((k : ℝ) - 1) := by
    rw [cast_card_offDiag, hk_eq]
  rw [Finset.sum_congr rfl fun pq _ => InnerProductGeometry.angle_eq_arccos_inner_of_norm_eq_one
    (norm_hyperUnitRow c K₀ r θ S pq.1) (norm_hyperUnitRow c K₀ r θ S pq.2), ← hcard]
  refine Real.sum_arccos_le_card_mul_arccos _ (fun pq _ => ⟨?_, ?_⟩) ?_
  · exact inner_hyperUnitRow_nonneg c K₀ r hθ0.le S pq.1 pq.2
  · exact (real_inner_le_norm _ _).trans_eq
      (by rw [norm_hyperUnitRow, norm_hyperUnitRow, one_mul])
  · rw [hcard]
    refine (mul_le_mul_of_nonneg_left ?_ (by nlinarith)).trans hcone_sum
    linarith [herr S hS (2 * S - 1) (by omega)]

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
  choose θ₀ hθ₀ hθ using fun k : Finset.Icc 2 K₀ => exists_theta_radius_of_hyperEdgeBound
    (K₀ := K₀) hcert.hr (Finset.mem_Icc.mp k.2).1 hη (hcert.hedge k.1 k.2)
  obtain ⟨θ, hθ_k, hθ_mem⟩ := ((eventually_all (p := fun k θ => θ ∈ Ioo (θ₀ k) 1)).mpr
    fun k => Ioo_mem_nhdsLT (hθ₀ k).2).and (Ioo_mem_nhdsLT zero_lt_one) |>.exists
  choose S₀ hS₀ hS using fun k => hθ k θ (hθ_k k)
  refine ⟨θ, hθ_mem, max 1 (Finset.univ.sup S₀), le_max_left _ _, fun c hfan e t => ?_⟩
  exact hS ⟨_, Finset.mem_Icc.mpr ⟨e.2.1, e.2.2⟩⟩ _
    ((Finset.le_sup (Finset.mem_univ _)).trans (le_max_right _ _)) c hfan e rfl t

end ParameterSelection

end Cslib.Circuits.Frontier.Hypergraph
