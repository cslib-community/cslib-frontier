/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Init
public import CslibFrontier.GameTheory.Mechanism.BulowKlemperer
public import CslibFrontier.GameTheory.Mechanism.FirstPrice
public import CslibFrontier.GameTheory.Mechanism.Holmstrom
public import CslibFrontier.GameTheory.Mechanism.MyersonSatterthwaite
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Checked witnesses for Holmström, Myerson–Satterthwaite, and Bulow–Klemperer

Non-vacuous client tests exercising:

* **Green–Laffont / Holmström**: finite-outcome VCG witness (`hᵢ` = Clarke pivot) and uniqueness
  on unrestricted and convex domains, paired with the concrete disconnected two-point counterexample
  (`disconnectedNonGroves`) showing connectedness is necessary.
* **Myerson–Satterthwaite**: explicit `Uniform[0, 1]` bilateral trade deficit `−1/6`, general
  positive-density impossibility on overlapping intervals, and the boundary witness showing that
  non-overlapping supports `v_s ≤ c ≤ v_b` admit a BIC, interim IR, ex-post efficient, strictly
  budget-balanced posted-price mechanism (`fixedPrice c`).
* **Bulow–Klemperer**: explicit verification for `Uniform[0, 1]` bidders (for `n = 1`, Myerson
  with reserve `1/2` earns `1/4 ≤ 1/3`, the `2`-bidder Vickrey revenue; general `n` application of
  both the DSIC and Bayes–Nash forms).
-/

public section

namespace CslibFrontierTests.MechanismGrovesMS

open MeasureTheory Set Cslib.GameTheory Cslib.GameTheory.SingleParameter

/-! ### Holmström / Green–Laffont: VCG witness and disconnected counterexample -/

/-- A two-agent public project welfare-maximizing rule. -/
noncomputable def projectRule (b : Fin 2 → Bool → ℝ) : Bool :=
  decide (Mechanism.welfare b false ≤ Mechanism.welfare b true)

theorem projectRule_isWelfareMaximizing : Mechanism.IsWelfareMaximizing projectRule := by
  intro b ω
  simp only [projectRule]
  by_cases h : Mechanism.welfare b false ≤ Mechanism.welfare b true
  · rw [decide_eq_true h]
    cases ω
    · exact h
    · exact le_rfl
  · rw [decide_eq_false h]
    cases ω
    · exact le_rfl
    · exact (not_le.1 h).le

/-- Non-vacuous Green–Laffont witness: VCG on `Fin 2` and `Bool` satisfies the hypotheses of
`exists_groves_of_isDSIC`, yielding a pivot `h` independent of each agent's own report. -/
example : ∃ h : Fin 2 → (Fin 2 → Bool → ℝ) → ℝ,
    (∀ i b v, h i (Function.update b i v) = h i b) ∧
    Mechanism.vcg projectRule = Mechanism.groves (Mechanism.vcg projectRule).outcome h :=
  Mechanism.exists_groves_of_isDSIC (Mechanism.vcg_isDSIC projectRule_isWelfareMaximizing)
    projectRule_isWelfareMaximizing

/-- On the convex domain of nonnegative valuations over `Bool`, Holmström's smoothly connected
theorem applies (`IsSmoothlyConnected.of_convex`) and characterizes VCG as a Groves mechanism. -/
example : Mechanism.IsSmoothlyConnected {v : Bool → ℝ | ∀ ω, 0 ≤ v ω} ∧
    ∃ h : Fin 2 → (Fin 2 → Bool → ℝ) → ℝ,
      (∀ i b v, h i (Function.update b i v) = h i b) ∧
      ∀ b, (∀ j : Fin 2, ∀ ω, 0 ≤ b j ω) →
        ∀ i, (Mechanism.vcg projectRule).payment b i =
          (Mechanism.groves (Mechanism.vcg projectRule).outcome h).payment b i := by
  have hconv : Convex ℝ {v : Bool → ℝ | ∀ ω, 0 ≤ v ω} := fun v hv w hw a b ha hb _ ω =>
    add_nonneg (mul_nonneg ha (hv ω)) (mul_nonneg hb (hw ω))
  have hsc := Mechanism.IsSmoothlyConnected.of_convex hconv
  refine ⟨hsc, ?_⟩
  exact Mechanism.exists_groves_of_isSmoothlyConnected
    ((Mechanism.vcg_isDSIC projectRule_isWelfareMaximizing).isDSICOn _)
    (fun b _ ω => projectRule_isWelfareMaximizing b ω)
    (fun _ => hsc)

/-- Disconnected two-point domain counterexample: `disconnectedNonGroves` is DSIC and
welfare-maximizing on `disconnectedDomains`, yet is not a Groves mechanism, and the domain is not
smoothly connected. -/
example : Mechanism.disconnectedNonGroves.IsDSICOn Mechanism.disconnectedDomains ∧
    Mechanism.IsWelfareMaximizingOn Mechanism.disconnectedNonGroves.outcome
      Mechanism.disconnectedDomains ∧
    ¬ Mechanism.IsSmoothlyConnected (Mechanism.disconnectedDomains 0) ∧
    ¬ ∃ h : Fin 2 → (Fin 2 → Bool → ℝ) → ℝ,
      (∀ i b v, h i (Function.update b i v) = h i b) ∧
      ∀ b, (∀ j, b j ∈ Mechanism.disconnectedDomains j) →
        ∀ i, Mechanism.disconnectedNonGroves.payment b i =
          (Mechanism.groves Mechanism.disconnectedNonGroves.outcome h).payment b i :=
  ⟨Mechanism.disconnectedNonGroves_isDSICOn,
    Mechanism.disconnectedNonGroves_isWelfareMaximizingOn,
    Mechanism.not_isSmoothlyConnected_disconnectedDomains,
    Mechanism.disconnectedNonGroves_not_groves⟩

/-! ### Myerson–Satterthwaite: `Uniform[0, 1]` deficit `−1/6` and non-overlapping boundary -/

/-- The uniform distribution on `[0, 1]`. -/
noncomputable abbrev unif : Measure ℝ := volume.restrict (Icc 0 1)

instance : IsProbabilityMeasure unif :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]⟩

/-- The uniform distribution on `[2, 3]` (for the non-overlapping support witness). -/
noncomputable abbrev unif23 : Measure ℝ := volume.restrict (Icc 2 3)

instance : IsProbabilityMeasure unif23 :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; norm_num⟩

/-- Non-vacuous `Uniform[0, 1]` witness: the VCG bilateral trade mechanism (`trade = 1_{v_s ≤ v_b}`,
buyer pays `v_s · trade`, seller receives `v_b · trade`) is BIC, interim IR, ex-post efficient,
has zero utility at `v_b = 0` and `v_s = 1`, and has exact expected budget deficit `−1/6`! -/
noncomputable def vcgTrade : BilateralTrade.Mechanism where
  trade v_b v_s := if v_s ≤ v_b then 1 else 0
  buyerPayment v_b v_s := if v_s ≤ v_b then v_s else 0
  sellerPayment v_b v_s := if v_s ≤ v_b then v_b else 0

theorem vcgTrade_isExPostEfficient : vcgTrade.IsExPostEfficient := by
  intro v_b v_s
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [vcgTrade, ite_eq_left h.le]
  · simp only [vcgTrade, ite_eq_right (not_le.2 h)]

theorem vcgTrade_integrable :
    Integrable (Function.uncurry vcgTrade.buyerPayment) (unif.prod unif) ∧
    Integrable (Function.uncurry vcgTrade.sellerPayment) (unif.prod unif) := by
  have hsm : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} :=
    measurableSet_le measurable_snd measurable_fst
  have hbox : ∀ᵐ p ∂(unif.prod unif), p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ Icc (0 : ℝ) 1 :=
    ((Measure.quasiMeasurePreserving_fst (μ := unif) (ν := unif)).ae
      (ae_restrict_mem measurableSet_Icc)).and
      ((Measure.quasiMeasurePreserving_snd (μ := unif) (ν := unif)).ae
        (ae_restrict_mem measurableSet_Icc))
  refine ⟨Integrable.of_bound
    (Measurable.ite hsm measurable_snd measurable_const).aestronglyMeasurable 1 ?_,
    Integrable.of_bound
    (Measurable.ite hsm measurable_fst measurable_const).aestronglyMeasurable 1 ?_⟩
  · filter_upwards [hbox] with p ⟨_, hp2⟩
    change ‖if p.2 ≤ p.1 then p.2 else 0‖ ≤ 1
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg hp2.1]; exact hp2.2
    · rw [norm_zero]; exact zero_le_one
  · filter_upwards [hbox] with p ⟨hp1, _⟩
    change ‖if p.2 ≤ p.1 then p.1 else 0‖ ≤ 1
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg hp1.1]; exact hp1.2
    · rw [norm_zero]; exact zero_le_one

/-- `vcgTrade` is BIC and interim IR on `[0, 1] × [0, 1]`, with zero utility for the worst types
`v_b = 0` and `v_s = 1`. -/
theorem vcgTrade_isBIC_isInterimIR_boundary :
    vcgTrade.IsBIC unif unif 0 1 0 1 ∧
    vcgTrade.IsInterimIR unif unif 0 1 0 1 ∧
    vcgTrade.interimBuyerUtility unif 0 = 0 ∧
    vcgTrade.interimSellerUtility unif 1 = 0 := by
  have hQb : ∀ v ∈ Icc (0 : ℝ) 1, vcgTrade.interimBuyerTrade unif v = v := fun v hv => by
    have hfun : (fun s => vcgTrade.trade v s) = (Iic v).indicator 1 := by
      ext s; by_cases h : s ≤ v
      · simp only [vcgTrade, ite_eq_left h, indicator_of_mem (show s ∈ Iic v from h), Pi.one_apply]
      · simp only [vcgTrade, ite_eq_right h, indicator_of_notMem (show s ∉ Iic v from h)]
    have hset : Iic v ∩ Icc (0 : ℝ) 1 = Icc 0 v := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc]
      exact ⟨fun ⟨h1, h2, _⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, h2.trans hv.2⟩⟩
    rw [BilateralTrade.Mechanism.interimBuyerTrade, hfun, integral_indicator_one measurableSet_Iic,
      measureReal_def, Measure.restrict_apply measurableSet_Iic, hset, Real.volume_Icc, sub_zero,
      ENNReal.toReal_ofReal hv.1]
  have hPb : ∀ v ∈ Icc (0 : ℝ) 1, vcgTrade.interimBuyerPayment unif v = v ^ 2 / 2 := fun v hv => by
    have hfun : (fun s => vcgTrade.buyerPayment v s) = (Iic v).indicator (fun x => x) := by
      ext s; by_cases h : s ≤ v
      · simp only [vcgTrade, ite_eq_left h, indicator_of_mem (show s ∈ Iic v from h)]
      · simp only [vcgTrade, ite_eq_right h, indicator_of_notMem (show s ∉ Iic v from h)]
    have hset : Iic v ∩ Icc (0 : ℝ) 1 = Icc 0 v := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc]
      exact ⟨fun ⟨h1, h2, _⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, h2.trans hv.2⟩⟩
    rw [BilateralTrade.Mechanism.interimBuyerPayment, hfun, integral_indicator measurableSet_Iic,
      Measure.restrict_restrict measurableSet_Iic, hset, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hv.1, integral_id]
    ring
  have hQs : ∀ s ∈ Icc (0 : ℝ) 1, vcgTrade.interimSellerTrade unif s = 1 - s := fun s hs => by
    have hfun : (fun v => vcgTrade.trade v s) = (Ici s).indicator 1 := by
      ext v; by_cases h : s ≤ v
      · simp only [vcgTrade, ite_eq_left h, indicator_of_mem (show v ∈ Ici s from h), Pi.one_apply]
      · simp only [vcgTrade, ite_eq_right h, indicator_of_notMem (show v ∉ Ici s from h)]
    have hset : Ici s ∩ Icc (0 : ℝ) 1 = Icc s 1 := by
      ext x; simp only [mem_inter_iff, mem_Ici, mem_Icc]
      exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h2⟩ => ⟨h1, hs.1.trans h1, h2⟩⟩
    rw [BilateralTrade.Mechanism.interimSellerTrade, hfun, integral_indicator_one measurableSet_Ici,
      measureReal_def, Measure.restrict_apply measurableSet_Ici, hset, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.2 hs.2)]
  have hPs : ∀ s ∈ Icc (0 : ℝ) 1, vcgTrade.interimSellerPayment unif s = (1 - s ^ 2) / 2 :=
    fun s hs => by
      have hfun : (fun v => vcgTrade.sellerPayment v s) = (Ici s).indicator (fun x => x) := by
        ext v; by_cases h : s ≤ v
        · simp only [vcgTrade, ite_eq_left h, indicator_of_mem (show v ∈ Ici s from h)]
        · simp only [vcgTrade, ite_eq_right h, indicator_of_notMem (show v ∉ Ici s from h)]
      have hset : Ici s ∩ Icc (0 : ℝ) 1 = Icc s 1 := by
        ext x; simp only [mem_inter_iff, mem_Ici, mem_Icc]
        exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h2⟩ => ⟨h1, hs.1.trans h1, h2⟩⟩
      rw [BilateralTrade.Mechanism.interimSellerPayment, hfun, integral_indicator measurableSet_Ici,
        Measure.restrict_restrict measurableSet_Ici, hset, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hs.2, integral_id]
      ring
  refine ⟨⟨fun v hv w hw => ?_, fun s hs t ht => ?_⟩, ⟨fun v hv => ?_, fun s hs => ?_⟩, ?_, ?_⟩
  · rw [hQb v hv, hQb w hw, hPb v hv, hPb w hw]; nlinarith [sq_nonneg (v - w)]
  · rw [hQs s hs, hQs t ht, hPs s hs, hPs t ht]; nlinarith [sq_nonneg (s - t)]
  · rw [BilateralTrade.Mechanism.interimBuyerUtility, hQb v hv, hPb v hv]; nlinarith [sq_nonneg v]
  · rw [BilateralTrade.Mechanism.interimSellerUtility, hQs s hs, hPs s hs]
    nlinarith [sq_nonneg (1 - s)]
  · rw [BilateralTrade.Mechanism.interimBuyerUtility, hQb 0 ⟨le_rfl, zero_le_one⟩,
      hPb 0 ⟨le_rfl, zero_le_one⟩]
    norm_num
  · rw [BilateralTrade.Mechanism.interimSellerUtility, hQs 1 ⟨zero_le_one, le_rfl⟩,
      hPs 1 ⟨zero_le_one, le_rfl⟩]
    norm_num

/-- **Checked `Uniform[0, 1]` Myerson–Satterthwaite witness**: `vcgTrade` attains the exact
expected budget deficit `−1/6` and violates ex-ante weak budget balance. -/
example :
    ∫ p, (vcgTrade.buyerPayment p.1 p.2 - vcgTrade.sellerPayment p.1 p.2) ∂(unif.prod unif) =
      -(1 / 6) ∧
    ¬ vcgTrade.IsExAnteBudgetBalanced unif unif := by
  obtain ⟨hBIC, hIR, hU0, hU1⟩ := vcgTrade_isBIC_isInterimIR_boundary
  obtain ⟨hpb, hps⟩ := vcgTrade_integrable
  have heq := BilateralTrade.Mechanism.budget_surplus_uniform_eq hBIC vcgTrade_isExPostEfficient
    hpb hps
  rw [hU0, hU1, add_zero, add_zero] at heq
  exact ⟨heq, BilateralTrade.Mechanism.not_isExAnteBudgetBalanced_uniform hBIC hIR
    vcgTrade_isExPostEfficient hpb hps⟩

/-- **Boundary witness (non-overlapping supports)**: when the seller's cost lies in `[0, 1]` and
the buyer's value lies in `[2, 3]` (`v_s ≤ 3/2 ≤ v_b`), the posted-price mechanism
`fixedPrice (3/2)` IS simultaneously BIC, interim IR, ex-post efficient, and ex-ante
budget-balanced! -/
example :
    (BilateralTrade.fixedPrice (3 / 2)).IsBIC unif23 unif 2 3 0 1 ∧
    (BilateralTrade.fixedPrice (3 / 2)).IsInterimIR unif23 unif 2 3 0 1 ∧
    (BilateralTrade.fixedPrice (3 / 2)).IsExPostEfficient ∧
    (BilateralTrade.fixedPrice (3 / 2)).IsExAnteBudgetBalanced unif23 unif := by
  have ⟨hBIC, hIR⟩ := BilateralTrade.fixedPrice_isBIC_and_isInterimIR
    (μ_b := unif23) (μ_s := unif) (a_b := 2) (b_b := 3) (a_s := 0) (b_s := 1) (c := 3 / 2)
    (by norm_num) (by norm_num) (ae_restrict_mem measurableSet_Icc)
    (ae_restrict_mem measurableSet_Icc)
  exact ⟨hBIC, hIR, BilateralTrade.fixedPrice_isExPostEfficient _,
    BilateralTrade.fixedPrice_isExAnteBudgetBalanced _ _ _⟩

/-! ### Bulow–Klemperer: checked witnesses for `Uniform[0, 1]` bidders -/

/-- For `n` i.i.d. `Uniform[0, 1]` bidders, Myerson's optimal auction revenue is at most the
`(n + 1)`-bidder Vickrey auction revenue (`n / (n + 2)`). -/
example (n : ℕ) :
    ∫ v, ∑ i : Fin n,
        (myerson (Vickrey.reserveAllocation (virtualValue unif fun _ => 1))).payment v i
        ∂Measure.pi (fun _ : Fin n => unif) ≤
      ∫ v, ∑ i : Fin (n + 1), (Vickrey.mechanism (ι := Fin (n + 1))).payment v i
        ∂Measure.pi (fun _ : Fin (n + 1) => unif) :=
  Vickrey.integral_sum_payment_reserve_le_vickrey_succ hasValueDensity_uniform isRegular_uniform n

/-- Concrete `n = 1` check: for `1` uniform bidder, Myerson's optimal auction (posted price `1/2`)
has expected revenue `1/4 ≤ 1/3`, the expected revenue of `2`-bidder Vickrey without reserve. -/
example :
    ∫ v, ∑ i : Fin 1,
        (myerson (Vickrey.reserveAllocation (virtualValue unif fun _ => 1))).payment v i
        ∂Measure.pi (fun _ : Fin 1 => unif) ≤ 1 / 3 := by
  have hBK := Vickrey.integral_sum_payment_reserve_le_vickrey_succ hasValueDensity_uniform
    isRegular_uniform 1
  have hV : ∫ v, ∑ i : Fin 2, (Vickrey.mechanism (ι := Fin 2)).payment v i
      ∂Measure.pi (fun _ : Fin 2 => unif) = 1 / 3 := by
    rw [FirstPrice.integral_sum_payment_vickrey (ι := Fin 2), Fintype.card_fin]
    norm_num
  exact hBK.trans_eq hV

/-- Non-vacuous Bayes–Nash Bulow–Klemperer check: the `2`-bidder first-price auction in its
`v / 2` Bayes–Nash equilibrium earns at most the `3`-bidder Vickrey auction (`1/3 ≤ 1/2`). -/
example :
    ∫ v, ∑ i : Fin 2, FirstPrice.mechanism.payment (fun j => FirstPrice.uniformBid 2 (v j)) i
        ∂Measure.pi (fun _ : Fin 2 => unif) ≤
      ∫ v, ∑ i : Fin 3, (Vickrey.mechanism (ι := Fin 3)).payment v i
        ∂Measure.pi (fun _ : Fin 3 => unif) := by
  have hBN : FirstPrice.mechanism.IsBayesNash (fun _ : Fin 2 => unif) (fun _ => 1)
      (fun _ => FirstPrice.uniformBid 2) := by
    simpa only [Fintype.card_fin] using FirstPrice.isBayesNash_uniformBid (ι := Fin 2)
  have h0 : ∀ i : Fin 2, FirstPrice.mechanism.interimPayment (fun _ : Fin 2 => unif)
      (fun _ => FirstPrice.uniformBid 2) i (FirstPrice.uniformBid 2 0) ≤ 0 := fun i => by
    rw [FirstPrice.interimPayment_eq, FirstPrice.uniformBid, mul_zero, zero_mul]
  have hp : ∀ i : Fin 2, Integrable (fun v : Fin 2 → ℝ =>
      FirstPrice.mechanism.payment (fun j => FirstPrice.uniformBid 2 (v j)) i)
      (Measure.pi fun _ : Fin 2 => unif) := fun i => by
    simpa only [Fintype.card_fin] using FirstPrice.integrable_payment_uniformBid (ι := Fin 2) i
  have hx : ∀ i : Fin 2, Measurable fun v : Fin 2 → ℝ =>
      FirstPrice.mechanism.allocation (fun j => FirstPrice.uniformBid 2 (v j)) i := fun i =>
    (Vickrey.measurable_allocation i).comp
      (measurable_pi_iff.2 fun j =>
        (FirstPrice.measurable_uniformBid 2).comp (measurable_pi_apply j))
  exact Vickrey.integral_sum_payment_le_vickrey_succ_of_isBayesNash hasValueDensity_uniform
    isRegular_uniform hBN h0 (fun b _ => Vickrey.allocation_mem_singleItemFeasible b) hp hx

end CslibFrontierTests.MechanismGrovesMS
