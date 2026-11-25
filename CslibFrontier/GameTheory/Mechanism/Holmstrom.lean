/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.VCG
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Basic
import CslibFrontier.GameTheory.Mechanism.Bayesian
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

/-!
# Uniqueness of Groves mechanisms (Green–Laffont and Holmström)

This file formalizes the uniqueness of Groves payment rules for dominant-strategy
incentive-compatible (DSIC), welfare-maximizing direct mechanisms:

* **Green–Laffont theorem** ([GreenLaffont1977]; [Nisan2007], §9.5.5, Theorem 9.37; locators not
  re-verified against primary PDF): on the unrestricted valuation domain `Ω → ℝ`, every DSIC,
  welfare-maximizing direct mechanism is a Groves mechanism (`Mechanism.exists_groves_of_isDSIC`).
* **Holmström's theorem** ([Holmstrom1979]; locator not re-verified against primary PDF): the same
  characterization holds on every **smoothly connected** valuation domain
  (`Mechanism.exists_groves_of_isSmoothlyConnected`), and on every **convex** valuation domain
  without any finiteness assumption on the outcome space (`Mechanism.exists_groves_of_convex`).
* **Connectedness is necessary**: on a disconnected two-point valuation domain, there is a DSIC,
  welfare-maximizing direct mechanism that is not a Groves mechanism
  (`Mechanism.disconnectedNonGroves_not_groves`).

Both proofs first establish **payment uniqueness** (revenue equivalence for DSIC mechanisms with
the same outcome rule): for two DSIC mechanisms `M₁, M₂` with the same outcome rule `f`, the
payment difference `p₁(vᵢ, b₋ᵢ) − p₂(vᵢ, b₋ᵢ)` is independent of `vᵢ` along every convex segment
(by reducing to `SingleParameter.IsTruthfulOn.payment_eq`) and along every uniformly differentiable
curve with bounded coordinate derivatives (by the envelope theorem: each truthful utility curve is
Lipschitz, hence absolutely continuous and a.e. differentiable, and its derivative at every
differentiable interior point is `γ'(t)(f(γ(t)))` by Fermat's theorem
`IsLocalMin.hasDerivAt_eq_zero`, so the difference of the two utilities has zero derivative a.e.
and is constant by `AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero`). Comparing `M`
against the zero-pivot Groves mechanism `groves M.outcome (fun _ _ => 0)` yields the Groves pivot
`hᵢ(b₋ᵢ)`.

## Main definitions

* `Mechanism.IsSmoothlyConnected`: Holmström's smoothly connected domain condition.
* `Mechanism.disconnectedDomains`, `Mechanism.disconnectedNonGroves`: two-agent counterexample on a
  disconnected two-point domain.

## Main results

* `Mechanism.IsSmoothlyConnected.of_convex`: every convex domain over finitely many outcomes is
  smoothly connected.
* `Mechanism.payment_sub_eq_of_isSmoothlyConnected`, `Mechanism.payment_sub_eq_of_convex`:
  DSIC payment uniqueness on smoothly connected and convex domains.
* `Mechanism.exists_groves_of_isSmoothlyConnected`, `Mechanism.exists_groves_of_convex`:
  **Holmström's theorem**.
* `Mechanism.exists_groves_of_isDSIC`: **Green–Laffont theorem** on unrestricted domains.
* `Mechanism.disconnectedNonGroves_not_groves`: failure of Groves uniqueness on a disconnected
  two-point domain.

## References

* [J. Green, J.-J. Laffont, *Characterization of satisfactory mechanisms for the revelation of
  preferences for public goods*][GreenLaffont1977]
* [B. Holmström, *Groves' scheme on restricted domains*][Holmstrom1979]
* [N. Nisan, *Introduction to Mechanism Design (for Computer Scientists)*][Nisan2007]
-/

open MeasureTheory Set

public section

namespace Cslib.GameTheory.Mechanism

variable {ι Ω : Type*}

/-- A valuation domain `S ⊆ (Ω → ℝ)` is **smoothly connected** ([Holmstrom1979]; locator not
re-verified against primary PDF) if any two valuations `v₀, v₁ ∈ S` are joined by a curve
`γ : ℝ → Ω → ℝ` staying in `S` on `[0, 1]` whose coordinates `t ↦ γ t ω` are differentiable on
`[0, 1]` with uniformly bounded derivatives `|γ' t ω| ≤ K`. -/
@[expose] def IsSmoothlyConnected (S : Set (Ω → ℝ)) : Prop :=
  ∀ v₀ ∈ S, ∀ v₁ ∈ S, ∃ (γ γ' : ℝ → Ω → ℝ) (K : ℝ),
    γ 0 = v₀ ∧ γ 1 = v₁ ∧
    (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ S) ∧
    (∀ (ω : Ω) (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
      HasDerivWithinAt (fun s => γ s ω) (γ' t ω) (Icc 0 1) t) ∧
    (∀ (ω : Ω) (t : ℝ), t ∈ Icc (0 : ℝ) 1 → |γ' t ω| ≤ K)

/-- Every convex domain of valuations over finitely many outcomes is smoothly connected, via
straight-line interpolation `γ(t) = (1 − t) • v₀ + t • v₁`. -/
theorem IsSmoothlyConnected.of_convex [Finite Ω] {S : Set (Ω → ℝ)} (hS : Convex ℝ S) :
    IsSmoothlyConnected S := by
  have := Fintype.ofFinite Ω
  intro v₀ hv₀ v₁ hv₁
  refine ⟨fun t => (1 - t) • v₀ + t • v₁, fun _ ω => v₁ ω - v₀ ω,
    Finset.univ.fold max 0 (fun ω => |v₁ ω - v₀ ω|),
    by simp only [sub_zero, one_smul, zero_smul, add_zero],
    by simp only [sub_self, zero_smul, one_smul, zero_add],
    fun t ht => hS hv₀ hv₁ (sub_nonneg.2 ht.2) ht.1 (by ring), fun ω t _ => ?_,
    fun ω _ _ => (Finset.le_fold_max _).2 (Or.inr ⟨ω, Finset.mem_univ ω, le_rfl⟩)⟩
  have h := (((hasDerivAt_const t (1 : ℝ)).fun_sub (hasDerivAt_id t)).mul_const (v₀ ω)).fun_add
    ((hasDerivAt_id t).mul_const (v₁ ω))
  rw [show (0 - 1) * v₀ ω + 1 * v₁ ω = v₁ ω - v₀ ω by ring] at h
  exact h.hasDerivWithinAt

/-! ### Payment uniqueness along convex segments and smooth curves -/

private theorem dsic_utility_sandwich [DecidableEq ι] {M : Mechanism ι Ω} {V : ι → Set (Ω → ℝ)}
    (hM : M.IsDSICOn V) {i : ι} {b : ι → Ω → ℝ} (hb : ∀ j, b j ∈ V j)
    {v w : Ω → ℝ} (hv : v ∈ V i) (hw : w ∈ V i) :
    (v (M.outcome (Function.update b i w)) - w (M.outcome (Function.update b i w))) ≤
      M.utility i v (Function.update b i v) - M.utility i w (Function.update b i w) := by
  have hb' : ∀ j, Function.update b i w j ∈ V j := fun j => by
    rcases eq_or_ne j i with rfl | hj
    · rw [Function.update_self]; exact hw
    · rw [Function.update_of_ne hj]; exact hb j
  have h := hM i (Function.update b i w) v hb' hv
  simp only [Function.update_idem, utility] at h ⊢
  linarith

/-- Along a uniformly differentiable curve `γ : [0, 1] → V i` with coordinate derivatives bounded
by `K`, the truthful utility `U(t)` is `|K|`-Lipschitz on `[0, 1]` and its derivative at every
differentiable interior point `t ∈ (0, 1)` is `γ'(t)(M.outcome (update b i (γ t)))`. -/
private theorem utility_curve_properties [DecidableEq ι] {M : Mechanism ι Ω} {V : ι → Set (Ω → ℝ)}
    (hM : M.IsDSICOn V) {i : ι} {b : ι → Ω → ℝ} (hb : ∀ j, b j ∈ V j)
    {γ γ' : ℝ → Ω → ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hγV : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ V i)
    (hγd : ∀ (ω : Ω) (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
      HasDerivWithinAt (fun s => γ s ω) (γ' t ω) (Icc 0 1) t)
    (hγK : ∀ (ω : Ω) (t : ℝ), t ∈ Icc (0 : ℝ) 1 → |γ' t ω| ≤ K) :
    let U : ℝ → ℝ := fun t => M.utility i (γ t) (Function.update b i (γ t))
    AbsolutelyContinuousOnInterval U 0 1 ∧
      ∀ t ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ U t →
        HasDerivAt U (γ' t (M.outcome (Function.update b i (γ t)))) t := by
  intro U
  have hlip_coord (ω : Ω) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
      |γ s ω - γ t ω| ≤ K * |s - t| := by
    simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun r => γ r ω) (f' := fun r => γ' r ω) (s := Icc 0 1) (C := K)
      (fun r hr => hγd ω r hr) (fun r hr => (Real.norm_eq_abs _).trans_le (hγK ω r hr))
      (convex_Icc 0 1) ht hs
  have hlipU : LipschitzOnWith (⟨K, hK0⟩ : NNReal) U (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    refine lipschitzOnWith_iff_dist_le_mul.2 fun s hs t ht => ?_
    change |M.utility i (γ s) (Function.update b i (γ s)) -
      M.utility i (γ t) (Function.update b i (γ t))| ≤ K * |s - t|
    have hb1 := abs_le.1 (hlip_coord (M.outcome (Function.update b i (γ t))) hs ht)
    have hb2 := abs_le.1 (hlip_coord (M.outcome (Function.update b i (γ s))) hs ht)
    exact abs_le.2 ⟨by linarith [dsic_utility_sandwich hM hb (hγV s hs) (hγV t ht)],
      by linarith [dsic_utility_sandwich hM hb (hγV t ht) (hγV s hs)]⟩
  refine ⟨hlipU.absolutelyContinuousOnInterval, fun t ht hdiff => ?_⟩
  set ω₀ := M.outcome (Function.update b i (γ t))
  have hγt : HasDerivAt (fun s => γ s ω₀) (γ' t ω₀) t :=
    (hγd ω₀ t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hmin : IsLocalMin (fun s => U s - γ s ω₀) t := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    linarith [dsic_utility_sandwich hM hb (hγV s hs) (hγV t (Ioo_subset_Icc_self ht))]
  exact sub_eq_zero.1 (hmin.hasDerivAt_eq_zero (hdiff.hasDerivAt.sub hγt)) ▸ hdiff.hasDerivAt

/-- **DSIC payment uniqueness on smoothly connected domains** ([Holmstrom1979]; locator not
re-verified against primary PDF): if two DSIC mechanisms `M₁, M₂` on `V` share the same outcome
rule and `V i` is smoothly connected, then `p₁(vᵢ, b₋ᵢ) − p₂(vᵢ, b₋ᵢ)` is independent of `vᵢ`. -/
theorem payment_sub_eq_of_isSmoothlyConnected [DecidableEq ι] {M₁ M₂ : Mechanism ι Ω}
    {V : ι → Set (Ω → ℝ)} (hout : M₁.outcome = M₂.outcome)
    (hM₁ : M₁.IsDSICOn V) (hM₂ : M₂.IsDSICOn V) {i : ι} (hV : IsSmoothlyConnected (V i))
    {b : ι → Ω → ℝ} (hb : ∀ j, b j ∈ V j) {v₀ v₁ : Ω → ℝ} (hv₀ : v₀ ∈ V i) (hv₁ : v₁ ∈ V i) :
    M₁.payment (Function.update b i v₁) i - M₂.payment (Function.update b i v₁) i =
      M₁.payment (Function.update b i v₀) i - M₂.payment (Function.update b i v₀) i := by
  obtain ⟨γ, γ', K, hγ0, hγ1, hγV, hγd, hγK⟩ := hV v₀ hv₀ v₁ hv₁
  have hγK' : ∀ (ω : Ω) (t : ℝ), t ∈ Icc (0 : ℝ) 1 → |γ' t ω| ≤ max K 0 := fun ω t ht =>
    (hγK ω t ht).trans (le_max_left K 0)
  obtain ⟨hAC₁, hD₁⟩ := utility_curve_properties hM₁ hb (le_max_right K 0) hγV hγd hγK'
  obtain ⟨hAC₂, hD₂⟩ := utility_curve_properties hM₂ hb (le_max_right K 0) hγV hγd hγK'
  set U₁ : ℝ → ℝ := fun t => M₁.utility i (γ t) (Function.update b i (γ t))
  set U₂ : ℝ → ℝ := fun t => M₂.utility i (γ t) (Function.update b i (γ t))
  have hae_ne (c : ℝ) : ∀ᵐ t : ℝ, t ≠ c := by
    rw [ae_iff]
    simp only [ne_eq, not_not, ofPred_eq_eq_singleton, Real.volume_singleton]
  have hzero : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) 1 → HasDerivAt (fun s => U₁ s - U₂ s) 0 t := by
    filter_upwards [hAC₁.ae_differentiableAt, hAC₂.ae_differentiableAt, hae_ne 0, hae_ne 1]
      with t hd₁ hd₂ ht0 ht1 ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := by
      rw [uIcc_of_le zero_le_one] at ht
      exact ⟨lt_of_le_of_ne ht.1 ht0.symm, lt_of_le_of_ne ht.2 ht1⟩
    have h1 := hD₁ t ht' (hd₁ ht)
    rw [hout] at h1
    simpa only [sub_self] using h1.fun_sub (hD₂ t ht' (hd₂ ht))
  obtain ⟨C, hC⟩ := (hAC₁.sub hAC₂).const_of_ae_hasDerivAt_zero hzero
  have hdiff : U₁ 1 - U₂ 1 = U₁ 0 - U₂ 0 :=
    (hC 1 right_mem_uIcc).trans (hC 0 left_mem_uIcc).symm
  simp only [U₁, U₂, utility, hγ0, hγ1, hout] at hdiff
  linarith

/-- **DSIC payment uniqueness on convex domains** ([Nisan2007], §9.5.5, Theorem 9.37;
[Holmstrom1979]; locators not re-verified against primary PDF): for an arbitrary (possibly infinite)
outcome space `Ω`, if two DSIC mechanisms `M₁, M₂` on `V` share the same outcome rule and `V i` is
convex, then `p₁(vᵢ, b₋ᵢ) − p₂(vᵢ, b₋ᵢ)` is independent of `vᵢ`.

The proof restricts both mechanisms to the affine segment `γ(t) = (1 − t) v₀ + t v₁`, reducing
directly to the one-dimensional payment identity `SingleParameter.IsTruthfulOn.payment_eq`. -/
theorem payment_sub_eq_of_convex [DecidableEq ι] {M₁ M₂ : Mechanism ι Ω}
    {V : ι → Set (Ω → ℝ)} (hout : M₁.outcome = M₂.outcome)
    (hM₁ : M₁.IsDSICOn V) (hM₂ : M₂.IsDSICOn V) {i : ι} (hV : Convex ℝ (V i))
    {b : ι → Ω → ℝ} (hb : ∀ j, b j ∈ V j) {v₀ v₁ : Ω → ℝ} (hv₀ : v₀ ∈ V i) (hv₁ : v₁ ∈ V i) :
    M₁.payment (Function.update b i v₁) i - M₂.payment (Function.update b i v₁) i =
      M₁.payment (Function.update b i v₀) i - M₂.payment (Function.update b i v₀) i := by
  let γ : ℝ → Ω → ℝ := fun t => (1 - t) • v₀ + t • v₁
  have hγ0 : γ 0 = v₀ := by simp only [γ, sub_zero, one_smul, zero_smul, add_zero]
  have hγ1 : γ 1 = v₁ := by simp only [γ, sub_self, zero_smul, one_smul, zero_add]
  have hγV : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ V i := fun t ht =>
    hV hv₀ hv₁ (sub_nonneg.2 ht.2) ht.1 (by ring)
  let X : ℝ → ℝ := fun t =>
    v₁ (M₁.outcome (Function.update b i (γ t))) - v₀ (M₁.outcome (Function.update b i (γ t)))
  have hT (M : Mechanism ι Ω) (houtM : M.outcome = M₁.outcome) (hM : M.IsDSICOn V) :
      SingleParameter.IsTruthfulOn X
        (fun t => M.payment (Function.update b i (γ t)) i -
          v₀ (M₁.outcome (Function.update b i (γ t))))
        (Icc 0 1) := fun t ht s hs => by
    have hbs : ∀ j, Function.update b i (γ s) j ∈ V j := fun j => by
      rcases eq_or_ne j i with rfl | hj
      · simpa only [Function.update_self] using hγV s hs
      · simpa only [Function.update_of_ne hj] using hb j
    have h := hM i (Function.update b i (γ s)) (γ t) hbs (hγV t ht)
    simp only [utility, Function.update_idem, γ, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      houtM] at h
    dsimp only [X]
    linarith
  have hP₁ := (hT M₁ rfl hM₁).payment_eq (v := 1) ⟨zero_le_one, le_rfl⟩
  have hP₂ := (hT M₂ hout.symm hM₂).payment_eq (v := 1) ⟨zero_le_one, le_rfl⟩
  simp only [hγ0, hγ1] at hP₁ hP₂
  linarith

/-! ### Uniqueness of Groves mechanisms -/

private theorem exists_groves_of_payment_sub_const [Fintype ι] [DecidableEq ι]
    {M : Mechanism ι Ω} {V : ι → Set (Ω → ℝ)}
    (hconst : ∀ (i : ι) (b : ι → Ω → ℝ), (∀ j, b j ∈ V j) → ∀ v₀ ∈ V i, ∀ v₁ ∈ V i,
      M.payment (Function.update b i v₁) i -
        (groves M.outcome (fun _ _ => 0)).payment (Function.update b i v₁) i =
      M.payment (Function.update b i v₀) i -
        (groves M.outcome (fun _ _ => 0)).payment (Function.update b i v₀) i) :
    ∃ h : ι → (ι → Ω → ℝ) → ℝ,
      (∀ i b v, h i (Function.update b i v) = h i b) ∧
      ∀ b, (∀ j, b j ∈ V j) → ∀ i, M.payment b i = (groves M.outcome h).payment b i := by
  classical
  let v₀ : ι → Ω → ℝ := fun i => if hne : (V i).Nonempty then hne.some else 0
  let h : ι → (ι → Ω → ℝ) → ℝ := fun i b =>
    M.payment (Function.update b i (v₀ i)) i +
      ∑ j ∈ Finset.univ.erase i, b j (M.outcome (Function.update b i (v₀ i)))
  refine ⟨h, ?_, ?_⟩
  · intro i b v
    simp only [h, Function.update_idem]
    congr 1
    exact Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  · intro b hb i
    have hne : (V i).Nonempty := ⟨b i, hb i⟩
    have hv₀ : v₀ i ∈ V i := by
      simp only [v₀, hne, ↓reduceDIte]
      exact hne.some_mem
    have key := hconst i b hb (v₀ i) hv₀ (b i) (hb i)
    have hsum : ∑ j ∈ Finset.univ.erase i, Function.update b i (v₀ i) j
        (M.outcome (Function.update b i (v₀ i))) =
      ∑ j ∈ Finset.univ.erase i, b j (M.outcome (Function.update b i (v₀ i))) :=
      Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    simp only [Function.update_eq_self, groves, zero_sub, sub_neg_eq_add, hsum] at key
    simp only [groves, h]
    linarith

/-- **Holmström's theorem on smoothly connected domains** ([Holmstrom1979]; locator not
re-verified against primary PDF): if every agent's valuation domain `V i` is smoothly connected,
then every DSIC, welfare-maximizing direct mechanism on `V` is a Groves mechanism on `V`
(`pᵢ(b) = hᵢ(b₋ᵢ) − ∑ⱼ≠ᵢ bⱼ(f(b))` for some `hᵢ` independent of `bᵢ`). -/
theorem exists_groves_of_isSmoothlyConnected [Fintype ι] [DecidableEq ι] {M : Mechanism ι Ω}
    {V : ι → Set (Ω → ℝ)} (hM : M.IsDSICOn V) (hf : IsWelfareMaximizingOn M.outcome V)
    (hV : ∀ i, IsSmoothlyConnected (V i)) :
    ∃ h : ι → (ι → Ω → ℝ) → ℝ,
      (∀ i b v, h i (Function.update b i v) = h i b) ∧
      ∀ b, (∀ j, b j ∈ V j) → ∀ i, M.payment b i = (groves M.outcome h).payment b i :=
  exists_groves_of_payment_sub_const fun i _ hb _ hv₀ _ hv₁ =>
    payment_sub_eq_of_isSmoothlyConnected (M₁ := M) (M₂ := groves M.outcome (fun _ _ => 0)) rfl hM
      (groves_isDSICOn hf fun _ _ _ _ _ => rfl) (hV i) hb hv₀ hv₁

/-- **Holmström's theorem on convex domains** ([Holmstrom1979]; [Nisan2007], §9.5.5, Theorem 9.37;
locators not re-verified against primary PDF): if every agent's valuation domain `V i` is convex,
then every DSIC, welfare-maximizing direct mechanism on `V` is a Groves mechanism on `V`, for any
(possibly infinite) outcome space `Ω`. -/
theorem exists_groves_of_convex [Fintype ι] [DecidableEq ι] {M : Mechanism ι Ω}
    {V : ι → Set (Ω → ℝ)} (hM : M.IsDSICOn V) (hf : IsWelfareMaximizingOn M.outcome V)
    (hV : ∀ i, Convex ℝ (V i)) :
    ∃ h : ι → (ι → Ω → ℝ) → ℝ,
      (∀ i b v, h i (Function.update b i v) = h i b) ∧
      ∀ b, (∀ j, b j ∈ V j) → ∀ i, M.payment b i = (groves M.outcome h).payment b i :=
  exists_groves_of_payment_sub_const fun i _ hb _ hv₀ _ hv₁ =>
    payment_sub_eq_of_convex (M₁ := M) (M₂ := groves M.outcome (fun _ _ => 0)) rfl hM
      (groves_isDSICOn hf fun _ _ _ _ _ => rfl) (hV i) hb hv₀ hv₁

/-- **Green–Laffont theorem** ([GreenLaffont1977]; [Nisan2007], §9.5.5; locators not re-verified
against primary PDF): on the unrestricted valuation domain `Ω → ℝ`, every DSIC, welfare-maximizing
direct mechanism is a Groves mechanism `M = groves M.outcome h` with `hᵢ` independent of `i`'s
report. -/
theorem exists_groves_of_isDSIC [Fintype ι] [DecidableEq ι] {M : Mechanism ι Ω}
    (hM : M.IsDSIC) (hf : IsWelfareMaximizing M.outcome) :
    ∃ h : ι → (ι → Ω → ℝ) → ℝ,
      (∀ i b v, h i (Function.update b i v) = h i b) ∧ M = groves M.outcome h := by
  obtain ⟨h, hh, hpay⟩ := exists_groves_of_convex (V := fun _ => Set.univ)
    (hM.isDSICOn _) (fun b _ ω => hf b ω) (fun _ => convex_univ)
  refine ⟨h, hh, ?_⟩
  cases M
  simpa only [groves, Mechanism.mk.injEq, true_and, funext_iff] using
    fun b i => hpay b (fun _ => Set.mem_univ _) i

/-! ### Counterexample on a disconnected two-point domain -/

/-- Valuation assigning `0` to `false` and `c` to `true`. -/
@[expose] def twoOutcomeVal (c : ℝ) : Bool → ℝ := fun ω => if ω then c else 0

/-- A two-agent valuation domain in which agent `0` has a disconnected two-point domain
`{0, 2}` on `true` and agent `1` has the singleton valuation `-1` on `true`. -/
@[expose] def disconnectedDomains : Fin 2 → Set (Bool → ℝ) :=
  ![{twoOutcomeVal 0, twoOutcomeVal 2}, {twoOutcomeVal (-1)}]

/-- A mechanism on `Fin 2` and `Bool` that maximizes welfare on `disconnectedDomains` and charges
agent `0` the amount `3/2` when `true` is chosen (instead of the Groves externality `1`). -/
@[expose] noncomputable def disconnectedNonGroves : Mechanism (Fin 2) Bool where
  outcome b := decide (welfare b false ≤ welfare b true)
  payment b i :=
    if i = 0 ∧ decide (welfare b false ≤ welfare b true) = true then 3 / 2 else 0

/-- `disconnectedNonGroves` maximizes welfare on all profiles (hence on `disconnectedDomains`). -/
theorem disconnectedNonGroves_isWelfareMaximizingOn :
    IsWelfareMaximizingOn disconnectedNonGroves.outcome disconnectedDomains := by
  intro b _ ω
  by_cases h : welfare b false ≤ welfare b true <;> cases ω <;>
    simp only [disconnectedNonGroves, h, decide_true, decide_false, le_refl, le_of_not_ge,
      not_false_eq_true]

/-- `disconnectedNonGroves` is DSIC on the disconnected domain `disconnectedDomains`:
type `0` prefers `(false, 0)` over `(true, 3/2)` (`0 ≥ -3/2`), while type `2` prefers
`(true, 3/2)` over `(false, 0)` (`2 - 3/2 = 1/2 ≥ 0`). -/
theorem disconnectedNonGroves_isDSICOn :
    disconnectedNonGroves.IsDSICOn disconnectedDomains := by
  intro i b v hb hv
  have hb0 : b 0 = twoOutcomeVal 0 ∨ b 0 = twoOutcomeVal 2 := by
    simpa only [disconnectedDomains, Matrix.cons_val_zero, Set.mem_insert_iff,
      Set.mem_singleton_iff] using hb 0
  have hb1 : b 1 = twoOutcomeVal (-1) := Set.mem_singleton_iff.1 (hb 1)
  rcases i with ⟨_ | _ | n, hn⟩
  · rw [Fin.zero_eta] at hv ⊢
    have hv0 : v = twoOutcomeVal 0 ∨ v = twoOutcomeVal 2 := by
      simpa only [disconnectedDomains, Matrix.cons_val_zero, Set.mem_insert_iff,
        Set.mem_singleton_iff] using hv
    simp only [utility, disconnectedNonGroves, welfare, Fin.sum_univ_two, Function.update_self,
      Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0), hb1, true_and]
    rcases hb0 with hb0 | hb0 <;> rcases hv0 with rfl | rfl <;>
      rw [hb0] <;> norm_num [twoOutcomeVal]
  · rw [Fin.mk_one] at hv ⊢
    rw [Set.mem_singleton_iff.1 hv, ← hb1, Function.update_eq_self]
  · omega

/-- **Connectedness is necessary for Groves uniqueness**: `disconnectedNonGroves` is DSIC and
welfare-maximizing on `disconnectedDomains`, yet no Groves pivot `h` reproduces its payments on
`disconnectedDomains`, because `p₀(2, -1) − p₀(0, -1) = 3/2 ≠ 1 = −(−1 − 0)`. -/
theorem disconnectedNonGroves_not_groves :
    ¬ ∃ h : Fin 2 → (Fin 2 → Bool → ℝ) → ℝ,
      (∀ i b v, h i (Function.update b i v) = h i b) ∧
      ∀ b, (∀ j, b j ∈ disconnectedDomains j) →
        ∀ i, disconnectedNonGroves.payment b i =
          (groves disconnectedNonGroves.outcome h).payment b i := by
  rintro ⟨h, hh, hpay⟩
  let bLo : Fin 2 → Bool → ℝ := ![twoOutcomeVal 0, twoOutcomeVal (-1)]
  let bHi : Fin 2 → Bool → ℝ := ![twoOutcomeVal 2, twoOutcomeVal (-1)]
  have hbLo : ∀ j, bLo j ∈ disconnectedDomains j := Fin.forall_fin_two.2 ⟨.inl rfl, rfl⟩
  have hbHi : ∀ j, bHi j ∈ disconnectedDomains j := Fin.forall_fin_two.2 ⟨.inr rfl, rfl⟩
  have hupd : bHi = Function.update bLo 0 (twoOutcomeVal 2) :=
    funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)
  have h0eq : h 0 bHi = h 0 bLo := hupd ▸ hh 0 bLo (twoOutcomeVal 2)
  have hLo := hpay bLo hbLo 0
  have hHi := hpay bHi hbHi 0
  simp only [groves, disconnectedNonGroves, welfare, Fin.sum_univ_two,
    show (Finset.univ : Finset (Fin 2)).erase 0 = {1} by decide, Finset.sum_singleton, bLo, bHi,
    Matrix.cons_val_zero, Matrix.cons_val_one, twoOutcomeVal] at hLo hHi
  norm_num at hLo hHi
  linarith

/-- The two-point domain `disconnectedDomains 0` is not smoothly connected (nor convex): any
continuous coordinate function `t ↦ γ t true` staying in `{0, 2}` cannot connect `0` to `2`. -/
theorem not_isSmoothlyConnected_disconnectedDomains :
    ¬ IsSmoothlyConnected (disconnectedDomains 0) := by
  intro hsc
  obtain ⟨γ, _, _, h0, h1, hmem, hderiv, _⟩ :=
    hsc (twoOutcomeVal 0) (Or.inl rfl) (twoOutcomeVal 2) (Or.inr rfl)
  obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc zero_le_one
    (fun t ht => (hderiv true t ht).continuousWithinAt)
    (by simp only [h0, h1, twoOutcomeVal, ↓reduceIte]; norm_num : (1 : ℝ) ∈ Icc _ _)
  have hmem' : γ t = twoOutcomeVal 0 ∨ γ t = twoOutcomeVal 2 := by
    simpa only [disconnectedDomains, Matrix.cons_val_zero, Set.mem_insert_iff,
      Set.mem_singleton_iff] using hmem t ht
  rcases hmem' with h | h <;> simp only [h, twoOutcomeVal, ↓reduceIte] at hteq <;> linarith

end Cslib.GameTheory.Mechanism
