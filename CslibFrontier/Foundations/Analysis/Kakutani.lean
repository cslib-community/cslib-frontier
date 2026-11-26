/-
Copyright (c) 2026 Matthew Doty, Nick L. Leppelmeier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Nick L. Leppelmeier
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Topology/MetricSpace/Kakutani.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Analysis.Brouwer.Simplex
public import CslibFrontier.Foundations.Analysis.InnerProductSpace.MetricProjection
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Dynamics.FixedPoints.Defs
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Semicontinuity.Hemicontinuity
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Sequences

/-!
# Brouwer on compact convex sets and Kakutani's fixed-point theorem

This module extends Brouwer's fixed-point theorem from the unit cube to arbitrary nonempty compact
convex sets in `ι → ℝ` for finite `ι`, and proves **Kakutani's fixed-point theorem**
([Kakutani1941]).

* `Cslib.Kakutani.exists_isFixedPt_of_isCompact_convex`: any continuous self-map of a nonempty
  compact convex set `K ⊆ (ι → ℝ)` (for finite `ι`) has a fixed point, proved by retracting a
  bounding cube onto `K` via `Cslib.metricProjection` in `EuclideanSpace ℝ ι`.
* `Cslib.Kakutani.exists_mem_of_upperHemicontinuousOn`: any upper hemicontinuous correspondence
  `F : (ι → ℝ) → Set (ι → ℝ)` mapping a nonempty compact convex set `K` to nonempty closed convex
  subsets of `K` has a fixed point `x ∈ K` with `x ∈ F x` ([Kakutani1941]), proved via Cellina's
  partition-of-unity continuous approximation and compactness.
* `Cslib.Kakutani.exists_mem_of_isClosed_graph`: closed-graph formulation of Kakutani's theorem.

## References

* [S. Kakutani, *A Generalization of Brouwer's Fixed Point Theorem*][Kakutani1941]
  (primary PDF unverified)
-/

public section

namespace Cslib.Kakutani

open Set Filter Topology Finset Function

section BrouwerConvex

variable {ι : Type*} [Finite ι]

/-- **Brouwer's fixed-point theorem** for an arbitrary nonempty compact convex set `K ⊆ (ι → ℝ)`
over a finite index type `ι`. -/
theorem exists_isFixedPt_of_isCompact_convex {K : Set (ι → ℝ)}
    (hne : K.Nonempty) (hcomp : IsCompact K) (hconv : Convex ℝ K)
    {f : (ι → ℝ) → (ι → ℝ)} (hf : MapsTo f K K) (hc : ContinuousOn f K) :
    ∃ x ∈ K, IsFixedPt f x := by
  let : Fintype ι := Fintype.ofFinite ι
  let e := WithLp.linearEquiv 2 ℝ (ι → ℝ)
  let K' : Set (EuclideanSpace ℝ ι) := e.symm '' K
  have hne' : K'.Nonempty := hne.image e.symm
  have hcomp' : IsCompact K' := hcomp.image (PiLp.continuous_toLp 2 fun _ : ι => ℝ)
  have hc' : IsComplete K' := hcomp'.isComplete
  have hconv' : Convex ℝ K' := hconv.linear_image e.symm.toLinearMap
  let π : (ι → ℝ) → (ι → ℝ) := fun x => WithLp.ofLp (Cslib.metricProjection K' (WithLp.toLp 2 x))
  have hπ_mem : ∀ x, π x ∈ K := by
    intro x
    obtain ⟨y, hy, hyEq⟩ := Cslib.metricProjection_mem hne' hc' hconv' (WithLp.toLp 2 x)
    have hEq : WithLp.toLp 2 y = Cslib.metricProjection K' (WithLp.toLp 2 x) := hyEq
    have hof : y = π x := by
      have := congrArg WithLp.ofLp hEq
      simpa [π] using this
    exact hof ▸ hy
  have hπ_eq : ∀ x ∈ K, π x = x := by
    intro x hx
    have hx' : WithLp.toLp 2 x ∈ K' := ⟨x, hx, rfl⟩
    have hfix := Cslib.metricProjection_eq_self hc' hconv' hx'
    have := congrArg WithLp.ofLp hfix
    simpa [π] using this
  have hπ_cont : Continuous π :=
    (PiLp.continuous_ofLp 2 fun _ : ι => ℝ).comp
      ((Cslib.lipschitzWith_metricProjection hne' hc' hconv').continuous.comp
        (PiLp.continuous_toLp 2 fun _ : ι => ℝ))
  obtain ⟨R, hKR⟩ := hcomp.isBounded.subset_closedBall (0 : ι → ℝ)
  let R' : ℝ := max R 1
  have hR' : 0 < R' := lt_of_lt_of_le zero_lt_one (le_max_right R 1)
  have hKR' : K ⊆ Metric.closedBall 0 R' :=
    hKR.trans (Metric.closedBall_subset_closedBall (le_max_left R 1))
  let φ : (ι → ℝ) → (ι → ℝ) := fun u i => (2 * u i - 1) * R'
  let ψ : (ι → ℝ) → (ι → ℝ) := fun v i => (v i / R' + 1) / 2
  have hφψ : ∀ v, φ (ψ v) = v := by
    intro v
    ext i
    dsimp [φ, ψ]
    field_simp [hR'.ne']
    ring
  let g : (ι → ℝ) → (ι → ℝ) := fun u => ψ (f (π (φ u)))
  have hg_maps : MapsTo g (Icc 0 1) (Icc 0 1) := by
    intro u _
    have hfx : f (π (φ u)) ∈ K := hf (hπ_mem (φ u))
    have hball : dist (f (π (φ u))) 0 ≤ R' := hKR' hfx
    rw [dist_zero_right, pi_norm_le_iff_of_nonneg hR'.le] at hball
    have hneg : (-R') / R' = -1 := by rw [neg_div, div_self hR'.ne']
    have hpos : R' / R' = 1 := div_self hR'.ne'
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have hi := (abs_le.mp (hball i)).1
      dsimp [g, ψ]
      linarith [div_le_div_of_nonneg_right hi hR'.le]
    · have hi := (abs_le.mp (hball i)).2
      dsimp [g, ψ]
      linarith [div_le_div_of_nonneg_right hi hR'.le]
  have hφ_cont : Continuous φ :=
    continuous_pi fun i => ((continuous_const.mul (continuous_apply i)).sub continuous_const).mul
      continuous_const
  have hψ_cont : Continuous ψ := continuous_pi fun i => by fun_prop
  have hg_cont : ContinuousOn g (Icc 0 1) := by
    have h1 : ContinuousOn (f ∘ π ∘ φ) (Icc 0 1) :=
      hc.comp (hπ_cont.comp hφ_cont).continuousOn fun u _ => hπ_mem (φ u)
    exact hψ_cont.comp_continuousOn h1
  obtain ⟨u, _, hgu⟩ := Cslib.Brouwer.exists_isFixedPt_cube_of_finite hg_maps hg_cont
  refine ⟨π (φ u), hπ_mem (φ u), ?_⟩
  have hfixφ : φ u = f (π (φ u)) := by
    calc
      φ u = φ (g u) := congrArg φ hgu.symm
      _ = φ (ψ (f (π (φ u)))) := rfl
      _ = f (π (φ u)) := hφψ (f (π (φ u)))
  change f (π (φ u)) = π (φ u)
  exact (hπ_eq (f (π (φ u))) (hf (hπ_mem (φ u)))).symm.trans (congrArg π hfixφ.symm)

end BrouwerConvex

section Kakutani

private lemma convex_biUnion_ball {ι : Type*} [Fintype ι] {C : Set (ι → ℝ)} (hC : Convex ℝ C)
    {r : ℝ} : Convex ℝ (⋃ w ∈ C, Metric.ball w r) := by
  intro x hx y hy a b ha hb hab
  simp only [mem_iUnion, exists_prop] at hx hy ⊢
  obtain ⟨w₁, hw₁, hx₁⟩ := hx
  obtain ⟨w₂, hw₂, hy₂⟩ := hy
  refine ⟨a • w₁ + b • w₂, hC hw₁ hw₂ ha hb hab, ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hx₁ hy₂ ⊢
  have hdiff : a • x + b • y - (a • w₁ + b • w₂) = a • (x - w₁) + b • (y - w₂) := by
    simp only [smul_sub]
    abel
  rw [hdiff]
  calc
    ‖a • (x - w₁) + b • (y - w₂)‖
        ≤ ‖a • (x - w₁)‖ + ‖b • (y - w₂)‖ := norm_add_le _ _
    _ = a * ‖x - w₁‖ + b * ‖y - w₂‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ < a * r + b * r := by
        rcases eq_or_lt_of_le ha with rfl | ha_pos
        · have hb1 : b = 1 := by linarith
          subst hb1
          simpa using hy₂
        · rcases eq_or_lt_of_le hb with rfl | hb_pos
          · have ha1 : a = 1 := by linarith
            subst ha1
            simpa using hx₁
          · exact add_lt_add (mul_lt_mul_of_pos_left hx₁ ha_pos)
              (mul_lt_mul_of_pos_left hy₂ hb_pos)
    _ = r := by rw [← add_mul, hab, one_mul]

private lemma continuous_sum_finset {α β E : Type*} [TopologicalSpace α]
    [AddCommMonoid E] [TopologicalSpace E] [ContinuousAdd E]
    (s : Finset β) {g : β → α → E} (hg : ∀ b ∈ s, Continuous (g b)) :
    Continuous fun x => ∑ b ∈ s, g b x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuous_const
  | @insert b s' hb ih =>
    simp only [Finset.sum_insert hb]
    exact (hg b (Finset.mem_insert_self b s')).add
      (ih fun c hc => hg c (Finset.mem_insert_of_mem hc))

private lemma continuousOn_sum_finset {α β E : Type*} [TopologicalSpace α]
    [AddCommMonoid E] [TopologicalSpace E] [ContinuousAdd E]
    (s : Finset β) {K : Set α} {g : β → α → E} (hg : ∀ b ∈ s, ContinuousOn (g b) K) :
    ContinuousOn (fun x => ∑ b ∈ s, g b x) K := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuousOn_const
  | @insert b s' hb ih =>
    simp only [Finset.sum_insert hb]
    exact (hg b (Finset.mem_insert_self b s')).add
      (ih fun c hc => hg c (Finset.mem_insert_of_mem hc))

private lemma exists_approxFixedPt_of_upperHemicontinuousOn {ι : Type*} [Fintype ι]
    {K : Set (ι → ℝ)} (hne : K.Nonempty) (hcomp : IsCompact K) (hconv : Convex ℝ K)
    {F : (ι → ℝ) → Set (ι → ℝ)}
    (hF_ne : ∀ x ∈ K, (F x).Nonempty) (hF_sub : ∀ x ∈ K, F x ⊆ K)
    (hF_conv : ∀ x ∈ K, Convex ℝ (F x)) (hF_uhc : UpperHemicontinuousOn F K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ K, ∃ z ∈ K, ∃ w ∈ F z, dist x z < ε ∧ dist x w < ε := by
  classical
  have hcov_ball : ∀ a : K, ∃ ρ > 0,
      ∀ x ∈ Metric.ball (a : ι → ℝ) ρ ∩ K, F x ⊆ ⋃ w ∈ F a, Metric.ball w (ε / 2) := by
    intro a
    have hUopen : IsOpen (⋃ w ∈ F a, Metric.ball w (ε / 2)) :=
      isOpen_biUnion fun _ _ => Metric.isOpen_ball
    have hFsub : F a ⊆ ⋃ w ∈ F a, Metric.ball w (ε / 2) := fun w hw =>
      mem_biUnion hw (Metric.mem_ball_self (half_pos hε))
    have hev := (upperHemicontinuousOn_iff_forall_isOpen.mp hF_uhc)
      a a.2 _ hUopen hFsub
    obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hev
    exact ⟨ρ, hρ, fun x hx => hsub hx⟩
  choose ρ hρ_pos hρ_sub using hcov_ball
  let δ : K → ℝ := fun a => min (ρ a) ε / 2
  have hδ_pos : ∀ a : K, 0 < δ a := fun a => half_pos (lt_min (hρ_pos a) hε)
  have hK_cov : K ⊆ ⋃ a : K, Metric.ball (a : ι → ℝ) (δ a) := fun x hx =>
    mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hδ_pos ⟨x, hx⟩)⟩
  obtain ⟨s, hs_cov⟩ := hcomp.elim_finite_subcover
    (fun a : K => Metric.ball (a : ι → ℝ) (δ a)) (fun _ => Metric.isOpen_ball) hK_cov
  choose y hy_mem using fun a : K => hF_ne a a.2
  let wfn : K → (ι → ℝ) → ℝ := fun a x => max 0 (δ a - dist x (a : ι → ℝ))
  let W : (ι → ℝ) → ℝ := fun x => ∑ a ∈ s, wfn a x
  have hW_pos : ∀ x ∈ K, 0 < W x := by
    intro x hx
    obtain ⟨a, has, hxa⟩ := mem_iUnion₂.mp (hs_cov hx)
    have hwa : 0 < wfn a x := lt_max_of_lt_right (sub_pos.mpr (Metric.mem_ball.mp hxa))
    exact Finset.sum_pos' (fun b _ => le_max_left 0 _) ⟨a, has, hwa⟩
  let f : (ι → ℝ) → (ι → ℝ) := fun x => ∑ a ∈ s, (wfn a x / W x) • y a
  have hf_maps : MapsTo f K K := by
    intro x hx
    refine hconv.sum_mem (fun a _ => div_nonneg (le_max_left 0 _) (hW_pos x hx).le)
      ?_ (fun a _ => hF_sub a a.2 (hy_mem a))
    rw [← Finset.sum_div, div_self (hW_pos x hx).ne']
  have hw_cont : ∀ a : K, Continuous (wfn a) := fun a =>
    continuous_const.max (continuous_const.sub (continuous_id.dist continuous_const))
  have hW_cont : Continuous W := continuous_sum_finset s fun a _ => hw_cont a
  have hf_cont : ContinuousOn f K := continuousOn_sum_finset s fun a _ =>
    ((hw_cont a).continuousOn.div hW_cont.continuousOn fun x hx =>
      (hW_pos x hx).ne').smul continuousOn_const
  obtain ⟨x, hxK, hfx⟩ := exists_isFixedPt_of_isCompact_convex hne hcomp hconv hf_maps hf_cont
  let s_act : Finset K := s.filter fun a => 0 < wfn a x
  have hs_act_ne : s_act.Nonempty := by
    by_contra! hne_act
    have hW0 : W x ≤ 0 := Finset.sum_nonpos fun a has => by
      by_contra hpos
      have hgt : 0 < wfn a x := not_le.mp hpos
      have hmem : a ∈ s_act := Finset.mem_filter.mpr ⟨has, hgt⟩
      simp [hne_act] at hmem
    linarith [hW_pos x hxK]
  obtain ⟨a₀, ha₀_act, ha₀_max⟩ := Finset.exists_max_image s_act δ hs_act_ne
  have ha₀_dist : dist x (a₀ : ι → ℝ) < δ a₀ := by
    have h0 : 0 < max 0 (δ a₀ - dist x (a₀ : ι → ℝ)) := (Finset.mem_filter.mp ha₀_act).2
    rcases max_choice 0 (δ a₀ - dist x (a₀ : ι → ℝ)) with h | h
    · linarith
    · linarith
  let U₀ : Set (ι → ℝ) := ⋃ w ∈ F a₀, Metric.ball w (ε / 2)
  have hya_mem : ∀ a ∈ s_act, y a ∈ U₀ := by
    intro a ha
    have h0 : 0 < max 0 (δ a - dist x (a : ι → ℝ)) := (Finset.mem_filter.mp ha).2
    have hxa : dist x (a : ι → ℝ) < δ a := by
      rcases max_choice 0 (δ a - dist x (a : ι → ℝ)) with h | h <;> linarith
    have hle_ρ : dist (a : ι → ℝ) (a₀ : ι → ℝ) < ρ a₀ := by
      have ha_le : δ a ≤ δ a₀ := ha₀_max a ha
      calc
        dist (a : ι → ℝ) (a₀ : ι → ℝ)
            ≤ dist (a : ι → ℝ) x + dist x (a₀ : ι → ℝ) := dist_triangle _ _ _
        _ = dist x (a : ι → ℝ) + dist x (a₀ : ι → ℝ) := by rw [dist_comm (a : ι → ℝ) x]
        _ < δ a + δ a₀ := add_lt_add hxa ha₀_dist
        _ ≤ δ a₀ + δ a₀ := by gcongr
        _ = min (ρ a₀) ε := by dsimp [δ]; ring
        _ ≤ ρ a₀ := min_le_left _ _
    exact hρ_sub a₀ a ⟨Metric.mem_ball.mpr hle_ρ, a.2⟩ (hy_mem a)
  have hW_act : W x = ∑ a ∈ s_act, wfn a x := by
    symm
    refine Finset.sum_filter_of_ne fun a _ hne0 => ?_
    exact lt_of_le_of_ne (le_max_left 0 _) (Ne.symm hne0)
  have hfx_act : f x = ∑ a ∈ s_act, (wfn a x / W x) • y a := by
    symm
    refine Finset.sum_filter_of_ne fun a _ hne0 => ?_
    have hw0 : wfn a x ≠ 0 := fun h0 => hne0 (by simp [h0])
    exact lt_of_le_of_ne (le_max_left 0 _) (Ne.symm hw0)
  have hx_mem_U₀ : x ∈ U₀ := by
    have hconvU₀ : Convex ℝ U₀ := convex_biUnion_ball (hF_conv a₀ a₀.2)
    have hcomb : (∑ a ∈ s_act, (wfn a x / W x) • y a) ∈ U₀ := by
      refine hconvU₀.sum_mem (fun a _ => div_nonneg (le_max_left 0 _) (hW_pos x hxK).le)
        ?_ hya_mem
      rw [← Finset.sum_div, ← hW_act, div_self (hW_pos x hxK).ne']
    rw [← hfx_act] at hcomb
    simpa [show f x = x from hfx] using hcomb
  obtain ⟨w, hw_mem, hxw⟩ := mem_iUnion₂.mp hx_mem_U₀
  have hxa₀_eps : dist x (a₀ : ι → ℝ) < ε :=
    ha₀_dist.trans_le (by dsimp [δ]; linarith [min_le_right (ρ a₀) ε])
  have hxw_eps : dist x w < ε := (Metric.mem_ball.mp hxw).trans (half_lt_self hε)
  exact ⟨x, hxK, a₀, a₀.2, w, hw_mem, hxa₀_eps, hxw_eps⟩

/-- **Kakutani's fixed-point theorem** ([Kakutani1941]): an upper hemicontinuous correspondence `F`
mapping a nonempty compact convex set `K ⊆ (ι → ℝ)` (for finite `ι`) to nonempty closed convex
subsets of `K` has a fixed point `x ∈ K` with `x ∈ F x`. -/
theorem exists_mem_of_upperHemicontinuousOn {ι : Type*} [Finite ι]
    {K : Set (ι → ℝ)} (hne : K.Nonempty) (hcomp : IsCompact K) (hconv : Convex ℝ K)
    {F : (ι → ℝ) → Set (ι → ℝ)}
    (hF_ne : ∀ x ∈ K, (F x).Nonempty) (hF_sub : ∀ x ∈ K, F x ⊆ K)
    (hF_closed : ∀ x ∈ K, IsClosed (F x)) (hF_conv : ∀ x ∈ K, Convex ℝ (F x))
    (hF_uhc : UpperHemicontinuousOn F K) :
    ∃ x ∈ K, x ∈ F x := by
  let : Fintype ι := Fintype.ofFinite ι
  have hseq : ∀ n : ℕ, ∃ x ∈ K, ∃ z ∈ K, ∃ w ∈ F z,
      dist x z < 1 / ((n : ℝ) + 1) ∧ dist x w < 1 / ((n : ℝ) + 1) := fun n =>
    exists_approxFixedPt_of_upperHemicontinuousOn hne hcomp hconv hF_ne hF_sub hF_conv hF_uhc
      (by positivity)
  choose x hxK z hzK w hw_mem hxz hxw using hseq
  obtain ⟨x₀, hx₀, φ, hφ, hlimz⟩ := hcomp.isSeqCompact hzK
  have hlimw : Tendsto (w ∘ φ) atTop (𝓝 x₀) := by
    rw [Metric.tendsto_atTop] at hlimz ⊢
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := hlimz (ε / 2) (half_pos hε)
    obtain ⟨N₂, hN₂⟩ := exists_nat_gt (4 / ε)
    refine ⟨max N₁ N₂, fun k hk => ?_⟩
    have hz_dist : dist (z (φ k)) x₀ < ε / 2 := hN₁ k (le_trans (le_max_left _ _) hk)
    have hk_ge : (N₂ : ℝ) ≤ (φ k : ℝ) := by
      exact_mod_cast (le_trans (le_max_right N₁ N₂) hk).trans (hφ.id_le k)
    have h4 : 4 / ε < (φ k : ℝ) + 1 := by linarith
    have h2 : 2 / ((φ k : ℝ) + 1) < ε / 2 := by
      rw [div_lt_iff₀ (by positivity)]
      have hprod : 4 < ((φ k : ℝ) + 1) * ε := (div_lt_iff₀ hε).mp h4
      linarith
    have htri : dist (w (φ k)) x₀ ≤
        dist (x (φ k)) (w (φ k)) + dist (x (φ k)) (z (φ k)) + dist (z (φ k)) x₀ := by
      have h1 := dist_triangle (w (φ k)) (z (φ k)) x₀
      have h2 := dist_triangle (w (φ k)) (x (φ k)) (z (φ k))
      rw [dist_comm (w (φ k)) (x (φ k))] at h2
      linarith
    have hsum_eq : 1 / ((φ k : ℝ) + 1) + 1 / ((φ k : ℝ) + 1) = 2 / ((φ k : ℝ) + 1) := by ring
    change dist (w (φ k)) x₀ < ε
    linarith [hxw (φ k), hxz (φ k)]
  refine ⟨x₀, hx₀, ?_⟩
  by_contra hx₀_not
  have hopen_compl : IsOpen (F x₀)ᶜ := (hF_closed x₀ hx₀).isOpen_compl
  obtain ⟨δ, hδ, hball_sub⟩ := Metric.isOpen_iff.mp hopen_compl x₀ hx₀_not
  have hFsub : F x₀ ⊆ (Metric.closedBall x₀ (δ / 2))ᶜ := by
    intro y hy hmem
    have hy_ball : y ∈ Metric.ball x₀ δ := by
      rw [Metric.mem_ball]
      exact (Metric.mem_closedBall.mp hmem).trans_lt (half_lt_self hδ)
    exact hball_sub hy_ball hy
  have hopen_out : IsOpen (Metric.closedBall x₀ (δ / 2))ᶜ := Metric.isClosed_closedBall.isOpen_compl
  have hev := (upperHemicontinuousOn_iff_forall_isOpen.mp hF_uhc) x₀ hx₀ _ hopen_out hFsub
  obtain ⟨r, hr, hr_sub⟩ := Metric.mem_nhdsWithin_iff.mp hev
  obtain ⟨K₁, hK₁⟩ := (Metric.tendsto_atTop.mp hlimz) r hr
  obtain ⟨K₂, hK₂⟩ := (Metric.tendsto_atTop.mp hlimw) (δ / 2) (half_pos hδ)
  let k := max K₁ K₂
  have hz_mem : z (φ k) ∈ Metric.ball x₀ r ∩ K :=
    ⟨Metric.mem_ball.mpr (hK₁ k (le_max_left _ _)), hzK (φ k)⟩
  have hw_ball : w (φ k) ∈ Metric.closedBall x₀ (δ / 2) :=
    Metric.mem_closedBall.mpr (hK₂ k (le_max_right _ _)).le
  exact hr_sub hz_mem (hw_mem (φ k)) hw_ball

/-- Closed-graph formulation of **Kakutani's fixed-point theorem** ([Kakutani1941]). -/
theorem exists_mem_of_isClosed_graph {ι : Type*} [Finite ι]
    {K : Set (ι → ℝ)} (hne : K.Nonempty) (hcomp : IsCompact K) (hconv : Convex ℝ K)
    {F : (ι → ℝ) → Set (ι → ℝ)}
    (hF_ne : ∀ x ∈ K, (F x).Nonempty) (hF_sub : ∀ x ∈ K, F x ⊆ K)
    (hF_conv : ∀ x ∈ K, Convex ℝ (F x))
    (hF_graph : IsClosed {p : (ι → ℝ) × (ι → ℝ) | p.1 ∈ K ∧ p.2 ∈ F p.1}) :
    ∃ x ∈ K, x ∈ F x := by
  let : Fintype ι := Fintype.ofFinite ι
  have hF_closed : ∀ x ∈ K, IsClosed (F x) := by
    intro x hx
    have hcont : Continuous fun y : ι → ℝ => (x, y) := continuous_const.prodMk continuous_id
    have heq : (fun y => (x, y)) ⁻¹' {p : (ι → ℝ) × (ι → ℝ) | p.1 ∈ K ∧ p.2 ∈ F p.1} = F x := by
      ext y
      simp [hx]
    rw [← heq]
    exact hF_graph.preimage hcont
  have hF_uhc : UpperHemicontinuousOn F K := by
    rw [upperHemicontinuousOn_iff_forall_isOpen]
    intro x₀ hx₀ U hU hsub
    by_contra hnot
    have hbad : ∀ n : ℕ, ∃ z ∈ Metric.ball x₀ (1 / ((n : ℝ) + 1)) ∩ K, ∃ w ∈ F z, w ∉ U := by
      intro n
      by_contra hnone
      apply hnot
      refine Metric.mem_nhdsWithin_iff.mpr ⟨1 / ((n : ℝ) + 1), by positivity, fun z hz => ?_⟩
      intro w hw
      by_contra hwU
      exact hnone ⟨z, hz, w, hw, hwU⟩
    choose z hz_mem w hw_mem hwU using hbad
    have hlimz : Tendsto z atTop (𝓝 x₀) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
      refine ⟨N, fun n hn => ?_⟩
      have hn1 : 1 / ε < (n : ℝ) + 1 := by
        have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      have hinv : 1 / ((n : ℝ) + 1) < ε := (div_lt_iff₀ (by positivity)).mpr <| by
        have := (div_lt_iff₀ hε).mp hn1
        linarith
      exact (Metric.mem_ball.mp (hz_mem n).1).trans hinv
    obtain ⟨w₀, _, φ, hφ, hlimw⟩ := hcomp.isSeqCompact fun n => hF_sub _ (hz_mem n).2 (hw_mem n)
    have hlim_prod : Tendsto (fun k => (z (φ k), w (φ k))) atTop (𝓝 (x₀, w₀)) :=
      (hlimz.comp hφ.tendsto_atTop).prodMk_nhds hlimw
    have hmem_graph : ∀ k, (z (φ k), w (φ k)) ∈
        {p : (ι → ℝ) × (ι → ℝ) | p.1 ∈ K ∧ p.2 ∈ F p.1} :=
      fun k => ⟨(hz_mem (φ k)).2, hw_mem (φ k)⟩
    have hw₀_graph := hF_graph.mem_of_tendsto hlim_prod (Eventually.of_forall hmem_graph)
    have hw₀U : w₀ ∈ U := hsub hw₀_graph.2
    have hw₀_compl : w₀ ∈ Uᶜ := hU.isClosed_compl.mem_of_tendsto hlimw
      (Eventually.of_forall fun k => hwU (φ k))
    exact hw₀_compl hw₀U
  exact exists_mem_of_upperHemicontinuousOn hne hcomp hconv hF_ne hF_sub hF_closed hF_conv hF_uhc

end Kakutani

end Cslib.Kakutani
