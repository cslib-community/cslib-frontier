/-
Copyright (c) 2026 Matthew Doty, Nick L. Leppelmeier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Nick L. Leppelmeier
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Topology/MetricSpace/Kakutani.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Analysis.Brouwer.Simplex
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Dynamics.FixedPoints.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Semicontinuity.Hemicontinuity
import CslibFrontier.Foundations.Analysis.Berge
import CslibFrontier.Foundations.Analysis.InnerProductSpace.MetricProjection
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Data.Finset.Max
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Sequences

/-!
# Brouwer on compact convex sets and Kakutani's fixed-point theorem

This module extends Brouwer's fixed-point theorem from the unit cube to arbitrary nonempty compact
convex subsets of finite-dimensional real normed spaces, and proves **Kakutani's fixed-point
theorem** ([Kakutani1941]; primary PDF unverified).

## Main results

* `Cslib.Brouwer.exists_isFixedPt_of_isCompact_convex`: any continuous self-map of a nonempty
  compact convex set `K ⊆ E` in a finite-dimensional real normed space has a fixed point, proved
  by retracting a bounding cube onto `K` via `Cslib.metricProjection` on coordinate space
  `EuclideanSpace ℝ ι` and transferring along a finite basis equivalence.
* `Cslib.Kakutani.exists_mem_of_upperHemicontinuousOn`: any upper hemicontinuous correspondence
  `F : E → Set E` mapping a nonempty compact convex set `K ⊆ E` to nonempty closed convex subsets
  of `K` has a fixed point `x ∈ K` with `x ∈ F x` ([Kakutani1941]; primary PDF unverified), proved
  via Cellina's partition-of-unity continuous approximation and compactness.
* `Cslib.Kakutani.exists_mem_of_isClosed_graph`: closed-graph formulation of Kakutani's theorem
  ([Kakutani1941]; primary PDF unverified).

## References

* [S. Kakutani, *A Generalization of Brouwer's Fixed Point Theorem*][Kakutani1941]
  (primary PDF unverified)
-/

public section

open Set Filter Topology Finset Function

namespace Cslib.Brouwer

section BrouwerConvex

private theorem exists_isFixedPt_of_isCompact_convex_pi {ι : Type*} [Finite ι] {K : Set (ι → ℝ)}
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

/-- **Brouwer's fixed-point theorem** for an arbitrary nonempty compact convex subset `K` of a
finite-dimensional real normed space `E`. -/
theorem exists_isFixedPt_of_isCompact_convex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hne : K.Nonempty) (hcomp : IsCompact K) (hconv : Convex ℝ K)
    {f : E → E} (hf : MapsTo f K K) (hc : ContinuousOn f K) :
    ∃ x ∈ K, IsFixedPt f x := by
  let e := (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv
  let A : Set (Fin (Module.finrank ℝ E) → ℝ) := e '' K
  have hneA : A.Nonempty := hne.image e
  have hcompA : IsCompact A := hcomp.image e.continuous
  have hconvA : Convex ℝ A := hconv.linear_image (e : E →ₗ[ℝ] Fin (Module.finrank ℝ E) → ℝ)
  exact exists_isFixedPt_of_leftInvOn
    (fun _ hg hgc => exists_isFixedPt_of_isCompact_convex_pi hneA hcompA hconvA hg hgc)
    (φ := e.symm) (ψ := e)
    (by rintro _ ⟨x, hx, rfl⟩; simpa using hx)
    (fun _ hx => ⟨_, hx, rfl⟩)
    e.symm.continuous.continuousOn
    e.continuous.continuousOn
    (fun _ _ => e.symm_apply_apply _)
    hf hc

end BrouwerConvex

end Cslib.Brouwer

namespace Cslib.Kakutani

section Kakutani

private lemma exists_approxFixedPt_of_upperHemicontinuousOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hne : K.Nonempty) (hcomp : IsCompact K) (hconv : Convex ℝ K)
    {F : E → Set E}
    (hF_ne : ∀ x ∈ K, (F x).Nonempty) (hF_sub : ∀ x ∈ K, F x ⊆ K)
    (hF_conv : ∀ x ∈ K, Convex ℝ (F x)) (hF_uhc : UpperHemicontinuousOn F K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ K, ∃ z ∈ K, ∃ w ∈ F z, dist x z < ε ∧ dist x w < ε := by
  classical
  have hcov_ball : ∀ a : K, ∃ ρ > 0,
      ∀ x ∈ Metric.ball (a : E) ρ ∩ K, F x ⊆ Metric.thickening (ε / 2) (F a) := by
    intro a
    have hev := (upperHemicontinuousOn_iff_forall_isOpen.mp hF_uhc)
      a a.property (Metric.thickening (ε / 2) (F a)) Metric.isOpen_thickening
      (Metric.self_subset_thickening (half_pos hε) (F a))
    obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hev
    exact ⟨ρ, hρ, fun x hx => hsub hx⟩
  choose ρ hρ_pos hρ_sub using hcov_ball
  let δ : K → ℝ := fun a => min (ρ a) ε / 2
  have hδ_pos : ∀ a : K, 0 < δ a := fun a => half_pos (lt_min (hρ_pos a) hε)
  have hK_cov : K ⊆ ⋃ a : K, Metric.ball (a : E) (δ a) := fun x hx =>
    mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hδ_pos ⟨x, hx⟩)⟩
  obtain ⟨s, hs_cov⟩ := hcomp.elim_finite_subcover
    (fun a : K => Metric.ball (a : E) (δ a)) (fun _ => Metric.isOpen_ball) hK_cov
  choose y hy_mem using fun a : K => hF_ne a a.property
  let wfn : K → E → ℝ := fun a x => max 0 (δ a - dist x (a : E))
  let W : E → ℝ := fun x => ∑ a ∈ s, wfn a x
  have hW_pos : ∀ x ∈ K, 0 < W x := by
    intro x hx
    obtain ⟨a, has, hxa⟩ := mem_iUnion₂.mp (hs_cov hx)
    have hwa : 0 < wfn a x := lt_max_of_lt_right (sub_pos.mpr (Metric.mem_ball.mp hxa))
    exact Finset.sum_pos' (fun b _ => le_max_left 0 _) ⟨a, has, hwa⟩
  let f : E → E := fun x => ∑ a ∈ s, (wfn a x / W x) • y a
  have hf_maps : MapsTo f K K := by
    intro x hx
    refine hconv.sum_mem (fun a _ => div_nonneg (le_max_left 0 _) (hW_pos x hx).le)
      ?_ (fun a _ => hF_sub a a.property (hy_mem a))
    rw [← Finset.sum_div, div_self (hW_pos x hx).ne']
  have hw_cont : ∀ a : K, Continuous (wfn a) := fun a =>
    continuous_const.max (continuous_const.sub (continuous_id.dist continuous_const))
  have hW_cont : Continuous W := continuous_finsetSum s fun a _ => hw_cont a
  have hf_cont : ContinuousOn f K := continuousOn_finsetSum s fun a _ =>
    ((hw_cont a).continuousOn.div hW_cont.continuousOn fun x hx =>
      (hW_pos x hx).ne').smul continuousOn_const
  obtain ⟨x, hxK, hfx⟩ := Cslib.Brouwer.exists_isFixedPt_of_isCompact_convex
    hne hcomp hconv hf_maps hf_cont
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
  have ha₀_dist : dist x (a₀ : E) < δ a₀ := by
    have h0 : 0 < max 0 (δ a₀ - dist x (a₀ : E)) := (Finset.mem_filter.mp ha₀_act).2
    rcases max_choice 0 (δ a₀ - dist x (a₀ : E)) with h | h
    · linarith
    · linarith
  let U₀ : Set E := Metric.thickening (ε / 2) (F a₀)
  have hya_mem : ∀ a ∈ s_act, y a ∈ U₀ := by
    intro a ha
    have h0 : 0 < max 0 (δ a - dist x (a : E)) := (Finset.mem_filter.mp ha).2
    have hxa : dist x (a : E) < δ a := by
      rcases max_choice 0 (δ a - dist x (a : E)) with h | h <;> linarith
    have hle_ρ : dist (a : E) (a₀ : E) < ρ a₀ := by
      have ha_le : δ a ≤ δ a₀ := ha₀_max a ha
      calc
        dist (a : E) (a₀ : E)
            ≤ dist (a : E) x + dist x (a₀ : E) := dist_triangle _ _ _
        _ = dist x (a : E) + dist x (a₀ : E) := by rw [dist_comm (a : E) x]
        _ < δ a + δ a₀ := add_lt_add hxa ha₀_dist
        _ ≤ δ a₀ + δ a₀ := by gcongr
        _ = min (ρ a₀) ε := by dsimp [δ]; ring
        _ ≤ ρ a₀ := min_le_left _ _
    exact hρ_sub a₀ a ⟨Metric.mem_ball.mpr hle_ρ, a.property⟩ (hy_mem a)
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
    have hconvU₀ : Convex ℝ U₀ := (hF_conv a₀ a₀.property).thickening (ε / 2)
    have hcomb : (∑ a ∈ s_act, (wfn a x / W x) • y a) ∈ U₀ := by
      refine hconvU₀.sum_mem (fun a _ => div_nonneg (le_max_left 0 _) (hW_pos x hxK).le)
        ?_ hya_mem
      rw [← Finset.sum_div, ← hW_act, div_self (hW_pos x hxK).ne']
    rw [← hfx_act] at hcomb
    simpa [show f x = x from hfx] using hcomb
  dsimp only [U₀] at hx_mem_U₀
  rw [Metric.thickening_eq_biUnion_ball] at hx_mem_U₀
  obtain ⟨w, hw_mem, hxw⟩ := mem_iUnion₂.mp hx_mem_U₀
  have hxa₀_eps : dist x (a₀ : E) < ε :=
    ha₀_dist.trans_le (by dsimp [δ]; linarith [min_le_right (ρ a₀) ε])
  have hxw_eps : dist x w < ε := (Metric.mem_ball.mp hxw).trans (half_lt_self hε)
  exact ⟨x, hxK, a₀, a₀.property, w, hw_mem, hxa₀_eps, hxw_eps⟩

/-- **Kakutani's fixed-point theorem** ([Kakutani1941]; primary PDF unverified): an upper
hemicontinuous correspondence `F` mapping a nonempty compact convex subset `K` of a
finite-dimensional real normed space `E` to nonempty closed convex subsets of `K` has a fixed
point `x ∈ K` with `x ∈ F x`. -/
theorem exists_mem_of_upperHemicontinuousOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hne : K.Nonempty) (hcomp : IsCompact K) (hconv : Convex ℝ K)
    {F : E → Set E}
    (hF_ne : ∀ x ∈ K, (F x).Nonempty) (hF_sub : ∀ x ∈ K, F x ⊆ K)
    (hF_closed : ∀ x ∈ K, IsClosed (F x)) (hF_conv : ∀ x ∈ K, Convex ℝ (F x))
    (hF_uhc : UpperHemicontinuousOn F K) :
    ∃ x ∈ K, x ∈ F x := by
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
  have hsub_lim : Tendsto (fun k => (⟨z (φ k), hzK (φ k)⟩ : K)) atTop (𝓝 (⟨x₀, hx₀⟩ : K)) :=
    tendsto_subtype_rng.mpr hlimz
  have huhc : UpperHemicontinuousAt (K.domRestrict F) ⟨x₀, hx₀⟩ :=
    upperHemicontinuousOn_iff_restrict.mpr hF_uhc ⟨x₀, hx₀⟩
  exact ⟨x₀, hx₀, huhc.mem_of_tendsto (hF_closed x₀ hx₀) hsub_lim
    (Eventually.of_forall fun k => hw_mem (φ k)).frequently hlimw⟩

/-- Closed-graph formulation of **Kakutani's fixed-point theorem** ([Kakutani1941]; primary PDF
unverified). -/
theorem exists_mem_of_isClosed_graph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hne : K.Nonempty) (hcomp : IsCompact K) (hconv : Convex ℝ K)
    {F : E → Set E}
    (hF_ne : ∀ x ∈ K, (F x).Nonempty) (hF_sub : ∀ x ∈ K, F x ⊆ K)
    (hF_conv : ∀ x ∈ K, Convex ℝ (F x))
    (hF_graph : IsClosed {p : E × E | p.1 ∈ K ∧ p.2 ∈ F p.1}) :
    ∃ x ∈ K, x ∈ F x := by
  have hF_closed : ∀ x ∈ K, IsClosed (F x) := fun x hx => by
    have heq : (fun y : E => (x, y)) ⁻¹' {p : E × E | p.1 ∈ K ∧ p.2 ∈ F p.1} = F x := by
      ext y
      simp [hx]
    exact heq ▸ hF_graph.preimage (continuous_const.prodMk continuous_id)
  have hF_uhc : UpperHemicontinuousOn F K :=
    Cslib.Berge.upperHemicontinuousOn_of_isClosed_graph hcomp.isSeqCompact hF_sub hF_graph
  exact exists_mem_of_upperHemicontinuousOn hne hcomp hconv hF_ne hF_sub hF_closed hF_conv hF_uhc

end Kakutani

end Cslib.Kakutani
