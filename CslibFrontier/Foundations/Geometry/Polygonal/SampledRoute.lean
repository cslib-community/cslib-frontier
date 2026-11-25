/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.Route
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.AffineSpace.Ordered
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Polygonal samples of continuous paths

Uniform samples on the closed unit interval give actual finite routes with exact endpoints.
Uniform continuity confines sufficiently fine chords to any prescribed open thickening of
the original image. For a finite family with disjoint images, one mesh works for every pair.
An affine increase in radius and a Lipschitz bound also ensure that sufficiently fine
segments satisfy the outward chord inequality. Sampling also realizes a continuous path
in an open set by a finite polygonal route with the same endpoints.
-/

public section

namespace Cslib.Polygonal.Route

open Filter Set
open scoped NNReal Topology

/-- Connect successive uniform samples of `γ` on `[0,1]` by straight segments. -/
noncomputable def sampled (γ : ℝ → ℂ) (m : ℕ) : Route :=
  ⟨m, fun i => γ ((i.val : ℝ) / (m + 1 : ℝ))⟩

/-- Sampling retains the initial endpoint. -/
@[simp] theorem sampled_start (γ : ℝ → ℂ) (m : ℕ) :
    (sampled γ m).start = γ 0 := by
  simp [sampled, start]

/-- Sampling retains the final endpoint. -/
@[simp] theorem sampled_finish (γ : ℝ → ℂ) (m : ℕ) :
    (sampled γ m).finish = γ 1 := by
  change γ (((m + 1 : ℕ) : ℝ) / (m + 1 : ℝ)) = γ 1
  rw [Nat.cast_add, Nat.cast_one, div_self (by positivity)]

private theorem eventually_uniform_mesh_lt {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, 1 / (m + 1 : ℝ) < δ :=
  (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (Iio_mem_nhds hδ)

private theorem sampled_segment (γ : ℝ → ℂ) (m : ℕ) (i : Fin (sampled γ m).segments) :
    ∃ a b : ℝ, a ∈ Icc 0 1 ∧ b ∈ Icc 0 1 ∧ b - a = 1 / (m + 1 : ℝ) ∧
      (sampled γ m).point i.castSucc = γ a ∧ (sampled γ m).point i.succ = γ b := by
  let a : ℝ := (i.val : ℝ) / (m + 1 : ℝ)
  let b : ℝ := ((i.val : ℝ) + 1) / (m + 1 : ℝ)
  have hmpos : 0 < (m + 1 : ℝ) := by positivity
  have hiv : (i.val : ℝ) + 1 ≤ m + 1 := by exact_mod_cast i.isLt
  have ha : a ∈ Icc 0 1 := ⟨by positivity, (div_le_one hmpos).mpr (by linarith)⟩
  have hb : b ∈ Icc 0 1 := ⟨by positivity, (div_le_one hmpos).mpr hiv⟩
  refine ⟨a, b, ha, hb, ?_, rfl, ?_⟩
  · dsimp [a, b]
    ring
  · change γ (((i.val + 1 : ℕ) : ℝ) / (m + 1 : ℝ)) = γ b
    rw [Nat.cast_add, Nat.cast_one]

/-- All sufficiently fine uniform samples of a continuous path stay in any positive
open metric thickening of its image, including along the interiors of the chords. -/
theorem eventually_sampled_support_subset (γ : ℝ → ℂ)
    (hγ : ContinuousOn γ (Icc 0 1)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, (sampled γ m).support ⊆ Metric.thickening ε (γ '' Icc 0 1) := by
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hγ) ε hε
  filter_upwards [eventually_uniform_mesh_lt hδ] with m hmesh x hx
  obtain ⟨i, t, ht, rfl⟩ := ((sampled γ m).mem_support_iff x).mp hx
  obtain ⟨a, b, ha, hb, hsub, hleft, hright⟩ := sampled_segment γ m i
  have hdist : dist b a < δ := by rwa [Real.dist_eq, hsub, abs_of_nonneg (by positivity)]
  rw [eval, hleft, hright]
  exact Metric.mem_thickening_iff.mpr ⟨γ a, mem_image_of_mem γ ha,
    (convex_ball (γ a) ε).segment_subset (Metric.mem_ball_self hε)
      (Metric.mem_ball.mpr (hclose b hb a ha hdist)) (lineMap_mem_segment ℝ _ _ ht)⟩

/-- Pairwise disjoint continuous path images give pairwise disjoint sampled route supports
on every sufficiently fine common mesh. -/
theorem eventually_pairwise_disjoint_sampled {ι : Type*} [Finite ι] (γ : ι → ℝ → ℂ)
    (hγ : ∀ i, ContinuousOn (γ i) (Icc 0 1))
    (hdisj : Pairwise (fun i j => Disjoint (γ i '' Icc 0 1) (γ j '' Icc 0 1))) :
    ∀ᶠ m : ℕ in atTop, Pairwise (fun i j => Disjoint (sampled (γ i) m).support
      (sampled (γ j) m).support) := by
  refine Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => ?_
  by_cases h : i = j
  · exact Filter.Eventually.of_forall fun _ hne => (hne h).elim
  obtain ⟨δ, hδ, hsep⟩ := (hdisj h).exists_thickenings
    (isCompact_Icc.image_of_continuousOn (hγ i))
    (isCompact_Icc.image_of_continuousOn (hγ j)).isClosed
  filter_upwards [eventually_sampled_support_subset (γ i) (hγ i) hδ,
    eventually_sampled_support_subset (γ j) (hγ j) hδ] with _ hi hj _
  exact hsep.mono hi hj

/-- A Lipschitz path whose radius grows affinely from a positive inner radius has
outward chords on every sufficiently fine uniform mesh. The squared chord length is
quadratic in the step size, whereas the squared radial gain has a positive linear bound. -/
theorem eventually_sampled_outward (γ : ℝ → ℂ) (z : ℂ) {K : ℝ≥0}
    (hγ : LipschitzOnWith K γ (Icc 0 1)) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hrad : ∀ t ∈ Icc 0 1, ‖γ t - z‖ = AffineMap.lineMap r R t) :
    ∀ᶠ m : ℕ in atTop, ∀ i : Fin (sampled γ m).segments,
      ‖(sampled γ m).point i.succ - (sampled γ m).point i.castSucc‖ ^ 2 <
        ‖(sampled γ m).point i.succ - z‖ ^ 2 - ‖(sampled γ m).point i.castSucc - z‖ ^ 2 := by
  have hslope : 0 < R - r := sub_pos.mpr hrR
  have hthreshold : 0 < 2 * r * (R - r) / ((K : ℝ) ^ 2 + 1) := by positivity
  filter_upwards [eventually_uniform_mesh_lt hthreshold] with m hmesh
  intro i
  obtain ⟨a, b, ha, hb, hstep, hleft, hright⟩ := sampled_segment γ m i
  have hpos : 0 < b - a := by rw [hstep]; positivity
  have hchord : ‖γ b - γ a‖ ≤ (K : ℝ) * (b - a) := by
    simpa only [dist_eq_norm, Real.norm_eq_abs, abs_of_pos hpos] using hγ.dist_le_mul b hb a ha
  have hsmall : (K : ℝ) ^ 2 * (b - a) < 2 * r * (R - r) := by
    rw [← hstep] at hmesh
    have h := (lt_div_iff₀ (by positivity : 0 < (K : ℝ) ^ 2 + 1)).mp hmesh
    linarith
  have hsum : 2 * r ≤ AffineMap.lineMap r R b + AffineMap.lineMap r R a := by
    simp only [AffineMap.lineMap_apply_ring']
    linarith [mul_nonneg ha.1 hslope.le, mul_nonneg hb.1 hslope.le]
  have hdiff : AffineMap.lineMap r R b - AffineMap.lineMap r R a = (b - a) * (R - r) := by
    simp only [AffineMap.lineMap_apply_ring']
    ring
  rw [hleft, hright, hrad a ha, hrad b hb]
  calc
    _ ≤ ((K : ℝ) * (b - a)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hchord
    _ = ((K : ℝ) ^ 2 * (b - a)) * (b - a) := by ring
    _ < (2 * r * (R - r)) * (b - a) := mul_lt_mul_of_pos_right hsmall hpos
    _ = (AffineMap.lineMap r R b - AffineMap.lineMap r R a) * (2 * r) := by rw [hdiff]; ring
    _ ≤ (AffineMap.lineMap r R b - AffineMap.lineMap r R a) *
        (AffineMap.lineMap r R b + AffineMap.lineMap r R a) :=
      mul_le_mul_of_nonneg_left hsum (by rw [hdiff]; positivity)
    _ = _ := by ring

/-- A continuous path inside an open region admits a polygonal route in the same region
with the original endpoints. -/
theorem exists_support_subset_of_joinedIn {U : Set ℂ} {a b : ℂ}
    (hU : IsOpen U) (h : JoinedIn U a b) :
    ∃ p : Route, p.start = a ∧ p.finish = b ∧ p.support ⊆ U := by
  let γ := h.somePath
  have hcompact : IsCompact (Set.range γ) := isCompact_range (map_continuous γ)
  have hsub : Set.range γ ⊆ U := by
    rintro z ⟨t, rfl⟩
    exact h.somePath_mem t
  obtain ⟨ε, hε, hthick⟩ := hcompact.exists_thickening_subset_open hU hsub
  obtain ⟨m, hm⟩ :=
    (eventually_sampled_support_subset γ.extend γ.continuous_extend.continuousOn hε).exists
  rw [γ.image_extend_of_subset Subset.rfl] at hm
  exact ⟨sampled γ.extend m, (sampled_start _ _).trans γ.extend_zero,
    (sampled_finish _ _).trans γ.extend_one, hm.trans hthick⟩

end Cslib.Polygonal.Route
