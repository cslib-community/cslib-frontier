/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.Route
public import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Polygonal samples of continuous paths

Uniform samples on the closed unit interval give actual finite routes with exact endpoints.
Uniform continuity confines sufficiently fine chords to any prescribed open thickening of
the original image. For a finite family with disjoint images, one mesh works for every pair.
These statements concern support approximation and contacts between different routes.
-/

public section

namespace Cslib.Polygonal.Route

open Filter Set
open scoped Topology

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
  have hm : (m + 1 : ℝ) ≠ 0 := by positivity
  change γ (((m + 1 : ℕ) : ℝ) / (m + 1 : ℝ)) = γ 1
  rw [Nat.cast_add, Nat.cast_one, div_self hm]

/-- All sufficiently fine uniform samples of a continuous path stay in any positive
open metric thickening of its image, including along the interiors of the chords. -/
theorem eventually_sampled_support_subset (γ : ℝ → ℂ)
    (hγ : ContinuousOn γ (Icc 0 1)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, (sampled γ m).support ⊆ Metric.thickening ε (γ '' Icc 0 1) := by
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hγ) ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  refine eventually_atTop.mpr ⟨N, fun m hm x hx => ?_⟩
  have hmpos : 0 < (m + 1 : ℝ) := by positivity
  have hmesh : 1 / (m + 1 : ℝ) < δ :=
    (one_div_le_one_div_of_le (by positivity : 0 < (N + 1 : ℝ))
      (by exact_mod_cast Nat.succ_le_succ hm)).trans_lt hN
  obtain ⟨i, t, ht, rfl⟩ := ((sampled γ m).mem_support_iff x).mp hx
  let a : ℝ := (i.val : ℝ) / (m + 1 : ℝ)
  let b : ℝ := ((i.val : ℝ) + 1) / (m + 1 : ℝ)
  have hiv : (i.val : ℝ) + 1 ≤ m + 1 := by exact_mod_cast i.isLt
  have ha : a ∈ Icc 0 1 := ⟨by positivity, (div_le_one hmpos).mpr (by linarith)⟩
  have hb : b ∈ Icc 0 1 := ⟨by positivity, (div_le_one hmpos).mpr hiv⟩
  have hsub : b - a = 1 / (m + 1 : ℝ) := by
    dsimp [a, b]
    ring
  have hdist : dist b a < δ := by
    rw [Real.dist_eq, hsub, abs_of_nonneg (by positivity)]
    exact hmesh
  have hpa : γ a ∈ Metric.ball (γ a) ε := Metric.mem_ball_self hε
  have hpb : γ b ∈ Metric.ball (γ a) ε := Metric.mem_ball.mpr (hclose b hb a ha hdist)
  have hline : (sampled γ m).eval i t = AffineMap.lineMap (γ a) (γ b) t := by
    change AffineMap.lineMap (γ a) (γ (((i.val + 1 : ℕ) : ℝ) / (m + 1 : ℝ))) t = _
    rw [Nat.cast_add, Nat.cast_one]
  rw [hline]
  exact Metric.mem_thickening_iff.mpr ⟨γ a, mem_image_of_mem γ ha,
    (convex_ball (γ a) ε).segment_subset hpa hpb (lineMap_mem_segment ℝ _ _ ht)⟩

/-- Pairwise disjoint continuous path images give pairwise disjoint sampled route supports
on every sufficiently fine common mesh. -/
theorem eventually_pairwise_disjoint_sampled {ι : Type*} [Finite ι] (γ : ι → ℝ → ℂ)
    (hγ : ∀ i, ContinuousOn (γ i) (Icc 0 1))
    (hdisj : Pairwise (fun i j => Disjoint (γ i '' Icc 0 1) (γ j '' Icc 0 1))) :
    ∀ᶠ m : ℕ in atTop, Pairwise (fun i j => Disjoint (sampled (γ i) m).support
      (sampled (γ j) m).support) := by
  have hcompact (i : ι) : IsCompact (γ i '' Icc 0 1) :=
    isCompact_Icc.image_of_continuousOn (hγ i)
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  by_cases h : i = j
  · exact Filter.Eventually.of_forall fun _ hne => (hne h).elim
  obtain ⟨δ, hδ, hsep⟩ := (hdisj h).exists_thickenings (hcompact i) (hcompact j).isClosed
  filter_upwards [eventually_sampled_support_subset (γ i) (hγ i) hδ,
    eventually_sampled_support_subset (γ j) (hγ j) hδ] with _ hi hj _
  exact hsep.mono hi hj

end Cslib.Polygonal.Route
