/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Module
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Monotone

/-!
# Straight escape from a star-convex obstacle

From a point in a compact convex region but outside a star-convex obstacle, continue the ray
from the star center to the region's frontier. Star convexity keeps the entire segment beyond
the starting point clear of the obstacle. This applies to a union of straight spokes at a
common center inside a bounding region.
-/

public section

namespace Cslib

/-- From a point of a compact convex region outside a star-convex obstacle, a straight
segment in the region reaches its frontier without touching the obstacle. -/
theorem exists_segment_to_frontier_avoiding_starConvex {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {K S : Set E} {c z : E}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hstar : StarConvex ℝ c S)
    (hc : c ∈ S) (hz : z ∈ K) (hzS : z ∉ S) :
    ∃ y ∈ frontier K, segment ℝ z y ⊆ K \ S := by
  have hne : z ≠ c := fun h => hzS (h.symm ▸ hc)
  have hnorm : 0 < ‖z - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  let ray (u : ℝ) : E := c + u • (z - c)
  have hray : Continuous ray := continuous_const.add (continuous_id.smul continuous_const)
  have hone : ray 1 = z := by
    change c + (1 : ℝ) • (z - c) = z
    rw [one_smul, add_comm, sub_add_cancel]
  let T : Set ℝ := Set.Ici 1 ∩ ray ⁻¹' K
  have hT : IsClosed T := isClosed_Ici.inter (hK.isClosed.preimage hray)
  have hTne : T.Nonempty := ⟨1, le_rfl, by simpa only [Set.mem_preimage, hone] using hz⟩
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball c
  have hTb : BddAbove T := by
    refine ⟨R / ‖z - c‖, ?_⟩
    rintro u ⟨hu, huK⟩
    have hd := Metric.mem_ball.mp (hR huK)
    rw [dist_eq_norm] at hd
    change ‖c + u • (z - c) - c‖ < R at hd
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (zero_le_one.trans hu)] at hd
    exact ((lt_div_iff₀ hnorm).mpr hd).le
  let t := sSup T
  have ht : t ∈ T := hT.csSup_mem hTne hTb
  have hmax {u : ℝ} (hu : u ∈ T) : u ≤ t := le_csSup hTb hu
  have hfrontier : ray t ∈ frontier K := by
    rw [hK.isClosed.frontier_eq]
    refine ⟨ht.2, ?_⟩
    intro hi
    have hi' : t ∈ ray ⁻¹' interior K := hi
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_interior.preimage hray) t hi'
    have hlt : t < t + ε / 2 := lt_add_of_pos_right _ (half_pos hε)
    have hnear : t + ε / 2 ∈ Metric.ball t ε := by
      rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hε)]
      exact half_lt_self hε
    have hinside : ray (t + ε / 2) ∈ interior K := hball hnear
    have huK : ray (t + ε / 2) ∈ K := interior_subset hinside
    have hu : t + ε / 2 ∈ T := ⟨ht.1.trans hlt.le, huK⟩
    exact (hmax hu).not_gt hlt
  refine ⟨ray t, hfrontier, ?_⟩
  intro w hw
  refine ⟨hconv.segment_subset hz ht.2 hw, ?_⟩
  rw [segment_eq_image_lineMap] at hw
  obtain ⟨s, hs, rfl⟩ := hw
  let u := 1 + s * (t - 1)
  have hu : 1 ≤ u := le_add_of_nonneg_right (mul_nonneg hs.1 (sub_nonneg.mpr ht.1))
  have heq : AffineMap.lineMap z (ray t) s = ray u := by
    calc
      _ = (1 - s) • ray 1 + s • ray t := by rw [AffineMap.lineMap_apply_module, hone]
      _ = ray u := by
        dsimp only [ray, u]
        module
  rw [heq]
  intro huS
  have hupos : 0 < u := zero_lt_one.trans_le hu
  have hback := hstar.add_smul_sub_mem huS (inv_nonneg.mpr hupos.le) (inv_le_one_of_one_le₀ hu)
  have hdiff : ray u - c = u • (z - c) := by simp [ray]
  rw [hdiff, smul_smul, inv_mul_cancel₀ hupos.ne', one_smul, add_comm c (z - c),
    sub_add_cancel] at hback
  exact hzS hback

end Cslib
