/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Paths in open sets with finitely many points removed

In real dimension at least two, a punctured ball is path connected by its sphere directions
and positive radii. Around a removed point a sufficiently small ball misses every other
removed point. These local detours keep the path component of any remaining point both open
and closed relative to the original region after taking its closure there.
-/

public section

namespace Cslib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem isPathConnected_punctured_ball (hrank : 1 < Module.rank ℝ E)
    (q : E) {r : ℝ} (hr : 0 < r) : IsPathConnected (Metric.ball q r \ {q}) := by
  let directions : Set E := Metric.sphere 0 1
  let radius := Set.Ioo (0 : ℝ) r
  let f (p : E × ℝ) := q + p.2 • p.1
  have hdirs : IsPathConnected directions := isPathConnected_sphere hrank 0 zero_le_one
  have hrad : IsPathConnected radius :=
    Convex.isPathConnected (convex_Ioo (𝕜 := ℝ) 0 r) (Set.nonempty_Ioo.mpr hr)
  have hf : Continuous f := continuous_const.add (continuous_snd.smul continuous_fst)
  have himage : f '' Set.prod directions radius = Metric.ball q r \ {q} := by
    ext z
    constructor
    · rintro ⟨⟨u, t⟩, ⟨hu, ht⟩, rfl⟩
      have hd : dist (q + t • u) q = t := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1.le,
          mem_sphere_zero_iff_norm.1 hu, mul_one]
      exact ⟨Metric.mem_ball.mpr (hd.trans_lt ht.2), fun he =>
        ht.1.ne (by rw [← hd, show q + t • u = q from he, dist_self])⟩
    · rintro ⟨hz, hzq⟩
      have hp : 0 < ‖z - q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzq)
      refine ⟨(‖z - q‖⁻¹ • (z - q), ‖z - q‖), ⟨?_, hp, by simpa [dist_eq_norm] using hz⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hp.ne']
      · change q + ‖z - q‖ • (‖z - q‖⁻¹ • (z - q)) = z
        rw [smul_smul, mul_inv_cancel₀ hp.ne', one_smul, add_sub_cancel]
  exact himage ▸ (hdirs.prod hrad).image hf

/-- Deleting a finite set from an open path-connected region of real dimension at least two
leaves a path-connected region. The deleted points need not all belong to the region. -/
theorem isPathConnected_sdiff_finite_of_isOpen (hrank : 1 < Module.rank ℝ E)
    {U F : Set E} (hU : IsOpen U) (hconn : IsPathConnected U) (hF : F.Finite) :
    IsPathConnected (U \ F) := by
  classical
  have : Nontrivial E := (rank_pos_iff_nontrivial (R := ℝ)).1 (zero_lt_one.trans hrank)
  let V := U \ F
  have hV : IsOpen V := hU.sdiff hF.isClosed
  obtain ⟨a, ha⟩ : V.Nonempty :=
    (hF.countable.dense_compl ℝ).inter_open_nonempty U hU hconn.nonempty
  let P := pathComponentIn V a
  have haP : a ∈ P := mem_pathComponentIn_self ha
  have hP : P ⊆ V := pathComponentIn_subset
  have hPopen : IsOpen P := hV.pathComponentIn a
  have hclosedV : closure P ∩ V ⊆ P := by
    rintro y ⟨hyc, hyv⟩
    obtain ⟨w, hyw, haw⟩ := mem_closure_iff.mp hyc (pathComponentIn V y)
      (hV.pathComponentIn y) (mem_pathComponentIn_self hyv)
    exact (show JoinedIn V a w from haw).trans (show JoinedIn V y w from hyw).symm
  let C := closure P ∩ U
  have hC : IsOpen C := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨hyc, hyu⟩
    by_cases hyf : y ∈ F
    · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp
        (hU.sdiff (show (F \ {y}).Finite from hF.sdiff).isClosed) y ⟨hyu, fun h => h.2 rfl⟩
      have hballV : Metric.ball y r \ {y} ⊆ V := fun z hz =>
        ⟨(hball hz.1).1, fun hzf => (hball hz.1).2 ⟨hzf, hz.2⟩⟩
      obtain ⟨w, hwb, haw⟩ := mem_closure_iff.mp hyc (Metric.ball y r)
        Metric.isOpen_ball (Metric.mem_ball_self hr)
      have hwy : w ∉ ({y} : Set E) := fun he => (hP haw).2 ((show w = y from he).symm ▸ hyf)
      have hballP : Metric.ball y r \ {y} ⊆ P := fun z hz =>
        (show JoinedIn V a w from haw).trans
          (((isPathConnected_punctured_ball hrank y hr).joinedIn w ⟨hwb, hwy⟩ z hz).mono hballV)
      refine Filter.mem_of_superset (Metric.ball_mem_nhds y hr) fun z hz => ⟨?_, (hball hz).1⟩
      by_cases hzy : z = y
      · exact hzy.symm ▸ hyc
      · exact subset_closure (hballP ⟨hz, hzy⟩)
    · have hyP : y ∈ P := hclosedV ⟨hyc, hyu, hyf⟩
      exact Filter.mem_of_superset (hPopen.mem_nhds hyP)
        (fun z hz => ⟨subset_closure hz, (hP hz).1⟩)
  have hCP : C ⊆ closure P := Set.inter_subset_left
  have hclos : closure C ∩ U ⊆ C := fun z hz => ⟨closure_minimal hCP isClosed_closure hz.1, hz.2⟩
  have hUC : U ⊆ C := hconn.isConnected.2.subset_of_closure_inter_subset hC
    ⟨a, ha.1, subset_closure haP, ha.1⟩ hclos
  exact ⟨a, ha, fun z hz => hclosedV ⟨(hUC hz.1).1, hz⟩⟩

end Cslib
