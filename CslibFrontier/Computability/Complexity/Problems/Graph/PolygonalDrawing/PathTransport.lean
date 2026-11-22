/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing
public import Mathlib.Topology.Path
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.SquareMove
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Moving a vertex along a path avoiding closed obstacles

The path need only be continuous. Compactness of its image supplies one positive clearance
from the closed obstacle set, and uniform continuity supplies a finite subdivision for that
clearance. Each local square move then fixes every protected vertex and whole protected route.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

/-- Move one vertex along a continuous path in the complement of a closed set protecting
the other declared vertices and the full supports of a selected set of edges. The output
remains embedded and each protected route is literally unchanged. -/
theorem IsEmbedding.exists_vertex_move_along_path {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices)
    (v : ℕ) {b : ℂ} (path : Path (D.vertex v) b) {K : Set ℂ} (hK : IsClosed K)
    (hpath : Set.range path ⊆ Kᶜ) (hvertices : ∀ w ∈ G.vertices, w ≠ v → D.vertex w ∈ K)
    (keep : Set (Fin G.edges.length)) (hkeep : ∀ e ∈ keep, (D.route e).support ⊆ K) :
    ∃ E : PolygonalDrawing G, E.IsEmbedding ∧ E.vertex v = b ∧
      (∀ w ∈ G.vertices, w ≠ v → E.vertex w = D.vertex w) ∧
      ∀ e ∈ keep, E.route e = D.route e := by
  have hcont : Continuous (fun t : unitInterval => path t) := map_continuous path
  obtain ⟨δ, hδ, hclear⟩ :=
    (isCompact_range hcont).exists_thickening_subset_open hK.isOpen_compl hpath
  let r := δ / 2
  have hr : 0 < r := half_pos hδ
  have outside (t : unitInterval) {z : ℂ} (hz : z ∈ K) :
      r ≤ max |z.re - (path t).re| |z.im - (path t).im| := by
    by_contra hn
    have hm := lt_of_not_ge hn
    have ha := (le_max_left _ _).trans_lt hm
    have hb := (le_max_right _ _).trans_lt hm
    have hd : dist z (path t) < δ := by
      rw [dist_eq_norm]
      have hnorm := Complex.norm_le_abs_re_add_abs_im (z - path t)
      rw [Complex.sub_re, Complex.sub_im] at hnorm
      linarith only [ha, hb, hnorm, show r = δ / 2 from rfl]
    exact hclear (Metric.mem_thickening_iff.mpr ⟨path t, ⟨t, rfl⟩, hd⟩) hz
  obtain ⟨η, hη, hnear⟩ :=
    Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous hcont) r hr
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / η)
  have hnpos : 0 < (n : ℝ) := (div_pos zero_lt_one hη).trans hn
  have hmesh : 1 / (n : ℝ) < η := by
    apply (div_lt_iff₀ hnpos).mpr
    simpa only [mul_comm] using (div_lt_iff₀ hη).mp hn
  let time (k : ℕ) (hk : k ≤ n) : unitInterval :=
    ⟨k / (n : ℝ), div_nonneg (Nat.cast_nonneg _) hnpos.le,
      (div_le_one hnpos).mpr (Nat.cast_le.mpr hk)⟩
  have step (k : ℕ) (hk : k + 1 ≤ n) (hk' : k ≤ n) :
      dist (time (k + 1) hk) (time k hk') < η := by
    change dist ((↑(k + 1) : ℝ) / n) ((k : ℝ) / n) < η
    rw [Real.dist_eq, ← sub_div, Nat.cast_succ, add_sub_cancel_left,
      abs_of_nonneg (div_nonneg zero_le_one hnpos.le)]
    exact hmesh
  have place (k : ℕ) (hk : k ≤ n) : ∃ E : PolygonalDrawing G,
      E.IsEmbedding ∧ E.vertex v = path (time k hk) ∧
        (∀ w ∈ G.vertices, w ≠ v → E.vertex w = D.vertex w) ∧
        ∀ e ∈ keep, E.route e = D.route e := by
    induction k with
    | zero =>
      have htime : time 0 hk = 0 := by
        apply Subtype.ext
        simp [time]
      exact ⟨D, hD, by rw [htime, path.source], fun _ _ _ => rfl, fun _ _ => rfl⟩
    | succ k ih =>
      have hk' : k ≤ n := (Nat.le_succ k).trans hk
      obtain ⟨E, hE, hv, hfixed, hroutes⟩ := ih hk'
      have hmove : ‖path (time (k + 1) hk) - E.vertex v‖ < r := by
        rw [hv, ← dist_eq_norm]
        exact hnear (step k hk hk')
      obtain ⟨F, hF, htarget, hvertices', hroutes'⟩ :=
        hE.exists_square_move hG v (path (time (k + 1) hk)) hr hmove
      refine ⟨F, hF, htarget, ?_, ?_⟩
      · intro w hw hne
        have hw' := hfixed w hw hne
        refine (hvertices' w ?_).trans hw'
        rw [hv, hw']
        exact outside (time k hk') (hvertices w hw hne)
      · intro e he
        have he' := hroutes e he
        refine (hroutes' e ?_).trans he'
        rw [he', hv]
        exact fun z hz => outside (time k hk') (hkeep e he hz)
  have htime : time n le_rfl = 1 := by
    apply Subtype.ext
    simp [time, hnpos.ne']
  simpa only [htime, path.target] using place n le_rfl

end Cslib.Complexity.Graph.PolygonalDrawing
