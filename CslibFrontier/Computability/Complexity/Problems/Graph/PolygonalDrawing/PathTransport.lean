/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing
public import Mathlib.Topology.Connected.PathConnected
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.SquareMove
import CslibFrontier.Foundations.Geometry.PuncturedPaths
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Moving a vertex along a path avoiding closed obstacles

The path need only be continuous. Compactness of its image supplies one positive clearance
from the closed obstacle set, and uniform continuity supplies a finite subdivision for that
clearance. Each local square move then fixes every protected vertex and whole protected route.

When the obstacle complement is path connected, a vertex can move to any vacant point in
that complement. The proof removes every other vertex position before choosing a path.
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
    by_contra! hm
    have hnorm := Complex.norm_le_abs_re_add_abs_im (z - path t)
    rw [Complex.sub_re, Complex.sub_im, ← dist_eq_norm] at hnorm
    exact hclear (Metric.mem_thickening_iff.mpr ⟨path t, ⟨t, rfl⟩,
      by linarith [(le_max_left _ _).trans_lt hm, (le_max_right _ _).trans_lt hm,
        show r = δ / 2 from rfl]⟩) hz
  obtain ⟨η, hη, hnear⟩ :=
    Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous hcont) r hr
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / η)
  have hnpos : 0 < (n : ℝ) := (div_pos zero_lt_one hη).trans hn
  have hmesh : 1 / (n : ℝ) < η :=
    (div_lt_iff₀ hnpos).mpr (by simpa only [mul_comm] using (div_lt_iff₀ hη).mp hn)
  let time (k : ℕ) (hk : k ≤ n) : unitInterval :=
    ⟨k / (n : ℝ), div_nonneg (Nat.cast_nonneg _) hnpos.le,
      (div_le_one hnpos).mpr (Nat.cast_le.mpr hk)⟩
  have step (k : ℕ) (hk : k + 1 ≤ n) (hk' : k ≤ n) :
      dist (time (k + 1) hk) (time k hk') < η := by
    change dist ((↑(k + 1) : ℝ) / n) ((k : ℝ) / n) < η
    rwa [Real.dist_eq, ← sub_div, Nat.cast_succ, add_sub_cancel_left,
      abs_of_nonneg (div_nonneg zero_le_one hnpos.le)]
  have place (k : ℕ) (hk : k ≤ n) : ∃ E : PolygonalDrawing G,
      E.IsEmbedding ∧ E.vertex v = path (time k hk) ∧
        (∀ w ∈ G.vertices, w ≠ v → E.vertex w = D.vertex w) ∧
        ∀ e ∈ keep, E.route e = D.route e := by
    induction k with
    | zero =>
      exact ⟨D, hD, by rw [show time 0 hk = 0 from Subtype.ext (by simp [time]), path.source],
        fun _ _ _ => rfl, fun _ _ => rfl⟩
    | succ k ih =>
      have hk' : k ≤ n := (Nat.le_succ k).trans hk
      obtain ⟨E, hE, hv, hfixed, hroutes⟩ := ih hk'
      have hmove : ‖path (time (k + 1) hk) - E.vertex v‖ < r := by
        simpa only [hv, dist_eq_norm] using hnear (step k hk hk')
      obtain ⟨F, hF, htarget, hvertices', hroutes'⟩ :=
        hE.exists_square_move hG v (path (time (k + 1) hk)) hr hmove
      refine ⟨F, hF, htarget, fun w hw hne => ?_, fun e he => ?_⟩
      · rw [hvertices' w (hv ▸ hfixed w hw hne ▸ outside _ (hvertices w hw hne)),
          hfixed w hw hne]
      · rw [hroutes' e fun z hz => hv ▸ outside _ (hkeep e he (hroutes e he ▸ hz)),
          hroutes e he]
  simpa only [show time n le_rfl = 1 from Subtype.ext (by simp [time, hnpos.ne']), path.target]
    using place n le_rfl

/-- Move a declared vertex to a vacant point in a path-connected closed-obstacle complement.
All other declared vertex positions stay fixed, and each selected route supported in the
obstacle is literally unchanged. -/
theorem IsEmbedding.exists_vertex_move_in_compl {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices)
    (v : ℕ) (hv : v ∈ G.vertices) {K : Set ℂ} (hK : IsClosed K)
    (hconn : IsPathConnected Kᶜ) (hsource : D.vertex v ∉ K)
    {b : ℂ} (htarget : b ∉ K)
    (hvacant : ∀ w ∈ G.vertices, w ≠ v → b ≠ D.vertex w)
    (keep : Set (Fin G.edges.length)) (hkeep : ∀ e ∈ keep, (D.route e).support ⊆ K) :
    ∃ E : PolygonalDrawing G, E.IsEmbedding ∧ E.vertex v = b ∧
      (∀ w ∈ G.vertices, w ≠ v → E.vertex w = D.vertex w) ∧
      ∀ e ∈ keep, E.route e = D.route e := by
  let names : Set ℕ := {w | w ∈ G.vertices ∧ w ≠ v}
  let occupied := D.vertex '' names
  have hnames : names.Finite := G.vertices.finite_toSet.subset fun _ hw => hw.1
  have hoccupied : occupied.Finite := hnames.image D.vertex
  have hrank : 1 < Module.rank ℝ ℂ := by simp [Complex.rank_real_complex]
  have hpath :=
    (isPathConnected_sdiff_finite_of_isOpen hrank hK.isOpen_compl hconn hoccupied).joinedIn
      (D.vertex v) ⟨hsource, fun ⟨w, ⟨hw, hwv⟩, heq⟩ => hwv (hD.vertices_injective hw hv heq)⟩
      b ⟨htarget, fun ⟨w, ⟨hw, hwv⟩, heq⟩ => hvacant w hw hwv heq.symm⟩
  refine hD.exists_vertex_move_along_path hG v hpath.somePath (hK.union hoccupied.isClosed)
    (Set.range_subset_iff.mpr fun t h => h.elim (hpath.somePath_mem t).1 (hpath.somePath_mem t).2)
    (fun w hw hwv => Or.inr ⟨w, ⟨hw, hwv⟩, rfl⟩) keep fun e he z hz => Or.inl (hkeep e he hz)

end Cslib.Complexity.Graph.PolygonalDrawing
