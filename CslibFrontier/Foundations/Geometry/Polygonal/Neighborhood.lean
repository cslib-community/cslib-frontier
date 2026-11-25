/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Set.Pairwise.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Topology.Algebra.Affine
import Mathlib.Topology.Separation.Hausdorff

/-!
# A small neighborhood of a finite straight-segment arrangement

A sufficiently small ball about any point avoids every segment of a finite arrangement
that does not contain that point. The proof uses compactness of actual real segments and
finite union. When each pair has at most one interior intersection, all crossings admit
pairwise disjoint closed neighborhoods that also avoid a prescribed finite set of points.
-/

public section

namespace Cslib.Polygonal

/-- A finite family of genuine planar segments has a neighborhood of `z` meeting only
segments that already contain `z`. Degenerate segments are allowed in this general lemma. -/
theorem exists_ball_only_incident_segments {ι : Type*} [Finite ι] (a b : ι → ℂ) (z : ℂ) :
    ∃ ε > 0, ∀ i w, w ∈ Metric.ball z ε → w ∈ segment ℝ (a i) (b i) →
      z ∈ segment ℝ (a i) (b i) := by
  classical
  let K : Set ℂ := ⋃ i, if z ∈ segment ℝ (a i) (b i) then ∅ else segment ℝ (a i) (b i)
  have hc : IsClosed K := by
    apply isClosed_iUnion_of_finite
    intro i
    split_ifs
    · exact isClosed_empty
    · rw [segment_eq_image_lineMap]
      exact (isCompact_Icc.image AffineMap.lineMap_continuous).isClosed
  have hz : z ∈ Kᶜ := by simp [K]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hc.isOpen_compl z hz
  refine ⟨ε, hε, fun i w hw hseg => ?_⟩
  by_contra hzi
  apply hball hw
  exact Set.mem_iUnion.mpr ⟨i, by simpa only [hzi, ↓reduceIte] using hseg⟩

/-- Common interior points of two distinct indexed segments of an arrangement. -/
@[expose] def openSegmentCrossings {ι : Type*} (a b : ι → ℂ) : Set ℂ :=
  {z | ∃ i j, i ≠ j ∧ z ∈ openSegment ℝ (a i) (b i) ∧ z ∈ openSegment ℝ (a j) (b j)}

/-- If each distinct pair of segments has at most one interior intersection, the
crossing points are finite. They have pairwise disjoint closed neighborhoods with
positive radii, avoiding the prescribed points and all segments missing their center. -/
theorem exists_openSegment_crossing_neighborhoods {ι : Type*} [Finite ι] (a b : ι → ℂ)
    {S : Set ℂ} (hS : S.Finite) (havoid : Disjoint (openSegmentCrossings a b) S)
    (hpair : ∀ i j, i ≠ j →
      (openSegment ℝ (a i) (b i) ∩ openSegment ℝ (a j) (b j)).Subsingleton) :
    let C := openSegmentCrossings a b
    C.Finite ∧ ∃ ρ : ℂ → ℝ,
      (∀ z ∈ C, 0 < ρ z) ∧ C.PairwiseDisjoint (fun z => Metric.closedBall z (ρ z)) ∧
      ∀ z ∈ C, Disjoint (Metric.closedBall z (ρ z)) S ∧
        ∀ i, z ∉ segment ℝ (a i) (b i) →
          Disjoint (Metric.closedBall z (ρ z)) (segment ℝ (a i) (b i)) := by
  classical
  let C := openSegmentCrossings a b
  let P := {p : ι × ι // p.1 ≠ p.2}
  let T (p : P) := openSegment ℝ (a p.val.1) (b p.val.1) ∩
    openSegment ℝ (a p.val.2) (b p.val.2)
  have hC : C = ⋃ p : P, T p := Set.ext fun z =>
    ⟨fun ⟨i, j, hij, hi, hj⟩ => Set.mem_iUnion.mpr ⟨⟨(i, j), hij⟩, hi, hj⟩, fun hz =>
      let ⟨p, hi, hj⟩ := Set.mem_iUnion.mp hz
      ⟨p.1.1, p.1.2, p.2, hi, hj⟩⟩
  have hfinite : C.Finite := hC ▸ Set.finite_iUnion fun p =>
    (hpair p.val.1 p.val.2 p.property).finite
  obtain ⟨U, hU, hdisj⟩ := hfinite.t2_separation
  have hlocal (z : ℂ) (hz : z ∈ C) : ∃ ε > 0,
      Metric.closedBall z ε ⊆ U z ∧ Disjoint (Metric.closedBall z ε) S ∧
      ∀ i, z ∉ segment ℝ (a i) (b i) →
        Disjoint (Metric.closedBall z ε) (segment ℝ (a i) (b i)) := by
    have : Finite S := hS.to_subtype
    let A : ι ⊕ S → ℂ := Sum.elim a Subtype.val
    let B : ι ⊕ S → ℂ := Sum.elim b Subtype.val
    obtain ⟨η, hη, hseg⟩ := exists_ball_only_incident_segments A B z
    obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp (hU z).2 z (hU z).1
    let ε := min η δ / 2
    have hm : 0 < min η δ := lt_min hη hδ
    have hsmall : ε < min η δ := half_lt_self hm
    have hball : Metric.closedBall z ε ⊆ Metric.ball z η :=
      Metric.closedBall_subset_ball (hsmall.trans_le (min_le_left η δ))
    refine ⟨ε, half_pos hm,
      (Metric.closedBall_subset_ball (hsmall.trans_le (min_le_right η δ))).trans hsub,
      Set.disjoint_left.mpr ?_, ?_⟩
    · intro w hw hws
      have hzz : z ∈ segment ℝ w w := hseg (Sum.inr ⟨w, hws⟩) w (hball hw)
        (left_mem_segment ℝ w w)
      rw [segment_same, Set.mem_singleton_iff] at hzz
      exact Set.disjoint_left.mp havoid hz (hzz.symm ▸ hws)
    · intro i hi
      exact Set.disjoint_left.mpr fun w hw hs => hi (hseg (Sum.inl i) w (hball hw) hs)
  choose radius hpos hsub havoidPts havoidSegments using hlocal
  let ρ (z : ℂ) := if hz : z ∈ C then radius z hz else 1
  have hρ {z : ℂ} (hz : z ∈ C) : ρ z = radius z hz := dite_eq_left hz
  refine ⟨hfinite, ρ, fun z hz => (hρ hz).symm ▸ hpos z hz, ?_, ?_⟩
  · exact hdisj.mono_on (fun {z} hz => (hρ hz).symm ▸ hsub z hz)
  · intro z hz
    rw [hρ hz]
    exact ⟨havoidPts z hz, havoidSegments z hz⟩

end Cslib.Polygonal
