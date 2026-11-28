/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Digraph.Layered
public import Mathlib.Order.Filter.Extr

import Mathlib.Order.WellFounded

/-!
# Min-isolation in layered digraphs

If constrained minimum weights differ across the vertices in a chosen internal layer,
then global minimizers must pass through the same vertex in that layer. Each piece of a
constrained minimizer is itself a minimum path between its endpoints. Induction on the
endpoint layer gap then yields uniqueness for all reachable pairs.

## Main results

* `LayeredDigraph.isMinOn_pathsThrough_comp_iff`: minimization through a fixed internal vertex
  is equivalent to minimizing both pieces of the path.
* `LayeredDigraph.isMinIsolating_of_separated`: separation at one internal layer per pair
  implies all-pairs min-isolation.

## References

* [Hoza2026NLUL], proof of Theorem 2.4. The separation
  hypothesis below allows any internal layer for each pair. Hoza chooses the layer
  of maximum 2-adic valuation and obtains separation from a seed-dependent weight assignment.
-/

public section

namespace Cslib.LayeredDigraph

variable {V : Type*} {G : LayeredDigraph V} {a b v : V}

/-- The paths from `a` to `b` visiting `v` as an internal vertex. -/
@[expose] def pathsThrough (G : LayeredDigraph V) (a b v : V) : Set (G.Path a b) :=
  {p | v ∈ p.internalVertices}

/-- Two paths concatenated at an internal vertex give a path through that vertex. -/
theorem comp_mem_pathsThrough (q : G.Path a v) (r : G.Path v b)
    (ha : G.layer a < G.layer v) (hb : G.layer v < G.layer b) :
    q.comp r ∈ G.pathsThrough a b v := by
  simp [pathsThrough, Path.internalVertices_comp q r ha hb]

variable (weight : V → ℕ)

/-- Minimizing a concatenation among paths through its common internal vertex is
equivalent to minimizing both component paths. -/
theorem isMinOn_pathsThrough_comp_iff (q : G.Path a v) (r : G.Path v b)
    (ha : G.layer a < G.layer v) (hb : G.layer v < G.layer b) :
    IsMinOn (Path.internalWeight weight) (G.pathsThrough a b v) (q.comp r) ↔
      IsMinOn (Path.internalWeight weight) Set.univ q ∧
        IsMinOn (Path.internalWeight weight) Set.univ r := by
  rw [isMinOn_univ_iff, isMinOn_univ_iff, isMinOn_iff]
  refine ⟨fun h => ⟨fun q' => ?_, fun r' => ?_⟩, fun ⟨hq, hr⟩ p hp => ?_⟩
  · have hq := h (q'.comp r) (comp_mem_pathsThrough q' r ha hb)
    rw [Path.internalWeight_comp weight q r ha hb, Path.internalWeight_comp weight q' r ha hb] at hq
    omega
  · have hr := h (q.comp r') (comp_mem_pathsThrough q r' ha hb)
    rw [Path.internalWeight_comp weight q r ha hb, Path.internalWeight_comp weight q r' ha hb] at hr
    omega
  · let _ := G.toQuiver
    obtain ⟨q', r', rfl⟩ := p.exists_eq_comp_of_mem_vertices (p.mem_internalVertices_iff.mp hp).1
    rw [Path.internalWeight_comp weight q r ha hb, Path.internalWeight_comp weight q' r' ha hb]
    exact Nat.add_le_add (Nat.add_le_add_right (hq q') _) (hr r')

/-- A vertex weighting is min-isolating if each reachable pair has a unique path of
minimum internal weight. -/
@[expose] def IsMinIsolating (G : LayeredDigraph V) (weight : V → ℕ) : Prop :=
  ∀ a b : V, Nonempty (G.Path a b) →
    ∃! p : G.Path a b, IsMinOn (Path.internalWeight weight) Set.univ p

/-- Suppose that for each pair whose endpoint layers differ by at least two, some
internal layer separates the minimum weights of paths constrained to go through
distinct vertices of that layer. Then the weighting is min-isolating. -/
theorem isMinIsolating_of_separated (G : LayeredDigraph V)
    (separated : ∀ a b : V, G.layer a + 1 < G.layer b →
      ∃ k, G.layer a < k ∧ k < G.layer b ∧
        ∀ ⦃u v : V⦄, G.layer u = k → G.layer v = k → u ≠ v →
          ∀ ⦃p q : G.Path a b⦄, p ∈ G.pathsThrough a b u → q ∈ G.pathsThrough a b v →
            IsMinOn (Path.internalWeight weight) (G.pathsThrough a b u) p →
            IsMinOn (Path.internalWeight weight) (G.pathsThrough a b v) q →
            p.internalWeight weight ≠ q.internalWeight weight) :
    G.IsMinIsolating weight := by
  intro a b hab
  generalize hn : G.layer b - G.layer a = n
  induction n using Nat.strong_induction_on generalizing a b with
  | ind n ih =>
    let _ := hab
    have ⟨p, hp⟩ : ∃ p : G.Path a b, IsMinOn (Path.internalWeight weight) Set.univ p :=
      ⟨Function.argmin _, isMinOn_univ_iff.mpr fun q =>
        le_of_not_gt (Function.not_lt_argmin _ q)⟩
    refine ⟨p, hp, fun q hq => ?_⟩
    by_cases hs : G.layer b ≤ G.layer a + 1
    · exact Path.eq_of_layer_le_succ hs q p
    obtain ⟨k, ha, hb, hsep⟩ := separated a b (by omega)
    obtain ⟨u, p₁, p₂, rfl, hu⟩ := p.exists_eq_comp_of_layer ha.le hb.le
    obtain ⟨v, q₁, q₂, rfl, hv⟩ := q.exists_eq_comp_of_layer ha.le hb.le
    have hau : G.layer a < G.layer u := hu ▸ ha
    have hub : G.layer u < G.layer b := hu ▸ hb
    have hpmin := hp.of_subset (Set.subset_univ (G.pathsThrough a b u))
    have hqmin := hq.of_subset (Set.subset_univ (G.pathsThrough a b v))
    obtain rfl : u = v := not_ne_iff.mp fun hne => hsep hu hv hne
      (comp_mem_pathsThrough p₁ p₂ hau hub) (comp_mem_pathsThrough q₁ q₂ (hv ▸ ha) (hv ▸ hb))
      hpmin hqmin (le_antisymm (isMinOn_univ_iff.mp hp _) (isMinOn_univ_iff.mp hq _))
    obtain ⟨_, _, h₁⟩ := ih (G.layer u - G.layer a) (by omega) a u ⟨p₁⟩ rfl
    obtain ⟨_, _, h₂⟩ := ih (G.layer b - G.layer u) (by omega) u b ⟨p₂⟩ rfl
    obtain ⟨hp₁, hp₂⟩ := (isMinOn_pathsThrough_comp_iff weight p₁ p₂ hau hub).mp hpmin
    obtain ⟨hq₁, hq₂⟩ := (isMinOn_pathsThrough_comp_iff weight q₁ q₂ hau hub).mp hqmin
    rw [(h₁ _ hq₁).trans (h₁ _ hp₁).symm, (h₂ _ hq₂).trans (h₂ _ hp₂).symm]

end Cslib.LayeredDigraph
