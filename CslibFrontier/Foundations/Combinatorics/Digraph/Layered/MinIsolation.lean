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
  change v ∈ (q.comp r).internalVertices
  rw [Path.internalVertices_comp q r ha hb]
  exact List.mem_append_right _ (List.mem_cons_self)

variable (weight : V → ℕ)

/-- Minimizing a concatenation among paths through its common internal vertex is
equivalent to minimizing both component paths. -/
theorem isMinOn_pathsThrough_comp_iff (q : G.Path a v) (r : G.Path v b)
    (ha : G.layer a < G.layer v) (hb : G.layer v < G.layer b) :
    IsMinOn (Path.internalWeight weight) (G.pathsThrough a b v) (q.comp r) ↔
      IsMinOn (Path.internalWeight weight) Set.univ q ∧
        IsMinOn (Path.internalWeight weight) Set.univ r := by
  rw [isMinOn_univ_iff, isMinOn_univ_iff, isMinOn_iff]
  constructor
  · intro h
    refine ⟨fun q' ↦ ?_, fun r' ↦ ?_⟩
    · have hq := h (q'.comp r) (comp_mem_pathsThrough q' r ha hb)
      rw [Path.internalWeight_comp weight q r ha hb,
        Path.internalWeight_comp weight q' r ha hb] at hq
      omega
    · have hr := h (q.comp r') (comp_mem_pathsThrough q r' ha hb)
      rw [Path.internalWeight_comp weight q r ha hb,
        Path.internalWeight_comp weight q r' ha hb] at hr
      omega
  · rintro ⟨hq, hr⟩ p hp
    change v ∈ p.internalVertices at hp
    let _ := G.toQuiver
    obtain ⟨q', r', rfl⟩ :=
      p.exists_eq_comp_of_mem_vertices (p.mem_internalVertices_iff.mp hp).1
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
  have existsMin (a b : V) [Nonempty (G.Path a b)] :
      ∃ p : G.Path a b, IsMinOn (Path.internalWeight weight) Set.univ p :=
    ⟨Function.argmin _, isMinOn_univ_iff.mpr fun q ↦
      le_of_not_gt (Function.not_lt_argmin _ q)⟩
  suffices h : ∀ n a b, G.layer b - G.layer a = n →
      ∀ [Nonempty (G.Path a b)], ∃! p : G.Path a b,
        IsMinOn (Path.internalWeight weight) Set.univ p by
    intro a b hab
    let _ := hab
    exact h _ a b rfl
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro a b hn hab
    obtain ⟨p, hp⟩ := existsMin a b
    refine ⟨p, hp, fun q hq ↦ ?_⟩
    by_cases hs : G.layer b ≤ G.layer a + 1
    · exact Path.eq_of_layer_le_succ hs q p
    obtain ⟨k, ha, hb, hsep⟩ := separated a b (by omega)
    obtain ⟨u, p₁, p₂, rfl, hu⟩ := p.exists_eq_comp_of_layer ha.le hb.le
    obtain ⟨v, q₁, q₂, rfl, hv⟩ := q.exists_eq_comp_of_layer ha.le hb.le
    have hau : G.layer a < G.layer u := by rwa [hu]
    have hub : G.layer u < G.layer b := by rwa [hu]
    have hpu := comp_mem_pathsThrough p₁ p₂ hau hub
    have hqv := comp_mem_pathsThrough q₁ q₂ (by rwa [hv]) (by rwa [hv])
    have hpmin := hp.of_subset (Set.subset_univ (G.pathsThrough a b u))
    have hqmin := hq.of_subset (Set.subset_univ (G.pathsThrough a b v))
    have huv : u = v := by
      by_contra hne
      apply hsep hu hv hne hpu hqv hpmin hqmin
      exact le_antisymm (isMinOn_univ_iff.mp hp _) (isMinOn_univ_iff.mp hq _)
    subst v
    have hleft : G.layer u - G.layer a < n := by omega
    have hright : G.layer b - G.layer u < n := by omega
    obtain ⟨_, _, h₁⟩ := @ih _ hleft a u rfl ⟨p₁⟩
    obtain ⟨_, _, h₂⟩ := @ih _ hright u b rfl ⟨p₂⟩
    obtain ⟨hp₁, hp₂⟩ := (isMinOn_pathsThrough_comp_iff weight p₁ p₂ hau hub).mp hpmin
    obtain ⟨hq₁, hq₂⟩ := (isMinOn_pathsThrough_comp_iff weight q₁ q₂ hau hub).mp hqmin
    rw [(h₁ _ hq₁).trans (h₁ _ hp₁).symm, (h₂ _ hq₂).trans (h₂ _ hp₂).symm]

end Cslib.LayeredDigraph
