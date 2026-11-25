/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Orthogonal.Isolation
import Mathlib.Data.List.Nodup

/-!
# Gluing local and exterior incidence routes

Two simple orthogonal routes can be joined at a common endpoint when their full real supports
intersect only there. The joined route is again simple and orthogonal; existing subdivision
lemmas identify its support, final endpoint, segment list, and Manhattan wire length.

## Main results

* `head_mem_segment_endpoint`, `last_mem_segment_endpoint`: an endpoint of a simple route
  can occur on a segment only as a segment endpoint.
* `isOrthogonal_join`, `isSimple_join`: geometric correctness of endpoint gluing.

## References

These finite polygonal-route gluing lemmas and proofs are original.
-/

public section

namespace Cslib.Orthogonal


/-- A simple route's initial listed vertex can lie on one of its segments only as an endpoint.
-/
theorem head_mem_segment_endpoint {r : Route} (hs : IsSimple r) {p : Point}
    (hp : r.head? = some p) {e : Point × Point} (he : e ∈ r.consecutivePairs)
    (hm : realPoint p ∈ segment e.1 e.2) : p = e.1 ∨ p = e.2 := by
  obtain ⟨_ | ⟨b, tail⟩, rfl⟩ := List.head?_eq_some_iff.mp hp
  · simp [List.consecutivePairs] at he
  · exact .inl (congrArg Prod.fst (segment_eq_first_of_head_mem hs he hm)).symm

/-- A simple route's final listed vertex can lie on one of its segments only as an endpoint.
-/
theorem last_mem_segment_endpoint {r : Route} (hs : IsSimple r) {p : Point}
    (hp : r.getLast? = some p) {e : Point × Point} (he : e ∈ r.consecutivePairs)
    (hm : realPoint p ∈ segment e.1 e.2) : p = e.1 ∨ p = e.2 := by
  induction r with
  | nil => simp at hp
  | cons a r ih =>
    cases r with
    | nil => simp [List.consecutivePairs] at he
    | cons b r =>
      have hp' : (b :: r).getLast? = some p := by simpa only [List.getLast?_cons_cons] using hp
      rcases List.mem_cons.mp he with rfl | he
      · exact .inr <| realPoint_injective <|
          first_segment_tail_contact hs hm (.inl ⟨p, List.mem_of_getLast? hp', rfl⟩)
      · exact ih hs.of_cons hp' he

/-- Joining properly orthogonal routes at their common listed endpoint remains orthogonal. -/
theorem isOrthogonal_join {q r : Route} {p : Point}
    (hq : q.getLast? = some p) (hr : r.head? = some p)
    (hoq : IsOrthogonal q) (hor : IsOrthogonal r) : IsOrthogonal (q ++ r.tail) := fun e he =>
  (List.mem_append.mp (consecutivePairs_join hq hr ▸ he)).elim (hoq e) (hor e)

/-- Joining simple routes whose only continuous intersection is their common endpoint
introduces neither repeated listed points nor forbidden segment contacts. -/
theorem isSimple_join {q r : Route} {p : Point}
    (hq : q.getLast? = some p) (hr : r.head? = some p)
    (hsq : IsSimple q) (hsr : IsSimple r)
    (hc : ∀ z ∈ support q, z ∈ support r → z = realPoint p) :
    IsSimple (q ++ r.tail) := by
  have hrnot : p ∉ r.tail := by
    obtain ⟨_, rfl⟩ := List.head?_eq_some_iff.mp hr
    exact (List.nodup_cons.mp hsr.1).1
  refine ⟨List.nodup_append.mpr ⟨hsq.1, hsr.1.tail, fun x hx _ hy heq => ?_⟩,
    fun e he f hf hne => ?_⟩
  · subst heq
    exact hrnot (realPoint_injective
      (hc _ (.inl ⟨x, hx, rfl⟩) (.inl ⟨x, List.mem_of_mem_tail hy, rfl⟩)) ▸ hy)
  · have hcross (e) (he : e ∈ q.consecutivePairs) (f) (hf : f ∈ r.consecutivePairs) :
        EndpointContacts e.1 e.2 f.1 f.2 := fun z hz hz' => by
      have hzp := hc z (.inr ⟨e, he, hz⟩) (.inr ⟨f, hf, hz'⟩)
      exact ⟨(last_mem_segment_endpoint hsq hq he (hzp ▸ hz)).imp
          (hzp.trans ∘ congrArg realPoint) (hzp.trans ∘ congrArg realPoint),
        (head_mem_segment_endpoint hsr hr hf (hzp ▸ hz')).imp
          (hzp.trans ∘ congrArg realPoint) (hzp.trans ∘ congrArg realPoint)⟩
    rw [consecutivePairs_join hq hr, List.mem_append] at he hf
    rcases he with he | he <;> rcases hf with hf | hf
    exacts [hsq.2 e he f hf hne, hcross e he f hf, (hcross f hf e he).symm, hsr.2 e he f hf hne]

end Cslib.Orthogonal
