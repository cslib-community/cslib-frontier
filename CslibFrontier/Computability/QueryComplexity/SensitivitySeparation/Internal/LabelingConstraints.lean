/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.TournamentCounts

/-!
# Superquadratic sensitivity separation: labeling constraints

For a tournament `T`, this file describes the internal edges `T.internalEdges I` of a vertex set and
shows that, for an injective vertex map `v`, requiring every directed edge `v i → v j` among chosen
vertices to carry the label `m j` is the same as prescribing the value of the labeling on each
internal edge of `s.image v`. This reformulation lets labeling events be counted as sets of
functions with fixed coordinates.

## Main results

* `Tournament.mem_internalEdges`: a pair lies in `T.internalEdges I` iff both endpoints lie in `I`
  and it is an edge.
* `Tournament.labelingConstraint_iff`: target-constant label constraints on an injected vertex set
  are exactly prescribed values on its internal edges.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/LabelingConstraints.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal.Tournament
variable {k : ℕ} (T : Tournament k)

/-- A pair `p` belongs to `T.internalEdges I` iff `p.1 ∈ I`, `p.2 ∈ I` and `T.Adj p.1 p.2`. -/
theorem mem_internalEdges {I : Finset (Fin k)} {p : Fin k × Fin k} :
    p ∈ T.internalEdges I ↔ (p.1 ∈ I ∧ p.2 ∈ I) ∧ T.Adj p.1 p.2 := by
  simp only [internalEdges, Finset.mem_filter, Finset.mem_product]

/-- For injective `v`, the condition that `A (v i, v j) = m j` for all `i, j ∈ s` with
`T.Adj (v i) (v j)` is equivalent to `A p = m (Function.invFun v p.2)` for every internal edge `p`
of `s.image v`. -/
theorem labelingConstraint_iff {α β : Type} [Nonempty α]
    (s : Finset α) (v : α → Fin k) (m : α → β) (hv : Function.Injective v)
    (A : (Fin k × Fin k) → β) :
    (∀ i ∈ s, ∀ j ∈ s, T.Adj (v i) (v j) → A (v i,v j) = m j) ↔
      ∀ p ∈ T.internalEdges (s.image v), A p = m (Function.invFun v p.2) := by
  refine ⟨fun h ⟨x, y⟩ hp => ?_, fun h i hi j hj ha => ?_⟩
  · obtain ⟨⟨hx, hy⟩, ha⟩ := T.mem_internalEdges.mp hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    simpa only [Function.leftInverse_invFun hv j] using h i hi j hj ha
  · have hp : (v i, v j) ∈ T.internalEdges (s.image v) :=
      T.mem_internalEdges.mpr ⟨⟨Finset.mem_image_of_mem v hi, Finset.mem_image_of_mem v hj⟩, ha⟩
    simpa only [Function.leftInverse_invFun hv j] using h (v i, v j) hp

end Internal.Tournament

end

end Cslib.QueryComplexity.SensitivitySeparation
