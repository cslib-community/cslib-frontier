/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/List/Nodup.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.List.Nodup

/-!
# Distinct items of mapped lists

The items `f i k` for the distinct indices `i` of a list and the distinct entries `k` of lists
`ks i` are distinct when `f` determines both `i` and `k` (`List.nodup_flatMap_map`).

## Main results

* `List.nodup_flatMap_map`: the flat map of the mapped lists has no duplicates.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the keys of the units that
the evaluator of the proof of Theorem J.3 writes (p. 54); source module `Nc.Grp.StepBase`.
-/

public section

namespace List

/-- The items `f i k` of several lists `ks i`, for the indices `i` of a list without duplicates,
are distinct if the lists have no duplicates and `f i k` determines `i` and `k`. -/
theorem nodup_flatMap_map {ι κ β : Type*} {l : List ι} (hl : l.Nodup) {ks : ι → List κ}
    (hks : ∀ i, (ks i).Nodup) {f : ι → κ → β}
    (hf : ∀ i k i' k', f i k = f i' k' → i = i' ∧ k = k') :
    (l.flatMap fun i => (ks i).map (f i)).Nodup :=
  nodup_flatMap.2 ⟨fun i _ => (hks i).map fun k k' h => (hf i k i k' h).2,
    hl.imp fun hii' => disjoint_left.2 fun a h h' => by
      obtain ⟨k, -, rfl⟩ := mem_map.1 h
      obtain ⟨k', -, h'⟩ := mem_map.1 h'
      exact hii' (hf _ _ _ _ h'.symm).1⟩

end List
