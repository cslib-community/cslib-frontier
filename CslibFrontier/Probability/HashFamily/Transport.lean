/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.HashFamily

/-!
# Changing the digest group of a Δ-universal hash family

An injective additive map `f : Y →+ Z` applied to every digest preserves `ε`-Δ-universality: the
difference of two digests is `d'` exactly when the difference of their images is `f d'`, and a
difference outside the range of `f` never occurs. A hash proved Δ-universal over a field therefore
stays Δ-universal when its digests are written as bit strings by an additive encoding, where the
difference is XOR.

## Main results

* `Cslib.Probability.IsDeltaUniversalHash.postcompose`: an injective additive map on digests
  preserves `ε`-Δ-universality.
-/

public section

namespace Cslib.Probability.IsDeltaUniversalHash

open scoped ENNReal

variable {ι X Y Z : Type*} [AddGroup Y] [AddGroup Z] {seed : PMF ι} {hash : ι → X → Y}
  {ε : ℝ≥0∞}

/-- An injective additive map on digests preserves `ε`-Δ-universality. -/
theorem postcompose (hh : IsDeltaUniversalHash seed hash ε) (f : Y →+ Z)
    (hf : Function.Injective f) :
    IsDeltaUniversalHash seed (fun i x => f (hash i x)) ε := fun x x' hx d => by
  by_cases hd : ∃ d', f d' = d
  · obtain ⟨d', rfl⟩ := hd
    have hset : {i | f (hash i x) - f (hash i x') = f d'} = {i | hash i x - hash i x' = d'} := by
      ext i
      simp only [Set.mem_ofPred_eq, ← map_sub]
      exact hf.eq_iff
    rw [hset]
    exact hh x x' hx d'
  · have hset : {i | f (hash i x) - f (hash i x') = d} = ∅ := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, ← map_sub]
      exact fun h => hd ⟨_, h⟩
    rw [hset]
    simp

end Cslib.Probability.IsDeltaUniversalHash
