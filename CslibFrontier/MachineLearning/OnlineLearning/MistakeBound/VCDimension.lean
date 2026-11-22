/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Halving
public import CslibFrontier.MachineLearning.PACLearning.VCDimension
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset

/-!
# VC dimension and Littlestone dimension

A set shattered by `C` (cslib's `PACLearning.SetShatters`) gives a complete mistake tree: label
the nodes at depth `j` with the `j`-th point of the set (`hasMistakeTree_of_setShatters`).
Hence the VC dimension is at most the Littlestone dimension (`evcDim_le_littlestoneDim`), and so at
most the optimal mistake bound [Littlestone1988, §3, Theorem 4]. In particular a class of infinite
VC dimension has infinite Littlestone dimension. With the halving bound this gives the chain
`evcDim C ≤ littlestoneDim C ≤ ⌊log₂ |C|⌋` for finite classes. Both inequalities are tight for the
class of all Boolean functions on a finite domain (`littlestoneDim_univ`). The first can be far
from tight: see `CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Thresholds`.

## Main results

* `Cslib.MachineLearning.OnlineLearning.MistakeBound.hasMistakeTree_of_setShatters`: a shattered
  set of size `d` gives a complete `d`-mistake tree.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.evcDim_le_littlestoneDim`: the VC dimension is
  at most the Littlestone dimension.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.evcDim_le_optimalMistakeBound`:
  [Littlestone1988, §3, Theorem 4].
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.littlestoneDim_eq_top_of_not_hasFiniteVCDim`:
  infinite VC dimension forces infinite Littlestone dimension.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.littlestoneDim_univ`: all Boolean functions on
  a finite domain `α` have Littlestone dimension `|α|`.

## References

* [N. Littlestone, *Learning quickly when irrelevant attributes abound: a new linear-threshold
  algorithm*][Littlestone1988]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.MistakeBound

open PACLearning (ConceptClass SetShatters evcDim HasFiniteVCDim)

variable {α : Type*}

/-- A finite set `W` shattered by `C` gives a complete mistake tree of height `|W|`
[Littlestone1988, §3, proof of Theorem 4]. -/
theorem hasMistakeTree_of_setShatters {C : ConceptClass α Bool} (W : Finset α)
    (hW : SetShatters C (W : Set α)) : HasMistakeTree W.card C := by
  classical
  induction W using Finset.induction_on generalizing C with
  | empty =>
    obtain ⟨c, hc, -⟩ := hW ∅ (Set.empty_subset _)
    exact ⟨c, hc⟩
  | insert a W ha ih =>
    rw [Finset.card_insert_of_notMem ha]
    refine ⟨a, fun y => ih ?_⟩
    intro W' hW'
    obtain ⟨c, hc, hcW⟩ := hW (W' ∪ {z | z = a ∧ y = true}) (by
      rintro z (hz | ⟨rfl, -⟩)
      · exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp (hW' hz)))
      · exact Finset.mem_coe.mpr (Finset.mem_insert_self _ _))
    have key : ∀ z, z ∈ (insert a W : Finset α) →
        (c z = true ↔ z ∈ W' ∨ (z = a ∧ y = true)) := by
      intro z hz
      have := congrArg (z ∈ ·) hcW
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_coe,
        eq_iff_iff] at this
      exact ⟨fun h => this.mp ⟨h, hz⟩, fun h => (this.mpr h).1⟩
    have hca : c a = y := by
      have := key a (Finset.mem_insert_self _ _)
      have haW' : a ∉ W' := fun h => ha (Finset.mem_coe.mp (hW' h))
      cases y <;> cases hc' : c a <;> simp_all
    refine ⟨c, (mem_versionSpace_singleton).mpr ⟨hc, hca⟩, ?_⟩
    ext z
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_coe]
    constructor
    · rintro ⟨hcz, hz⟩
      have := (key z (Finset.mem_insert_of_mem hz)).mp hcz
      rcases this with h | ⟨rfl, -⟩
      · exact h
      · exact absurd hz ha
    · intro hz
      have hzW : z ∈ W := Finset.mem_coe.mp (hW' hz)
      exact ⟨(key z (Finset.mem_insert_of_mem hzW)).mpr (Or.inl hz), hzW⟩

theorem natCast_le_littlestoneDim_of_setShatters {C : ConceptClass α Bool} (W : Finset α)
    (hW : SetShatters C (W : Set α)) : (W.card : ℕ∞) ≤ littlestoneDim C :=
  le_littlestoneDim_of_hasMistakeTree (hasMistakeTree_of_setShatters W hW)

/-- The VC dimension is at most the Littlestone dimension. -/
theorem evcDim_le_littlestoneDim (C : ConceptClass α Bool) :
    evcDim C ≤ littlestoneDim C :=
  PACLearning.evcDim_le_iff.mpr (natCast_le_littlestoneDim_of_setShatters (C := C))

/-- The VC dimension is at most the optimal mistake bound. [Littlestone1988, §3, Theorem 4]
treats finite Boolean classes and assigns both quantities the value −1 on the empty class.
The extended-natural bounds here both give zero on the empty class and allow infinite classes. -/
theorem evcDim_le_optimalMistakeBound (C : ConceptClass α Bool) :
    evcDim C ≤ optimalMistakeBound C :=
  (evcDim_le_littlestoneDim C).trans (littlestoneDim_le_optimalMistakeBound C)

/-- A class of infinite VC dimension has infinite Littlestone dimension. -/
theorem littlestoneDim_eq_top_of_not_hasFiniteVCDim {C : ConceptClass α Bool}
    (h : ¬ HasFiniteVCDim C) : littlestoneDim C = ⊤ := by
  exact top_le_iff.mp (PACLearning.evcDim_eq_top_iff.mpr h ▸ evcDim_le_littlestoneDim C)

/-- The class of all Boolean functions on a finite domain `α` has Littlestone dimension `|α|`: the
whole domain is shattered, and there are `2 ^ |α|` functions. -/
theorem littlestoneDim_univ [Fintype α] :
    littlestoneDim (Set.univ : ConceptClass α Bool) = Fintype.card α := by
  classical
  apply le_antisymm
  · rw [← Finset.coe_univ]
    refine (littlestoneDim_le_log_card _).trans ?_
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Nat.log_pow (by norm_num)]
  · have hW : SetShatters (Set.univ : ConceptClass α Bool) ((Finset.univ : Finset α) : Set α) := by
      intro W' _
      refine ⟨fun x => decide (x ∈ W'), Set.mem_univ _, ?_⟩
      ext z
      simp
    simpa using natCast_le_littlestoneDim_of_setShatters _ hW

end Cslib.MachineLearning.OnlineLearning.MistakeBound
