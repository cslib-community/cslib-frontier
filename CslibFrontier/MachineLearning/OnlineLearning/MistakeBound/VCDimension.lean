/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Halving
public import CslibFrontier.MachineLearning.PACLearning.NatarajanDimension
import Mathlib.Data.Fintype.Powerset

/-!
# Natarajan, VC and Littlestone dimensions

Every finite set `W` that is Natarajan-shattered by `C : ConceptClass α β`
(`PACLearning.NatarajanShatters`) gives a complete mistake tree of height `|W|`: at depth `j`,
query the `j`-th point of `W` with the two distinct witness labels `f₀ x ≠ f₁ x`
(`hasMistakeTree_of_natarajanShatters`). Hence `natarajanDim C ≤ littlestoneDim C`
(`natarajanDim_le_littlestoneDim`), and for Boolean classes (`natarajanDim_eq_evcDim`) the extended
and natural VC dimensions are at most the Littlestone dimension (`evcDim_le_littlestoneDim`,
`vcDim_le_littlestoneDim`) and at most the optimal mistake bound (`evcDim_le_optimalMistakeBound`,
[Littlestone1988, §3, Theorem 4]). In particular, infinite Natarajan or VC dimension forces
infinite Littlestone dimension.

Along any root-to-leaf path of a mistake tree, an instance queried at an ancestor has a fixed value
across the entire subtree, so it cannot split again (`le_card_of_hasMistakeTree_of_agree_outside`).
Thus on a finite domain `α`, `littlestoneDim C ≤ |α|` (`littlestoneDim_le_card`) regardless of the
label alphabet `β` (sharper than the halving bound `⌊log₂ |β| ^ |α|⌋` when `|β| ≥ 3`), and equality
holds for `Set.univ : ConceptClass α β` whenever `β` is nontrivial
(`littlestoneDim_univ_of_nontrivial`, `littlestoneDim_univ`). The inequality
`vcDim C ≤ littlestoneDim C` can be arbitrarily loose: see
`CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Thresholds`.

## Main results

* `Cslib.MachineLearning.OnlineLearning.MistakeBound.hasMistakeTree_of_natarajanShatters`,
  `Cslib.MachineLearning.OnlineLearning.MistakeBound.hasMistakeTree_of_setShatters`: a shattered
  finite set of size `d` gives a complete `d`-mistake tree.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.natarajanDim_le_littlestoneDim`,
  `Cslib.MachineLearning.OnlineLearning.MistakeBound.evcDim_le_littlestoneDim`,
  `Cslib.MachineLearning.OnlineLearning.MistakeBound.vcDim_le_littlestoneDim`: the Natarajan and VC
  dimensions are at most the Littlestone dimension.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.natarajanDim_le_optimalMistakeBound`,
  `Cslib.MachineLearning.OnlineLearning.MistakeBound.evcDim_le_optimalMistakeBound`:
  [Littlestone1988, §3, Theorem 4; DanielySabatoBenDavidShalevShwartz2015].
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.littlestoneDim_le_card`,
  `Cslib.MachineLearning.OnlineLearning.MistakeBound.littlestoneDim_univ_of_nontrivial`,
  `Cslib.MachineLearning.OnlineLearning.MistakeBound.littlestoneDim_univ`: finite-domain upper
  bound `|α|` and exact value on `Set.univ`.

## References

* [A. Daniely, S. Sabato, S. Ben-David, S. Shalev-Shwartz, *Multiclass Learnability and the ERM
  Principle*][DanielySabatoBenDavidShalevShwartz2015]
* [N. Littlestone, *Learning quickly when irrelevant attributes abound: a new linear-threshold
  algorithm*][Littlestone1988]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.MistakeBound

open PACLearning (ConceptClass SetShatters NatarajanShatters vcDim evcDim natarajanDim
  HasFiniteVCDim HasFiniteNatarajanDim)

variable {α β : Type*}

/-! ### Natarajan and VC lower bounds -/

/-- A finite set `W` Natarajan-shattered by `C` gives a complete mistake tree of height `|W|`
[Littlestone1988, §3, proof of Theorem 4; DanielySabatoBenDavidShalevShwartz2015]. -/
theorem hasMistakeTree_of_natarajanShatters {C : ConceptClass α β} (W : Finset α)
    (hW : NatarajanShatters C (W : Set α)) : HasMistakeTree W.card C := by
  classical
  induction W using Finset.induction_on generalizing C with
  | empty => exact hW.nonempty
  | insert a W ha ih =>
    rw [Finset.card_insert_of_notMem ha]
    obtain ⟨f₀, f₁, hne, h⟩ := Finset.coe_insert a W ▸ hW
    have ha_mem : a ∈ insert a (W : Set α) := Set.mem_insert a _
    refine ⟨a, f₀ a, f₁ a, hne a ha_mem, ih ?_, ih ?_⟩
    · refine ⟨f₀, f₁, fun x hx => hne x (Set.mem_insert_of_mem a hx), fun B hB => ?_⟩
      obtain ⟨c, hc, h₀, h₁⟩ := h (insert a B) (Set.insert_subset_insert hB)
      refine ⟨c, mem_versionSpace_singleton.mpr ⟨hc, h₀ a (Set.mem_insert a B)⟩,
        fun x hx => h₀ x (Set.mem_insert_of_mem a hx), fun x hx => ?_⟩
      have hxa : x ≠ a := fun hxeq => ha (Finset.mem_coe.mp (hxeq ▸ hx.1))
      exact h₁ x ⟨Set.mem_insert_of_mem a hx.1, fun hx' =>
        (Set.mem_insert_iff.mp hx').elim hxa hx.2⟩
    · refine ⟨f₀, f₁, fun x hx => hne x (Set.mem_insert_of_mem a hx), fun B hB => ?_⟩
      have haB : a ∉ B := fun ha' => ha (Finset.mem_coe.mp (hB ha'))
      obtain ⟨c, hc, h₀, h₁⟩ := h B (hB.trans (Set.subset_insert a _))
      exact ⟨c, mem_versionSpace_singleton.mpr ⟨hc, h₁ a ⟨ha_mem, haB⟩⟩, h₀,
        fun x hx => h₁ x ⟨Set.mem_insert_of_mem a hx.1, hx.2⟩⟩

theorem natCast_le_littlestoneDim_of_natarajanShatters {C : ConceptClass α β} (W : Finset α)
    (hW : NatarajanShatters C (W : Set α)) : (W.card : ℕ∞) ≤ littlestoneDim C :=
  le_littlestoneDim_of_hasMistakeTree (hasMistakeTree_of_natarajanShatters W hW)

/-- The Natarajan dimension is at most the Littlestone dimension
[DanielySabatoBenDavidShalevShwartz2015]. -/
theorem natarajanDim_le_littlestoneDim (C : ConceptClass α β) :
    natarajanDim C ≤ littlestoneDim C :=
  PACLearning.natarajanDim_le_iff.mpr (natCast_le_littlestoneDim_of_natarajanShatters (C := C))

/-- The Natarajan dimension is at most the optimal mistake bound. -/
theorem natarajanDim_le_optimalMistakeBound [DecidableEq β] (C : ConceptClass α β) :
    natarajanDim C ≤ optimalMistakeBound C :=
  (natarajanDim_le_littlestoneDim C).trans (littlestoneDim_le_optimalMistakeBound C)

/-- A class of infinite Natarajan dimension has infinite Littlestone dimension. -/
theorem littlestoneDim_eq_top_of_not_hasFiniteNatarajanDim {C : ConceptClass α β}
    (h : ¬ HasFiniteNatarajanDim C) : littlestoneDim C = ⊤ := by
  rw [PACLearning.HasFiniteNatarajanDim, not_not] at h
  exact top_le_iff.mp (h ▸ natarajanDim_le_littlestoneDim C)

/-- A finite set `W` shattered by a Boolean class `C` gives a complete mistake tree of height `|W|`
[Littlestone1988, §3, proof of Theorem 4]. -/
theorem hasMistakeTree_of_setShatters {C : ConceptClass α Bool} (W : Finset α)
    (hW : SetShatters C (W : Set α)) : HasMistakeTree W.card C :=
  hasMistakeTree_of_natarajanShatters W (PACLearning.natarajanShatters_iff_setShatters.mpr hW)

theorem natCast_le_littlestoneDim_of_setShatters {C : ConceptClass α Bool} (W : Finset α)
    (hW : SetShatters C (W : Set α)) : (W.card : ℕ∞) ≤ littlestoneDim C :=
  le_littlestoneDim_of_hasMistakeTree (hasMistakeTree_of_setShatters W hW)

/-- The extended VC dimension is at most the Littlestone dimension. -/
theorem evcDim_le_littlestoneDim (C : ConceptClass α Bool) :
    evcDim C ≤ littlestoneDim C :=
  PACLearning.natarajanDim_eq_evcDim C ▸ natarajanDim_le_littlestoneDim C

/-- The natural-valued VC dimension is at most the Littlestone dimension (when `C` has infinite VC
dimension, `vcDim C = 0` by `sSup` convention while `littlestoneDim C = ⊤`). -/
theorem vcDim_le_littlestoneDim (C : ConceptClass α Bool) :
    (vcDim C : ℕ∞) ≤ littlestoneDim C := by
  by_cases hC : HasFiniteVCDim C
  · exact PACLearning.natCast_vcDim hC ▸ evcDim_le_littlestoneDim C
  · exact (PACLearning.evcDim_eq_top_iff.mpr hC ▸ evcDim_le_littlestoneDim C).trans' le_top

/-- The VC dimension is at most the optimal mistake bound. [Littlestone1988, §3, Theorem 4]
treats finite Boolean classes and assigns both quantities the value −1 on the empty class.
The extended-natural bounds here both give zero on the empty class and allow infinite classes. -/
theorem evcDim_le_optimalMistakeBound (C : ConceptClass α Bool) :
    evcDim C ≤ optimalMistakeBound C :=
  (evcDim_le_littlestoneDim C).trans (littlestoneDim_le_optimalMistakeBound C)

/-- A class of infinite VC dimension has infinite Littlestone dimension. -/
theorem littlestoneDim_eq_top_of_not_hasFiniteVCDim {C : ConceptClass α Bool}
    (h : ¬ HasFiniteVCDim C) : littlestoneDim C = ⊤ :=
  top_le_iff.mp (PACLearning.evcDim_eq_top_iff.mpr h ▸ evcDim_le_littlestoneDim C)

/-! ### Finite-domain bounds -/

/-- If all concepts in `C` agree outside a finite set `S`, every complete mistake tree for `C` has
height at most `|S|`: each queried root must lie in `S` and is fixed on its subtrees. -/
theorem le_card_of_hasMistakeTree_of_agree_outside {d : ℕ} {C : ConceptClass α β} (S : Finset α)
    (hd : HasMistakeTree d C)
    (hagree : ∀ z ∉ S, ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ z = c₂ z) : d ≤ S.card := by
  classical
  induction d generalizing C S with
  | zero => exact Nat.zero_le _
  | succ d ih =>
    obtain ⟨x, y₀, y₁, hne, h0, h1⟩ := hd
    obtain ⟨c₀, hc₀⟩ := h0.nonempty
    obtain ⟨c₁, hc₁⟩ := h1.nonempty
    rw [mem_versionSpace_singleton] at hc₀ hc₁
    have hxS : x ∈ S := by
      by_contra hxS
      exact hne (hc₀.2.symm.trans ((hagree x hxS c₀ hc₀.1 c₁ hc₁.1).trans hc₁.2))
    have hd_le : d ≤ (S.erase x).card := ih (S.erase x) h0 fun z hz d₁ hd₁ d₂ hd₂ => by
      rw [mem_versionSpace_singleton] at hd₁ hd₂
      by_cases hzx : z = x
      · subst hzx; exact hd₁.2.trans hd₂.2.symm
      · exact hagree z (fun hzS => hz (Finset.mem_erase.mpr ⟨hzx, hzS⟩)) d₁ hd₁.1 d₂ hd₂.1
    have hcard := Finset.card_erase_add_one hxS
    omega

/-- On a finite domain `α`, every concept class has Littlestone dimension at most `|α|`, regardless
of the label alphabet `β`. -/
theorem littlestoneDim_le_card [Fintype α] (C : ConceptClass α β) :
    littlestoneDim C ≤ Fintype.card α :=
  littlestoneDim_le_iff.mpr fun _ hd => by
    exact_mod_cast le_card_of_hasMistakeTree_of_agree_outside Finset.univ hd
      fun _ hz => absurd (Finset.mem_univ _) hz

/-- The class of all functions from a finite domain `α` to a nontrivial label alphabet `β` has
Littlestone dimension `|α|`. -/
theorem littlestoneDim_univ_of_nontrivial [Fintype α] [Nontrivial β] :
    littlestoneDim (Set.univ : ConceptClass α β) = Fintype.card α := by
  classical
  apply le_antisymm (littlestoneDim_le_card _)
  obtain ⟨y₀, y₁, hne⟩ := exists_pair_ne β
  simpa using natCast_le_littlestoneDim_of_natarajanShatters Finset.univ
    ⟨fun _ => y₀, fun _ => y₁, fun _ _ => hne, fun B _ =>
      ⟨fun x => if x ∈ B then y₀ else y₁, Set.mem_univ _,
        fun _ hx => ite_eq_left hx, fun _ hx => ite_eq_right hx.2⟩⟩

/-- The class of all Boolean functions on a finite domain `α` has Littlestone dimension `|α|`. -/
theorem littlestoneDim_univ [Fintype α] :
    littlestoneDim (Set.univ : ConceptClass α Bool) = Fintype.card α :=
  littlestoneDim_univ_of_nontrivial

end Cslib.MachineLearning.OnlineLearning.MistakeBound
