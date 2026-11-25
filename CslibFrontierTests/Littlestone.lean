/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Init
public import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.SOA
public import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Thresholds
public import CslibFrontier.MachineLearning.PACLearning.Compression.MistakeBound
public import CslibFrontier.MachineLearning.PACLearning.Compression.Thresholds

/-! Checked instances for binary and multiclass mistake trees, Littlestone dimension, the standard
optimal algorithm, plurality halving, Natarajan/VC lower bounds, threshold separations on `ℕ` and
`ℚ`, and multiclass mistake-bound sample compression. -/

public section

namespace CslibFrontierTests.Littlestone

open Cslib.MachineLearning Cslib.MachineLearning.OnlineLearning.MistakeBound
open PACLearning (ConceptClass NatarajanShatters natarajanDim vcDim evcDim IsPACLearnerFor
  IsPACLearnable realizableDistributions SampleCompressionScheme)
open scoped NNReal

/-! ### Explicit binary and multiclass shattered mistake trees -/

/-- A concrete height-`2` multiclass (`Fin 3`) mistake tree on `Fin 3` whose sibling branches use
adaptive instances AND distinct non-uniform label pairs (`0 ≠ 1` at the root, `0 ≠ 2` on the left,
`1 ≠ 2` on the right). -/
def adaptiveThreeTree : MistakeTree (Fin 3) (Fin 3) 2 :=
  .node 0 0 1 (by decide)
    (.node 1 0 2 (by decide) .leaf .leaf)
    (.node 2 1 2 (by decide) .leaf .leaf)

example : adaptiveThreeTree.path ![false, false] = [(0, 0), (1, 0)] := by decide
example : adaptiveThreeTree.path ![false, true] = [(0, 0), (1, 2)] := by decide
example : adaptiveThreeTree.path ![true, false] = [(0, 1), (2, 1)] := by decide
example : adaptiveThreeTree.path ![true, true] = [(0, 1), (2, 2)] := by decide

/-- Four 3-class concepts realizing the four root-to-leaf paths of `adaptiveThreeTree`. -/
def fourBranchClass : Finset (Fin 3 → Fin 3) :=
  {![0, 0, 0], ![0, 2, 0], ![1, 0, 1], ![1, 0, 2]}

example : fourBranchClass.card = 4 := by decide

theorem adaptiveThreeTree_shatters :
    adaptiveThreeTree.Shatters (fourBranchClass : ConceptClass (Fin 3) (Fin 3)) := by
  intro bs
  rw [realizable_iff]
  cases h0 : bs 0 <;> cases h1 : bs 1
  · refine ⟨![0, 0, 0], by decide, ?_⟩
    have hp : adaptiveThreeTree.path bs = [(0, 0), (1, 0)] := by
      simp [adaptiveThreeTree, h0, h1]
    rw [hp]; decide
  · refine ⟨![0, 2, 0], by decide, ?_⟩
    have hp : adaptiveThreeTree.path bs = [(0, 0), (1, 2)] := by
      simp [adaptiveThreeTree, h0, h1]
    rw [hp]; decide
  · refine ⟨![1, 0, 1], by decide, ?_⟩
    have hp : adaptiveThreeTree.path bs = [(0, 1), (2, 1)] := by
      simp [adaptiveThreeTree, h0, h1]
    rw [hp]; decide
  · refine ⟨![1, 0, 2], by decide, ?_⟩
    have hp : adaptiveThreeTree.path bs = [(0, 1), (2, 2)] := by
      simp [adaptiveThreeTree, h0, h1]
    rw [hp]; decide

/-- `fourBranchClass` has exact Littlestone dimension `2` and optimal mistake bound `2`:
`adaptiveThreeTree` witnesses `≥ 2`, while `⌊log₂ 4⌋ = 2` upper-bounds it. -/
example : littlestoneDim (fourBranchClass : ConceptClass (Fin 3) (Fin 3)) = 2 ∧
    optimalMistakeBound (fourBranchClass : ConceptClass (Fin 3) (Fin 3)) = 2 := by
  have hge : (2 : ℕ∞) ≤ littlestoneDim (fourBranchClass : ConceptClass (Fin 3) (Fin 3)) :=
    le_littlestoneDim_of_hasMistakeTree
      (hasMistakeTree_iff_exists_tree.mpr ⟨adaptiveThreeTree, adaptiveThreeTree_shatters⟩)
  have hle : littlestoneDim (fourBranchClass : ConceptClass (Fin 3) (Fin 3)) ≤ 2 := by
    refine (littlestoneDim_le_log_card fourBranchClass).trans ?_
    have hcard : Nat.log 2 fourBranchClass.card = 2 := by decide
    exact_mod_cast hcard.le
  have heq : littlestoneDim (fourBranchClass : ConceptClass (Fin 3) (Fin 3)) = 2 :=
    le_antisymm hle hge
  exact ⟨heq, (optimalMistakeBound_eq_littlestoneDim _).trans heq⟩

/-- Every deterministic 3-class learner can be forced to err twice on a realizable sequence of
length `2` from `fourBranchClass`. -/
example (A : OnlineLearner (Fin 3) (Fin 3)) :
    ∃ S : List (Fin 3 × Fin 3),
      S.length = 2 ∧ Realizable (fourBranchClass : ConceptClass (Fin 3) (Fin 3)) S ∧
        mistakes A S = 2 :=
  exists_realizable_mistakes_eq A
    (hasMistakeTree_iff_exists_tree.mpr ⟨adaptiveThreeTree, adaptiveThreeTree_shatters⟩)

/-! ### Computable plurality halving on `Fin 3` -/

/-- On `fourBranchClass`, at query `0` labels `0` and `1` tie with two votes each; plurality
halving breaks ties towards `0 : Fin 3`, errs when the target is `![1, 0, 2]`, then ties between
`1` and `2` at query `2` (predicting `1`) and errs a second time, matching `⌊log₂ 4⌋ = 2`. -/
example : halving fourBranchClass [] 0 = 0 ∧
    halving fourBranchClass [(0, 1)] 2 = 1 ∧
    mistakes (halving fourBranchClass) [(0, 1), (2, 2)] = 2 := by
  decide

/-- When the target is `![0, 0, 0]`, plurality halving makes zero mistakes on `[(0, 0), (1, 0)]`. -/
example : mistakes (halving fourBranchClass) [(0, 0), (1, 0)] = 0 := by decide

/-- Plurality halving makes at most `2` mistakes on every realizable sequence of
`fourBranchClass`. -/
example : mistakeBound (halving fourBranchClass)
    (fourBranchClass : ConceptClass (Fin 3) (Fin 3)) ≤ 2 := by
  refine (mistakeBound_halving_le fourBranchClass).trans ?_
  have hcard : Nat.log 2 fourBranchClass.card = 2 := by decide
  exact_mod_cast hcard.le

/-! ### Multiclass SOA strictly beats `⌊log₂ |C|⌋` -/

/-- All functions `Fin 3 → Fin 3`: there are `3 ^ 3 = 27` functions so `⌊log₂ |C|⌋ = 4`, whereas
`natarajanDim = littlestoneDim = optimalMistakeBound = mistakeBound (soa Set.univ) = 3`. -/
example :
    natarajanDim (Set.univ : ConceptClass (Fin 3) (Fin 3)) = 3 ∧
    littlestoneDim (Set.univ : ConceptClass (Fin 3) (Fin 3)) = 3 ∧
    optimalMistakeBound (Set.univ : ConceptClass (Fin 3) (Fin 3)) = 3 ∧
    mistakeBound (soa Set.univ) (Set.univ : ConceptClass (Fin 3) (Fin 3)) = 3 ∧
    Nat.log 2 (Finset.univ : Finset (Fin 3 → Fin 3)).card = 4 := by
  have hl : littlestoneDim (Set.univ : ConceptClass (Fin 3) (Fin 3)) = 3 := by
    simpa using littlestoneDim_univ_of_nontrivial (α := Fin 3) (β := Fin 3)
  have hn : natarajanDim (Set.univ : ConceptClass (Fin 3) (Fin 3)) = 3 := by
    apply le_antisymm
    · exact hl ▸ natarajanDim_le_littlestoneDim _
    · have hsh : NatarajanShatters (Set.univ : ConceptClass (Fin 3) (Fin 3))
          ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)) := by
        refine ⟨fun _ => 0, fun _ => 1, fun _ _ => Fin.zero_ne_one, fun B _ => ?_⟩
        classical
        refine ⟨fun x => if x ∈ B then 0 else 1, Set.mem_univ _, ?_, ?_⟩
        · intro x hx; exact ite_eq_left hx
        · intro x hx; exact ite_eq_right hx.2
      simpa using hsh.card_le_natarajanDim
  refine ⟨hn, hl, (optimalMistakeBound_eq_littlestoneDim _).trans hl,
    (mistakeBound_soa _).trans hl, by decide⟩

/-- `[Nonempty β]` is necessary in `optimalMistakeBound_eq_littlestoneDim`: when `α = Unit` and
`β = Empty`, no `OnlineLearner Unit Empty` exists (`iInf` over an empty type is `⊤`), whereas
`littlestoneDim ∅ = 0`. -/
example : littlestoneDim (∅ : ConceptClass Unit Empty) = 0 ∧
    optimalMistakeBound (∅ : ConceptClass Unit Empty) = ⊤ := by
  refine ⟨littlestoneDim_empty, ?_⟩
  have : IsEmpty (OnlineLearner Unit Empty) := ⟨fun A => (A [] ()).elim⟩
  simp

/-! ### `vcDim ≤ littlestoneDim` and threshold separations on `ℕ` and `ℚ` -/

/-- General inequality `(vcDim C : ℕ∞) ≤ littlestoneDim C` alongside concrete threshold separations
on `ℕ` (`vcDim = 1`, `littlestoneDim = ⊤`) and `ℚ` (`vcDim = 1`, `littlestoneDim = ⊤`). -/
example :
    (∀ (α : Type) (C : ConceptClass α Bool), (vcDim C : ℕ∞) ≤ littlestoneDim C) ∧
    vcDim (thresholdClass ℕ) = 1 ∧ littlestoneDim (thresholdClass ℕ) = ⊤ ∧
    vcDim (thresholdClass ℚ) = 1 ∧ littlestoneDim (thresholdClass ℚ) = ⊤ ∧
    optimalMistakeBound (thresholdClass ℚ) = ⊤ :=
  ⟨fun _ C => vcDim_le_littlestoneDim C,
    vcDim_thresholdClass, littlestoneDim_thresholdClass,
    vcDim_thresholdClass, littlestoneDim_thresholdClass,
    (optimalMistakeBound_eq_littlestoneDim (thresholdClass ℚ)).trans littlestoneDim_thresholdClass⟩

/-- Thresholds on `ℚ` are PAC learnable over their realizable distributions despite having
`optimalMistakeBound (thresholdClass ℚ) = ⊤`. -/
example : IsPACLearnable (thresholdClass ℚ) (realizableDistributions (thresholdClass ℚ)) :=
  PACLearning.isPACLearnable_thresholdClass

/-- Even the thresholds restricted to the open rational interval `(0, 1) ⊆ ℚ` have VC dimension `1`
and infinite Littlestone dimension. -/
def unitIntervalThresholdsQ : ConceptClass ℚ Bool :=
  thresholdConcept '' Set.Ioo (0 : ℚ) 1

example : vcDim unitIntervalThresholdsQ = 1 ∧ littlestoneDim unitIntervalThresholdsQ = ⊤ := by
  refine ⟨?_, ?_⟩
  · refine vcDim_eq_one_of_subset_thresholdClass
      (by rintro _ ⟨θ, _, rfl⟩; exact thresholdConcept_mem_thresholdClass θ) (1 / 2 : ℚ) ?_
    intro W' hW'
    rcases Set.subset_singleton_iff_eq.mp hW' with rfl | rfl
    · refine ⟨thresholdConcept (1 / 4 : ℚ), ⟨1 / 4, by norm_num, rfl⟩, ?_⟩
      ext z; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        thresholdConcept_apply, decide_eq_true_eq, Set.mem_empty_iff_false, iff_false, not_and]
      rintro h rfl; norm_num at h
    · refine ⟨thresholdConcept (3 / 4 : ℚ), ⟨3 / 4, by norm_num, rfl⟩, ?_⟩
      ext z; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        thresholdConcept_apply, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun h => ⟨by subst h; norm_num, h⟩⟩
  · refine ENat.eq_top_iff_forall_ge.mpr fun k =>
      le_littlestoneDim_of_hasMistakeTree
        (hasMistakeTree_thresholdConcept_Ioo k (by norm_num : (0 : ℚ) < 1))

/-! ### Multiclass `natarajanDim = 1` vs `littlestoneDim = ⊤` on `ℚ` -/

/-- A 3-class threshold family on `ℚ` outputting `1 : Fin 3` below `θ` and `0 : Fin 3` at or above
`θ` has `natarajanDim = 1` and `littlestoneDim = ⊤`. -/
def threeClassThresholdsQ : ConceptClass ℚ (Fin 3) :=
  Set.range fun θ : ℚ => fun x : ℚ => if x < θ then (1 : Fin 3) else 0

private theorem hasMistakeTree_threeClassThresholdsQ_Ioo (k : ℕ) {lo hi : ℚ} (h : lo < hi) :
    HasMistakeTree k ((fun θ : ℚ => fun x : ℚ => if x < θ then (1 : Fin 3) else 0) ''
      Set.Ioo lo hi) := by
  induction k generalizing lo hi with
  | zero =>
    obtain ⟨m, hm⟩ := exists_between h
    exact ⟨_, m, hm, rfl⟩
  | succ k ih =>
    obtain ⟨m, hlo, hhi⟩ := exists_between h
    refine ⟨m, 0, 1, by decide, (ih hlo).mono ?_, (ih hhi).mono ?_⟩
    · rintro _ ⟨θ, ⟨h1, h2⟩, rfl⟩
      refine mem_versionSpace_singleton.mpr ⟨⟨θ, ⟨h1, h2.trans hhi⟩, rfl⟩, ?_⟩
      exact ite_eq_right (not_lt.mpr h2.le)
    · rintro _ ⟨θ, ⟨h1, h2⟩, rfl⟩
      refine mem_versionSpace_singleton.mpr ⟨⟨θ, ⟨hlo.trans h1, h2⟩, rfl⟩, ?_⟩
      exact ite_eq_left h1

example : natarajanDim threeClassThresholdsQ = 1 ∧ littlestoneDim threeClassThresholdsQ = ⊤ := by
  refine ⟨?_, ?_⟩
  · apply le_antisymm
    · refine PACLearning.natarajanDim_le_iff.mpr fun W hW => ?_
      by_contra hlt
      have hcard : 1 < W.card := by
        have : (1 : ℕ∞) < (W.card : ℕ∞) := not_le.mp hlt
        exact_mod_cast this
      -- Embed into Boolean `thresholdClass ℚ` via `(· == 1)`
      refine not_setShatters_thresholdClass (α := ℚ) hcard ?_
      refine PACLearning.natarajanShatters_iff_setShatters.mp ?_
      obtain ⟨f₀, f₁, hne, hB⟩ := hW
      -- Every realized value is `0` or `1`, forcing `(f₀ x == 1) ≠ (f₁ x == 1)` on `W`
      have h01 : ∀ x ∈ (W : Set ℚ), f₀ x ∈ ({0, 1} : Set (Fin 3)) ∧
          f₁ x ∈ ({0, 1} : Set (Fin 3)) := by
        intro x hx
        obtain ⟨_, ⟨θ₀, rfl⟩, h₀, -⟩ := hB {x} (Set.singleton_subset_iff.mpr hx)
        obtain ⟨_, ⟨θ₁, rfl⟩, -, h₁⟩ := hB ∅ (Set.empty_subset _)
        have hx₀ := h₀ x rfl
        have hx₁ := h₁ x ⟨hx, Set.notMem_empty x⟩
        constructor
        · rw [← hx₀]; dsimp only; split <;> simp
        · rw [← hx₁]; dsimp only; split <;> simp
      refine ⟨fun x => f₀ x == 1, fun x => f₁ x == 1, fun x hx => ?_, fun B hBW => ?_⟩
      · obtain ⟨hf0, hf1⟩ := h01 x hx
        have hne' := hne x hx
        rcases hf0 with h0 | h0 <;> rcases hf1 with h1 | h1
        · exfalso; exact hne' (h0.trans h1.symm)
        · dsimp only; rw [h0, Set.mem_singleton_iff.mp h1]; decide
        · dsimp only; rw [Set.mem_singleton_iff.mp h0, h1]; decide
        · exfalso
          exact hne' ((Set.mem_singleton_iff.mp h0).trans (Set.mem_singleton_iff.mp h1).symm)
      · obtain ⟨_, ⟨θ, rfl⟩, h₀, h₁⟩ := hB B hBW
        refine ⟨thresholdConcept θ, thresholdConcept_mem_thresholdClass θ,
          fun x hx => ?_, fun x hx => ?_⟩
        · have h := h₀ x hx
          dsimp only at h ⊢
          rw [← h, thresholdConcept_apply]
          split <;> rename_i hlt' <;> simp [hlt']
        · have h := h₁ x hx
          dsimp only at h ⊢
          rw [← h, thresholdConcept_apply]
          split <;> rename_i hlt' <;> simp [hlt']
    · have hsh : NatarajanShatters threeClassThresholdsQ ({(0 : ℚ)} : Finset ℚ) := by
        refine ⟨fun _ => 1, fun _ => 0, fun _ _ => Fin.zero_ne_one.symm, fun B hB => ?_⟩
        rcases Set.subset_singleton_iff_eq.mp (by simpa using hB) with rfl | rfl
        · refine ⟨_, ⟨0, rfl⟩, fun _ hx => hx.elim, fun x hx => ?_⟩
          have hx0 : x = 0 := by simpa using hx.1
          subst hx0; simp
        · refine ⟨_, ⟨1, rfl⟩, fun x hx => ?_, fun x hx => (hx.2 (by simpa using hx.1)).elim⟩
          have hx0 : x = 0 := by simpa using hx
          subst hx0; simp
      simpa using hsh.card_le_natarajanDim
  · refine ENat.eq_top_iff_forall_ge.mpr fun k =>
      le_littlestoneDim_of_hasMistakeTree
        ((hasMistakeTree_threeClassThresholdsQ_Ioo k (by norm_num : (0 : ℚ) < 1)).mono
          (Set.image_subset_range _ _))

/-! ### Multiclass mistake-bound compression (`SampleCompressionScheme.ofLittlestoneDim`) -/

/-- All 3-class functions on `Fin 2` (`littlestoneDim = 2`): `10` examples suffice for `(1/2, 1/2)`
realizable multiclass PAC learning via `SampleCompressionScheme.ofLittlestoneDim`
(`11 ^ 2 · 2 ^ (-8) ≤ 1 / 2`). -/
example :
    let half : Set.Ioo (0 : ℝ≥0) 1 := ⟨1 / 2, by norm_num⟩
    IsPACLearnerFor 10 half half (Set.univ : ConceptClass (Fin 2) (Fin 3))
      (realizableDistributions (Set.univ : ConceptClass (Fin 2) (Fin 3))) :=
  SampleCompressionScheme.isPACLearnerFor_of_littlestoneDim_le (d := 2)
    (by simpa using (littlestoneDim_univ_of_nontrivial (α := Fin 2) (β := Fin 3)).le)
    (by norm_num)

end CslibFrontierTests.Littlestone
