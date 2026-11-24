/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.GameTheory.RandomAssignment.Basic
import CslibFrontier.GameTheory.RandomAssignment.Impossibility
import CslibFrontier.GameTheory.RandomAssignment.ProbabilisticSerial
import CslibFrontier.GameTheory.RandomAssignment.RandomSerialDictatorship
import Mathlib.Tactic.NormNum

/-!
# Random assignment: concrete examples and boundary checks

Checked positive and negative boundary instances for the `sd`-dominance partial order,
Random Serial Dictatorship (`rsd`), Probabilistic Serial (`probabilisticSerial`), and the
Bogomolnaia–Moulin impossibility theorem ([BogomolnaiaMoulin2001]; primary PDF not consulted).
-/

namespace CslibFrontierTests.GameTheory.RandomAssignment

open Cslib.GameTheory.RandomAssignment

private lemma iic0 : Finset.Iic (0 : Fin 3) = {0} := by decide
private lemma iic1 : Finset.Iic (1 : Fin 3) = {0, 1} := by decide
private lemma iic2 : Finset.Iic (2 : Fin 3) = Finset.univ := by decide

private lemma upperContour_refl_0 (x : Fin 3 → ℝ) :
    upperContourSum (Equiv.refl (Fin 3)) x 0 = x 0 := by
  simp only [upperContourSum, iic0, Finset.sum_singleton, Equiv.refl_apply]

private lemma upperContour_refl_1 (x : Fin 3 → ℝ) :
    upperContourSum (Equiv.refl (Fin 3)) x 1 = x 0 + x 1 := by
  simp only [upperContourSum, iic1, Finset.sum_pair (by decide : (0 : Fin 3) ≠ 1), Equiv.refl_apply]

private lemma upperContour_refl_2 (x : Fin 3 → ℝ) :
    upperContourSum (Equiv.refl (Fin 3)) x 2 = x 0 + x 1 + x 2 := by
  simp only [upperContourSum, iic2, Equiv.refl_apply, Fin.sum_univ_three]

/-! ### `sd`-dominance and expected-utility witness -/

/-- Under the identity ranking `0 > 1 > 2`, lottery `(1/2, 1/2, 0)` strictly `sd`-dominates
`(1/3, 1/3, 1/3)`, and achieves strictly higher expected utility against `u = (3, 1, 0)`. -/
example :
    let x : Fin 3 → ℝ := ![1 / 2, 1 / 2, 0]
    let y : Fin 3 → ℝ := ![1 / 3, 1 / 3, 1 / 3]
    SDDominatesStrict (Equiv.refl (Fin 3)) x y ∧
      ∑ o : Fin 3, x o * ![3, 1, 0] o > ∑ o : Fin 3, y o * ![3, 1, 0] o := by
  refine ⟨⟨fun k => ?_, ⟨0, ?_⟩⟩, ?_⟩
  · fin_cases k
    · change upperContourSum (Equiv.refl (Fin 3)) _ 0 ≤ upperContourSum (Equiv.refl (Fin 3)) _ 0
      rw [upperContour_refl_0, upperContour_refl_0]; norm_num
    · change upperContourSum (Equiv.refl (Fin 3)) _ 1 ≤ upperContourSum (Equiv.refl (Fin 3)) _ 1
      rw [upperContour_refl_1, upperContour_refl_1]; norm_num
    · change upperContourSum (Equiv.refl (Fin 3)) _ 2 ≤ upperContourSum (Equiv.refl (Fin 3)) _ 2
      rw [upperContour_refl_2, upperContour_refl_2]; norm_num
  · rw [upperContour_refl_0, upperContour_refl_0]; norm_num
  · simp [Fin.sum_univ_three]; norm_num

/-- Two incomparable lotteries under `0 > 1 > 2`: `(1/2, 0, 1/2)` and `(0, 1, 0)` neither
`sd`-dominates the other (`1/2 > 0` at rank `0`, `1/2 < 1` at rank `1`). -/
example :
    let x : Fin 3 → ℝ := ![1 / 2, 0, 1 / 2]
    let y : Fin 3 → ℝ := ![0, 1, 0]
    ¬ SDDominates (Equiv.refl (Fin 3)) x y ∧ ¬ SDDominates (Equiv.refl (Fin 3)) y x := by
  constructor
  · intro h
    have h1 := h 1
    rw [upperContour_refl_1, upperContour_refl_1] at h1
    norm_num at h1
  · intro h
    have h0 := h 0
    rw [upperContour_refl_0, upperContour_refl_0] at h0
    norm_num at h0

/-- Abel summation characterization: expected-utility dominance under `Equiv.refl (Fin 3)` for a
concrete `antitone` utility vector `u = (5, 2, 0)`. -/
example :
    let u : Fin 3 → ℝ := ![5, 2, 0]
    let x : Fin 3 → ℝ := ![1 / 2, 1 / 2, 0]
    let y : Fin 3 → ℝ := ![0, 1, 0]
    ∑ o : Fin 3, y o * u o ≤ ∑ o : Fin 3, x o * u o := by
  intro u x y
  have hdom : SDDominates (Equiv.refl (Fin 3)) x y := by
    intro k
    fin_cases k
    · change upperContourSum (Equiv.refl (Fin 3)) y 0 ≤ upperContourSum (Equiv.refl (Fin 3)) x 0
      rw [upperContour_refl_0, upperContour_refl_0]; norm_num [x, y]
    · change upperContourSum (Equiv.refl (Fin 3)) y 1 ≤ upperContourSum (Equiv.refl (Fin 3)) x 1
      rw [upperContour_refl_1, upperContour_refl_1]; norm_num [x, y]
    · change upperContourSum (Equiv.refl (Fin 3)) y 2 ≤ upperContourSum (Equiv.refl (Fin 3)) x 2
      rw [upperContour_refl_2, upperContour_refl_2]; norm_num [x, y]
  have hsum : ∑ o : Fin 3, x o = ∑ o : Fin 3, y o := by
    simp [x, y, Fin.sum_univ_three]; norm_num
  have hanti : Antitone (fun r : Fin 3 => u (Equiv.refl (Fin 3) r)) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp [u] at hab ⊢
    norm_num
  exact (sdDominates_iff_forall_antitone (Equiv.refl (Fin 3)) hsum).mp hdom u hanti

/-! ### Edge sizes for Random Serial Dictatorship (`n = 0, 1, 2, 3, 4, 5`) -/

/-- `rsd` is feasible, `sd`-efficient, `ETE`, and `sd`-strategy-proof for `n = 0, 1, 2, 3`. -/
example (p : Profile 0) : IsSDEfficient p (rsd p) := rsd_isSDEfficient_of_le_three (by omega) p
example (p : Profile 1) : IsSDEfficient p (rsd p) := rsd_isSDEfficient_of_le_three (by omega) p
example (p : Profile 2) : IsSDEfficient p (rsd p) := rsd_isSDEfficient_of_le_three (by omega) p
example (p : Profile 3) : IsSDEfficient p (rsd p) := rsd_isSDEfficient_of_le_three (by omega) p

/-- For `n = 1`, `rsd` and `probabilisticSerial` both give the trivial unit matrix `1`. -/
example (p : Profile 1) : rsd p 0 0 = 1 ∧ probabilisticSerial p 0 0 = 1 := by
  have hr := (mem_doublyStochastic_iff_sum.mp (rsd_mem_doublyStochastic p)).2.1 0
  have hp := (mem_doublyStochastic_iff_sum.mp (probabilisticSerial_mem_doublyStochastic p)).2.1 0
  simp only [Fin.sum_univ_one] at hr hp
  exact ⟨hr, hp⟩

/-- At `n = 3`, `rsd` is `sd`-efficient yet fails `sd`-envy-freeness on `profileThree`:
agent `0` gets `(1/2, 1/6, 1/3)` while agent `2` gets `(0, 5/6, 1/6)`. -/
example :
    IsSDEfficient profileThree (rsd profileThree) ∧
      ¬ IsSDEnvyFree profileThree (rsd profileThree) ∧
      rsd profileThree 0 0 + rsd profileThree 0 1 <
        rsd profileThree 2 0 + rsd profileThree 2 1 := by
  obtain ⟨r00, r01, _⟩ := rsd_profileThree_row0
  obtain ⟨r20, r21, _⟩ := rsd_profileThree_row2
  refine ⟨rsd_isSDEfficient_of_le_three (by omega) profileThree, not_isSDEnvyFree_rsd_three, ?_⟩
  linarith

/-- At `n = 4`, `rsd rsdIneffProfileFour` gives `(5/12, 1/12, 5/12, 1/12)` to agents `0, 1` and is
ex-post efficient yet **not** `sd`-efficient (strictly dominated by half-lotteries). -/
example :
    IsExPostEfficient rsdIneffProfileFour (rsd rsdIneffProfileFour) ∧
      ¬ IsSDEfficient rsdIneffProfileFour (rsd rsdIneffProfileFour) ∧
      rsd rsdIneffProfileFour 0 0 = 5 / 12 ∧ rsd rsdIneffProfileFour 0 1 = 1 / 12 := by
  refine ⟨rsd_isExPostEfficient _, not_isSDEfficient_rsd_four, ?_, ?_⟩
  · simpa using rsd_ineffProfileFour_apply 0 0
  · simpa using rsd_ineffProfileFour_apply 0 1

/-- For `n = 5`, the padded profile witnesses failure of `sd`-efficiency for `rsd`. -/
example : ¬ IsSDEfficient (rsdIneffProfile (n := 5) (by omega))
    (rsd (rsdIneffProfile (n := 5) (by omega))) :=
  not_isSDEfficient_rsd_of_four_le (by omega)

/-! ### Non-trivial trade cycle on `rsdIneffProfileFour` -/

/-- The `rsd` allocation on `rsdIneffProfileFour` admits a strict 2-cycle `0 ↔ 1` under agents
`0` (`0 > 1`) and `2` (`1 > 0`). -/
example :
    tradeRel rsdIneffProfileFour (rsd rsdIneffProfileFour) 0 1 ∧
      tradeRel rsdIneffProfileFour (rsd rsdIneffProfileFour) 1 0 := by
  constructor
  · refine ⟨0, ?_, ?_⟩
    · have h : rsd rsdIneffProfileFour 0 1 = 1 / 12 := by
        simpa using rsd_ineffProfileFour_apply 0 1
      rw [h]; norm_num
    · simp [rsdIneffProfileFour]
  · refine ⟨2, ?_, ?_⟩
    · have h : rsd rsdIneffProfileFour 2 0 = 1 / 12 := by
        simpa using rsd_ineffProfileFour_apply 2 0
      rw [h]; norm_num
    · have h1 : (rsdIneffProfileFour 2).symm 1 = 0 := by
        rw [Equiv.symm_apply_eq]
        change (1 : Fin 4) = (Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3) 0
        decide
      have h0 : (rsdIneffProfileFour 2).symm 0 = 1 := by
        rw [Equiv.symm_apply_eq]
        change (0 : Fin 4) = (Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3) 1
        decide
      rw [h1, h0]
      decide

/-! ### Probabilistic Serial concrete checks (`n = 3, 4`) -/

/-- At `n = 3`, `probabilisticSerial` is feasible, `sd`-envy-free, `sd`-efficient, and ex-post
efficient, while strictly failing strong `sd`-strategy-proofness on `psManipProfile`:
agent `2`'s cumulative `{1, 0}` share rises from `3/4` to `5/6`. -/
example :
    let p := psManipProfile (n := 3) (by omega)
    let p' := Function.update p ⟨2, by omega⟩ (Equiv.refl (Fin 3))
    IsSDEfficient p (probabilisticSerial p) ∧
      IsSDEnvyFree p (probabilisticSerial p) ∧
      IsExPostEfficient p (probabilisticSerial p) ∧
      probabilisticSerial p 2 1 + probabilisticSerial p 2 0 = 3 / 4 ∧
      probabilisticSerial p' 2 1 + probabilisticSerial p' 2 0 = 5 / 6 ∧
      ¬ IsSDStrategyProof (probabilisticSerial (n := 3)) := by
  obtain ⟨⟨ht0, ht1, _⟩, ⟨hm0, hm1, _⟩⟩ := probabilisticSerial_manip_values (n := 3) (by omega)
  refine ⟨probabilisticSerial_isSDEfficient _, probabilisticSerial_isSDEnvyFree _,
    probabilisticSerial_isExPostEfficient _, ?_, ?_,
    not_isSDStrategyProof_probabilisticSerial (by omega)⟩
  · change probabilisticSerial _ ⟨2, _⟩ ⟨1, _⟩ + probabilisticSerial _ ⟨2, _⟩ ⟨0, _⟩ = 3 / 4
    linarith
  · change probabilisticSerial _ ⟨2, _⟩ ⟨1, _⟩ + probabilisticSerial _ ⟨2, _⟩ ⟨0, _⟩ = 5 / 6
    linarith

/-- At `n = 4`, `probabilisticSerial` also fails `sd`-strategy-proofness via the padded witness. -/
example : ¬ IsSDStrategyProof (probabilisticSerial (n := 4)) :=
  not_isSDStrategyProof_probabilisticSerial (by omega)

/-! ### Sharp `n ≤ 3` vs `n ≥ 4` impossibility threshold -/

/-- Positive boundary (`n = 3`): a feasible, `sd`-efficient, `ETE`, `sd`-strategy-proof rule
exists. -/
example : ∃ φ : AssignmentRule 3,
    IsFeasible φ ∧
    (∀ p : Profile 3, IsSDEfficient p (φ p)) ∧
    (∀ p : Profile 3, IsEqualTreatmentOfEquals p (φ p)) ∧
    IsSDStrategyProof φ :=
  (exists_sdEfficient_ete_sdStrategyProof_iff 3).mpr (by omega)

/-- Negative boundary (`n = 4`): no rule satisfies feasibility, `sd`-efficiency, `ETE`, and
strong `sd`-strategy-proofness simultaneously. -/
example : ¬ ∃ φ : AssignmentRule 4,
    IsFeasible φ ∧
    (∀ p : Profile 4, IsSDEfficient p (φ p)) ∧
    (∀ p : Profile 4, IsEqualTreatmentOfEquals p (φ p)) ∧
    IsSDStrategyProof φ := by
  rw [exists_sdEfficient_ete_sdStrategyProof_iff 4]
  omega

/-- Negative instance for `n = 5` (including the `sd`-envy-free corollary). -/
example (φ : AssignmentRule 5)
    (hfeas : IsFeasible φ)
    (heff : ∀ p : Profile 5, IsSDEfficient p (φ p))
    (hef : ∀ p : Profile 5, IsSDEnvyFree p (φ p))
    (hsp : IsSDStrategyProof φ) : False :=
  bogomolnaiaMoulin_impossibility_envyFree (by omega) φ hfeas heff hef hsp

end CslibFrontierTests.GameTheory.RandomAssignment
