/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.Combinatorics.SetFamily.Bollobas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Regression, tightness, and separation witnesses for `Bollobas.lean`. -/

set_option linter.privateModule false

open Finset

-- 1. Tight symmetric Bollobás witness (`r = 2`, `s = 2` on `Fin 4`): all `2`-subsets and their
-- complements achieve equality `∑ = 1` over `ℚ` and `ℝ`, and `#s = 6 = (2 + 2).choose 2`.
private def twoSubsets : Finset (Finset (Fin 4)) :=
  Finset.powersetCard 2 Finset.univ

private theorem twoSubsets_disjoint (S : Finset (Fin 4)) :
    Disjoint S (Finset.univ \ S) :=
  disjoint_sdiff_self_right

private theorem twoSubsets_cross :
    ∀ S ∈ twoSubsets, ∀ T ∈ twoSubsets, S ≠ T → ¬ Disjoint S (Finset.univ \ T) := by
  intro S hS T hT hST hdisj
  apply hST
  refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
  · by_contra hxT
    exact Finset.disjoint_left.mp hdisj hx (Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxT⟩)
  · rw [(Finset.mem_powersetCard.mp hS).2, (Finset.mem_powersetCard.mp hT).2]

private theorem twoSubsets_card : #twoSubsets = 6 := by
  rw [twoSubsets, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  decide

example :
    ∑ S ∈ twoSubsets, ((#S + #(Finset.univ \ S)).choose #S : ℚ)⁻¹ ≤ 1 :=
  Finset.sum_inv_choose_le_one_of_disjoint (fun S _ => twoSubsets_disjoint S) twoSubsets_cross

example :
    ∑ S ∈ twoSubsets, ((#S + #(Finset.univ \ S)).choose #S : ℝ)⁻¹ ≤ 1 :=
  Finset.sum_inv_choose_le_one_of_disjoint (fun S _ => twoSubsets_disjoint S) twoSubsets_cross

example :
    ∑ S ∈ twoSubsets, ((#S + #(Finset.univ \ S)).choose #S : ℚ)⁻¹ = 1 ∧
    #twoSubsets ≤ (2 + 2).choose 2 ∧
    #twoSubsets = (2 + 2).choose 2 := by
  refine ⟨?_, Finset.card_le_choose_of_disjoint ?_ ?_ (fun S _ => twoSubsets_disjoint S)
      twoSubsets_cross, by rw [twoSubsets_card]; decide⟩
  · have hsum :
        ∑ S ∈ twoSubsets, ((#S + #(Finset.univ \ S)).choose #S : ℚ)⁻¹ =
          ∑ _S ∈ twoSubsets, (6 : ℚ)⁻¹ := by
      refine Finset.sum_congr rfl fun S hS => ?_
      have hcardS : #S = 2 := (Finset.mem_powersetCard.mp hS).2
      have hcardSc : #(Finset.univ \ S) = 2 := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin,
          hcardS]
      rw [hcardS, hcardSc, show Nat.choose 4 2 = 6 by decide]
      norm_num
    rw [hsum, Finset.sum_const, twoSubsets_card]
    norm_num
  · intro S hS
    exact ((Finset.mem_powersetCard.mp hS).2).le
  · intro S hS
    have hcardS : #S = 2 := (Finset.mem_powersetCard.mp hS).2
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin,
      hcardS]

-- 2. Unequal-size symmetric witness on `Fin 3`: `(A₀, B₀) = ({0}, {1})` of sizes `(1, 1)` and
-- `(A₁, B₁) = ({1, 2}, {0})` of sizes `(2, 1)` give LYM sum `1/2 + 1/3 = 5/6 ≤ 1`.
private def unequalA : Fin 2 → Finset (Fin 3)
  | 0 => {0}
  | 1 => {1, 2}

private def unequalB : Fin 2 → Finset (Fin 3)
  | 0 => {1}
  | 1 => {0}

example :
    ∑ i ∈ (Finset.univ : Finset (Fin 2)),
        ((#(unequalA i) + #(unequalB i)).choose #(unequalA i) : ℚ)⁻¹ ≤ 1 ∧
    ∑ i ∈ (Finset.univ : Finset (Fin 2)),
        ((#(unequalA i) + #(unequalB i)).choose #(unequalA i) : ℚ)⁻¹ = 5 / 6 := by
  refine ⟨Finset.sum_inv_choose_le_one_of_disjoint ?_ ?_, ?_⟩
  · intro i _
    fin_cases i <;> decide
  · intro i _ j _ hij
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide
  · rw [Fin.sum_univ_two]
    have hcards : #(unequalA 0) = 1 ∧ #(unequalB 0) = 1 ∧
        #(unequalA 1) = 2 ∧ #(unequalB 1) = 1 := by
      refine ⟨by decide, by decide, by decide, by decide⟩
    rw [hcards.1, hcards.2.1, hcards.2.2.1, hcards.2.2.2]
    norm_num

-- 3. Strict separation between Frankl's skew theorem and the symmetric Bollobás theorem:
-- `A = [{0}, {1}]`, `B = [{2}, {0}]` satisfy `i < j → ¬ Disjoint (A i) (B j)` with equality
-- `2 = (1 + 1).choose 1`, whereas the symmetric condition fails at `1 ≠ 0` (`Disjoint {1} {2}`).
private def skewA : Fin 2 → Finset (Fin 3)
  | 0 => {0}
  | 1 => {1}

private def skewB : Fin 2 → Finset (Fin 3)
  | 0 => {2}
  | 1 => {0}

example :
    Fintype.card (Fin 2) ≤ (1 + 1).choose 1 ∧
    Disjoint (skewA 1) (skewB 0) := by
  refine ⟨Fintype.card_le_choose_of_lt_not_disjoint skewA skewB ?_ ?_ ?_ ?_, by decide⟩
  · intro i; fin_cases i <;> decide
  · intro i; fin_cases i <;> decide
  · intro i; fin_cases i <;> decide
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | decide

-- 4. Separation showing the LYM sum `≤ 1` fails in the skew setting:
-- `({0}, ∅), (∅, {0})` satisfy Frankl's skew condition (`Fintype.card (Fin 2) ≤ (1 + 1).choose 1`),
-- while `∑ ((#(A i) + #(B i)).choose #(A i))⁻¹ = 2 > 1`.
private def skewLymA : Fin 2 → Finset (Fin 1)
  | 0 => {0}
  | 1 => ∅

private def skewLymB : Fin 2 → Finset (Fin 1)
  | 0 => ∅
  | 1 => {0}

example :
    Fintype.card (Fin 2) ≤ (1 + 1).choose 1 ∧
    (1 : ℚ) < ∑ i ∈ (Finset.univ : Finset (Fin 2)),
        ((#(skewLymA i) + #(skewLymB i)).choose #(skewLymA i) : ℚ)⁻¹ := by
  refine ⟨Fintype.card_le_choose_of_lt_not_disjoint skewLymA skewLymB ?_ ?_ ?_ ?_, ?_⟩
  · intro i; fin_cases i <;> decide
  · intro i; fin_cases i <;> decide
  · intro i; fin_cases i <;> decide
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | decide
  · rw [Fin.sum_univ_two]
    have hcards : #(skewLymA 0) = 1 ∧ #(skewLymB 0) = 0 ∧
        #(skewLymA 1) = 0 ∧ #(skewLymB 1) = 1 := by
      refine ⟨by decide, by decide, by decide, by decide⟩
    rw [hcards.1, hcards.2.1, hcards.2.2.1, hcards.2.2.2]
    norm_num

-- 5. Boundary case `r = 0, s = 0` and infinite ground type `ℕ`.
example :
    Fintype.card (Fin 1) ≤ (0 + 0).choose 0 :=
  Fintype.card_le_choose_of_lt_not_disjoint
    (fun _ : Fin 1 => (∅ : Finset ℕ)) (fun _ : Fin 1 => (∅ : Finset ℕ))
    (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => disjoint_empty_left _)
    (fun i j hij => absurd hij (by omega))
