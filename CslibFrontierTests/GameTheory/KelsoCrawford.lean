/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.GameTheory.Mechanism.CombinatorialAuction.GrossSubstitutes
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Gross substitutes and the Kelso–Crawford ascending auction: client checks and counterexamples

Nonvacuous client tests for
`CslibFrontier.GameTheory.Mechanism.CombinatorialAuction.GrossSubstitutes`:

* **Printed `n ε` welfare erratum in Theorem 11.30 (p. 291):** a 1-bidder (`N = Unit`), 2-item
  (`M = Bool`) additive gross-substitutes market at `ε = 1` where `kelsoCrawford v 1` halts at
  `kelsoCrawfordInit Unit Bool` with welfare `0`, optimal welfare is `3 / 2`, the printed bound
  `welfare v b - |N| * ε ≤ welfare v a` fails (`3 / 2 - 1 = 1 / 2 > 0`), the proved item-count bound
  `IsEpsWalrasianEquilibrium.welfare_le` holds (`3 / 2 - 2 = -1 / 2 ≤ 0`), and the single-item
  refinement `IsEpsWalrasianEquilibrium.welfare_le_of_card_le_one` holds (`3 / 4 - 1 = -1 / 4 ≤ 0`);
* **Heterogeneous 3-bidder, 3-item substitutes market:** unit-demand, downward-sloping symmetric,
  and additive bidders on `Fin 3`, checking `exists_isWalrasianEquilibrium_of_isGrossSubstitutes`,
  `exists_isIntegral_isLPROptimal_of_isGrossSubstitutes`, `kelsoCrawford_isEpsWalrasianEquilibrium`,
  strict Gul–Stacchetti submodularity (`IsGrossSubstitutes.submodular`), and an explicit Walrasian
  equilibrium;
* **Complementarity failure on Example 11.14 (`noEquilibriumVal`):** two independent proofs of
  `¬ IsGrossSubstitutes (noEquilibriumVal true)` — first via Exercise 11.6 submodularity, and second
  via `exists_isWalrasianEquilibrium_of_isGrossSubstitutes` paired with
  `not_exists_isWalrasianEquilibrium_noEquilibriumVal`;
* **Example 11.32 demand reduction & non-normalized (`v i ∅ < 0`) gross substitutes:** client
  instantiation of `demandReduction_manipulation` and exact equilibrium existence without
  `0 ≤ v i ∅`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.KelsoCrawford

open Finset Cslib.GameTheory.CombinatorialAuction

/-! ### 1. Counterexample to printed `n ε` (`|N| * ε`) in NRTV Theorem 11.30 (p. 291) -/

/-- One bidder (`Unit`), two items (`Bool`), additive value `3 / 4` per item. -/
private noncomputable def erratumVal (_ : Unit) : Finset Bool → ℝ :=
  additiveValuation (fun _ => 3 / 4)

private theorem erratumVal_isGrossSubstitutes (i : Unit) : IsGrossSubstitutes (erratumVal i) :=
  isGrossSubstitutes_additiveValuation _

private theorem erratumVal_init_demand (i : Unit) :
    IsDemand (erratumVal i) (fun _ => (1 : ℝ)) ∅ := by
  intro S
  simp only [erratumVal, Cslib.Algorithms.Lean.Submodular.modularSum, sum_const, card_empty,
    nsmul_eq_mul]
  have hnn : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  norm_num
  linarith

/-- `kelsoCrawford erratumVal 1` halts at round `0` (`kelsoCrawfordInit Unit Bool`) with welfare
`0`, refuting the printed `|N| * ε` bound (`3 / 2 - 1 > 0`) while confirming `|M| * ε` and the
single-item `|N| * ε` bound. -/
example :
    kelsoCrawford erratumVal 1 = kelsoCrawfordInit Unit Bool ∧
    IsEpsWalrasianEquilibrium erratumVal 1 (kelsoCrawford erratumVal 1).price
      (kelsoCrawford erratumVal 1).alloc ∧
    (∃ b : Allocation Unit Bool,
      welfare erratumVal (kelsoCrawford erratumVal 1).alloc <
        welfare erratumVal b - (Fintype.card Unit : ℝ) * 1 ∧
      welfare erratumVal b - (Fintype.card Bool : ℝ) * 1 ≤
        welfare erratumVal (kelsoCrawford erratumVal 1).alloc) ∧
    (∀ b₁ : Allocation Unit Bool, (∀ i, (b₁.bundle i).card ≤ 1) →
      welfare erratumVal b₁ - (Fintype.card Unit : ℝ) * 1 ≤
        welfare erratumVal (kelsoCrawford erratumVal 1).alloc) := by
  have hkc : kelsoCrawford erratumVal 1 = kelsoCrawfordInit Unit Bool :=
    kelsoCrawford_eq_init erratumVal_init_demand
  have heps := (kelsoCrawford_isEpsWalrasianEquilibrium erratumVal_isGrossSubstitutes
    (by norm_num : (0 : ℝ) < 1)).1
  let bFull : Allocation Unit Bool :=
    ⟨fun _ => univ, fun i₁ i₂ hne => (hne (Subsingleton.elim i₁ i₂)).elim⟩
  have hw0 : welfare erratumVal (kelsoCrawford erratumVal 1).alloc = 0 := by
    simp [hkc, welfare, erratumVal]
  have hwFull : welfare erratumVal bFull = 3 / 2 := by
    simp [welfare, bFull, erratumVal, Cslib.Algorithms.Lean.Submodular.modularSum]
    norm_num
  refine ⟨hkc, heps, ⟨bFull, ?_, heps.welfare_le (by norm_num) bFull⟩,
    fun b₁ hb₁ => heps.welfare_le_of_card_le_one (by norm_num) hb₁⟩
  rw [hw0, hwFull, Fintype.card_unit]
  norm_num

/-! ### 2. Heterogeneous 3-bidder, 3-item substitutes market -/

private def slopeWeights (k : ℕ) : ℝ :=
  if k = 0 then 5 else if k = 1 then 3 else 0

private theorem slopeWeights_antitone : Antitone slopeWeights := by
  intro a b hab
  unfold slopeWeights
  split_ifs <;> first | omega | norm_num

/-- Three-bidder market over `Fin 3`:
* bidder `0`: unit-demand `![6, 5, 1]`;
* bidder `1`: downward-sloping symmetric `(5, 3, 0, …)`;
* bidder `2`: additive `![1, 2, 4]`. -/
private def hetVal (i : Fin 3) : Finset (Fin 3) → ℝ :=
  match i with
  | 0 => unitDemandValuation ![6, 5, 1]
  | 1 => downwardSlopingValuation slopeWeights
  | 2 => additiveValuation ![1, 2, 4]

private theorem hetVal_isGrossSubstitutes (i : Fin 3) : IsGrossSubstitutes (hetVal i) := by
  fin_cases i
  · exact isGrossSubstitutes_unitDemandValuation fun j => by fin_cases j <;> norm_num
  · exact isGrossSubstitutes_downwardSlopingValuation slopeWeights_antitone
  · exact isGrossSubstitutes_additiveValuation _

private theorem hetVal_empty_nonneg (i : Fin 3) : 0 ≤ hetVal i ∅ := by
  fin_cases i <;> simp [hetVal]

/-- Nonvacuous instantiation of exact Walrasian equilibrium existence, zero `LPR` integrality gap,
finite-step `1 / 10`-equilibrium via `kelsoCrawford`, and strict submodularity on `{0, 1}` vs
`{1, 2}` (`8 + 5 = 13 < 16 = 8 + 8`). -/
example :
    (∃ (p : Fin 3 → ℝ) (a : Allocation (Fin 3) (Fin 3)), IsWalrasianEquilibrium hetVal p a) ∧
    (∃ x : Fin 3 → Finset (Fin 3) → ℝ, IsLPROptimal hetVal x ∧ IsIntegral x) ∧
    IsEpsWalrasianEquilibrium hetVal (1 / 10) (kelsoCrawford hetVal (1 / 10)).price
      (kelsoCrawford hetVal (1 / 10)).alloc ∧
    Cslib.Algorithms.Lean.Submodular.IsSubmodular (hetVal 1) ∧
    hetVal 1 (({0, 1} : Finset (Fin 3)) ∪ {1, 2}) +
      hetVal 1 (({0, 1} : Finset (Fin 3)) ∩ {1, 2}) <
        hetVal 1 {0, 1} + hetVal 1 {1, 2} := by
  refine ⟨exists_isWalrasianEquilibrium_of_isGrossSubstitutes hetVal_isGrossSubstitutes,
    exists_isIntegral_isLPROptimal_of_isGrossSubstitutes hetVal_empty_nonneg
      hetVal_isGrossSubstitutes,
    (kelsoCrawford_isEpsWalrasianEquilibrium hetVal_isGrossSubstitutes (by norm_num)).1,
    (hetVal_isGrossSubstitutes 1).submodular, ?_⟩
  have hu : (({0, 1} : Finset (Fin 3)) ∪ {1, 2}).card = 3 := by decide
  have hi : (({0, 1} : Finset (Fin 3)) ∩ {1, 2}).card = 1 := by decide
  have h01 : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
  have h12 : ({1, 2} : Finset (Fin 3)).card = 2 := by decide
  simp only [hetVal, downwardSlopingValuation, hu, hi, h01, h12]
  norm_num [Finset.sum_range_succ, slopeWeights]

/-! ### 3. Complementarity failure on Example 11.14 (`noEquilibriumVal`) -/

private theorem noEquilibriumVal_false_eq :
    noEquilibriumVal false = unitDemandValuation (fun _ : Bool => 2) := by
  funext S
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp [noEquilibriumVal]
  · obtain ⟨b, -, hb⟩ := exists_mem_unitDemandValuation_eq
      (w := fun _ : Bool => (2 : ℝ)) (fun _ => by norm_num) hS
    simp [noEquilibriumVal, hS, hb]

private theorem noEquilibriumVal_false_isGrossSubstitutes :
    IsGrossSubstitutes (noEquilibriumVal false) := by
  rw [noEquilibriumVal_false_eq]
  exact isGrossSubstitutes_unitDemandValuation fun _ => by norm_num

/-- Proof 1 (combinatorial, via Exercise 11.6): `noEquilibriumVal true` violates submodularity on
`{false}` and `{true}` (`3 + 0 > 0 + 0`), hence is not gross substitutes. -/
example : ¬ IsGrossSubstitutes (noEquilibriumVal true) := by
  intro hgs
  have hsub := hgs.submodular {false} {true}
  have hu : ({false} ∪ {true} : Finset Bool) = univ := by decide
  have hi : ({false} ∩ {true} : Finset Bool) = ∅ := by decide
  have hf : ({false} : Finset Bool) ≠ univ := by decide
  have ht : ({true} : Finset Bool) ≠ univ := by decide
  have he : (∅ : Finset Bool) ≠ univ := by decide
  rw [hu, hi] at hsub
  simp only [noEquilibriumVal, ↓reduceIte, he, hf, ht] at hsub
  norm_num at hsub

/-- Proof 2 (economic, via Kelso–Crawford existence + Example 11.14 non-existence): because Alice's
valuation `noEquilibriumVal false` is gross substitutes, if Bob's complementary valuation
`noEquilibriumVal true` were also gross substitutes then `noEquilibriumVal` would admit a Walrasian
equilibrium, contradicting `not_exists_isWalrasianEquilibrium_noEquilibriumVal`. -/
example : ¬ IsGrossSubstitutes (noEquilibriumVal true) := fun hbob =>
  not_exists_isWalrasianEquilibrium_noEquilibriumVal
    (exists_isWalrasianEquilibrium_of_isGrossSubstitutes fun i => by
      cases i
      · exact noEquilibriumVal_false_isGrossSubstitutes
      · exact hbob)

/-! ### 4. Example 11.32 demand reduction & non-normalized gross-substitutes existence -/

/-- Client check of Example 11.32 (`demandReduction_manipulation`): Bob's payoff is at most `2` in
every truthful Walrasian equilibrium, whereas misreporting a unit-demand substitutes valuation
yields a Walrasian equilibrium giving Bob true payoff `5`. -/
example :
    IsWalrasianEquilibrium demandReductionVal (fun _ => 4)
      ⟨fun i => if i then univ else ∅, by
        intro i₁ i₂ hne
        cases i₁ <;> cases i₂ <;> first | exact (hne rfl).elim | exact by decide⟩ ∧
    ∃ (vMis : Finset Bool → ℝ) (aMis : Allocation Bool Bool),
      IsGrossSubstitutes vMis ∧
      IsWalrasianEquilibrium (fun i => if i then vMis else demandReductionVal false)
        (fun _ => 0) aMis ∧
      demandReductionVal true (aMis.bundle true) - ∑ _j ∈ aMis.bundle true, (0 : ℝ) = 5 :=
  ⟨demandReductionVal_truthful_equilibrium, demandReduction_manipulation.2⟩

/-- Shifting a gross-substitutes valuation by a constant (`v i ∅ = -7 < 0`) preserves
`IsGrossSubstitutes` and still admits an exact Walrasian equilibrium via
`exists_isWalrasianEquilibrium_of_isGrossSubstitutes` (no `0 ≤ v i ∅` hypothesis required). -/
example :
    ∃ (p : Bool → ℝ) (a : Allocation Bool Bool),
      IsWalrasianEquilibrium (fun i S => demandReductionVal i S - 7) p a := by
  refine exists_isWalrasianEquilibrium_of_isGrossSubstitutes fun i p q hpq A hA => ?_
  have hA' : IsDemand (demandReductionVal i) p A := fun S => by linarith [hA S]
  obtain ⟨D, hD, hsub⟩ := demandReductionVal_isGrossSubstitutes i hpq hA'
  exact ⟨D, fun S => by linarith [hD S], hsub⟩

end CslibFrontierTests.GameTheory.KelsoCrawford
