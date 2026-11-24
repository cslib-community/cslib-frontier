/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.GameTheory.Market.EisenbergGale
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Market equilibria: checked instances and boundary counterexamples

This test module imports only the public surface of `CslibFrontier.GameTheory.Market.EisenbergGale`
(and transitively `CslibFrontier.GameTheory.Market.Basic`), verifying that downstream clients can
construct markets, certify equilibria, and apply the headline theorems without `import all`:

1. **Interior-split asymmetric linear Fisher market (`Fin 2 × Fin 2`):** `IsNonDegenerate` holds,
   good `0` is split `3/5` vs. `2/5` across buyers at unique prices `![5, 5]`, satisfying
   `IsEquilibrium`, `IsEisenbergGaleKKT`, `IsParetoOptimal`, `eisenbergGaleDualPrice`, and the
   linear exchange reduction (`toLinearExchangeMarket`).
2. **Non-uniqueness of equilibrium allocations vs. uniqueness of utilities and prices:** a symmetric
   `Fin 2 × Fin 2` Fisher market admits two distinct equilibrium allocations (`x₁ ≠ x₂`), whose
   utilities (`![1, 1]`) and prices (`![2, 2]`) coincide and whose midpoint remains an equilibrium
   allocation (`convex_setOf_exists_isEquilibrium`).
3. **Edgeworth-box linear exchange market and off-equilibrium Walras's law:** competitive
   equilibrium and Pareto optimality at `p = ![1, 1]`, plus non-zero excess demand `![2, -1]` at
   non-clearing prices `p' = ![1, 2]` satisfying `expenditure p' excessDemand = 0`.
4. **Necessity of local nonsatiation:** a 2-trader, 1-good exchange economy with one satiated
   trader violates both Walras's law (`expenditure p excessDemand = -1 ≠ 0`) and the First Welfare
   Theorem (admitting a Pareto-dominated competitive equilibrium).
5. **Necessity of `good_desired` for positive equilibrium prices:** a linear Fisher market with an
   undesired good forces `p 1 = 0` at every equilibrium and admits both full-disposal and
   zero-disposal equilibrium allocations.
-/

public section

namespace CslibFrontierTests.GameTheory.Market

open Cslib.GameTheory.Market

/-! ### 1. Interior-split asymmetric `2 × 2` linear Fisher market -/

/-- Asymmetric unit-supply `2 × 2` linear Fisher market: buyer `0` has budget `3` and utilities
`![4, 1]`; buyer `1` has budget `7` and utilities `![2, 2]`. -/
noncomputable def splitFisher : LinearFisherMarket (Fin 2) (Fin 2) :=
  LinearFisherMarket.unitSupply ![3, 7] ![![4, 1], ![2, 2]]
    (by simp [Fin.forall_fin_two])
    (by simp [Fin.forall_fin_two])

theorem splitFisher_isNonDegenerate : splitFisher.IsNonDegenerate where
  budget_pos := by simp [splitFisher, Fin.forall_fin_two]
  supply_pos := by simp [splitFisher]
  buyer_nonsatiated := by
    simp [splitFisher, Fin.forall_fin_two, Fin.exists_fin_two]
  good_desired := by
    simp [splitFisher, Fin.forall_fin_two, Fin.exists_fin_two]

/-- Unique equilibrium allocation of `splitFisher`, splitting good `0` as `3/5 + 2/5 = 1`. -/
noncomputable def splitAlloc : Fin 2 → Fin 2 → ℝ :=
  ![![3 / 5, 0], ![2 / 5, 1]]

/-- Unique equilibrium price vector `![5, 5]` of `splitFisher`. -/
def splitPrices : Fin 2 → ℝ :=
  ![5, 5]

theorem splitFisher_isEquilibrium : splitFisher.IsEquilibrium splitAlloc splitPrices := by
  rw [LinearFisherMarket.isEquilibrium_iff_bangPerBuck
    splitFisher_isNonDegenerate.buyer_nonsatiated splitFisher_isNonDegenerate.good_desired]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [splitPrices, Fin.forall_fin_two]
  · simp [splitAlloc, Fin.forall_fin_two]
    norm_num
  · simp [splitFisher, splitAlloc, Fin.forall_fin_two, Fin.sum_univ_two]
    norm_num
  · simp [splitFisher, expenditure_eq_sum, splitAlloc, splitPrices,
      Fin.forall_fin_two, Fin.sum_univ_two]
    norm_num
  · simp [splitFisher, LinearFisherMarket.bangPerBuck_eq, splitAlloc, splitPrices,
      Fin.forall_fin_two]
    norm_num

theorem splitFisher_isEisenbergGaleKKT :
    splitFisher.IsEisenbergGaleKKT splitAlloc splitPrices :=
  (LinearFisherMarket.isEquilibrium_iff_isEisenbergGaleKKT splitFisher_isNonDegenerate
    splitAlloc splitPrices).1 splitFisher_isEquilibrium

theorem splitFisher_isParetoOptimal : splitFisher.IsParetoOptimal splitAlloc :=
  splitFisher_isEquilibrium.isParetoOptimal splitFisher_isNonDegenerate.buyer_nonsatiated

theorem splitFisher_toLinearExchange_equilibrium :
    splitFisher.toLinearExchangeMarket.IsCompetitiveEquilibrium splitAlloc splitPrices :=
  ((LinearFisherMarket.isEquilibrium_iff_toLinearExchangeMarket
    splitFisher_isNonDegenerate).1 splitFisher_isEquilibrium).2

theorem splitFisher_isMaxOn_eisenbergGaleObjective :
    splitFisher.IsPositiveUtilityAllocation splitAlloc ∧
      IsMaxOn splitFisher.eisenbergGaleObjective
        {y | splitFisher.IsPositiveUtilityAllocation y} splitAlloc :=
  (LinearFisherMarket.isEquilibrium_iff_isMaxOn_eisenbergGaleObjective
    splitFisher_isNonDegenerate splitAlloc).1 ⟨splitPrices, splitFisher_isEquilibrium⟩

theorem splitFisher_eisenbergGaleDualPrice :
    splitFisher.eisenbergGaleDualPrice splitAlloc = splitPrices := by
  funext g
  have hbu0 : splitFisher.buyerUtility splitAlloc 0 = 12 / 5 := by
    simp only [LinearFisherMarket.buyerUtility_eq, linearUtility_eq_sum, splitFisher,
      LinearFisherMarket.unitSupply_utility, splitAlloc, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    norm_num
  have hbu1 : splitFisher.buyerUtility splitAlloc 1 = 14 / 5 := by
    simp only [LinearFisherMarket.buyerUtility_eq, linearUtility_eq_sum, splitFisher,
      LinearFisherMarket.unitSupply_utility, splitAlloc, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    norm_num
  rw [LinearFisherMarket.eisenbergGaleDualPrice_of_nonempty]
  fin_cases g
  · apply le_antisymm
    · refine Finset.sup'_le _ _ fun i _ => ?_
      fin_cases i
      · change splitFisher.budget 0 * splitFisher.utility 0 0 /
            splitFisher.buyerUtility splitAlloc 0 ≤ splitPrices 0
        rw [hbu0]
        simp [splitFisher, splitPrices]
        norm_num
      · change splitFisher.budget 1 * splitFisher.utility 1 0 /
            splitFisher.buyerUtility splitAlloc 1 ≤ splitPrices 0
        rw [hbu1]
        simp [splitFisher, splitPrices]
        norm_num
    · refine le_trans ?_ (Finset.le_sup' (f := fun i =>
        splitFisher.budget i * splitFisher.utility i 0 / splitFisher.buyerUtility splitAlloc i)
        (Finset.mem_univ 0))
      rw [hbu0]
      simp [splitFisher, splitPrices]
      norm_num
  · apply le_antisymm
    · refine Finset.sup'_le _ _ fun i _ => ?_
      fin_cases i
      · change splitFisher.budget 0 * splitFisher.utility 0 1 /
            splitFisher.buyerUtility splitAlloc 0 ≤ splitPrices 1
        rw [hbu0]
        simp [splitFisher, splitPrices]
        norm_num
      · change splitFisher.budget 1 * splitFisher.utility 1 1 /
            splitFisher.buyerUtility splitAlloc 1 ≤ splitPrices 1
        rw [hbu1]
        simp [splitFisher, splitPrices]
        norm_num
    · refine le_trans ?_ (Finset.le_sup' (f := fun i =>
        splitFisher.budget i * splitFisher.utility i 1 / splitFisher.buyerUtility splitAlloc i)
        (Finset.mem_univ 1))
      rw [hbu1]
      simp [splitFisher, splitPrices]
      norm_num

theorem splitFisher_price_unique (x : Fin 2 → Fin 2 → ℝ) (p : Fin 2 → ℝ)
    (heq : splitFisher.IsEquilibrium x p) : p = splitPrices :=
  LinearFisherMarket.price_eq_of_isEquilibrium splitFisher_isNonDegenerate
    heq splitFisher_isEquilibrium

theorem splitFisher_exists_isEquilibrium :
    ∃ x p, splitFisher.IsEquilibrium x p ∧ p = splitPrices := by
  obtain ⟨x, p, heq⟩ := splitFisher_isNonDegenerate.exists_isEquilibrium
  exact ⟨x, p, heq, splitFisher_price_unique x p heq⟩

/-! ### 2. Distinct equilibrium allocations with unique utilities, unique prices, and convexity -/

/-- Symmetric `2 × 2` unit-supply Fisher market with budgets `![2, 2]` and all utilities `1`. -/
noncomputable def symFisher : LinearFisherMarket (Fin 2) (Fin 2) :=
  LinearFisherMarket.unitSupply ![2, 2] ![![1, 1], ![1, 1]]
    (by simp [Fin.forall_fin_two])
    (by simp [Fin.forall_fin_two])

theorem symFisher_isNonDegenerate : symFisher.IsNonDegenerate where
  budget_pos := by simp [symFisher, Fin.forall_fin_two]
  supply_pos := by simp [symFisher]
  buyer_nonsatiated := by
    simp [symFisher, Fin.forall_fin_two, Fin.exists_fin_two]
  good_desired := by
    simp [symFisher, Fin.forall_fin_two, Fin.exists_fin_two]

def symAlloc₁ : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![0, 1]]
def symAlloc₂ : Fin 2 → Fin 2 → ℝ := ![![0, 1], ![1, 0]]
def symPrices : Fin 2 → ℝ := ![2, 2]

theorem symAlloc₁_ne_symAlloc₂ : symAlloc₁ ≠ symAlloc₂ := by
  intro h
  have h00 : symAlloc₁ 0 0 = symAlloc₂ 0 0 := congrFun (congrFun h 0) 0
  norm_num [symAlloc₁, symAlloc₂] at h00

theorem symFisher_isEquilibrium₁ : symFisher.IsEquilibrium symAlloc₁ symPrices := by
  rw [LinearFisherMarket.isEquilibrium_iff_bangPerBuck
    symFisher_isNonDegenerate.buyer_nonsatiated symFisher_isNonDegenerate.good_desired]
  simp [symFisher, LinearFisherMarket.bangPerBuck_eq, expenditure_eq_sum,
    symAlloc₁, symPrices, Fin.forall_fin_two, Fin.sum_univ_two]

theorem symFisher_isEquilibrium₂ : symFisher.IsEquilibrium symAlloc₂ symPrices := by
  rw [LinearFisherMarket.isEquilibrium_iff_bangPerBuck
    symFisher_isNonDegenerate.buyer_nonsatiated symFisher_isNonDegenerate.good_desired]
  simp [symFisher, LinearFisherMarket.bangPerBuck_eq, expenditure_eq_sum,
    symAlloc₂, symPrices, Fin.forall_fin_two, Fin.sum_univ_two]

/-- Both distinct equilibrium allocations yield identical utilities and their midpoint is an
equilibrium allocation. -/
theorem symFisher_midpoint_equilibrium_and_unique_utilities :
    symFisher.buyerUtility symAlloc₁ = symFisher.buyerUtility symAlloc₂ ∧
      ∃ p : Fin 2 → ℝ,
        symFisher.IsEquilibrium ((1 / 2 : ℝ) • symAlloc₁ + (1 / 2 : ℝ) • symAlloc₂) p := by
  refine ⟨LinearFisherMarket.buyerUtility_eq_of_isEquilibrium symFisher_isNonDegenerate
    symFisher_isEquilibrium₁ symFisher_isEquilibrium₂, ?_⟩
  exact LinearFisherMarket.convex_setOf_exists_isEquilibrium symFisher_isNonDegenerate
    ⟨symPrices, symFisher_isEquilibrium₁⟩ ⟨symPrices, symFisher_isEquilibrium₂⟩
    (by norm_num) (by norm_num) (by norm_num)

/-! ### 3. Edgeworth-box linear exchange economy and off-equilibrium Walras's law -/

/-- `2 × 2` Edgeworth box: trader `0` owns `![2, 0]` with utilities `![1, 3]`; trader `1` owns
`![0, 2]` with utilities `![3, 1]`. -/
def edgeworthBox : LinearExchangeMarket (Fin 2) (Fin 2) where
  endowment := ![![2, 0], ![0, 2]]
  utility := ![![1, 3], ![3, 1]]
  endowment_nonneg := by simp [Fin.forall_fin_two]
  utility_nonneg := by simp [Fin.forall_fin_two]

theorem edgeworthBox_nonsatiated : ∀ i : Fin 2, ∃ g : Fin 2, 0 < edgeworthBox.utility i g := by
  simp [edgeworthBox, Fin.forall_fin_two, Fin.exists_fin_two]

theorem edgeworthBox_equilibrium_and_pareto :
    edgeworthBox.IsCompetitiveEquilibrium ![![0, 2], ![2, 0]] ![1, 1] ∧
      edgeworthBox.IsParetoOptimal ![![0, 2], ![2, 0]] := by
  have heq : edgeworthBox.IsCompetitiveEquilibrium ![![0, 2], ![2, 0]] ![1, 1] := by
    rw [edgeworthBox.isCompetitiveEquilibrium_iff_bangPerBuck
      (by simp [Fin.forall_fin_two]) edgeworthBox_nonsatiated]
    simp [edgeworthBox, ExchangeMarket.totalSupply_eq_sum,
      ExchangeMarket.income_eq, expenditure_eq_sum, Fin.forall_fin_two, Fin.sum_univ_two]
  exact ⟨heq, heq.isParetoOptimal edgeworthBox_nonsatiated⟩

/-- At non-equilibrium prices `p' = ![1, 2]`, optimal demands `![![0, 1], ![4, 0]]` produce nonzero
excess demand `![2, -1]`, yet Walras's law `expenditure p' excessDemand = 0` holds. -/
theorem edgeworthBox_offEquilibrium_walras :
    let p' : Fin 2 → ℝ := ![1, 2]
    let x' : Fin 2 → Fin 2 → ℝ := ![![0, 1], ![4, 0]]
    (∀ i, x' i ∈ edgeworthBox.toExchangeMarket.demandSet p' i) ∧
      edgeworthBox.toExchangeMarket.excessDemand x' 0 = 2 ∧
      edgeworthBox.toExchangeMarket.excessDemand x' 1 = -1 ∧
      expenditure p' (edgeworthBox.toExchangeMarket.excessDemand x') = 0 := by
  dsimp only
  have hdem : ∀ i : Fin 2,
      (![![0, 1], ![4, 0]] : Fin 2 → Fin 2 → ℝ) i ∈
        edgeworthBox.toExchangeMarket.demandSet ![1, 2] i := by
    intro i
    have hp' : ∀ g : Fin 2, 0 < (![1, 2] : Fin 2 → ℝ) g := by simp [Fin.forall_fin_two]
    have hp'_nn : ∀ g : Fin 2, 0 ≤ (![1, 2] : Fin 2 → ℝ) g := fun g => (hp' g).le
    rw [ExchangeMarket.mem_demandSet, LinearExchangeMarket.toExchangeMarket_utility]
    refine (mem_demandSet_linearUtility_iff (edgeworthBox.utility_nonneg i)
      (edgeworthBox.toExchangeMarket.income_nonneg hp'_nn i) hp' (edgeworthBox_nonsatiated i)).2 ?_
    fin_cases i <;>
      · simp [edgeworthBox, ExchangeMarket.income_eq,
          expenditure_eq_sum, Fin.forall_fin_two, Fin.sum_univ_two]
        norm_num
  refine ⟨hdem, ?_, ?_, edgeworthBox.walras_law edgeworthBox_nonsatiated hdem⟩
  · simp [edgeworthBox, ExchangeMarket.excessDemand_eq,
      ExchangeMarket.totalSupply_eq_sum, Fin.sum_univ_two]
    norm_num
  · simp [edgeworthBox, ExchangeMarket.excessDemand_eq,
      ExchangeMarket.totalSupply_eq_sum, Fin.sum_univ_two]
    norm_num

/-! ### 4. Counterexample without local nonsatiation: Walras's law and Welfare fail -/

/-- Two-trader, one-good exchange economy where trader `0` is completely satiated (`u₀ = 0`, owning
`1` unit) and trader `1` is strictly increasing (`u₁(b) = b ()`, owning `0` units). -/
def satiatedMarket : ExchangeMarket (Fin 2) Unit where
  endowment := fun i _ => if i = 0 then 1 else 0
  utility := fun i b => if i = 0 then 0 else b ()
  endowment_nonneg := by simp [Fin.forall_fin_two]

theorem satiatedMarket_not_locallyNonsatiated :
    ¬ IsLocallyNonsatiated (satiatedMarket.utility 0) := by
  rintro hlns
  obtain ⟨b', -, -, hlt⟩ := hlns 0 (fun _ => le_rfl) 1 one_pos
  simp [satiatedMarket] at hlt

/-- Without local nonsatiation, optimal demand choices (`x = 0`) at price `p () = 1` violate
Walras's law (`expenditure p excessDemand = -1 ≠ 0`). -/
theorem satiatedMarket_walras_counterexample :
    (∀ i : Fin 2, (0 : Unit → ℝ) ∈ satiatedMarket.demandSet (fun _ => 1) i) ∧
      expenditure (fun _ : Unit => (1 : ℝ)) (satiatedMarket.excessDemand (fun _ _ => 0)) = -1 := by
  refine ⟨?_, ?_⟩
  · intro i
    rw [ExchangeMarket.mem_demandSet, mem_demandSet]
    fin_cases i
    · refine ⟨⟨fun _ => le_rfl, ?_⟩, fun _ _ => le_rfl⟩
      simp [satiatedMarket, ExchangeMarket.income_eq, expenditure_eq_sum]
    · refine ⟨⟨fun _ => le_rfl, ?_⟩, fun b' hb' => ?_⟩
      · simp [satiatedMarket, ExchangeMarket.income_eq, expenditure_eq_sum]
      · have hle : b' () ≤ 0 := by
          simpa [satiatedMarket, ExchangeMarket.income_eq, expenditure_eq_sum] using hb'.2
        simpa [satiatedMarket] using hle
  · simp [satiatedMarket, ExchangeMarket.excessDemand_eq, ExchangeMarket.totalSupply_eq_sum,
      expenditure_eq_sum]

/-- Without local nonsatiation, the no-trade allocation `x = satiatedMarket.endowment` is a
competitive equilibrium at price `1`, yet fails Pareto optimality (`¬ IsParetoOptimal`). -/
theorem satiatedMarket_firstWelfare_counterexample :
    satiatedMarket.IsCompetitiveEquilibrium satiatedMarket.endowment (fun _ => 1) ∧
      ¬ satiatedMarket.IsParetoOptimal satiatedMarket.endowment := by
  refine ⟨⟨fun _ => zero_le_one, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    rw [ExchangeMarket.mem_demandSet, mem_demandSet]
    fin_cases i
    · refine ⟨⟨by simp [satiatedMarket], by simp [ExchangeMarket.income_eq]⟩,
        fun _ _ => le_rfl⟩
    · refine ⟨⟨by simp [satiatedMarket], by simp [ExchangeMarket.income_eq]⟩, fun b' hb' => ?_⟩
      have hle : b' () ≤ 0 := by
        simpa [satiatedMarket, ExchangeMarket.income_eq, expenditure_eq_sum] using hb'.2
      simpa [satiatedMarket] using hle
  · intro _
    simp [ExchangeMarket.excessDemand_eq, ExchangeMarket.totalSupply_eq_sum]
  · intro _
    simp [ExchangeMarket.excessDemand_eq, ExchangeMarket.totalSupply_eq_sum]
  · rintro ⟨-, hno_dom⟩
    refine hno_dom ⟨fun i _ => if i = 0 then 0 else 1, ?_, ?_, ⟨1, ?_⟩⟩
    · refine ⟨by simp [Fin.forall_fin_two], fun _ => ?_⟩
      simp [satiatedMarket, ExchangeMarket.totalSupply_eq_sum, Fin.sum_univ_two]
    · simp [satiatedMarket, Fin.forall_fin_two]
    · simp [satiatedMarket]

/-! ### 5. Counterexample when `good_desired` is dropped: zero equilibrium price -/

/-- One-buyer, two-good linear Fisher market where good `1` has marginal utility `0` for all buyers:
every equilibrium must price good `1` at `0`, violating strict price positivity. -/
noncomputable def undesiredGoodMarket : LinearFisherMarket Unit (Fin 2) :=
  LinearFisherMarket.unitSupply (fun _ => 2) (fun _ => ![1, 0])
    (fun _ => by norm_num)
    (by simp [Fin.forall_fin_two])

theorem undesiredGoodMarket_equilibrium_zero_price :
    undesiredGoodMarket.IsEquilibrium (fun _ => ![1, 0]) ![2, 0] ∧
      undesiredGoodMarket.IsEquilibrium (fun _ => ![1, 1]) ![2, 0] ∧
      ∀ (x : Unit → Fin 2 → ℝ) (p : Fin 2 → ℝ),
        undesiredGoodMarket.IsEquilibrium x p → p 1 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨by simp [Fin.forall_fin_two], fun _ => ?_,
      by simp [undesiredGoodMarket, Fin.forall_fin_two],
      by simp [undesiredGoodMarket, Fin.forall_fin_two]⟩
    rw [FisherMarket.mem_demandSet, mem_demandSet]
    refine ⟨⟨by simp [Fin.forall_fin_two], ?_⟩, ?_⟩
    · simp [undesiredGoodMarket, expenditure_eq_sum, Fin.sum_univ_two]
    · intro b' hb'
      have hb'0 : 2 * b' 0 ≤ 2 := by
        simpa [undesiredGoodMarket, expenditure_eq_sum, Fin.sum_univ_two] using hb'.2
      simp only [undesiredGoodMarket, LinearFisherMarket.toFisherMarket_utility,
        LinearFisherMarket.unitSupply_utility, linearUtility_eq_sum, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      linarith
  · refine ⟨by simp [Fin.forall_fin_two], fun _ => ?_,
      by simp [undesiredGoodMarket, Fin.forall_fin_two],
      by simp [undesiredGoodMarket, Fin.forall_fin_two]⟩
    rw [FisherMarket.mem_demandSet, mem_demandSet]
    refine ⟨⟨by simp [Fin.forall_fin_two], ?_⟩, ?_⟩
    · simp [undesiredGoodMarket, expenditure_eq_sum, Fin.sum_univ_two]
    · intro b' hb'
      have hb'0 : 2 * b' 0 ≤ 2 := by
        simpa [undesiredGoodMarket, expenditure_eq_sum, Fin.sum_univ_two] using hb'.2
      simp only [undesiredGoodMarket, LinearFisherMarket.toFisherMarket_utility,
        LinearFisherMarket.unitSupply_utility, linearUtility_eq_sum, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      linarith
  · intro x p heq
    by_contra hp1_ne
    have hdem_x := mem_demandSet.1 (undesiredGoodMarket.toFisherMarket.mem_demandSet.1 (heq.2.1 ()))
    have hp1_pos : 0 < p 1 := lt_of_le_of_ne (heq.1 1) (Ne.symm hp1_ne)
    have hmem_x : x () ∈ demandSet (linearUtility (undesiredGoodMarket.utility ())) p
        (undesiredGoodMarket.budget ()) := by
      simpa only [LinearFisherMarket.toFisherMarket_utility,
        LinearFisherMarket.toFisherMarket_budget] using
        undesiredGoodMarket.toFisherMarket.mem_demandSet.1 (heq.2.1 ())
    have hp0_pos : 0 < p 0 :=
      price_pos_of_mem_demandSet_linearUtility heq.1 hmem_x
        (by simp [undesiredGoodMarket])
    have hx1_eq : x () 1 = 1 := by
      simpa [undesiredGoodMarket] using heq.sum_eq_supply_of_price_pos hp1_pos
    let b' : Fin 2 → ℝ := ![x () 0 + p 1 / p 0, 0]
    have hb'_nn : ∀ g : Fin 2, 0 ≤ b' g := by
      simp only [b', Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, le_refl, and_true]
      exact add_nonneg (hdem_x.1.1 0) (div_nonneg hp1_pos.le hp0_pos.le)
    have hb'_exp : expenditure p b' ≤ 2 := by
      have hexp_x : p 0 * x () 0 + p 1 * 1 ≤ 2 := by
        have h := hdem_x.1.2
        simpa [undesiredGoodMarket, expenditure_eq_sum, Fin.sum_univ_two, hx1_eq] using h
      have hexp_b' : expenditure p b' = p 0 * x () 0 + p 1 := by
        simp only [expenditure_eq_sum, b', Fin.sum_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero, add_zero, mul_add]
        rw [mul_div_cancel₀ _ hp0_pos.ne']
      linarith
    have hopt := hdem_x.2 b' ⟨hb'_nn, by simpa [undesiredGoodMarket] using hb'_exp⟩
    simp only [undesiredGoodMarket, LinearFisherMarket.toFisherMarket_utility,
      LinearFisherMarket.unitSupply_utility, linearUtility_eq_sum, b', Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hopt
    linarith [div_pos hp1_pos hp0_pos]

end CslibFrontierTests.GameTheory.Market
