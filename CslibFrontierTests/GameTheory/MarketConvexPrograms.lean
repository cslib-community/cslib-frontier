/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.GameTheory.Market.ConvexExchange
public import CslibFrontier.GameTheory.Market.HomogeneousFisher
public import CslibFrontier.GameTheory.Market.Leontief
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Convex programming for market equilibria: checked instances and boundary witnesses

This test module imports only the public surface of `HomogeneousFisher`, `ConvexExchange`, and
`Leontief` (no `import all`), exercising every headline theorem of [CodenottiVaradarajan2007],
Sections 6.2, 6.4.1, 6.4.2, 6.5.1, and 6.5.2 on concrete economies and verifying boundary sharpness:

1. **§6.2 Homogeneous Fisher market and Eisenberg's convex program:**
   * verifies Euler's identity (`IsHomogeneousDegOne.sum_partial_mul_eq`) on CES utility
     `cesUtility ![1, 4] (1 / 2)` at `![1, 1]`;
   * exercises a mixed-exponent asymmetric-budget CES Fisher market (`ρ = ![1/2, -1]`,
     `budget = ![1, 3]`, `supply = ![2, 2]`), certifying global Eisenberg optimality via
     `FisherMarket.IsEquilibrium.isMaxOn_eisenbergObjective` and recovering a strictly positive
     exact-clearing equilibrium via `cesFisherMarket_exists_isEquilibrium_of_isMaxOn` and
     `FisherMarket.exists_isEquilibrium_iff_isMaxOn_eisenbergObjective`;
   * exercises the zero-price surplus reassignment boundary theorem
     `FisherMarket.exists_isEquilibrium_exactClearing_of_isMaxOn_eisenbergObjective` on a linear
     Fisher market with an undesired good.
2. **§6.4.1 Linear-exchange convex feasibility program (Nenakov–Primak / Jain):**
   * checks `LinearExchangeMarket.isConvexProgramFeasible_iff_isCompetitiveEquilibrium` and
     `LinearExchangeMarket.convex_setOf_isConvexProgramFeasible` on an asymmetric `2 × 2` linear
     exchange market with non-equal equilibrium prices `![1, 2]` (`ψ = ![0, Real.log 2]`).
3. **§6.4.2 CES demand uniqueness `(6.7)` and Proposition 6.11:**
   * verifies `demandSet_cesUtility_eq` at both `ρ = 1/2` and `ρ = -1`;
   * exercises `convexOn_cesTransformedDemand` (Proposition 6.11), `isWalrasianEquilibrium_sq_iff`,
     and `convex_setOf_transformedEquilibrium` on a mixed-exponent CES exchange market with
     `ρ = ![-1, -1/2]`.
4. **§6.5.1 Multiple disconnected equilibria for `ρ < -1` (Gjerstad):**
   * instantiates `gjerstadMarket` at `ρ = -2` and `a = (2 / 7) ^ (3 / 2)`, certifying
     `gjerstadMarket_isWalrasianEquilibrium_half`, `gjerstadMarket_exists_disconnected_equilibria`,
     the explicit rational off-diagonal equilibrium `![1/9, 8/9]`, and that `![1/3, 2/3]` is not an
     equilibrium.
5. **§6.5.2 Bimatrix-to-Leontief exchange economy correspondence:**
   * exercises `bimatrixLeontiefNashEquivEquilibriumPrice` on an asymmetric `2 × 2` strictly
     positive bimatrix game with interior mixed Nash equilibrium `(![1/4, 3/4], ![1/3, 2/3])`;
   * verifies the boundary zero-price case on a `2 × 2` coordination game with pure Nash equilibrium
     `(![1, 0], ![1, 0])` and normalized equilibrium price `Sum.elim ![1/2, 0] ![1/2, 0]`.
-/

public section

namespace CslibFrontierTests.GameTheory.MarketConvexPrograms

open Cslib.GameTheory
open Cslib.GameTheory.Market
open Finset

/-! ### 1. §6.2 Homogeneous Fisher markets and Eisenberg's convex program -/

/-- Euler's identity check on `cesUtility ![1, 4] (1 / 2)` at `b = ![1, 1]`. -/
theorem euler_ces_instance :
    let α : Fin 2 → ℝ := ![1, 4]
    let b : Fin 2 → ℝ := ![1, 1]
    let L : (Fin 2 → ℝ) →L[ℝ] ℝ :=
      ((∑ k : Fin 2, α k * (b k) ^ (1 / 2 : ℝ)) ^ (1 / (1 / 2 : ℝ) - 1)) •
        ∑ g : Fin 2, (α g * (b g) ^ ((1 / 2 : ℝ) - 1)) • ContinuousLinearMap.proj (R := ℝ) g
    ∑ g : Fin 2, L (Pi.single g 1) * b g = cesUtility α (1 / 2) b := by
  intro α b L
  have hα : ∀ g : Fin 2, 0 < α g := by
    simp only [α, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num
  have hb : ∀ g : Fin 2, 0 < b g := by
    simp only [b, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num
  have hL : HasFDerivWithinAt (cesUtility α (1 / 2)) L {x : Fin 2 → ℝ | ∀ g, 0 ≤ x g} b :=
    (hasFDerivAt_cesUtility hα (by norm_num : (1 / 2 : ℝ) ≠ 0) hb).hasFDerivWithinAt
  exact (isHomogeneousDegOne_cesUtility (fun g => (hα g).le) (by norm_num)).sum_partial_mul_eq
    (fun g => (hb g).le) hL

/-- Mixed-exponent asymmetric-budget CES Fisher market:
buyer `0` has budget `1`, `ρ = 1/2`; buyer `1` has budget `3`, `ρ = -1`; supply `![2, 2]`. -/
noncomputable def mixedCESFisher : FisherMarket (Fin 2) (Fin 2) where
  budget := ![1, 3]
  supply := ![2, 2]
  utility := ![cesUtility ![1, 1] (1 / 2), cesUtility ![1, 1] (-1)]
  budget_nonneg := by
    simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num
  supply_nonneg := by
    simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num

/-- Equilibrium allocation `![![1/2, 1/2], ![3/2, 3/2]]` for `mixedCESFisher`. -/
noncomputable def mixedCESAlloc : Fin 2 → Fin 2 → ℝ := ![![1 / 2, 1 / 2], ![3 / 2, 3 / 2]]

theorem mixedCESFisher_isMaxOn_eisenbergObjective :
    IsMaxOn mixedCESFisher.eisenbergObjective
      {y | mixedCESFisher.IsPositiveUtilityAllocation y} mixedCESAlloc := by
  have heq : mixedCESFisher.IsEquilibrium mixedCESAlloc ![1, 1] := by
    refine ⟨by simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num,
      fun i => ?_, ?_, ?_⟩
    · fin_cases i
      · rw [FisherMarket.mem_demandSet]
        have hmem := cesDemand_mem_demandSet (α := ![1, 1]) (p := ![1, 1]) (ρ := 1 / 2) (m := 1)
          (by simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num)
          (by norm_num) (by norm_num)
          (by simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num)
          (by norm_num)
        have hval : cesDemand ![1, 1] (1 / 2) ![1, 1] 1 = mixedCESAlloc 0 := by
          funext g
          rw [cesDemand_apply]
          fin_cases g <;> simp [mixedCESAlloc, Fin.sum_univ_two] <;> norm_num
        rw [hval] at hmem
        exact hmem
      · rw [FisherMarket.mem_demandSet]
        have hmem := cesDemand_mem_demandSet (α := ![1, 1]) (p := ![1, 1]) (ρ := -1) (m := 3)
          (by simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num)
          (by norm_num) (by norm_num)
          (by simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num)
          (by norm_num)
        have hval : cesDemand ![1, 1] (-1) ![1, 1] 3 = mixedCESAlloc 1 := by
          funext g
          rw [cesDemand_apply]
          fin_cases g <;> simp [mixedCESAlloc, Fin.sum_univ_two] <;> norm_num
        rw [hval] at hmem
        exact hmem
    · intro g; fin_cases g <;> simp [mixedCESFisher, mixedCESAlloc, Fin.sum_univ_two] <;> norm_num
    · intro g; fin_cases g <;> simp [mixedCESFisher, mixedCESAlloc, Fin.sum_univ_two] <;> norm_num
  have hhom : ∀ i : Fin 2, IsHomogeneousDegOne (mixedCESFisher.utility i) := by
    intro i; fin_cases i
    · exact isHomogeneousDegOne_cesUtility
        (by simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num)
        (by norm_num)
    · exact isHomogeneousDegOne_cesUtility
        (by simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num)
        (by norm_num)
  have hpos : ∀ i : Fin 2, 0 < mixedCESFisher.utility i (mixedCESAlloc i) := by
    intro i; fin_cases i
    · change 0 < cesUtility ![1, 1] (1 / 2) ![1 / 2, 1 / 2]
      rw [cesUtility_of_bundle_pos _ _
        (by simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num)]
      exact Real.rpow_pos_of_pos (by
        rw [Fin.sum_univ_two]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]
        positivity) _
    · change 0 < cesUtility ![1, 1] (-1) ![3 / 2, 3 / 2]
      rw [cesUtility_of_bundle_pos _ _
        (by simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num)]
      exact Real.rpow_pos_of_pos (by
        rw [Fin.sum_univ_two]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]
        positivity) _
  exact heq.isMaxOn_eisenbergObjective
    (by simp only [mixedCESFisher, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        norm_num)
    hhom hpos

/-- Unconditional CES Fisher equilibrium recovery from
`mixedCESFisher_isMaxOn_eisenbergObjective`. -/
theorem mixedCESFisher_exists_isEquilibrium :
    ∃ π : Fin 2 → ℝ, (∀ g, 0 < π g) ∧ mixedCESFisher.IsEquilibrium mixedCESAlloc π ∧
      ∀ g : Fin 2, ∑ i : Fin 2, mixedCESAlloc i g = mixedCESFisher.supply g := by
  have hx : mixedCESFisher.IsPositiveUtilityAllocation mixedCESAlloc := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i g; fin_cases i <;> fin_cases g <;> simp [mixedCESAlloc] <;> norm_num
    · intro g; fin_cases g <;> simp [mixedCESFisher, mixedCESAlloc, Fin.sum_univ_two] <;> norm_num
    · intro i; fin_cases i
      · change 0 < cesUtility ![1, 1] (1 / 2) ![1 / 2, 1 / 2]
        rw [cesUtility_of_bundle_pos _ _
          (by simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num)]
        exact Real.rpow_pos_of_pos (by
          rw [Fin.sum_univ_two]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]
          positivity) _
      · change 0 < cesUtility ![1, 1] (-1) ![3 / 2, 3 / 2]
        rw [cesUtility_of_bundle_pos _ _
          (by simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num)]
        exact Real.rpow_pos_of_pos (by
          rw [Fin.sum_univ_two]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]
          positivity) _
  exact cesFisherMarket_exists_isEquilibrium_of_isMaxOn
    (α := ![![1, 1], ![1, 1]]) (ρ := ![1 / 2, -1])
    (by intro i; fin_cases i <;> rfl)
    (by intro i g; fin_cases i <;> fin_cases g <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> simp [mixedCESFisher])
    (by intro g; fin_cases g <;> simp [mixedCESFisher])
    hx mixedCESFisher_isMaxOn_eisenbergObjective

/-- Boundary zero-price surplus reassignment witness on a `1 × 2` linear Fisher market with an
undesired good `1`: `exists_isEquilibrium_exactClearing_of_isMaxOn_eisenbergObjective` clears both
goods while preserving equilibrium. -/
theorem linearFisher_exactClearing_boundary :
    let M : LinearFisherMarket (Fin 1) (Fin 2) := {
      budget := ![1]
      supply := ![1, 1]
      utility := ![![1, 0]]
      budget_nonneg := by simp
      supply_nonneg := by
        simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num
      utility_nonneg := by
        intro i g; fin_cases i; fin_cases g <;> norm_num }
    ∃ (x' : Fin 1 → Fin 2 → ℝ) (π : Fin 2 → ℝ),
      M.toFisherMarket.IsEquilibrium x' π ∧
      ∀ g : Fin 2, ∑ i : Fin 1, x' i g = M.toFisherMarket.supply g := by
  intro M
  let x : Fin 1 → Fin 2 → ℝ := ![![1, 0]]
  have hx : M.toFisherMarket.IsPositiveUtilityAllocation x := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i g; fin_cases i; fin_cases g <;> simp [x]
    · intro g; fin_cases g <;> simp [M, x]
    · intro i; fin_cases i
      rw [LinearFisherMarket.toFisherMarket_utility]
      simp only [M, x, linearUtility_eq_sum, Fin.sum_univ_two, Fin.isValue]
      norm_num
  have hmax : IsMaxOn M.toFisherMarket.eisenbergObjective
      {y | M.toFisherMarket.IsPositiveUtilityAllocation y} x := by
    rw [isMaxOn_iff]
    intro y hy
    simp only [FisherMarket.eisenbergObjective_eq, Fin.sum_univ_one,
      LinearFisherMarket.toFisherMarket_budget, LinearFisherMarket.toFisherMarket_utility,
      linearUtility_eq_sum, Fin.sum_univ_two]
    have hy0 : y 0 0 ≤ 1 := by simpa [M] using hy.1.2 0
    have hyu : 0 < y 0 0 := by
      have h := hy.2 0
      simpa [M, linearUtility_eq_sum, Fin.sum_univ_two] using h
    have hlog : Real.log (y 0 0) ≤ Real.log 1 := Real.log_le_log hyu hy0
    simpa [M, x] using hlog
  exact FisherMarket.exists_isEquilibrium_exactClearing_of_isMaxOn_eisenbergObjective
    (by intro i; fin_cases i; simp [M])
    (fun i => by rw [LinearFisherMarket.toFisherMarket_utility]; exact concaveOn_linearUtility _)
    (fun i => by
      rw [LinearFisherMarket.toFisherMarket_utility]; exact isHomogeneousDegOne_linearUtility _)
    (0 : Fin 1)
    (fun b₁ b₂ _ hle => by
      rw [LinearFisherMarket.toFisherMarket_utility, linearUtility_eq_sum, linearUtility_eq_sum]
      exact sum_le_sum fun g _ => mul_le_mul_of_nonneg_left (hle g) (M.utility_nonneg 0 g))
    hx hmax
    (fun i => by
      rw [LinearFisherMarket.toFisherMarket_utility]
      exact (differentiableAt_linearUtility _ _).differentiableWithinAt)

/-! ### 2. §6.4.1 Linear-exchange convex feasibility program -/

/-- Asymmetric `2 × 2` linear exchange market with non-equal equilibrium prices `![1, 2]`:
trader `0` holds `![2, 0]` with utilities `![1, 4]`; trader `1` holds `![0, 1]` with `![3, 1]`. -/
def linearExch2x2 : LinearExchangeMarket (Fin 2) (Fin 2) where
  endowment := ![![2, 0], ![0, 1]]
  utility := ![![1, 4], ![3, 1]]
  endowment_nonneg := by
    intro i g; fin_cases i <;> fin_cases g <;> norm_num
  utility_nonneg := by
    intro i g; fin_cases i <;> fin_cases g <;> norm_num

/-- Feasible `(ψ, x)` with `ψ = ![0, Real.log 2]` (prices `![1, 2]`) and `x = ![![0, 1], ![2, 0]]`,
certifying both the equivalence and convexity of the linear-exchange program. -/
theorem linearExch2x2_convexProgram_and_equilibrium :
    let ψ : Fin 2 → ℝ := ![0, Real.log 2]
    let x : Fin 2 → Fin 2 → ℝ := ![![0, 1], ![2, 0]]
    linearExch2x2.IsConvexProgramFeasible ψ x ∧
    linearExch2x2.IsCompetitiveEquilibrium x (fun g => Real.exp (ψ g)) ∧
    linearExch2x2.IsConvexProgramFeasible ![1 / 2, Real.log 2 + 1 / 2] x := by
  intro ψ x
  have hfeas : linearExch2x2.IsConvexProgramFeasible ψ x := by
    refine ⟨?_, ?_, ?_⟩
    · intro i g; fin_cases i <;> fin_cases g <;> simp [x]
    · intro g
      rw [ExchangeMarket.totalSupply_eq_sum]
      fin_cases g <;>
        simp [linearExch2x2, LinearExchangeMarket.toExchangeMarket_endowment, x, Fin.sum_univ_two]
    · intro i g
      fin_cases i <;> fin_cases g <;>
        simp [linearExch2x2, ψ, x, Fin.sum_univ_two, Real.exp_sub,
          Real.exp_log (by norm_num : (0 : ℝ) < 2)] <;>
        norm_num
  have hdes : ∀ i : Fin 2, ∃ g : Fin 2, 0 < linearExch2x2.utility i g := fun i => by
    fin_cases i
    · exact ⟨0, by simp [linearExch2x2]⟩
    · exact ⟨0, by simp [linearExch2x2]⟩
  have heq : linearExch2x2.IsCompetitiveEquilibrium x (fun g => Real.exp (ψ g)) :=
    (linearExch2x2.isConvexProgramFeasible_iff_isCompetitiveEquilibrium hdes ψ x).1 hfeas
  have hfeas_shift : linearExch2x2.IsConvexProgramFeasible ![1, Real.log 2 + 1] x := by
    refine ⟨hfeas.1, hfeas.2.1, fun i g => ?_⟩
    fin_cases i <;> fin_cases g <;>
      simp [linearExch2x2, x, Fin.sum_univ_two, Real.exp_neg,
        Real.exp_log (by norm_num : (0 : ℝ) < 2)] <;> norm_num
  have hmid := linearExch2x2.convex_setOf_isConvexProgramFeasible
    (x := (ψ, x)) (y := (![1, Real.log 2 + 1], x)) hfeas hfeas_shift
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hpair : ((1 / 2 : ℝ) • (ψ, x) + (1 / 2 : ℝ) • (![1, Real.log 2 + 1], x)) =
      (![1 / 2, Real.log 2 + 1 / 2], x) := by
    refine Prod.ext (funext fun g => ?_) (funext fun i => funext fun g => ?_)
    · fin_cases g
      · simp [ψ]
      · simp [ψ]; ring
    · simp only [Prod.smul_snd, Prod.snd_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  rw [hpair] at hmid
  exact ⟨hfeas, heq, hmid⟩

/-! ### 3. §6.4.2 CES demand uniqueness `(6.7)` and Proposition 6.11 -/

/-- Strict uniqueness of closed-form CES demand `(6.7)` for both `ρ = 1/2` and `ρ = -1`. -/
theorem ces_demand_uniqueness_instances :
    demandSet (cesUtility ![1, 1] (1 / 2)) ![1, 1] 2 = {![1, 1]} ∧
    demandSet (cesUtility ![1, 1] (-1)) ![1, 1] 2 = {![1, 1]} := by
  have h1 := demandSet_cesUtility_eq (α := ![1, 1]) (p := ![1, 1]) (ρ := 1 / 2) (m := 2)
    (by simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num)
    (by norm_num) (by norm_num)
    (by simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num)
    (by norm_num)
  have h2 := demandSet_cesUtility_eq (α := ![1, 1]) (p := ![1, 1]) (ρ := -1) (m := 2)
    (by simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num)
    (by norm_num) (by norm_num)
    (by simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num)
    (by norm_num)
  have hv1 : cesDemand ![1, 1] (1 / 2) ![1, 1] 2 = ![1, 1] := by
    funext g; rw [cesDemand_apply]
    fin_cases g <;> simp [Fin.sum_univ_two] <;> norm_num
  have hv2 : cesDemand ![1, 1] (-1) ![1, 1] 2 = ![1, 1] := by
    funext g; rw [cesDemand_apply]
    fin_cases g <;> simp [Fin.sum_univ_two] <;> norm_num
  exact ⟨h1.trans (by rw [hv1]), h2.trans (by rw [hv2])⟩

/-- Mixed `-1 ≤ ρ_i < 0` CES exchange economy (`ρ = ![-1, -1/2]`) exercising Proposition 6.11 and
convexity of the transformed equilibrium price set. -/
noncomputable def mixedNegCESExchange : CESExchangeMarket (Fin 2) (Fin 2) where
  endowment := ![![1, 0], ![0, 1]]
  weight := ![![1, 1], ![1, 1]]
  rho := ![-1, -1 / 2]
  endowment_nonneg := by intro i g; fin_cases i <;> fin_cases g <;> norm_num
  weight_pos := by intro i g; fin_cases i <;> fin_cases g <;> norm_num
  rho_lt_one := by intro i; fin_cases i <;> norm_num
  rho_ne_zero := by intro i; fin_cases i <;> norm_num

theorem mixedNegCESExchange_prop611_and_convex_equilibria :
    ConvexOn ℝ {σ : Fin 2 → ℝ | ∀ k, 0 < σ k}
      (fun σ => cesTransformedDemand ![1, 1] ![0, 1] (-1 / 2) σ 0) ∧
    Convex ℝ mixedNegCESExchange.transformedEquilibriumSet ∧
    (![1, 1] : Fin 2 → ℝ) ∈ mixedNegCESExchange.transformedEquilibriumSet := by
  have hprop := convexOn_cesTransformedDemand (α := ![1, 1]) (w := ![0, 1]) (ρ_i := -1 / 2)
    (by simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num)
    (by simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num)
    (by norm_num) (by norm_num) 0
  have hconv := mixedNegCESExchange.convex_setOf_transformedEquilibrium
    (by intro i; fin_cases i
        · simp [mixedNegCESExchange]
        · simp [mixedNegCESExchange]; norm_num)
    (by intro i; fin_cases i
        · simp [mixedNegCESExchange]
        · simp [mixedNegCESExchange]; norm_num)
  have hmem : (![1, 1] : Fin 2 → ℝ) ∈ mixedNegCESExchange.transformedEquilibriumSet := by
    rw [← mixedNegCESExchange.isWalrasianEquilibrium_sq_iff
      (by simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num)]
    refine ⟨by intro g; fin_cases g <;> norm_num, fun g => ?_⟩
    rw [mixedNegCESExchange.excessDemandFn_eq, ExchangeMarket.totalSupply_eq_sum]
    fin_cases g <;>
      simp [mixedNegCESExchange, CESExchangeMarket.toExchangeMarket_endowment,
        cesDemand_apply, expenditure_eq_sum, Fin.sum_univ_two] <;>
      norm_num
  exact ⟨hprop, hconv, hmem⟩

/-! ### 4. §6.5.1 Gjerstad multiple disconnected equilibria at `ρ = -2` -/

/-- Concrete `ρ = -2`, `a = (2 / 7) ^ (3 / 2)` instance of NRTV §6.5.1:
`(1/2, 1/2)` and `(1/9, 8/9)` are equilibria, while `(1/3, 2/3)` is not. -/
theorem gjerstad_rho_neg_two_disconnected :
    let a : ℝ := (2 / 7 : ℝ) ^ (3 / 2 : ℝ)
    have ha : 0 < a := Real.rpow_pos_of_pos (by norm_num) _
    let E := gjerstadMarket (-2) a (by norm_num) (by norm_num) ha
    IsWalrasianEquilibrium E.excessDemandFn ![1 / 2, 1 / 2] ∧
    IsWalrasianEquilibrium E.excessDemandFn ![1 / 9, 8 / 9] ∧
    ¬ IsWalrasianEquilibrium E.excessDemandFn ![1 / 3, 2 / 3] := by
  intro a ha E
  have hhalf : IsWalrasianEquilibrium E.excessDemandFn ![1 / 2, 1 / 2] :=
    gjerstadMarket_isWalrasianEquilibrium_half (by norm_num) (by norm_num) ha
  have hab : a ^ (-(-2 : ℝ) / (1 - (-2 : ℝ))) = 2 / 7 := by
    dsimp only [a]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2 / 7)]
    norm_num
  have hdisc := gjerstadMarket_exists_disconnected_equilibria (ρ := -2) (a := a)
    (by norm_num) ha (by rw [hab]; norm_num)
  obtain ⟨_, p, hp0, hp_half, _, _, huniq⟩ := hdisc
  have h8_23 : (8 : ℝ) ^ (2 / 3 : ℝ) = 4 := by
    have h8 : (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by norm_num
    rw [h8, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have h8_13 : (8 : ℝ) ^ (1 / 3 : ℝ) = 2 := by
    have h8 : (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by norm_num
    rw [h8, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have h9_eq : IsWalrasianEquilibrium E.excessDemandFn ![1 / 9, 8 / 9] := by
    have hpos9 : ∀ g : Fin 2, 0 < (![1 / 9, 8 / 9] : Fin 2 → ℝ) g := by
      simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num
    -- Verify `E.excessDemandFn ![1/9, 8/9] = 0` directly via `![1/9, 8/9] = (1/9) • ![1, 8]`.
    have hscale : (![1 / 9, 8 / 9] : Fin 2 → ℝ) = (1 / 9 : ℝ) • ![1, 8] := by
      funext g; fin_cases g <;> norm_num
    refine ⟨hpos9, fun g => ?_⟩
    rw [hscale, E.isHomogeneousDegZero_excessDemandFn (by norm_num : (0 : ℝ) < 1 / 9)
      (by simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num)]
    have h1 : a ^ ((-2 : ℝ) / (1 - (-2 : ℝ))) = 7 / 2 := by
      have : (-2 : ℝ) / (1 - (-2 : ℝ)) = -((-(-2 : ℝ)) / (1 - (-2 : ℝ))) := by norm_num
      rw [this, Real.rpow_neg ha.le, hab]; norm_num
    have h2 : (a ^ (-(-2 : ℝ))) ^ (1 / 3 : ℝ) = 2 / 7 := by
      rw [← Real.rpow_mul ha.le]; convert hab using 2; norm_num
    have h3 : (a ^ (-2 : ℝ)) ^ (1 / 3 : ℝ) = 7 / 2 := by
      rw [← Real.rpow_mul ha.le]; convert h1 using 2; norm_num
    rw [E.excessDemandFn_eq, ExchangeMarket.totalSupply_eq_sum]
    have he1 : (1 : ℝ) / (1 - (-2 : ℝ)) = 1 / 3 := by norm_num
    have he2 : -(-2 : ℝ) / (1 - (-2 : ℝ)) = 2 / 3 := by norm_num
    fin_cases g
    · dsimp only [Fin.zero_eta]
      simp only [E, CESExchangeMarket.toExchangeMarket_endowment, gjerstadMarket_endowment,
        gjerstadMarket_weight, gjerstadMarket_rho, cesDemand_apply, expenditure_eq_sum,
        Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul,
        zero_add, Real.one_rpow]
      rw [he1, he2, h2, h3, h8_23]
      norm_num
    · dsimp only [Fin.mk_one]
      simp only [E, CESExchangeMarket.toExchangeMarket_endowment, gjerstadMarket_endowment,
        gjerstadMarket_weight, gjerstadMarket_rho, cesDemand_apply, expenditure_eq_sum,
        Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul,
        zero_add, Real.one_rpow]
      rw [he1, he2, h2, h3, h8_13, h8_23]
      norm_num
  have hp_eq : p = 1 / 9 := by
    by_contra hne
    have h9' : IsWalrasianEquilibrium E.excessDemandFn ![1 / 9, 1 - 1 / 9] := by
      convert h9_eq using 1; funext g; fin_cases g <;> norm_num
    exact huniq (1 / 9) (by norm_num) (by norm_num) (Ne.symm hne) h9'
  have hnot3 : ¬ IsWalrasianEquilibrium E.excessDemandFn ![1 / 3, 2 / 3] := by
    intro h3
    have h3' : IsWalrasianEquilibrium E.excessDemandFn ![1 / 3, 1 - 1 / 3] := by
      convert h3 using 1; funext g; fin_cases g <;> norm_num
    exact huniq (1 / 3) (by norm_num) (by norm_num) (by linarith) h3'
  exact ⟨hhalf, h9_eq, hnot3⟩

/-! ### 5. §6.5.2 Bimatrix-to-Leontief exchange economy correspondence -/

/-- Strictly positive asymmetric `2 × 2` bimatrix game with unique interior mixed Nash equilibrium
`(![1/4, 3/4], ![1/3, 2/3])`. -/
def asymBimatrix : BimatrixGame (Fin 2) (Fin 2) where
  A := ![![3, 1], ![1, 2]]
  B := ![![1, 4], ![2, 1]]

theorem asymBimatrix_leontief_correspondence :
    have hA : ∀ i j, 0 < asymBimatrix.A i j := by
      intro i j; fin_cases i <;> fin_cases j <;> simp [asymBimatrix]
    have hB : ∀ i j, 0 < asymBimatrix.B i j := by
      intro i j; fin_cases i <;> fin_cases j <;> simp [asymBimatrix]
    ∃ π : Fin 2 ⊕ Fin 2 → ℝ,
      IsBimatrixLeontiefEquilibriumPrice asymBimatrix hA hB π ∧
      bimatrixLeontiefToStrategy asymBimatrix π = (![1 / 4, 3 / 4], ![1 / 3, 2 / 3]) := by
  intro hA hB
  have hnash : asymBimatrix.IsNash ![1 / 4, 3 / 4] ![1 / 3, 2 / 3] := by
    rw [BimatrixGame.isNash_iff, BimatrixGame.isBestResponse₁_iff_le_payoff₁,
      BimatrixGame.isBestResponse₂_iff_le_payoff₂]
    refine ⟨⟨isMixedStrategy_iff.2
        ⟨by simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num,
          by simp [Fin.sum_univ_two]; norm_num⟩, fun i => ?_⟩,
      ⟨isMixedStrategy_iff.2
        ⟨by simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num,
          by simp [Fin.sum_univ_two]; norm_num⟩, fun j => ?_⟩⟩
    · fin_cases i <;>
        simp [BimatrixGame.payoff₁_eq_dotProduct, asymBimatrix, Matrix.mulVec, dotProduct,
          Fin.sum_univ_two] <;> norm_num
    · fin_cases j <;>
        simp [BimatrixGame.payoff₂_eq_dotProduct, asymBimatrix, Matrix.vecMul, dotProduct,
          Fin.sum_univ_two] <;> norm_num
  let e := bimatrixLeontiefNashEquivEquilibriumPrice asymBimatrix hA hB
  let π := e ⟨(![1 / 4, 3 / 4], ![1 / 3, 2 / 3]), hnash⟩
  have hinv : (e.symm π).1 = (![1 / 4, 3 / 4], ![1 / 3, 2 / 3]) :=
    congrArg Subtype.val (e.left_inv _)
  rw [bimatrixLeontiefNashEquivEquilibriumPrice_symm_apply] at hinv
  exact ⟨π.1, π.2, hinv⟩

/-- Boundary zero-price pure Nash witness on a `2 × 2` strictly positive coordination game:
pure Nash equilibrium `(![1, 0], ![1, 0])` corresponds to normalized equilibrium price vector
`Sum.elim ![1/2, 0] ![1/2, 0]` with zero prices on the unplayed strategies. -/
theorem coordBimatrix_zeroPrice_boundary :
    let G : BimatrixGame (Fin 2) (Fin 2) := ⟨![![2, 1], ![1, 2]], ![![2, 1], ![1, 2]]⟩
    have hA : ∀ i j, 0 < G.A i j := by intro i j; fin_cases i <;> fin_cases j <;> simp [G]
    have hB : ∀ i j, 0 < G.B i j := by intro i j; fin_cases i <;> fin_cases j <;> simp [G]
    let π : Fin 2 ⊕ Fin 2 → ℝ := Sum.elim ![1 / 2, 0] ![1 / 2, 0]
    IsBimatrixLeontiefEquilibriumPrice G hA hB π ∧
    bimatrixLeontiefToStrategy G π = (![1, 0], ![1, 0]) := by
  intro G hA hB π
  let E := bimatrixLeontiefMarket G hA hB
  let X : (Fin 2 ⊕ Fin 2) → (Fin 2 ⊕ Fin 2) → ℝ :=
    Sum.elim
      ![Sum.elim ![0, 0] ![1, 1 / 2], 0]
      ![Sum.elim ![1, 1 / 2] ![0, 0], 0]
  have hπ_nn : ∀ g, 0 ≤ π g := by
    intro g; rcases g with i | i <;> fin_cases i <;> simp [π]
  have hπ_sum : ∑ g : Fin 2 ⊕ Fin 2, π g = 1 := by
    simp [π, Fintype.sum_sum_type, Fin.sum_univ_two]; norm_num
  have heq : E.toExchangeMarket.IsCompetitiveEquilibrium X π := by
    refine ⟨hπ_nn, fun t => ?_, fun g => ?_, fun g => ?_⟩
    · rcases t with i | j
      · fin_cases i
        · dsimp only [Fin.zero_eta]
          rw [ExchangeMarket.mem_demandSet, E.toExchangeMarket_utility]
          have hinc : E.toExchangeMarket.income π (Sum.inl 0) = 1 / 2 := by
            simp [E, bimatrixLeontiefMarket_income, π]
          have hcost : expenditure π (E.proportion (Sum.inl 0)) = 1 := by
            simp [E, bimatrixLeontiefMarket_cost_inl, G, π, Matrix.mulVec, dotProduct,
              Fin.sum_univ_two]
          rw [hinc, mem_demandSet_leontiefUtility_iff (E.proportion_nonneg (Sum.inl 0))
            ⟨Sum.inr 0, by simp [E, hB 0 0]⟩ hπ_nn (by norm_num) (by rw [hcost]; norm_num)]
          refine ⟨⟨by intro g; rcases g with k | k <;> fin_cases k <;> simp [X],
            by simp [expenditure_eq_sum, X, π, Fintype.sum_sum_type, Fin.sum_univ_two]⟩,
            fun g _ => ?_⟩
          rw [hcost]
          rcases g with k | k <;> fin_cases k <;> simp [X, E, G]
        · dsimp only [Fin.mk_one]
          rw [ExchangeMarket.mem_demandSet, E.toExchangeMarket_utility]
          have hinc : E.toExchangeMarket.income π (Sum.inl 1) = 0 := by
            simp [E, bimatrixLeontiefMarket_income, π]
          have hcost : 0 < expenditure π (E.proportion (Sum.inl 1)) := by
            simp [E, bimatrixLeontiefMarket_cost_inl, G, π, Matrix.mulVec, dotProduct,
              Fin.sum_univ_two]
          rw [hinc, mem_demandSet_leontiefUtility_iff (E.proportion_nonneg (Sum.inl 1))
            ⟨Sum.inr 0, by simp [E, hB 1 0]⟩ hπ_nn le_rfl hcost]
          refine ⟨⟨fun _ => le_rfl, by simp [expenditure_eq_sum, X]⟩,
            fun _ _ => by simp [X]⟩
      · fin_cases j
        · dsimp only [Fin.zero_eta]
          rw [ExchangeMarket.mem_demandSet, E.toExchangeMarket_utility]
          have hinc : E.toExchangeMarket.income π (Sum.inr 0) = 1 / 2 := by
            simp [E, bimatrixLeontiefMarket_income, π]
          have hcost : expenditure π (E.proportion (Sum.inr 0)) = 1 := by
            simp [E, bimatrixLeontiefMarket_cost_inr, G, π, Matrix.vecMul, dotProduct,
              Fin.sum_univ_two]
          rw [hinc, mem_demandSet_leontiefUtility_iff (E.proportion_nonneg (Sum.inr 0))
            ⟨Sum.inl 0, by simp [E, hA 0 0]⟩ hπ_nn (by norm_num) (by rw [hcost]; norm_num)]
          refine ⟨⟨by intro g; rcases g with k | k <;> fin_cases k <;> simp [X],
            by simp [expenditure_eq_sum, X, π, Fintype.sum_sum_type, Fin.sum_univ_two]⟩,
            fun g _ => ?_⟩
          rw [hcost]
          rcases g with k | k <;> fin_cases k <;> simp [X, E, G]
        · dsimp only [Fin.mk_one]
          rw [ExchangeMarket.mem_demandSet, E.toExchangeMarket_utility]
          have hinc : E.toExchangeMarket.income π (Sum.inr 1) = 0 := by
            simp [E, bimatrixLeontiefMarket_income, π]
          have hcost : 0 < expenditure π (E.proportion (Sum.inr 1)) := by
            simp [E, bimatrixLeontiefMarket_cost_inr, G, π, Matrix.vecMul, dotProduct,
              Fin.sum_univ_two]
          rw [hinc, mem_demandSet_leontiefUtility_iff (E.proportion_nonneg (Sum.inr 1))
            ⟨Sum.inl 0, by simp [E, hA 0 1]⟩ hπ_nn le_rfl hcost]
          refine ⟨⟨fun _ => le_rfl, by simp [expenditure_eq_sum, X]⟩,
            fun _ _ => by simp [X]⟩
    · rw [ExchangeMarket.excessDemand_eq, bimatrixLeontiefMarket_totalSupply]
      rcases g with i | i <;> fin_cases i <;>
        simp [X, Fintype.sum_sum_type, Fin.sum_univ_two] <;> norm_num
    · rw [ExchangeMarket.excessDemand_eq, bimatrixLeontiefMarket_totalSupply]
      rcases g with i | i <;> fin_cases i <;>
        simp [X, π, Fintype.sum_sum_type, Fin.sum_univ_two]
  have hstrat : bimatrixLeontiefToStrategy G π = (![1, 0], ![1, 0]) := by
    ext i
    · fin_cases i <;>
        simp [bimatrixLeontiefToStrategy, G, π, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · fin_cases i <;>
        simp [bimatrixLeontiefToStrategy, G, π, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  exact ⟨⟨hπ_sum, X, heq⟩, hstrat⟩

end CslibFrontierTests.GameTheory.MarketConvexPrograms
