/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.GameTheory.Market.Tatonnement
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Gross substitutability and discrete tâtonnement: checked instances and counterexamples

This test module imports only the public surface of `CslibFrontier.GameTheory.Market.Tatonnement`
(and transitively `GrossSubstitutes` and `Basic`), exercising every headline theorem on concrete
non-vacuous economies and verifying boundary sharpness without `import all`:

1. **Asymmetric strict-GS `2 × 2` Cobb–Douglas exchange market (`cobbDouglas2x2`):**
   certifies strict gross substitutability (`isGrossSubstitutes_excessDemandFn`), the unique
   equilibrium price ray `![7, 10]` via the homogeneous linear equations of **Exercise 6.2**
   (`isWalrasianEquilibrium_iff_linearEquations`) and strict-GS ray uniqueness
   (`IsGrossSubstitutes.eq_smul_of_isWalrasianEquilibrium`), exact competitive equilibrium
   (`isCompetitiveEquilibrium_of_isWalrasianEquilibrium`) with fractional Marshallian demands
   `![![12/7, 6/5], ![9/7, 9/5]]`, uniqueness of individual Cobb–Douglas demand (**Exercise 6.1**,
   `demandSet_cobbDouglasUtility_eq`), and the Arrow–Block–Hurwicz separating hyperplane
   `0 < expenditure ![7, 10] (Z ![1, 1])` (**Lemma 6.4**).
2. **Boundary separation between WGS and strict GS (`Fin 3`, NRTV §6.1.4 & Exercise 6.3):**
   a decoupled `3`-good excess-demand system `decoupledZ(p) = ![p₁/p₀ - 1, p₀/p₁ - 1, 0]` satisfies
   `IsHomogeneousDegZero`, `SatisfiesWalrasLaw`, and `IsWeakGrossSubstitutes`, fails
   `IsGrossSubstitutes`, and admits non-proportional positive Walrasian equilibria `![1, 1, 1]` and
   `![1, 1, 2]` (demonstrating why strict GS rather than pure WGS is required for uniqueness up to
   scaling), while still satisfying convexity of equilibria (**Exercise 6.3**) and **Lemma 6.4**.
3. **CES substitutes (`ρ = 1/2`) vs. complements failure of WGS (`ρ = -1`, NRTV §6.1.5 & §6.4.2):**
   checks closed-form CES demand optimality (`cesDemand_mem_demandSet`, Equation `(6.7)`) for both
   `ρ = 1/2 > 0` and `ρ = -1 < 0`, verifies WGS at `ρ = 1/2`
   (`isWeakGrossSubstitutes_cesExcessDemand`), and proves a concrete counterexample showing that
   harmonic-mean CES excess demand (`ρ = -1`, `α = ![1, 1]`, `w = ![0, 1]`) violates
   `IsWeakGrossSubstitutes` when `p` rises from `![1, 1]` to `![4, 1]`.
4. **Approximate equilibria (`Exercise 6.5`), normalizations (`Lemma 6.5`–`Lemma 6.6`), and
   end-to-end discrete tâtonnement (`Theorem 6.9`–`Theorem 6.10`):**
   certifies a weak `(13/10)`-approximate equilibrium of `cobbDouglas2x2` at perturbed prices
   `![7, 11]` via **Exercise 6.5**, and applies
   `CobbDouglasExchangeMarket.exists_weakApproxEquilibrium_tatonnement` (**Theorem 6.10**) to obtain
   a weak `(3/2)`-approximate equilibrium of `cobbDouglas2x2` from projected discrete tâtonnement.
-/

public section

namespace CslibFrontierTests.GameTheory.GrossSubstitutes

open Cslib.GameTheory.Market
open Finset

/-! ### 1. Strict-GS `2 × 2` Cobb–Douglas exchange market -/

/-- Asymmetric `2 × 2` Cobb–Douglas exchange market:
* trader `0` holds endowment `![2, 1]` and expenditure shares `![1/2, 1/2]`;
* trader `1` holds endowment `![1, 2]` and expenditure shares `![1/3, 2/3]`. -/
noncomputable def cobbDouglas2x2 : CobbDouglasExchangeMarket (Fin 2) (Fin 2) where
  endowment := ![![2, 1], ![1, 2]]
  weight := ![![1 / 2, 1 / 2], ![1 / 3, 2 / 3]]
  endowment_nonneg := by
    simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  weight_nonneg := by
    simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  sum_weight := by
    simp only [Fin.forall_fin_two, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num

/-- Unique normalized equilibrium price vector `![7, 10]` of `cobbDouglas2x2`. -/
def cdEqPrices : Fin 2 → ℝ := ![7, 10]

theorem cdEqPrices_pos : ∀ g : Fin 2, 0 < cdEqPrices g := by
  simp [cdEqPrices, Fin.forall_fin_two]

theorem cobbDouglas2x2_totalSupply :
    ∀ g : Fin 2, cobbDouglas2x2.toExchangeMarket.totalSupply g = 3 := by
  simp only [ExchangeMarket.totalSupply_eq_sum, cobbDouglas2x2,
    CobbDouglasExchangeMarket.toExchangeMarket_endowment, Fin.forall_fin_two, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

theorem cobbDouglas2x2_isGrossSubstitutes :
    IsGrossSubstitutes cobbDouglas2x2.excessDemandFn := by
  refine cobbDouglas2x2.isGrossSubstitutes_excessDemandFn fun g j hj => ?_
  fin_cases g <;> fin_cases j
  · exact (hj rfl).elim
  · refine ⟨0, ?_, ?_⟩ <;> simp [cobbDouglas2x2]
  · refine ⟨0, ?_, ?_⟩ <;> simp [cobbDouglas2x2]
  · exact (hj rfl).elim

theorem cobbDouglas2x2_isWalrasianEquilibrium :
    IsWalrasianEquilibrium cobbDouglas2x2.excessDemandFn cdEqPrices := by
  rw [cobbDouglas2x2.isWalrasianEquilibrium_iff_linearEquations cdEqPrices_pos]
  intro g
  rw [cobbDouglas2x2_totalSupply g]
  fin_cases g <;>
    · simp only [cobbDouglas2x2, cdEqPrices, expenditure_eq_sum, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      norm_num

theorem cobbDouglas2x2_unique_ray {p : Fin 2 → ℝ}
    (heq : IsWalrasianEquilibrium cobbDouglas2x2.excessDemandFn p) :
    ∃ c : ℝ, 0 < c ∧ p = c • cdEqPrices :=
  cobbDouglas2x2_isGrossSubstitutes.eq_smul_of_isWalrasianEquilibrium
    cobbDouglas2x2.isHomogeneousDegZero_excessDemandFn
    cobbDouglas2x2.satisfiesWalrasLaw_excessDemandFn
    cobbDouglas2x2_isWalrasianEquilibrium heq

theorem cobbDouglas2x2_isCompetitiveEquilibrium :
    cobbDouglas2x2.toExchangeMarket.IsCompetitiveEquilibrium
      (fun i => cobbDouglasDemand (cobbDouglas2x2.weight i) cdEqPrices
        (cobbDouglas2x2.toExchangeMarket.income cdEqPrices i))
      cdEqPrices :=
  cobbDouglas2x2.isCompetitiveEquilibrium_of_isWalrasianEquilibrium
    cobbDouglas2x2_isWalrasianEquilibrium

theorem cobbDouglas2x2_trader0_demandSet_eq :
    demandSet (cobbDouglasUtility (cobbDouglas2x2.weight 0)) cdEqPrices 24 =
      {![12 / 7, 6 / 5]} := by
  have hα_pos : ∀ g : Fin 2, 0 < cobbDouglas2x2.weight 0 g := by
    simp only [cobbDouglas2x2, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  rw [demandSet_cobbDouglasUtility_eq hα_pos (cobbDouglas2x2.sum_weight 0) cdEqPrices_pos
    (by norm_num)]
  congr 1
  funext g
  fin_cases g
  · simp only [cobbDouglasDemand_apply, cobbDouglas2x2, cdEqPrices,
      Fin.zero_eta, Matrix.cons_val_zero]
    norm_num
  · simp only [cobbDouglasDemand_apply, cobbDouglas2x2, cdEqPrices,
      Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num

theorem cobbDouglas2x2_not_equilibrium_ones :
    ¬ IsWalrasianEquilibrium cobbDouglas2x2.excessDemandFn ![1, 1] := by
  intro heq
  have hz1 : cobbDouglas2x2.excessDemandFn ![1, 1] 1 ≤ 0 := heq.2 1
  rw [cobbDouglas2x2.excessDemandFn_eq, cobbDouglas2x2_totalSupply 1] at hz1
  simp only [cobbDouglas2x2, expenditure_eq_sum, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hz1
  norm_num at hz1

/-- Concrete verification of **Lemma 6.4** (Arrow–Block–Hurwicz separating hyperplane) at
off-equilibrium prices `![1, 1]`. -/
theorem cobbDouglas2x2_separating_hyperplane :
    0 < expenditure cdEqPrices (cobbDouglas2x2.excessDemandFn ![1, 1]) :=
  cobbDouglas2x2.isWeakGrossSubstitutes_excessDemandFn.expenditure_pos_of_not_isWalrasianEquilibrium
    cobbDouglas2x2.isHomogeneousDegZero_excessDemandFn
    cobbDouglas2x2.satisfiesWalrasLaw_excessDemandFn
    cobbDouglas2x2_isWalrasianEquilibrium
    (by simp [Fin.forall_fin_two])
    cobbDouglas2x2_not_equilibrium_ones

/-! ### 2. Boundary separation: WGS vs. strict GS (`Fin 3`, NRTV §6.1.4 & Exercise 6.3) -/

/-- Decoupled `3`-good excess-demand map: goods `0` and `1` form a `2`-good Cobb–Douglas submarket
while good `2` has identically zero excess demand. -/
noncomputable def decoupledZ (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![p 1 / p 0 - 1, p 0 / p 1 - 1, 0]

theorem decoupledZ_homogeneous : IsHomogeneousDegZero decoupledZ := by
  intro c hc p _
  funext g
  fin_cases g
  · simp only [decoupledZ, Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Matrix.cons_val_zero]
    exact congrArg (· - 1) (mul_div_mul_left _ _ hc.ne')
  · simp only [decoupledZ, Pi.smul_apply, smul_eq_mul, Fin.mk_one, Matrix.cons_val_one]
    exact congrArg (· - 1) (mul_div_mul_left _ _ hc.ne')
  · rfl

theorem decoupledZ_walras : SatisfiesWalrasLaw decoupledZ := by
  intro p hp
  rw [expenditure_eq_sum, Fin.sum_univ_three]
  have hp0 := (hp 0).ne'
  have hp1 := (hp 1).ne'
  simp only [decoupledZ, Matrix.cons_val_zero, Matrix.cons_val_one]
  change p 0 * (p 1 / p 0 - 1) + p 1 * (p 0 / p 1 - 1) + p 2 * 0 = 0
  field_simp [hp0, hp1]
  ring

theorem decoupledZ_wgs : IsWeakGrossSubstitutes decoupledZ := by
  intro p p' hp hle g hfg
  fin_cases g
  · dsimp only [Fin.zero_eta] at hfg
    change p 1 / p 0 - 1 ≤ p' 1 / p' 0 - 1
    rw [hfg]
    linarith [div_le_div_of_nonneg_right (hle 1) (hp 0).le]
  · dsimp only [Fin.mk_one] at hfg
    change p 0 / p 1 - 1 ≤ p' 0 / p' 1 - 1
    rw [hfg]
    linarith [div_le_div_of_nonneg_right (hle 0) (hp 1).le]
  · change (0 : ℝ) ≤ 0
    exact le_rfl

/-- `decoupledZ` fails **strict** gross substitutability: raising `p 2` from `1` to `2` while
holding `p 0 = p 1 = 1` leaves `decoupledZ p 0 = 0` unchanged. -/
theorem decoupledZ_not_strict_gs : ¬ IsGrossSubstitutes decoupledZ := by
  intro hgs
  have hlt := hgs (p := ![1, 1, 1]) (p' := ![1, 1, 2])
    (by simp [Fin.forall_fin_succ])
    (by simp [Fin.forall_fin_succ])
    ⟨2, by norm_num⟩
    0 rfl
  norm_num [decoupledZ] at hlt

/-- Consequently, `decoupledZ` admits two non-proportional positive Walrasian equilibria
`![1, 1, 1]` and `![1, 1, 2]`, showing that strict GS (not pure WGS) is needed for equilibrium
price uniqueness up to scaling. -/
theorem decoupledZ_two_independent_equilibria :
    IsWalrasianEquilibrium decoupledZ ![1, 1, 1] ∧
      IsWalrasianEquilibrium decoupledZ ![1, 1, 2] ∧
      ∀ c : ℝ, (![1, 1, 2] : Fin 3 → ℝ) ≠ c • (![1, 1, 1] : Fin 3 → ℝ) := by
  refine ⟨⟨by simp [Fin.forall_fin_succ], ?_⟩, ⟨by simp [Fin.forall_fin_succ], ?_⟩, fun c hc => ?_⟩
  · intro g
    fin_cases g <;> norm_num [decoupledZ]
  · intro g
    fin_cases g <;> norm_num [decoupledZ]
  · have h0 := congrFun hc 0
    have h2 := congrFun hc 2
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons] at h0 h2
    linarith

/-- Nevertheless, **Exercise 6.3** and **Lemma 6.4** continue to hold for `decoupledZ`: its positive
equilibrium set is convex and strictly separates non-equilibria such as `![1, 2, 3]`. -/
theorem decoupledZ_convex_and_separating :
    Convex ℝ {p : Fin 3 → ℝ | IsWalrasianEquilibrium decoupledZ p} ∧
      0 < expenditure ![1, 1, 2] (decoupledZ ![1, 2, 3]) := by
  refine ⟨decoupledZ_wgs.convex_setOf_isWalrasianEquilibrium decoupledZ_homogeneous
    decoupledZ_walras, ?_⟩
  refine decoupledZ_wgs.expenditure_pos_of_not_isWalrasianEquilibrium
    decoupledZ_homogeneous decoupledZ_walras decoupledZ_two_independent_equilibria.2.1
    (by simp [Fin.forall_fin_succ]) ?_
  intro heq
  have h0 := heq.2 0
  norm_num [decoupledZ] at h0

/-! ### 3. CES substitutes (`ρ = 1/2`) vs. complements failure of WGS (`ρ = -1`) -/

theorem ces_substitutes_and_complements_mem_demandSet :
    cesDemand ![1, 1] (1 / 2) ![1, 4] 6 ∈
        demandSet (cesUtility (![1, 1] : Fin 2 → ℝ) (1 / 2)) ![1, 4] 6 ∧
      cesDemand ![1, 1] (-1) ![1, 4] 6 ∈
        demandSet (cesUtility (![1, 1] : Fin 2 → ℝ) (-1)) ![1, 4] 6 := by
  have hα : ∀ g : Fin 2, 0 < (![1, 1] : Fin 2 → ℝ) g := by simp [Fin.forall_fin_two]
  have hp : ∀ g : Fin 2, 0 < (![1, 4] : Fin 2 → ℝ) g := by simp [Fin.forall_fin_two]
  exact ⟨cesDemand_mem_demandSet hα (by norm_num) (by norm_num) hp (by norm_num),
    cesDemand_mem_demandSet hα (by norm_num) (by norm_num) hp (by norm_num)⟩

theorem ces_half_isWeakGrossSubstitutes :
    IsWeakGrossSubstitutes (fun p (g : Fin 2) =>
      cesDemand ![1, 1] (1 / 2) p (expenditure p ![0, 1]) g - (![0, 1] : Fin 2 → ℝ) g) :=
  isWeakGrossSubstitutes_cesExcessDemand
    (by simp [Fin.forall_fin_two])
    (by simp [Fin.forall_fin_two])
    (by norm_num) (by norm_num)

/-- Boundary counterexample: in the complements regime `ρ = -1 < 0`, a CES trader with weights
`![1, 1]` and endowment `![0, 1]` violates `IsWeakGrossSubstitutes` when `p` rises from `![1, 1]`
to `![4, 1]` (excess demand for good `1` drops from `-1/2` to `-2/3`). -/
theorem ces_neg_one_not_isWeakGrossSubstitutes :
    ¬ IsWeakGrossSubstitutes (fun p (g : Fin 2) =>
      cesDemand ![1, 1] (-1) p (expenditure p ![0, 1]) g - (![0, 1] : Fin 2 → ℝ) g) := by
  intro hwgs
  have hle := hwgs (p := ![1, 1]) (p' := ![4, 1])
    (by simp [Fin.forall_fin_two])
    (by simp [Fin.forall_fin_two])
    1 rfl
  have hsqrt4 : (4 : ℝ) ^ (-(-1 : ℝ) / (1 - (-1 : ℝ))) = 2 := by
    have hexp : -(-1 : ℝ) / (1 - (-1 : ℝ)) = 1 / 2 := by norm_num
    have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
    rw [hexp, h4, ← Real.rpow_mul (by norm_num)]
    norm_num
  simp only [cesDemand_apply, expenditure_eq_sum, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Real.one_rpow, hsqrt4] at hle
  norm_num at hle

/-! ### 4. Exercise 6.5 and end-to-end discrete tâtonnement (`Theorem 6.10`) -/

/-- **Exercise 6.5** checked on `cobbDouglas2x2`: perturbing equilibrium prices `![7, 10]` to
`![7, 11]` gives a weak `(13 / 10)`-approximate equilibrium. -/
theorem cobbDouglas2x2_perturbed_isWeakApproxEquilibrium :
    cobbDouglas2x2.toExchangeMarket.IsWeakApproxEquilibrium (13 / 10) ![7, 11] := by
  have hexc := cobbDouglas2x2.toExchangeMarket.isWeakApproxEquilibrium_of_priceRatio_le
    (xHat := fun i => cobbDouglasDemand (cobbDouglas2x2.weight i) cdEqPrices
      (cobbDouglas2x2.toExchangeMarket.income cdEqPrices i))
    (pHat := cdEqPrices) (p := ![7, 11]) (ε := 3 / 10)
    cobbDouglas2x2.isRayConcave_toExchangeMarket_utility
    (fun i _ hb => cobbDouglas2x2.toExchangeMarket_utility_nonneg i hb)
    cobbDouglas2x2_isCompetitiveEquilibrium
    cdEqPrices_pos
    (by simp [Fin.forall_fin_two])
    (by norm_num)
    (fun j k => by
      fin_cases j <;> fin_cases k <;> norm_num [cdEqPrices])
  convert hexc using 1
  norm_num

/-- **Theorem 6.10** instantiated end-to-end on `cobbDouglas2x2` at `ε = 1 / 2`: projected discrete
tâtonnement visits a price vector whose un-rescaled image is a weak `(3 / 2)`-approximate
equilibrium of `cobbDouglas2x2.toExchangeMarket` within the explicit polynomial iteration bound. -/
theorem cobbDouglas2x2_exists_tatonnement_approxEquilibrium :
    let W := cobbDouglas2x2.toExchangeMarket.totalSupply
    let Z' : (Fin 2 → ℝ) → Fin 2 → ℝ :=
      fun p g => cobbDouglas2x2.excessDemandFn (fun l => p l / W l) g / W g
    let η : ℝ := (1 / 2) / 3
    let δ : ℝ := tatonnementDelta 2 η η
    let μ : ℝ := tatonnementMu 2 η δ
    ∃ k ≤ Nat.floor ((2 : ℝ) / μ),
      cobbDouglas2x2.toExchangeMarket.IsWeakApproxEquilibrium (3 / 2)
        (fun g => tatonnementIter (phantomExcessDemand Z' η) η δ (fun _ => 1) k g / W g) := by
  have hW : ∀ g : Fin 2, 0 < cobbDouglas2x2.toExchangeMarket.totalSupply g := by
    intro g; rw [cobbDouglas2x2_totalSupply g]; norm_num
  simpa only [Fintype.card_fin, Nat.cast_ofNat, show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num]
    using cobbDouglas2x2.exists_weakApproxEquilibrium_tatonnement hW
      (ε := 1 / 2) (by norm_num) (by norm_num)

end CslibFrontierTests.GameTheory.GrossSubstitutes
