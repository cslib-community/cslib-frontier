/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.BudgetedAuction.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact continuous 2-bidder adaptive clinching auction

Closed-form continuous-price adaptive clinching auction for two bidders with linear valuations
`v : Fin 2 → ℝ` (`v i ≥ 0`), divisible supply `m > 0`, and strictly positive **public** hard
budgets `B : Fin 2 → ℝ` (`0 < B i`) ([DobzinskiLaviNisan2012]; primary PDF not inspected,
theorem/page locators unverified).

Assuming `0 < b₁ ≤ b₂` (symmetrized to arbitrary `B 0, B 1 > 0` by `Equiv.swap 0 1`), let
`p₀ = b₁ / m` be the entry price and `p_eq = p₀ * exp ((b₂ - b₁) / b₁)` the budget-equalization
price. Along the ascending clock `p ≥ 0` while both bidders remain active, cumulative allocations
`(x₀, x₁)`, payments `(pay₀, pay₁)`, and remaining supply `S` evolve across three phases:

* **Phase 0 (`p ≤ p₀`):** `x₀ = x₁ = 0`, `pay₀ = pay₁ = 0`, `S = m`.
* **Phase 1 (`p₀ < p ≤ p_eq`):** `x₀ = 0`, `x₁ = m - b₁ / p`, `pay₀ = 0`,
  `pay₁ = b₁ * log (p * m / b₁)`, `S = b₁ / p`.
* **Phase 2 (`p_eq < p`):** letting `Sₑ = b₁ / p_eq`, `S = Sₑ * (p_eq / p) ^ 2`,
  `dx = (Sₑ - S) / 2`, `dpay = b₁ * (1 - p_eq / p)`, giving
  `x₀ = dx`, `x₁ = (m - Sₑ) + dx`, `pay₀ = dpay`, `pay₁ = (b₂ - b₁) + dpay`.

When the lower bidder exits at `p = min v₀ v₁`, the surviving bidder receives all remaining supply
`S(p)` at price `p` (splitting `S(p) / 2` equally on positive ties `v₀ = v₁ > 0`, and outputting
`(0, 0)` when `v₀ = v₁ = 0`).

Without any measure theory or calculus, we prove all guarantees directly via the elementary curve
sandwich `(x q - x p) * p ≤ pay q - pay p ≤ (x q - x p) * q`:
* `twoBidderClinching_isFeasible` / `twoBidderClinching_sum_alloc` (exact market clearing)
* `twoBidderClinching_hasNonnegPayment` / `twoBidderClinching_isBudgetFeasible`
* `twoBidderClinching_isParetoOptimal` (exact Pareto optimality via `Outcome.isParetoOptimal_iff`)
* `twoBidderClinchingSP_isIR` / `twoBidderClinchingSP_isNormalized` / `twoBidderClinchingSP_isDSIC`
* `twoBidderClinching_budget_manipulation` and `twoBidderClinching_not_privateBudgetDSIC`:
  explicit manipulation witness showing why hard budgets **must** be public (`1 / 4 < 1 - log 2`).

## Main definitions

* `Cslib.GameTheory.BudgetedAuction.twoBidderClinching`: closed-form 2-bidder adaptive clinching
  auction outcome.
* `Cslib.GameTheory.BudgetedAuction.twoBidderClinchingSP`: `SingleParameter.Mechanism (Fin 2)` for
  fixed public budgets `B`.
* `Cslib.GameTheory.BudgetedAuction.twoBidderClinchingMechanism`: `BudgetedMechanism (Fin 2)` when
  budgets are also reported.

## Main results

* `Cslib.GameTheory.BudgetedAuction.twoBidderClinching_isParetoOptimal`
* `Cslib.GameTheory.BudgetedAuction.twoBidderClinchingSP_isDSIC`
* `Cslib.GameTheory.BudgetedAuction.twoBidderClinching_budget_manipulation`
* `Cslib.GameTheory.BudgetedAuction.twoBidderClinching_not_privateBudgetDSIC`

## References

* [S. Dobzinski, R. Lavi, and N. Nisan,
  *Multi-unit auctions with budget limits*][DobzinskiLaviNisan2012]
  (primary PDF not inspected; theorem/page locators unverified)
-/

public section

namespace Cslib.GameTheory.BudgetedAuction

/-- Swap `0` and `1` in `Fin 2`. -/
private def swap01 : Fin 2 ≃ Fin 2 := Equiv.swap 0 1

@[simp] private theorem swap01_zero : swap01 0 = 1 := rfl
@[simp] private theorem swap01_one : swap01 1 = 0 := rfl

private theorem swap01_invol (i : Fin 2) : swap01 (swap01 i) = i := by
  fin_cases i <;> rfl

/-- Swap bidder coordinates of a `Fin 2` outcome via `swap01`. -/
private def swapOutcome (o : Outcome (Fin 2)) : Outcome (Fin 2) where
  alloc i := o.alloc (swap01 i)
  payment i := o.payment (swap01 i)

private noncomputable def entryPrice (m b₁ : ℝ) : ℝ := b₁ / m

private noncomputable def eqPrice (m b₁ b₂ : ℝ) : ℝ :=
  entryPrice m b₁ * Real.exp ((b₂ - b₁) / b₁)

private noncomputable def trajX0 (m b₁ b₂ p : ℝ) : ℝ :=
  if p ≤ eqPrice m b₁ b₂ then 0
  else (b₁ / eqPrice m b₁ b₂) * (1 - (eqPrice m b₁ b₂ / p) ^ 2) / 2

private noncomputable def trajP0 (m b₁ b₂ p : ℝ) : ℝ :=
  if p ≤ eqPrice m b₁ b₂ then 0
  else b₁ * (1 - eqPrice m b₁ b₂ / p)

private noncomputable def trajX1 (m b₁ b₂ p : ℝ) : ℝ :=
  if p ≤ entryPrice m b₁ then 0
  else if p ≤ eqPrice m b₁ b₂ then m - b₁ / p
  else (m - b₁ / eqPrice m b₁ b₂) +
    (b₁ / eqPrice m b₁ b₂) * (1 - (eqPrice m b₁ b₂ / p) ^ 2) / 2

private noncomputable def trajP1 (m b₁ b₂ p : ℝ) : ℝ :=
  if p ≤ entryPrice m b₁ then 0
  else if p ≤ eqPrice m b₁ b₂ then b₁ * Real.log (p * m / b₁)
  else (b₂ - b₁) + b₁ * (1 - eqPrice m b₁ b₂ / p)

private noncomputable def trajSupply (m b₁ b₂ p : ℝ) : ℝ :=
  if p ≤ entryPrice m b₁ then m
  else if p ≤ eqPrice m b₁ b₂ then b₁ / p
  else (b₁ / eqPrice m b₁ b₂) * (eqPrice m b₁ b₂ / p) ^ 2

private noncomputable def orderedClinching (m b₁ b₂ v₁ v₂ : ℝ) : Outcome (Fin 2) :=
  if v₁ < v₂ then
    { alloc := ![trajX0 m b₁ b₂ v₁, trajX1 m b₁ b₂ v₁ + trajSupply m b₁ b₂ v₁]
      payment := ![trajP0 m b₁ b₂ v₁, trajP1 m b₁ b₂ v₁ + v₁ * trajSupply m b₁ b₂ v₁] }
  else if v₂ < v₁ then
    { alloc := ![trajX0 m b₁ b₂ v₂ + trajSupply m b₁ b₂ v₂, trajX1 m b₁ b₂ v₂]
      payment := ![trajP0 m b₁ b₂ v₂ + v₂ * trajSupply m b₁ b₂ v₂, trajP1 m b₁ b₂ v₂] }
  else if v₁ = 0 then
    { alloc := ![0, 0]
      payment := ![0, 0] }
  else
    { alloc := ![trajX0 m b₁ b₂ v₁ + trajSupply m b₁ b₂ v₁ / 2,
        trajX1 m b₁ b₂ v₁ + trajSupply m b₁ b₂ v₁ / 2]
      payment := ![trajP0 m b₁ b₂ v₁ + v₁ * (trajSupply m b₁ b₂ v₁ / 2),
        trajP1 m b₁ b₂ v₁ + v₁ * (trajSupply m b₁ b₂ v₁ / 2)] }

/-- **Continuous 2-bidder adaptive clinching auction** ([DobzinskiLaviNisan2012], primary PDF not
inspected): given divisible supply `m > 0`, fixed public budgets `B : Fin 2 → ℝ` (`0 < B i`), and
nonnegative valuations `v : Fin 2 → ℝ`, runs the closed-form 3-phase continuous adaptive clinching
trajectory until `min (v 0) (v 1)` and assigns the remaining supply to the higher bidder (splitting
evenly on positive ties, and outputting `(0, 0)` when `v 0 = v 1 = 0`). -/
noncomputable def twoBidderClinching (m : ℝ) (B v : Fin 2 → ℝ) : Outcome (Fin 2) :=
  if B 0 ≤ B 1 then
    orderedClinching m (B 0) (B 1) (v 0) (v 1)
  else
    swapOutcome (orderedClinching m (B 1) (B 0) (v 1) (v 0))

/-- `twoBidderClinching` as a `BudgetedMechanism (Fin 2)` when budgets are also reported. -/
@[expose] noncomputable def twoBidderClinchingMechanism (m : ℝ) : BudgetedMechanism (Fin 2) where
  outcome θ := twoBidderClinching m (fun i => (θ i).budget) (fun i => (θ i).val)

/-- `twoBidderClinching` as a `SingleParameter.Mechanism (Fin 2)` for fixed public budgets `B`. -/
@[expose] noncomputable def twoBidderClinchingSP (m : ℝ) (B : Fin 2 → ℝ) :
    SingleParameter.Mechanism (Fin 2) :=
  (twoBidderClinchingMechanism m).toSingleParameter B

/-- Symmetry under swapping the two bidders when `B 1 < B 0`. -/
theorem twoBidderClinching_swap (m : ℝ) {B v : Fin 2 → ℝ} (h : B 1 < B 0) (i : Fin 2) :
    (twoBidderClinching m B v).alloc i =
      (twoBidderClinching m ![B 1, B 0] ![v 1, v 0]).alloc (Equiv.swap 0 1 i) ∧
    (twoBidderClinching m B v).payment i =
      (twoBidderClinching m ![B 1, B 0] ![v 1, v 0]).payment (Equiv.swap 0 1 i) := by
  have hnot : ¬ B 0 ≤ B 1 := not_le.mpr h
  have h1 : (![B 1, B 0] : Fin 2 → ℝ) 0 ≤ (![B 1, B 0] : Fin 2 → ℝ) 1 := h.le
  dsimp only [twoBidderClinching]
  simp only [ite_eq_right hnot, ite_eq_left h1, swapOutcome]
  have hb0 : (![B 1, B 0] : Fin 2 → ℝ) 0 = B 1 := rfl
  have hb1 : (![B 1, B 0] : Fin 2 → ℝ) 1 = B 0 := rfl
  have hv0 : (![v 1, v 0] : Fin 2 → ℝ) 0 = v 1 := rfl
  have hv1 : (![v 1, v 0] : Fin 2 → ℝ) 1 = v 0 := rfl
  rw [hb0, hb1, hv0, hv1]
  exact ⟨rfl, rfl⟩

/-- Phase-0 explicit evaluation: when `B 0 ≤ B 1` and `v 0 < v 1` with `v 0 ≤ B 0 / m`, bidder `1`
receives the full supply `m` at price `v 0`. -/
theorem twoBidderClinching_phase0_lt {m : ℝ} {B v : Fin 2 → ℝ}
    (hm : 0 < m) (hB0 : 0 < B 0) (hB : B 0 ≤ B 1)
    (h1 : v 0 < v 1) (hp : v 0 ≤ B 0 / m) :
    (twoBidderClinching m B v).alloc 0 = 0 ∧ (twoBidderClinching m B v).alloc 1 = m ∧
      (twoBidderClinching m B v).payment 0 = 0 ∧
      (twoBidderClinching m B v).payment 1 = v 0 * m := by
  have hpe : B 0 / m ≤ eqPrice m (B 0) (B 1) := by
    have hexp : 1 ≤ Real.exp ((B 1 - B 0) / B 0) :=
      Real.one_le_exp (div_nonneg (sub_nonneg.mpr hB) hB0.le)
    have hpos : 0 < B 0 / m := div_pos hB0 hm
    dsimp only [eqPrice, entryPrice]; nlinarith
  have hle_e : v 0 ≤ eqPrice m (B 0) (B 1) := hp.trans hpe
  dsimp only [twoBidderClinching]
  rw [ite_eq_left hB]
  dsimp only [orderedClinching]
  rw [ite_eq_left h1]
  simp only [trajX0, trajX1, trajP0, trajP1, trajSupply, entryPrice, Matrix.cons_val_zero,
    Matrix.cons_val_one, hle_e, hp, ↓reduceIte, zero_add, and_self]

/-- Zero-bid explicit evaluation: when `v 0 = 0` and `v 1 = 0`, both allocations and payments are
`0`. -/
theorem twoBidderClinching_zero_zero (m : ℝ) (B : Fin 2 → ℝ) :
    twoBidderClinching m B ![0, 0] = ⟨![0, 0], ![0, 0]⟩ := by
  ext i <;> fin_cases i <;>
    (dsimp only [twoBidderClinching]; split_ifs <;>
      simp [orderedClinching, swapOutcome])

private theorem entryPrice_pos {m b₁ : ℝ} (hm : 0 < m) (hb₁ : 0 < b₁) :
    0 < entryPrice m b₁ :=
  div_pos hb₁ hm

private theorem entryPrice_le_eqPrice {m b₁ b₂ : ℝ} (hm : 0 < m) (hb₁ : 0 < b₁) (hle : b₁ ≤ b₂) :
    entryPrice m b₁ ≤ eqPrice m b₁ b₂ := by
  have hexp : 1 ≤ Real.exp ((b₂ - b₁) / b₁) :=
    Real.one_le_exp (div_nonneg (sub_nonneg.mpr hle) hb₁.le)
  have hp₀ := entryPrice_pos hm hb₁
  dsimp only [eqPrice]
  nlinarith

private theorem eqPrice_pos {m b₁ b₂ : ℝ} (hm : 0 < m) (hb₁ : 0 < b₁) :
    0 < eqPrice m b₁ b₂ :=
  mul_pos (entryPrice_pos hm hb₁) (Real.exp_pos _)

private theorem log_eqPrice {m b₁ b₂ : ℝ} (hm : 0 < m) (hb₁ : 0 < b₁) :
    b₁ * Real.log (eqPrice m b₁ b₂ * m / b₁) = b₂ - b₁ := by
  have harg : eqPrice m b₁ b₂ * m / b₁ = Real.exp ((b₂ - b₁) / b₁) := by
    dsimp only [eqPrice, entryPrice]
    field_simp [hm.ne', hb₁.ne']
  rw [harg, Real.log_exp]
  field_simp [hb₁.ne']

/-- Monotonicity and envelope payment sandwich `(x q - x p) * p ≤ pay q - pay p ≤ (x q - x p) * q`
on `[0, ∞)`. -/
private def IsEnvCurve (x pay : ℝ → ℝ) : Prop :=
  (∀ ⦃p q : ℝ⦄, 0 ≤ p → p ≤ q → x p ≤ x q) ∧
  (∀ ⦃p q : ℝ⦄, 0 ≤ p → p ≤ q →
    p * (x q - x p) ≤ pay q - pay p ∧ pay q - pay p ≤ q * (x q - x p))

private theorem env_trans {x pay : ℝ → ℝ} {p r q : ℝ} (hpr : p ≤ r) (hrq : r ≤ q)
    (hxp : x p ≤ x r) (hxr : x r ≤ x q)
    (h1 : p * (x r - x p) ≤ pay r - pay p ∧ pay r - pay p ≤ r * (x r - x p))
    (h2 : r * (x q - x r) ≤ pay q - pay r ∧ pay q - pay r ≤ q * (x q - x r)) :
    p * (x q - x p) ≤ pay q - pay p ∧ pay q - pay p ≤ q * (x q - x p) := by
  have hdx1 : 0 ≤ x r - x p := sub_nonneg.mpr hxp
  have hdx2 : 0 ≤ x q - x r := sub_nonneg.mpr hxr
  refine ⟨?_, ?_⟩
  · have : p * (x q - x r) ≤ r * (x q - x r) := mul_le_mul_of_nonneg_right hpr hdx2
    linarith [h1.1, h2.1]
  · have : r * (x r - x p) ≤ q * (x r - x p) := mul_le_mul_of_nonneg_right hrq hdx1
    linarith [h1.2, h2.2]

private theorem phase2_sandwich {b₁ pe p q : ℝ} (hb₁ : 0 < b₁) (hpe : 0 < pe)
    (hp : pe ≤ p) (hpq : p ≤ q) :
    let dx := fun t : ℝ => (b₁ / pe) * (1 - (pe / t) ^ 2) / 2
    let dp := fun t : ℝ => b₁ * (1 - pe / t)
    dx p ≤ dx q ∧
      p * (dx q - dx p) ≤ dp q - dp p ∧ dp q - dp p ≤ q * (dx q - dx p) := by
  intro dx dp
  have hp_pos : 0 < p := lt_of_lt_of_le hpe hp
  have hq_pos : 0 < q := lt_of_lt_of_le hp_pos hpq
  have hdiff_x : dx q - dx p = b₁ * pe * (q - p) * (q + p) / (2 * p ^ 2 * q ^ 2) := by
    dsimp only [dx]; field_simp [hpe.ne', hp_pos.ne', hq_pos.ne']; ring
  have hdiff_p : dp q - dp p = b₁ * pe * (q - p) / (p * q) := by
    dsimp only [dp]; field_simp [hp_pos.ne', hq_pos.ne']; ring
  have hqp_nn : 0 ≤ q - p := sub_nonneg.mpr hpq
  refine ⟨?_, ?_, ?_⟩
  · rw [← sub_nonneg, hdiff_x]; positivity
  · rw [← sub_nonneg, hdiff_x, hdiff_p]
    have heq : b₁ * pe * (q - p) / (p * q) -
        p * (b₁ * pe * (q - p) * (q + p) / (2 * p ^ 2 * q ^ 2)) =
        b₁ * pe * (q - p) ^ 2 / (2 * p * q ^ 2) := by
      field_simp [hp_pos.ne', hq_pos.ne']; ring
    rw [heq]; positivity
  · rw [← sub_nonneg, hdiff_x, hdiff_p]
    have heq : q * (b₁ * pe * (q - p) * (q + p) / (2 * p ^ 2 * q ^ 2)) -
        b₁ * pe * (q - p) / (p * q) =
        b₁ * pe * (q - p) ^ 2 / (2 * p ^ 2 * q) := by
      field_simp [hp_pos.ne', hq_pos.ne']; ring
    rw [heq]; positivity

private theorem phase1_sandwich {m b₁ p q : ℝ} (hm : 0 < m) (hb₁ : 0 < b₁)
    (hp : 0 < p) (hpq : p ≤ q) :
    let x := fun t : ℝ => m - b₁ / t
    let pay := fun t : ℝ => b₁ * Real.log (t * m / b₁)
    x p ≤ x q ∧
      p * (x q - x p) ≤ pay q - pay p ∧ pay q - pay p ≤ q * (x q - x p) := by
  intro x pay
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have hratio_pos : 0 < q / p := div_pos hq hp
  have hlog_diff : Real.log (q * m / b₁) - Real.log (p * m / b₁) = Real.log (q / p) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1; field_simp [hm.ne', hb₁.ne', hp.ne']
  have hdp : pay q - pay p = b₁ * Real.log (q / p) := by
    dsimp only [pay]; rw [← mul_sub, hlog_diff]
  have hdx : x q - x p = b₁ * (1 / p - 1 / q) := by
    dsimp only [x]; field_simp [hp.ne', hq.ne']; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [← sub_nonneg, hdx]
    exact mul_nonneg hb₁.le (sub_nonneg.mpr (one_div_le_one_div_of_le hp hpq))
  · rw [hdp, hdx]
    have hmul : p * (b₁ * (1 / p - 1 / q)) = b₁ * (1 - (q / p)⁻¹) := by
      field_simp [hp.ne', hq.ne']
    rw [hmul]
    exact mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hratio_pos) hb₁.le
  · rw [hdp, hdx]
    have hmul : q * (b₁ * (1 / p - 1 / q)) = b₁ * (q / p - 1) := by
      field_simp [hp.ne', hq.ne']
    rw [hmul]
    exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hratio_pos) hb₁.le

private theorem traj0_isEnvCurve {m b₁ b₂ : ℝ} (hm : 0 < m) (hb₁ : 0 < b₁) :
    IsEnvCurve (trajX0 m b₁ b₂) (trajP0 m b₁ b₂) := by
  set pe := eqPrice m b₁ b₂
  have hpe : 0 < pe := eqPrice_pos hm hb₁
  have hx_pe : (b₁ / pe) * (1 - (pe / pe) ^ 2) / 2 = 0 := by rw [div_self hpe.ne']; ring
  have hp_pe : b₁ * (1 - pe / pe) = 0 := by rw [div_self hpe.ne']; ring
  have hmono : ∀ ⦃p q : ℝ⦄, 0 ≤ p → p ≤ q → trajX0 m b₁ b₂ p ≤ trajX0 m b₁ b₂ q := by
    intro p q _ hpq
    by_cases hp : p ≤ pe <;> by_cases hq : q ≤ pe
    · dsimp only [trajX0]; rw [ite_eq_left hp, ite_eq_left hq]
    · have hs := (phase2_sandwich hb₁ hpe le_rfl (lt_of_not_ge hq).le).1
      dsimp only [trajX0]; rw [ite_eq_left hp, ite_eq_right hq]
      linarith [hx_pe]
    · exact absurd (hpq.trans hq) hp
    · dsimp only [trajX0]; rw [ite_eq_right hp, ite_eq_right hq]
      exact (phase2_sandwich hb₁ hpe (le_of_not_ge hp) hpq).1
  refine ⟨hmono, fun {p q} _ hpq => ?_⟩
  by_cases hp : p ≤ pe <;> by_cases hq : q ≤ pe
  · have hx_p : trajX0 m b₁ b₂ p = 0 := ite_eq_left hp
    have hx_q : trajX0 m b₁ b₂ q = 0 := ite_eq_left hq
    have hp_p : trajP0 m b₁ b₂ p = 0 := ite_eq_left hp
    have hp_q : trajP0 m b₁ b₂ q = 0 := ite_eq_left hq
    rw [hx_p, hx_q, hp_p, hp_q]; simp
  · have hq_gt : pe < q := lt_of_not_ge hq
    have hph := phase2_sandwich hb₁ hpe le_rfl hq_gt.le
    have hzero : trajX0 m b₁ b₂ pe = 0 ∧ trajP0 m b₁ b₂ pe = 0 :=
      ⟨ite_eq_left le_rfl, ite_eq_left le_rfl⟩
    have hpz : trajX0 m b₁ b₂ p = 0 ∧ trajP0 m b₁ b₂ p = 0 :=
      ⟨ite_eq_left hp, ite_eq_left hp⟩
    have hq_x : trajX0 m b₁ b₂ q = (b₁ / pe) * (1 - (pe / q) ^ 2) / 2 := ite_eq_right hq
    have hq_p : trajP0 m b₁ b₂ q = b₁ * (1 - pe / q) := ite_eq_right hq
    have h2x : trajX0 m b₁ b₂ pe ≤ trajX0 m b₁ b₂ q := by
      rw [hzero.1, hq_x]; linarith [hph.1, hx_pe]
    refine env_trans hp hq_gt.le (by rw [hpz.1, hzero.1]) h2x
      (by rw [hpz.1, hpz.2, hzero.1, hzero.2]; simp) ?_
    rw [hzero.1, hzero.2, hq_x, hq_p]
    have h1 := hph.2.1; have h2 := hph.2.2
    dsimp only at h1 h2
    rw [div_self hpe.ne'] at h1 h2
    exact ⟨by linarith, by linarith⟩
  · exact absurd (hpq.trans hq) hp
  · have hpx : trajX0 m b₁ b₂ p = (b₁ / pe) * (1 - (pe / p) ^ 2) / 2 := ite_eq_right hp
    have hqx : trajX0 m b₁ b₂ q = (b₁ / pe) * (1 - (pe / q) ^ 2) / 2 := ite_eq_right hq
    have hpp : trajP0 m b₁ b₂ p = b₁ * (1 - pe / p) := ite_eq_right hp
    have hqp : trajP0 m b₁ b₂ q = b₁ * (1 - pe / q) := ite_eq_right hq
    rw [hpx, hqx, hpp, hqp]
    exact (phase2_sandwich hb₁ hpe (le_of_not_ge hp) hpq).2

private theorem traj1_eval_p0 {m b₁ : ℝ} (hm : 0 < m) (hb₁ : 0 < b₁) :
    m - b₁ / entryPrice m b₁ = 0 ∧
      b₁ * Real.log (entryPrice m b₁ * m / b₁) = 0 := by
  dsimp only [entryPrice]
  refine ⟨by field_simp [hm.ne', hb₁.ne']; ring, ?_⟩
  have h : b₁ / m * m / b₁ = 1 := by field_simp [hm.ne', hb₁.ne']
  rw [h, Real.log_one, mul_zero]

private theorem traj1_isEnvCurve {m b₁ b₂ : ℝ} (hm : 0 < m) (hb₁ : 0 < b₁) (hle : b₁ ≤ b₂) :
    IsEnvCurve (trajX1 m b₁ b₂) (trajP1 m b₁ b₂) := by
  set p₀ := entryPrice m b₁
  set pe := eqPrice m b₁ b₂
  have hp₀_pos : 0 < p₀ := entryPrice_pos hm hb₁
  have hpe_pos : 0 < pe := eqPrice_pos hm hb₁
  have hp₀_le : p₀ ≤ pe := entryPrice_le_eqPrice hm hb₁ hle
  obtain ⟨hx0_eq, hp0_eq⟩ := traj1_eval_p0 hm hb₁
  have hlog_pe : b₁ * Real.log (pe * m / b₁) = b₂ - b₁ := log_eqPrice hm hb₁
  have hx1_p0 : trajX1 m b₁ b₂ p₀ = 0 := ite_eq_left le_rfl
  have hp1_p0 : trajP1 m b₁ b₂ p₀ = 0 := ite_eq_left le_rfl
  have hx1_pe : trajX1 m b₁ b₂ pe = m - b₁ / pe := by
    by_cases he : pe ≤ p₀
    · have hpeq : pe = p₀ := le_antisymm he hp₀_le
      rw [hpeq, hx1_p0, hx0_eq]
    · dsimp only [trajX1]; rw [ite_eq_right he, ite_eq_left le_rfl]
  have hp1_pe : trajP1 m b₁ b₂ pe = b₂ - b₁ := by
    by_cases he : pe ≤ p₀
    · have hpeq : pe = p₀ := le_antisymm he hp₀_le
      rw [hpeq, hp1_p0, ← hlog_pe, hpeq, hp0_eq]
    · dsimp only [trajP1]; rw [ite_eq_right he, ite_eq_left le_rfl, hlog_pe]
  have hband1 : ∀ {p q : ℝ}, p₀ ≤ p → p ≤ q → q ≤ pe →
      trajX1 m b₁ b₂ p ≤ trajX1 m b₁ b₂ q ∧
        p * (trajX1 m b₁ b₂ q - trajX1 m b₁ b₂ p) ≤ trajP1 m b₁ b₂ q - trajP1 m b₁ b₂ p ∧
        trajP1 m b₁ b₂ q - trajP1 m b₁ b₂ p ≤ q * (trajX1 m b₁ b₂ q - trajX1 m b₁ b₂ p) := by
    intro p q hpp hpq hqp
    have eval_eq : ∀ t, p₀ ≤ t → t ≤ pe →
        trajX1 m b₁ b₂ t = m - b₁ / t ∧ trajP1 m b₁ b₂ t = b₁ * Real.log (t * m / b₁) := by
      intro t ht1 ht2
      by_cases hle0 : t ≤ p₀
      · have ht : t = p₀ := le_antisymm hle0 ht1
        subst ht; exact ⟨by rw [hx1_p0, hx0_eq], by rw [hp1_p0, hp0_eq]⟩
      · exact ⟨by dsimp only [trajX1]; rw [ite_eq_right hle0, ite_eq_left ht2],
          by dsimp only [trajP1]; rw [ite_eq_right hle0, ite_eq_left ht2]⟩
    obtain ⟨hxp, hpp'⟩ := eval_eq p hpp (hpq.trans hqp)
    obtain ⟨hxq, hpq'⟩ := eval_eq q (hpp.trans hpq) hqp
    rw [hxp, hxq, hpp', hpq']
    exact phase1_sandwich hm hb₁ (lt_of_lt_of_le hp₀_pos hpp) hpq
  have hband2 : ∀ {p q : ℝ}, pe ≤ p → p ≤ q →
      trajX1 m b₁ b₂ p ≤ trajX1 m b₁ b₂ q ∧
        p * (trajX1 m b₁ b₂ q - trajX1 m b₁ b₂ p) ≤ trajP1 m b₁ b₂ q - trajP1 m b₁ b₂ p ∧
        trajP1 m b₁ b₂ q - trajP1 m b₁ b₂ p ≤ q * (trajX1 m b₁ b₂ q - trajX1 m b₁ b₂ p) := by
    intro p q hpp hpq
    have eval_eq : ∀ t, pe ≤ t →
        trajX1 m b₁ b₂ t = (m - b₁ / pe) + (b₁ / pe) * (1 - (pe / t) ^ 2) / 2 ∧
          trajP1 m b₁ b₂ t = (b₂ - b₁) + b₁ * (1 - pe / t) := by
      intro t ht
      by_cases hte : t ≤ pe
      · have hteq : t = pe := le_antisymm hte ht
        subst hteq; rw [div_self hpe_pos.ne']
        exact ⟨by rw [hx1_pe]; ring, by rw [hp1_pe]; ring⟩
      · have hnot0 : ¬ t ≤ p₀ := fun h => hte (h.trans hp₀_le)
        exact ⟨by dsimp only [trajX1]; rw [ite_eq_right hnot0, ite_eq_right hte],
          by dsimp only [trajP1]; rw [ite_eq_right hnot0, ite_eq_right hte]⟩
    obtain ⟨hxp, hpp'⟩ := eval_eq p hpp
    obtain ⟨hxq, hpq'⟩ := eval_eq q (hpp.trans hpq)
    have hph := phase2_sandwich hb₁ hpe_pos hpp hpq
    rw [hxp, hxq, hpp', hpq']
    exact ⟨by linarith [hph.1], by linarith [hph.2.1], by linarith [hph.2.2]⟩
  have hall : ∀ {p q : ℝ}, p ≤ q →
      trajX1 m b₁ b₂ p ≤ trajX1 m b₁ b₂ q ∧
        p * (trajX1 m b₁ b₂ q - trajX1 m b₁ b₂ p) ≤ trajP1 m b₁ b₂ q - trajP1 m b₁ b₂ p ∧
        trajP1 m b₁ b₂ q - trajP1 m b₁ b₂ p ≤ q * (trajX1 m b₁ b₂ q - trajX1 m b₁ b₂ p) := by
    intro p q hpq
    by_cases hp0 : p ≤ p₀
    · have hp_x0 : trajX1 m b₁ b₂ p = 0 := ite_eq_left hp0
      have hp_p0 : trajP1 m b₁ b₂ p = 0 := ite_eq_left hp0
      by_cases hq0 : q ≤ p₀
      · have hq_x0 : trajX1 m b₁ b₂ q = 0 := ite_eq_left hq0
        have hq_p0 : trajP1 m b₁ b₂ q = 0 := ite_eq_left hq0
        rw [hp_x0, hp_p0, hq_x0, hq_p0]; simp
      · have h0_le_q : p₀ ≤ q := (lt_of_not_ge hq0).le
        have hstep0 : p * (trajX1 m b₁ b₂ p₀ - trajX1 m b₁ b₂ p) ≤
            trajP1 m b₁ b₂ p₀ - trajP1 m b₁ b₂ p ∧
            trajP1 m b₁ b₂ p₀ - trajP1 m b₁ b₂ p ≤
              p₀ * (trajX1 m b₁ b₂ p₀ - trajX1 m b₁ b₂ p) := by
          rw [hp_x0, hp_p0, hx1_p0, hp1_p0]; simp
        by_cases hqe : q ≤ pe
        · have hb := hband1 le_rfl h0_le_q hqe
          refine ⟨le_trans (by rw [hp_x0, hx1_p0]) hb.1,
            env_trans hp0 h0_le_q (by rw [hp_x0, hx1_p0]) hb.1 hstep0 hb.2⟩
        · have hpe_le_q : pe ≤ q := (lt_of_not_ge hqe).le
          have hb1 := hband1 le_rfl hp₀_le le_rfl
          have hb2 := hband2 le_rfl hpe_le_q
          have hm1 := env_trans hp0 hp₀_le (by rw [hp_x0, hx1_p0]) hb1.1 hstep0 hb1.2
          refine ⟨le_trans (le_trans (by rw [hp_x0, hx1_p0]) hb1.1) hb2.1,
            env_trans (hp0.trans hp₀_le) hpe_le_q
              (le_trans (by rw [hp_x0, hx1_p0]) hb1.1) hb2.1 hm1 hb2.2⟩
    · have hp0_le_p : p₀ ≤ p := (lt_of_not_ge hp0).le
      by_cases hpe : p ≤ pe
      · by_cases hqe : q ≤ pe
        · exact hband1 hp0_le_p hpq hqe
        · have hpe_le_q : pe ≤ q := (lt_of_not_ge hqe).le
          have hb1 := hband1 hp0_le_p hpe le_rfl
          have hb2 := hband2 le_rfl hpe_le_q
          exact ⟨hb1.1.trans hb2.1, env_trans hpe hpe_le_q hb1.1 hb2.1 hb1.2 hb2.2⟩
      · exact hband2 (lt_of_not_ge hpe).le hpq
  exact ⟨fun {_ _} _ hpq => (hall hpq).1, fun {_ _} _ hpq => (hall hpq).2⟩

private theorem env_stop_dsic {x pay S : ℝ → ℝ} (henv : IsEnvCurve x pay)
    (hS : ∀ t, 0 ≤ t → 0 ≤ S t) {other v b : ℝ}
    (ho : 0 ≤ other) (hv : 0 ≤ v) (hb : 0 ≤ b) :
    let u := fun (z : ℝ) =>
      if z < other then v * x z - pay z
      else if other < z then v * (x other + S other) - (pay other + other * S other)
      else v * (x other + S other / 2) - (pay other + other * (S other / 2))
    u b ≤ u v := by
  intro u
  have hS0 : 0 ≤ S other := hS other ho
  have hs_le : ∀ z, 0 ≤ z → z ≤ v → v * x z - pay z ≤ v * x v - pay v := fun z hz hzv => by
    have := (henv.2 hz hzv).2; linarith
  have hs_ge : ∀ z, 0 ≤ z → v ≤ z → v * x z - pay z ≤ v * x v - pay v := fun z _ hvz => by
    have := (henv.2 hv hvz).1; linarith
  by_cases hlt : v < other
  · rw [show u v = v * x v - pay v from ite_eq_left hlt]
    by_cases hbl : b < other
    · rw [show u b = v * x b - pay b from ite_eq_left hbl]
      rcases le_total b v with hbv | hvb
      · exact hs_le b hb hbv
      · exact hs_ge b hb hvb
    · by_cases hbg : other < b
      · rw [show u b = v * (x other + S other) - (pay other + other * S other) from by
          dsimp only [u]; rw [ite_eq_right hbl, ite_eq_left hbg]]
        have : (v - other) * S other ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hS0
        linarith [hs_ge other ho hlt.le]
      · rw [show u b = v * (x other + S other / 2) - (pay other + other * (S other / 2)) from by
          dsimp only [u]; rw [ite_eq_right hbl, ite_eq_right hbg]]
        have : (v - other) * (S other / 2) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
        linarith [hs_ge other ho hlt.le]
  · by_cases hgt : other < v
    · rw [show u v = v * (x other + S other) - (pay other + other * S other) from by
        dsimp only [u]; rw [ite_eq_right hlt, ite_eq_left hgt]]
      by_cases hbl : b < other
      · rw [show u b = v * x b - pay b from ite_eq_left hbl]
        have hmon : x b ≤ x other := henv.1 hb hbl.le
        have hsand := (henv.2 hb hbl.le).2
        have hv_mul : other * (x other - x b) ≤ v * (x other - x b) :=
          mul_le_mul_of_nonneg_right hgt.le (sub_nonneg.mpr hmon)
        have hgain : 0 ≤ (v - other) * S other := mul_nonneg (sub_nonneg.mpr hgt.le) hS0
        linarith
      · by_cases hbg : other < b
        · rw [show u b = v * (x other + S other) - (pay other + other * S other) from by
            dsimp only [u]; rw [ite_eq_right hbl, ite_eq_left hbg]]
        · rw [show u b = v * (x other + S other / 2) - (pay other + other * (S other / 2)) from by
            dsimp only [u]; rw [ite_eq_right hbl, ite_eq_right hbg]]
          have hgain : 0 ≤ (v - other) * (S other / 2) :=
            mul_nonneg (sub_nonneg.mpr hgt.le) (by linarith)
          linarith
    · have heq : v = other := le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
      subst heq
      rw [show u v = v * x v - pay v from by
        dsimp only [u]; rw [ite_eq_right hlt, ite_eq_right hgt]; ring]
      by_cases hbl : b < v
      · rw [show u b = v * x b - pay b from ite_eq_left hbl]
        exact hs_le b hb hbl.le
      · by_cases hbg : v < b
        · rw [show u b = v * (x v + S v) - (pay v + v * S v) from by
            dsimp only [u]; rw [ite_eq_right hbl, ite_eq_left hbg]]; linarith
        · rw [show u b = v * (x v + S v / 2) - (pay v + v * (S v / 2)) from by
            dsimp only [u]; rw [ite_eq_right hbl, ite_eq_right hbg]]; linarith

/-- Bundled invariants of the both-active trajectory at price `p ≥ 0`. -/
private structure TrajInv (m b₁ b₂ p : ℝ) : Prop where
  x0_nn : 0 ≤ trajX0 m b₁ b₂ p
  x1_nn : 0 ≤ trajX1 m b₁ b₂ p
  sup_nn : 0 ≤ trajSupply m b₁ b₂ p
  p0_nn : 0 ≤ trajP0 m b₁ b₂ p
  p1_nn : 0 ≤ trajP1 m b₁ b₂ p
  sum_eq : trajX0 m b₁ b₂ p + trajX1 m b₁ b₂ p + trajSupply m b₁ b₂ p = m
  bf0 : trajP0 m b₁ b₂ p + p * trajSupply m b₁ b₂ p ≤ b₁
  bf1 : trajP1 m b₁ b₂ p + p * trajSupply m b₁ b₂ p ≤ b₂
  exh0 : entryPrice m b₁ < p → trajP0 m b₁ b₂ p + p * trajSupply m b₁ b₂ p = b₁
  exh1 : eqPrice m b₁ b₂ < p → trajP1 m b₁ b₂ p + p * trajSupply m b₁ b₂ p = b₂

private theorem traj_invariants {m b₁ b₂ p : ℝ} (hm : 0 < m) (hb₁ : 0 < b₁) (hle : b₁ ≤ b₂) :
    TrajInv m b₁ b₂ p := by
  set p₀ := entryPrice m b₁
  set pe := eqPrice m b₁ b₂
  have hp₀_pos : 0 < p₀ := entryPrice_pos hm hb₁
  have hpe_pos : 0 < pe := eqPrice_pos hm hb₁
  have hp₀_le : p₀ ≤ pe := entryPrice_le_eqPrice hm hb₁ hle
  by_cases h0 : p ≤ p₀
  · have he : p ≤ pe := h0.trans hp₀_le
    have hx0 : trajX0 m b₁ b₂ p = 0 := ite_eq_left he
    have hx1 : trajX1 m b₁ b₂ p = 0 := ite_eq_left h0
    have hp0 : trajP0 m b₁ b₂ p = 0 := ite_eq_left he
    have hp1 : trajP1 m b₁ b₂ p = 0 := ite_eq_left h0
    have hS : trajSupply m b₁ b₂ p = m := ite_eq_left h0
    have hpm : p * m ≤ b₁ := by
      have : p * m ≤ p₀ * m := mul_le_mul_of_nonneg_right h0 hm.le
      have hp0m : p₀ * m = b₁ := div_mul_cancel₀ b₁ hm.ne'
      linarith
    exact ⟨by rw [hx0], by rw [hx1], by rw [hS]; exact hm.le, by rw [hp0], by rw [hp1],
      by rw [hx0, hx1, hS]; ring, by rw [hp0, hS]; linarith, by rw [hp1, hS]; linarith,
      fun h => absurd h (not_lt.mpr h0), fun h => absurd h (not_lt.mpr he)⟩
  · have hp_gt0 : p₀ < p := lt_of_not_ge h0
    have hp_pos : 0 < p := hp₀_pos.trans hp_gt0
    by_cases he : p ≤ pe
    · have hx0 : trajX0 m b₁ b₂ p = 0 := ite_eq_left he
      have hx1 : trajX1 m b₁ b₂ p = m - b₁ / p := by
        dsimp only [trajX1]; rw [ite_eq_right h0, ite_eq_left he]
      have hp0 : trajP0 m b₁ b₂ p = 0 := ite_eq_left he
      have hp1 : trajP1 m b₁ b₂ p = b₁ * Real.log (p * m / b₁) := by
        dsimp only [trajP1]; rw [ite_eq_right h0, ite_eq_left he]
      have hS : trajSupply m b₁ b₂ p = b₁ / p := by
        dsimp only [trajSupply]; rw [ite_eq_right h0, ite_eq_left he]
      have hb1_eq : b₁ = p₀ * m := (div_mul_cancel₀ b₁ hm.ne').symm
      have hx1_nn : 0 ≤ m - b₁ / p := by
        have : b₁ / p ≤ m := (div_le_iff₀ hp_pos).mpr (by nlinarith)
        linarith
      have harg_ge : 1 ≤ p * m / b₁ := (one_le_div hb₁).mpr (by nlinarith)
      have hlog_le : Real.log (p * m / b₁) ≤ Real.log (pe * m / b₁) :=
        Real.log_le_log (by positivity) (by gcongr)
      have hp1_le : b₁ * Real.log (p * m / b₁) ≤ b₂ - b₁ :=
        (mul_le_mul_of_nonneg_left hlog_le hb₁.le).trans_eq (log_eqPrice hm hb₁)
      have hmul_b : p * (b₁ / p) = b₁ := mul_div_cancel₀ b₁ hp_pos.ne'
      exact ⟨by rw [hx0], by rw [hx1]; exact hx1_nn, by rw [hS]; exact div_nonneg hb₁.le hp_pos.le,
        by rw [hp0], by rw [hp1]; exact mul_nonneg hb₁.le (Real.log_nonneg harg_ge),
        by rw [hx0, hx1, hS]; ring, by rw [hp0, hS, hmul_b]; linarith,
        by rw [hp1, hS, hmul_b]; linarith, fun _ => by rw [hp0, hS, hmul_b]; ring,
        fun h => absurd h (not_lt.mpr he)⟩
    · have hp_gte : pe < p := lt_of_not_ge he
      have hx0 : trajX0 m b₁ b₂ p = (b₁ / pe) * (1 - (pe / p) ^ 2) / 2 := ite_eq_right he
      have hx1 : trajX1 m b₁ b₂ p = (m - b₁ / pe) + (b₁ / pe) * (1 - (pe / p) ^ 2) / 2 := by
        dsimp only [trajX1]; rw [ite_eq_right h0, ite_eq_right he]
      have hp0 : trajP0 m b₁ b₂ p = b₁ * (1 - pe / p) := ite_eq_right he
      have hp1 : trajP1 m b₁ b₂ p = (b₂ - b₁) + b₁ * (1 - pe / p) := by
        dsimp only [trajP1]; rw [ite_eq_right h0, ite_eq_right he]
      have hS : trajSupply m b₁ b₂ p = (b₁ / pe) * (pe / p) ^ 2 := by
        dsimp only [trajSupply]; rw [ite_eq_right h0, ite_eq_right he]
      have hfrac_lt : pe / p < 1 := (div_lt_one hp_pos).mpr hp_gte
      have hsq_le : (pe / p) ^ 2 ≤ 1 := by nlinarith [div_nonneg hpe_pos.le hp_pos.le]
      have hdx_nn : 0 ≤ b₁ / pe * (1 - (pe / p) ^ 2) / 2 :=
        div_nonneg (mul_nonneg (div_nonneg hb₁.le hpe_pos.le) (sub_nonneg.mpr hsq_le)) (by norm_num)
      have hb1_eq : b₁ = p₀ * m := (div_mul_cancel₀ b₁ hm.ne').symm
      have hm_ge : 0 ≤ m - b₁ / pe := by
        have : b₁ / pe ≤ m := (div_le_iff₀ hpe_pos).mpr (by nlinarith)
        linarith
      have hdp_nn : 0 ≤ b₁ * (1 - pe / p) := mul_nonneg hb₁.le (sub_nonneg.mpr hfrac_lt.le)
      have hps : p * ((b₁ / pe) * (pe / p) ^ 2) = b₁ * (pe / p) := by
        field_simp [hpe_pos.ne', hp_pos.ne']
      exact ⟨by rw [hx0]; exact hdx_nn, by rw [hx1]; exact add_nonneg hm_ge hdx_nn,
        by rw [hS]; positivity, by rw [hp0]; exact hdp_nn,
        by rw [hp1]; exact add_nonneg (sub_nonneg.mpr hle) hdp_nn,
        by rw [hx0, hx1, hS]; ring, by rw [hp0, hS, hps]; linarith,
        by rw [hp1, hS, hps]; linarith, fun _ => by rw [hp0, hS, hps]; ring,
        fun _ => by rw [hp1, hS, hps]; ring⟩

private theorem orderedClinching_zero_vals {m b₁ b₂ : ℝ} (hm : 0 < m) (hb₁ : 0 < b₁) :
    trajX0 m b₁ b₂ 0 = 0 ∧ trajP0 m b₁ b₂ 0 = 0 ∧
      trajX1 m b₁ b₂ 0 = 0 ∧ trajP1 m b₁ b₂ 0 = 0 := by
  have hp₀ : (0 : ℝ) ≤ entryPrice m b₁ := (entryPrice_pos hm hb₁).le
  have hpe : (0 : ℝ) ≤ eqPrice m b₁ b₂ := (eqPrice_pos hm hb₁).le
  exact ⟨ite_eq_left hpe, ite_eq_left hpe, ite_eq_left hp₀, ite_eq_left hp₀⟩

private structure OrderedProps (m b₁ b₂ v₁ v₂ : ℝ) : Prop where
  feas : (orderedClinching m b₁ b₂ v₁ v₂).IsFeasible m
  nonneg : (orderedClinching m b₁ b₂ v₁ v₂).HasNonnegPayment
  bf : (orderedClinching m b₁ b₂ v₁ v₂).IsBudgetFeasible ![b₁, b₂]
  ir : (orderedClinching m b₁ b₂ v₁ v₂).IsIR ![v₁, v₂]
  po : (orderedClinching m b₁ b₂ v₁ v₂).IsParetoOptimal m ![v₁, v₂] ![b₁, b₂]

private theorem orderedClinching_props {m b₁ b₂ v₁ v₂ : ℝ} (hm : 0 < m)
    (hb₁ : 0 < b₁) (hle : b₁ ≤ b₂) (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂) :
    OrderedProps m b₁ b₂ v₁ v₂ := by
  have he0 := traj0_isEnvCurve (b₂ := b₂) hm hb₁
  have he1 := traj1_isEnvCurve hm hb₁ hle
  obtain ⟨hzx0, hzp0, hzx1, hzp1⟩ := orderedClinching_zero_vals (b₂ := b₂) hm hb₁
  have hir_p0 : ∀ p, 0 ≤ p → trajP0 m b₁ b₂ p ≤ p * trajX0 m b₁ b₂ p := fun p hp => by
    have h := (he0.2 le_rfl hp).2; rw [hzx0, hzp0, sub_zero, sub_zero] at h; exact h
  have hir_p1 : ∀ p, 0 ≤ p → trajP1 m b₁ b₂ p ≤ p * trajX1 m b₁ b₂ p := fun p hp => by
    have h := (he1.2 le_rfl hp).2; rw [hzx1, hzp1, sub_zero, sub_zero] at h; exact h
  have hv_nn : ∀ i : Fin 2, 0 ≤ (![v₁, v₂] : Fin 2 → ℝ) i := fun i => by fin_cases i <;> assumption
  by_cases hlt : v₁ < v₂
  · have inv : TrajInv m b₁ b₂ v₁ := traj_invariants hm hb₁ hle
    have ho : orderedClinching m b₁ b₂ v₁ v₂ =
        ⟨![trajX0 m b₁ b₂ v₁, trajX1 m b₁ b₂ v₁ + trajSupply m b₁ b₂ v₁],
         ![trajP0 m b₁ b₂ v₁, trajP1 m b₁ b₂ v₁ + v₁ * trajSupply m b₁ b₂ v₁]⟩ := ite_eq_left hlt
    have hfeas : (orderedClinching m b₁ b₂ v₁ v₂).IsFeasible m := by
      rw [ho]
      refine ⟨fun i => ?_, by simp [Fin.sum_univ_two]; linarith [inv.sum_eq]⟩
      fin_cases i
      · exact inv.x0_nn
      · exact add_nonneg inv.x1_nn inv.sup_nn
    have hnn : (orderedClinching m b₁ b₂ v₁ v₂).HasNonnegPayment := fun i => by
      rw [ho]; fin_cases i
      · exact inv.p0_nn
      · exact add_nonneg inv.p1_nn (mul_nonneg hv₁ inv.sup_nn)
    have hbf : (orderedClinching m b₁ b₂ v₁ v₂).IsBudgetFeasible ![b₁, b₂] := fun i => by
      rw [ho]; fin_cases i
      · simp; linarith [inv.bf0, mul_nonneg hv₁ inv.sup_nn]
      · exact inv.bf1
    have hir : (orderedClinching m b₁ b₂ v₁ v₂).IsIR ![v₁, v₂] := fun i => by
      rw [ho]; fin_cases i
      · simp [Outcome.utility]; linarith [hir_p0 v₁ hv₁]
      · have h1 : v₁ * trajX1 m b₁ b₂ v₁ ≤ v₂ * trajX1 m b₁ b₂ v₁ :=
          mul_le_mul_of_nonneg_right hlt.le inv.x1_nn
        have h2 : v₁ * trajSupply m b₁ b₂ v₁ ≤ v₂ * trajSupply m b₁ b₂ v₁ :=
          mul_le_mul_of_nonneg_right hlt.le inv.sup_nn
        simp [Outcome.utility]; linarith [hir_p1 v₁ hv₁]
    have hpo : (orderedClinching m b₁ b₂ v₁ v₂).IsParetoOptimal m ![v₁, v₂] ![b₁, b₂] := by
      rw [Outcome.isParetoOptimal_iff hv_nn hfeas hbf, ho]
      refine ⟨fun _ => ⟨by simp [Fin.sum_univ_two]; linarith [inv.sum_eq], fun i hi => ?_⟩,
        fun i j hi hij => ?_⟩
      · fin_cases i
        · have hi0 : v₁ = 0 := hi
          exact by rw [hi0]; exact hzx0
        · have hi1 : v₂ = 0 := hi; linarith
      · fin_cases i <;> fin_cases j
        · exact absurd hij (lt_irrefl _)
        · have hpos0 : 0 < trajX0 m b₁ b₂ v₁ := hi
          have hgt : eqPrice m b₁ b₂ < v₁ := by
            by_contra hle_pe
            have h0 : trajX0 m b₁ b₂ v₁ = 0 := ite_eq_left (not_lt.mp hle_pe)
            linarith
          exact inv.exh1 hgt
        · have hij' : v₂ < v₁ := hij; linarith
        · exact absurd hij (lt_irrefl _)
    exact ⟨hfeas, hnn, hbf, hir, hpo⟩
  · by_cases hgt : v₂ < v₁
    · have inv : TrajInv m b₁ b₂ v₂ := traj_invariants hm hb₁ hle
      have ho : orderedClinching m b₁ b₂ v₁ v₂ =
          ⟨![trajX0 m b₁ b₂ v₂ + trajSupply m b₁ b₂ v₂, trajX1 m b₁ b₂ v₂],
           ![trajP0 m b₁ b₂ v₂ + v₂ * trajSupply m b₁ b₂ v₂, trajP1 m b₁ b₂ v₂]⟩ := by
        dsimp only [orderedClinching]; rw [ite_eq_right hlt, ite_eq_left hgt]
      have hfeas : (orderedClinching m b₁ b₂ v₁ v₂).IsFeasible m := by
        rw [ho]
        refine ⟨fun i => ?_, by simp [Fin.sum_univ_two]; linarith [inv.sum_eq]⟩
        fin_cases i
        · exact add_nonneg inv.x0_nn inv.sup_nn
        · exact inv.x1_nn
      have hnn : (orderedClinching m b₁ b₂ v₁ v₂).HasNonnegPayment := fun i => by
        rw [ho]; fin_cases i
        · exact add_nonneg inv.p0_nn (mul_nonneg hv₂ inv.sup_nn)
        · exact inv.p1_nn
      have hbf : (orderedClinching m b₁ b₂ v₁ v₂).IsBudgetFeasible ![b₁, b₂] := fun i => by
        rw [ho]; fin_cases i
        · exact inv.bf0
        · simp; linarith [inv.bf1, mul_nonneg hv₂ inv.sup_nn]
      have hir : (orderedClinching m b₁ b₂ v₁ v₂).IsIR ![v₁, v₂] := fun i => by
        rw [ho]; fin_cases i
        · have h1 : v₂ * trajX0 m b₁ b₂ v₂ ≤ v₁ * trajX0 m b₁ b₂ v₂ :=
            mul_le_mul_of_nonneg_right hgt.le inv.x0_nn
          have h2 : v₂ * trajSupply m b₁ b₂ v₂ ≤ v₁ * trajSupply m b₁ b₂ v₂ :=
            mul_le_mul_of_nonneg_right hgt.le inv.sup_nn
          simp [Outcome.utility]; linarith [hir_p0 v₂ hv₂]
        · simp [Outcome.utility]; linarith [hir_p1 v₂ hv₂]
      have hpo : (orderedClinching m b₁ b₂ v₁ v₂).IsParetoOptimal m ![v₁, v₂] ![b₁, b₂] := by
        rw [Outcome.isParetoOptimal_iff hv_nn hfeas hbf, ho]
        refine ⟨fun _ => ⟨by simp [Fin.sum_univ_two]; linarith [inv.sum_eq], fun i hi => ?_⟩,
          fun i j hi hij => ?_⟩
        · fin_cases i
          · have hi0 : v₁ = 0 := hi; linarith
          · have hi1 : v₂ = 0 := hi
            exact by rw [hi1]; exact hzx1
        · fin_cases i <;> fin_cases j
          · exact absurd hij (lt_irrefl _)
          · have hij' : v₁ < v₂ := hij; linarith
          · have hpos1 : 0 < trajX1 m b₁ b₂ v₂ := hi
            have hgt0 : entryPrice m b₁ < v₂ := by
              by_contra hle_p0
              have h0 : trajX1 m b₁ b₂ v₂ = 0 := ite_eq_left (not_lt.mp hle_p0)
              linarith
            exact inv.exh0 hgt0
          · exact absurd hij (lt_irrefl _)
      exact ⟨hfeas, hnn, hbf, hir, hpo⟩
    · have heq : v₁ = v₂ := le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
      subst heq
      by_cases hv0 : v₁ = 0
      · subst hv0
        have ho : orderedClinching m b₁ b₂ 0 0 = ⟨![0, 0], ![0, 0]⟩ := by
          simp [orderedClinching]
        have hfeas : (orderedClinching m b₁ b₂ 0 0).IsFeasible m := by
          rw [ho]; exact ⟨fun i => by fin_cases i <;> simp, by simp [Fin.sum_univ_two, hm.le]⟩
        have hnn : (orderedClinching m b₁ b₂ 0 0).HasNonnegPayment := fun i => by
          rw [ho]; fin_cases i <;> simp
        have hbf : (orderedClinching m b₁ b₂ 0 0).IsBudgetFeasible ![b₁, b₂] := fun i => by
          rw [ho]; fin_cases i <;> simp <;> linarith
        have hir : (orderedClinching m b₁ b₂ 0 0).IsIR ![0, 0] := fun i => by
          rw [ho]; fin_cases i <;> simp [Outcome.utility]
        have hpo : (orderedClinching m b₁ b₂ 0 0).IsParetoOptimal m ![0, 0] ![b₁, b₂] := by
          rw [Outcome.isParetoOptimal_iff hv_nn hfeas hbf]
          refine ⟨fun ⟨i, hi⟩ => ?_, fun i j _ hij => ?_⟩
          · fin_cases i <;> simp at hi
          · fin_cases i <;> fin_cases j <;> simp at hij
        exact ⟨hfeas, hnn, hbf, hir, hpo⟩
      · have inv : TrajInv m b₁ b₂ v₁ := traj_invariants hm hb₁ hle
        have ho : orderedClinching m b₁ b₂ v₁ v₁ =
            ⟨![trajX0 m b₁ b₂ v₁ + trajSupply m b₁ b₂ v₁ / 2,
               trajX1 m b₁ b₂ v₁ + trajSupply m b₁ b₂ v₁ / 2],
             ![trajP0 m b₁ b₂ v₁ + v₁ * (trajSupply m b₁ b₂ v₁ / 2),
               trajP1 m b₁ b₂ v₁ + v₁ * (trajSupply m b₁ b₂ v₁ / 2)]⟩ := by
          dsimp only [orderedClinching]; rw [ite_eq_right hlt, ite_eq_right hgt, ite_eq_right hv0]
        have hfeas : (orderedClinching m b₁ b₂ v₁ v₁).IsFeasible m := by
          rw [ho]
          exact ⟨fun i => by fin_cases i <;> simp <;> linarith [inv.x0_nn, inv.x1_nn, inv.sup_nn],
            by simp [Fin.sum_univ_two]; linarith [inv.sum_eq]⟩
        have hnn : (orderedClinching m b₁ b₂ v₁ v₁).HasNonnegPayment := fun i => by
          rw [ho]; have hvp := mul_nonneg hv₁ inv.sup_nn
          fin_cases i <;> simp <;> linarith [inv.p0_nn, inv.p1_nn]
        have hbf : (orderedClinching m b₁ b₂ v₁ v₁).IsBudgetFeasible ![b₁, b₂] := fun i => by
          rw [ho]; have hvp := mul_nonneg hv₁ inv.sup_nn
          fin_cases i <;> simp <;> linarith [inv.bf0, inv.bf1]
        have hir : (orderedClinching m b₁ b₂ v₁ v₁).IsIR ![v₁, v₁] := fun i => by
          rw [ho]; fin_cases i <;> simp [Outcome.utility]
          · linarith [hir_p0 v₁ hv₁]
          · linarith [hir_p1 v₁ hv₁]
        have hpo : (orderedClinching m b₁ b₂ v₁ v₁).IsParetoOptimal m ![v₁, v₁] ![b₁, b₂] := by
          rw [Outcome.isParetoOptimal_iff hv_nn hfeas hbf, ho]
          refine ⟨fun _ => ⟨by simp [Fin.sum_univ_two]; linarith [inv.sum_eq], fun i hi => ?_⟩,
            fun i j _ hij => ?_⟩
          · fin_cases i <;> exact absurd hi hv0
          · fin_cases i <;> fin_cases j <;> simp at hij
        exact ⟨hfeas, hnn, hbf, hir, hpo⟩

private theorem swapOutcome_pareto {o : Outcome (Fin 2)} {m : ℝ} {v B : Fin 2 → ℝ}
    (h : o.IsParetoOptimal m (fun i => v (swap01 i)) (fun i => B (swap01 i))) :
    (swapOutcome o).IsParetoOptimal m v B := by
  have hsum_eq : ∀ f : Fin 2 → ℝ, (∑ i, f (swap01 i)) = ∑ i, f i := fun f => by
    simp only [Fin.sum_univ_two, swap01_zero, swap01_one]; ring
  refine ⟨⟨fun i => h.1.1 (swap01 i), ?_⟩,
    fun i => by
      have hi := h.2.1 (swap01 i)
      dsimp only [swapOutcome]
      simpa [swap01_invol] using hi,
    fun o' hdom => ?_⟩
  · simpa [swapOutcome, hsum_eq o.alloc] using h.1.2
  · refine h.2.2 (swapOutcome o') ⟨⟨fun i => hdom.1.1 (swap01 i), ?_⟩,
      fun i => hdom.2.1 (swap01 i), fun i => ?_, ?_, ?_⟩
    · simpa [swapOutcome, hsum_eq o'.alloc] using hdom.1.2
    · simpa only [Outcome.utility, swapOutcome, swap01_invol] using hdom.2.2.1 (swap01 i)
    · simpa only [Outcome.revenue, swapOutcome, hsum_eq o.payment, hsum_eq o'.payment]
        using hdom.2.2.2.1
    · rcases hdom.2.2.2.2 with ⟨i, hi⟩ | hrev
      · left; exact ⟨swap01 i,
          by simpa only [Outcome.utility, swapOutcome, swap01_invol] using hi⟩
      · right; simpa only [Outcome.revenue, swapOutcome, hsum_eq o.payment, hsum_eq o'.payment]
          using hrev

private theorem fin2_vec_eq (f : Fin 2 → ℝ) : ![f 0, f 1] = f := by
  ext i; fin_cases i <;> rfl

/-- Supply feasibility of `twoBidderClinching`. -/
theorem twoBidderClinching_isFeasible {m : ℝ} (hm : 0 < m) {B v : Fin 2 → ℝ}
    (hB : ∀ i, 0 < B i) (hv : ∀ i, 0 ≤ v i) :
    (twoBidderClinching m B v).IsFeasible m := by
  dsimp only [twoBidderClinching]
  split_ifs with hle
  · exact (orderedClinching_props hm (hB 0) hle (hv 0) (hv 1)).feas
  · have h := (orderedClinching_props hm (hB 1) (lt_of_not_ge hle).le (hv 1) (hv 0)).feas
    refine ⟨fun i => h.1 (swap01 i), ?_⟩
    have := h.2
    simp only [swapOutcome, Fin.sum_univ_two, swap01_zero, swap01_one] at this ⊢
    linarith

/-- Nonnegative payments of `twoBidderClinching`. -/
theorem twoBidderClinching_hasNonnegPayment {m : ℝ} (hm : 0 < m) {B v : Fin 2 → ℝ}
    (hB : ∀ i, 0 < B i) (hv : ∀ i, 0 ≤ v i) :
    (twoBidderClinching m B v).HasNonnegPayment := by
  dsimp only [twoBidderClinching]
  split_ifs with hle
  · exact (orderedClinching_props hm (hB 0) hle (hv 0) (hv 1)).nonneg
  · exact fun i =>
      (orderedClinching_props hm (hB 1) (lt_of_not_ge hle).le (hv 1) (hv 0)).nonneg (swap01 i)

/-- Hard budget feasibility of `twoBidderClinching`. -/
theorem twoBidderClinching_isBudgetFeasible {m : ℝ} (hm : 0 < m) {B v : Fin 2 → ℝ}
    (hB : ∀ i, 0 < B i) (hv : ∀ i, 0 ≤ v i) :
    (twoBidderClinching m B v).IsBudgetFeasible B := by
  dsimp only [twoBidderClinching]
  split_ifs with hle
  · have h := (orderedClinching_props hm (hB 0) hle (hv 0) (hv 1)).bf
    simpa only [fin2_vec_eq B] using h
  · have h := (orderedClinching_props hm (hB 1) (lt_of_not_ge hle).le (hv 1) (hv 0)).bf
    intro i; fin_cases i
    · simpa [swapOutcome] using h 1
    · simpa [swapOutcome] using h 0

/-- **Exact Pareto optimality** of the continuous 2-bidder adaptive clinching auction for every
supply `m > 0`, strictly positive public budgets `B`, and nonnegative valuations `v`
([DobzinskiLaviNisan2012], primary PDF not inspected). -/
theorem twoBidderClinching_isParetoOptimal {m : ℝ} (hm : 0 < m) {B v : Fin 2 → ℝ}
    (hB : ∀ i, 0 < B i) (hv : ∀ i, 0 ≤ v i) :
    (twoBidderClinching m B v).IsParetoOptimal m v B := by
  dsimp only [twoBidderClinching]
  split_ifs with hle
  · have h := (orderedClinching_props hm (hB 0) hle (hv 0) (hv 1)).po
    simpa only [fin2_vec_eq v, fin2_vec_eq B] using h
  · have h := (orderedClinching_props hm (hB 1) (lt_of_not_ge hle).le (hv 1) (hv 0)).po
    have hv_eq : ![v 1, v 0] = fun i => v (swap01 i) := by ext i; fin_cases i <;> rfl
    have hB_eq : ![B 1, B 0] = fun i => B (swap01 i) := by ext i; fin_cases i <;> rfl
    rw [hv_eq, hB_eq] at h
    exact swapOutcome_pareto h

/-- Exact market clearing of `twoBidderClinching` when some bidder has positive value. -/
theorem twoBidderClinching_sum_alloc {m : ℝ} (hm : 0 < m) {B v : Fin 2 → ℝ}
    (hB : ∀ i, 0 < B i) (hv : ∀ i, 0 ≤ v i) (hpos : ∃ i, 0 < v i) :
    ∑ i, (twoBidderClinching m B v).alloc i = m :=
  (((Outcome.isParetoOptimal_iff hv
      (twoBidderClinching_isFeasible hm hB hv)
      (twoBidderClinching_isBudgetFeasible hm hB hv)).mp
    (twoBidderClinching_isParetoOptimal hm hB hv)).1 hpos).1

/-- Individual rationality of `twoBidderClinchingSP` (`SingleParameter.Mechanism.IsIR`). -/
theorem twoBidderClinchingSP_isIR {m : ℝ} (hm : 0 < m) {B : Fin 2 → ℝ} (hB : ∀ i, 0 < B i) :
    (twoBidderClinchingSP m B).IsIR := by
  intro i b hb
  dsimp only [SingleParameter.Mechanism.utility, twoBidderClinchingSP,
    BudgetedMechanism.toSingleParameter, twoBidderClinchingMechanism, twoBidderClinching]
  split_ifs with hle
  · have h := (orderedClinching_props hm (hB 0) hle (hb 0) (hb 1)).ir i
    simpa only [Outcome.utility, fin2_vec_eq b] using h
  · have h := (orderedClinching_props hm (hB 1) (lt_of_not_ge hle).le (hb 1) (hb 0)).ir
    fin_cases i
    · simpa [Outcome.utility, swapOutcome] using h 1
    · simpa [Outcome.utility, swapOutcome] using h 0

/-- Normalization of `twoBidderClinchingSP`: a bidder bidding `0` pays `0`. -/
theorem twoBidderClinchingSP_isNormalized {m : ℝ} (hm : 0 < m) {B : Fin 2 → ℝ}
    (hB : ∀ i, 0 < B i) :
    (twoBidderClinchingSP m B).IsNormalized := by
  have helper : ∀ {b₁ b₂ v₀ : ℝ}, 0 < b₁ → 0 ≤ v₀ →
      (orderedClinching m b₁ b₂ 0 v₀).payment 0 = 0 ∧
        (orderedClinching m b₁ b₂ v₀ 0).payment 1 = 0 := by
    intro b₁ b₂ v₀ hb₁ hv₀
    obtain ⟨_, hzp0, _, hzp1⟩ := orderedClinching_zero_vals (b₂ := b₂) hm hb₁
    refine ⟨?_, ?_⟩
    · by_cases hlt : 0 < v₀
      · simp [orderedClinching, hlt, hzp0]
      · have h0 : v₀ = 0 := le_antisymm (le_of_not_gt hlt) hv₀
        subst h0; simp [orderedClinching]
    · by_cases hlt : 0 < v₀
      · simp [orderedClinching, not_lt.mpr hv₀, hlt, hzp1]
      · have h0 : v₀ = 0 := le_antisymm (le_of_not_gt hlt) hv₀
        subst h0; simp [orderedClinching]
  intro i b hb
  dsimp only [twoBidderClinchingSP, BudgetedMechanism.toSingleParameter,
    twoBidderClinchingMechanism, twoBidderClinching]
  split_ifs with hle
  · fin_cases i
    · exact (helper (hB 0) (hb 1)).1
    · exact (helper (hB 0) (hb 0)).2
  · fin_cases i
    · exact (helper (hB 1) (hb 1)).2
    · exact (helper (hB 1) (hb 0)).1

private theorem ordered_dsic_zero_branch {m v b : ℝ} (hm : 0 < m) (hv : 0 ≤ v) :
    (if 0 < b then v * m else 0) ≤ (if 0 < v then v * m else 0) := by
  by_cases hzv : 0 < v <;> by_cases hzb : 0 < b
  · rw [ite_eq_left hzb, ite_eq_left hzv]
  · rw [ite_eq_right hzb, ite_eq_left hzv]; exact mul_nonneg hv hm.le
  · have hv0 : v = 0 := le_antisymm (le_of_not_gt hzv) hv
    subst hv0; simp
  · rw [ite_eq_right hzb, ite_eq_right hzv]

private theorem ordered_dsic_0 {m b₁ b₂ v₁ b₁' v₂ : ℝ} (hm : 0 < m) (hb₁ : 0 < b₁) (hle : b₁ ≤ b₂)
    (hv₁ : 0 ≤ v₁) (hb₁' : 0 ≤ b₁') (hv₂ : 0 ≤ v₂) :
    v₁ * (orderedClinching m b₁ b₂ b₁' v₂).alloc 0 - (orderedClinching m b₁ b₂ b₁' v₂).payment 0 ≤
      v₁ * (orderedClinching m b₁ b₂ v₁ v₂).alloc 0 -
        (orderedClinching m b₁ b₂ v₁ v₂).payment 0 := by
  by_cases hv₂0 : v₂ = 0
  · subst hv₂0
    obtain ⟨hzx0, hzp0, _, _⟩ := orderedClinching_zero_vals (b₂ := b₂) hm hb₁
    have hS0 : trajSupply m b₁ b₂ 0 = m := ite_eq_left (entryPrice_pos hm hb₁).le
    have eval0 : ∀ z, 0 ≤ z →
        v₁ * (orderedClinching m b₁ b₂ z 0).alloc 0 -
          (orderedClinching m b₁ b₂ z 0).payment 0 = if 0 < z then v₁ * m else 0 := by
      intro z hznn
      by_cases hzp : 0 < z
      · simp [orderedClinching, not_lt.mpr hznn, hzp, hzx0, hzp0, hS0]
      · have hz0 : z = 0 := le_antisymm (le_of_not_gt hzp) hznn
        subst hz0; simp [orderedClinching]
    rw [eval0 b₁' hb₁', eval0 v₁ hv₁]
    exact ordered_dsic_zero_branch hm hv₁
  · have he := env_stop_dsic (traj0_isEnvCurve (b₂ := b₂) hm hb₁)
      (fun t _ => (traj_invariants hm hb₁ hle (p := t)).sup_nn) hv₂ hv₁ hb₁'
    have heval : ∀ z : ℝ,
        v₁ * (orderedClinching m b₁ b₂ z v₂).alloc 0 - (orderedClinching m b₁ b₂ z v₂).payment 0 =
          if z < v₂ then v₁ * trajX0 m b₁ b₂ z - trajP0 m b₁ b₂ z
          else if v₂ < z then
            v₁ * (trajX0 m b₁ b₂ v₂ + trajSupply m b₁ b₂ v₂) -
              (trajP0 m b₁ b₂ v₂ + v₂ * trajSupply m b₁ b₂ v₂)
          else
            v₁ * (trajX0 m b₁ b₂ v₂ + trajSupply m b₁ b₂ v₂ / 2) -
              (trajP0 m b₁ b₂ v₂ + v₂ * (trajSupply m b₁ b₂ v₂ / 2)) := by
      intro z
      by_cases h1 : z < v₂
      · simp [orderedClinching, h1]
      · by_cases h2 : v₂ < z
        · simp [orderedClinching, h1, h2]
        · have hze : z = v₂ := le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)
          subst hze; simp [orderedClinching, hv₂0]
    rw [heval b₁', heval v₁]
    exact he

private theorem ordered_dsic_1 {m b₁ b₂ v₁ v₂ b₂' : ℝ} (hm : 0 < m) (hb₁ : 0 < b₁) (hle : b₁ ≤ b₂)
    (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂) (hb₂' : 0 ≤ b₂') :
    v₂ * (orderedClinching m b₁ b₂ v₁ b₂').alloc 1 - (orderedClinching m b₁ b₂ v₁ b₂').payment 1 ≤
      v₂ * (orderedClinching m b₁ b₂ v₁ v₂).alloc 1 -
        (orderedClinching m b₁ b₂ v₁ v₂).payment 1 := by
  by_cases hv₁0 : v₁ = 0
  · subst hv₁0
    obtain ⟨_, _, hzx1, hzp1⟩ := orderedClinching_zero_vals (b₂ := b₂) hm hb₁
    have hS0 : trajSupply m b₁ b₂ 0 = m := ite_eq_left (entryPrice_pos hm hb₁).le
    have eval0 : ∀ z, 0 ≤ z →
        v₂ * (orderedClinching m b₁ b₂ 0 z).alloc 1 -
          (orderedClinching m b₁ b₂ 0 z).payment 1 = if 0 < z then v₂ * m else 0 := by
      intro z hznn
      by_cases hzp : 0 < z
      · simp [orderedClinching, hzp, hzx1, hzp1, hS0]
      · have hz0 : z = 0 := le_antisymm (le_of_not_gt hzp) hznn
        subst hz0; simp [orderedClinching]
    rw [eval0 b₂' hb₂', eval0 v₂ hv₂]
    exact ordered_dsic_zero_branch hm hv₂
  · have he := env_stop_dsic (traj1_isEnvCurve hm hb₁ hle)
      (fun t _ => (traj_invariants hm hb₁ hle (p := t)).sup_nn) hv₁ hv₂ hb₂'
    have heval : ∀ z : ℝ,
        v₂ * (orderedClinching m b₁ b₂ v₁ z).alloc 1 - (orderedClinching m b₁ b₂ v₁ z).payment 1 =
          if z < v₁ then v₂ * trajX1 m b₁ b₂ z - trajP1 m b₁ b₂ z
          else if v₁ < z then
            v₂ * (trajX1 m b₁ b₂ v₁ + trajSupply m b₁ b₂ v₁) -
              (trajP1 m b₁ b₂ v₁ + v₁ * trajSupply m b₁ b₂ v₁)
          else
            v₂ * (trajX1 m b₁ b₂ v₁ + trajSupply m b₁ b₂ v₁ / 2) -
              (trajP1 m b₁ b₂ v₁ + v₁ * (trajSupply m b₁ b₂ v₁ / 2)) := by
      intro z
      by_cases h1 : z < v₁
      · simp [orderedClinching, h1, not_lt.mpr h1.le]
      · by_cases h2 : v₁ < z
        · simp [orderedClinching, h1, h2]
        · have hze : z = v₁ := le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)
          subst hze; simp [orderedClinching, hv₁0]
    rw [heval b₂', heval v₂]
    exact he

/-- **Dominant-strategy incentive compatibility in valuations** for the continuous 2-bidder
adaptive clinching auction `twoBidderClinchingSP` at fixed strictly positive public budgets `B`
([DobzinskiLaviNisan2012], primary PDF not inspected). -/
theorem twoBidderClinchingSP_isDSIC {m : ℝ} (hm : 0 < m) {B : Fin 2 → ℝ} (hB : ∀ i, 0 < B i) :
    (twoBidderClinchingSP m B).IsDSIC := by
  intro i b v hb hv
  dsimp only [SingleParameter.Mechanism.utility, twoBidderClinchingSP,
    BudgetedMechanism.toSingleParameter, twoBidderClinchingMechanism, twoBidderClinching]
  split_ifs with hle
  · fin_cases i
    · exact ordered_dsic_0 hm (hB 0) hle hv (hb 0) (hb 1)
    · exact ordered_dsic_1 hm (hB 0) hle (hb 0) hv (hb 1)
  · have hle' : B 1 ≤ B 0 := (lt_of_not_ge hle).le
    fin_cases i
    · exact ordered_dsic_1 hm (hB 1) hle' (hb 1) hv (hb 0)
    · exact ordered_dsic_0 hm (hB 1) hle' hv (hb 1) (hb 0)

/-- Elementary bound `Real.log 2 < 3 / 4`, proved from `(23 / 20) ^ 5 ≤ exp (3 / 4)`. -/
private theorem log_two_lt_three_fourths : Real.log 2 < 3 / 4 := by
  have h1 : (23 / 20 : ℝ) ≤ Real.exp (3 / 20) := by
    have := Real.add_one_le_exp (3 / 20 : ℝ); linarith
  have hpow : (23 / 20 : ℝ) ^ 5 ≤ Real.exp (3 / 4) := by
    calc
      (23 / 20 : ℝ) ^ 5 ≤ (Real.exp (3 / 20)) ^ 5 := pow_le_pow_left₀ (by norm_num) h1 5
      _ = Real.exp (5 * (3 / 20 : ℝ)) := (Real.exp_nat_mul (3 / 20) 5).symm
      _ = Real.exp (3 / 4) := by norm_num
  have htwo : (2 : ℝ) < (23 / 20 : ℝ) ^ 5 := by norm_num
  calc
    Real.log 2 < Real.log (Real.exp (3 / 4)) := Real.log_lt_log (by norm_num) (htwo.trans_le hpow)
    _ = 3 / 4 := Real.log_exp (3 / 4)

/-- **Explicit budget-manipulation witness** showing `twoBidderClinchingMechanism m` is **not**
truthful when budgets are private (`m > 0`). On the symmetric-budget profile
`θ = ![⟨10 / m, 1⟩, ⟨2 / m, 1⟩]`:
* truthful reporting yields bidder `1` allocation `(3 / 8) * m`, payment `1 / 2`, utility `1 / 4`;
* over-reporting budget `b' = ⟨2 / m, 1 + Real.log 2⟩` yields allocation `m / 2`, payment
  `Real.log 2 ≤ 1` (strictly within true budget `1`), and utility `1 - Real.log 2 > 1 / 4`. -/
theorem twoBidderClinching_budget_manipulation {m : ℝ} (hm : 0 < m) :
    let θ : Fin 2 → BidderType := ![⟨10 / m, 1⟩, ⟨2 / m, 1⟩]
    let b' : BidderType := ⟨2 / m, 1 + Real.log 2⟩
    (∀ k, (θ k).IsPos) ∧ b'.IsPos ∧
      ((twoBidderClinchingMechanism m).outcome θ).payment 1 = 1 / 2 ∧
      ((twoBidderClinchingMechanism m).outcome θ).utility (fun k => (θ k).val) 1 = 1 / 4 ∧
      ((twoBidderClinchingMechanism m).outcome (Function.update θ 1 b')).payment 1 = Real.log 2 ∧
      ((twoBidderClinchingMechanism m).outcome (Function.update θ 1 b')).payment 1 ≤
        (θ 1).budget ∧
      ((twoBidderClinchingMechanism m).outcome (Function.update θ 1 b')).utility
        (fun k => (θ k).val) 1 = 1 - Real.log 2 ∧
      ((twoBidderClinchingMechanism m).outcome θ).utility (fun k => (θ k).val) 1 <
        ((twoBidderClinchingMechanism m).outcome (Function.update θ 1 b')).utility
          (fun k => (θ k).val) 1 := by
  intro θ b'
  have hlog_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_lt : Real.log 2 < 3 / 4 := log_two_lt_three_fourths
  have hpos_θ : ∀ k, (θ k).IsPos := fun k => by
    fin_cases k <;> exact ⟨div_pos (by norm_num) hm, zero_lt_one⟩
  have hpos_b' : b'.IsPos := ⟨div_pos (by norm_num) hm, by linarith⟩
  have hlt_v : (2 : ℝ) / m < 10 / m := by rw [div_lt_div_iff_of_pos_right hm]; norm_num
  have hnot_lt : ¬ (10 / m < 2 / m) := not_lt.mpr hlt_v.le
  have hp0 : entryPrice m 1 = 1 / m := rfl
  have hpe_honest : eqPrice m 1 1 = 1 / m := by
    simp only [eqPrice, entryPrice, sub_self, zero_div, Real.exp_zero, mul_one]
  have hgt_p0 : ¬ (2 / m ≤ 1 / m) := by
    rw [not_le, div_lt_div_iff_of_pos_right hm]; norm_num
  have hhon_out : (twoBidderClinchingMechanism m).outcome θ =
      orderedClinching m 1 1 (10 / m) (2 / m) := by
    dsimp only [twoBidderClinchingMechanism, twoBidderClinching, θ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, le_refl, ↓reduceIte]
  have hhon_x : ((twoBidderClinchingMechanism m).outcome θ).alloc 1 = 3 / 8 * m := by
    rw [hhon_out]; dsimp only [orderedClinching]
    rw [ite_eq_right hnot_lt, ite_eq_left hlt_v]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, trajX1, hp0, hpe_honest]
    rw [ite_eq_right hgt_p0, ite_eq_right hgt_p0]
    field_simp [hm.ne']; ring
  have hhon_p : ((twoBidderClinchingMechanism m).outcome θ).payment 1 = 1 / 2 := by
    rw [hhon_out]; dsimp only [orderedClinching]
    rw [ite_eq_right hnot_lt, ite_eq_left hlt_v]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, trajP1, hp0, hpe_honest]
    rw [ite_eq_right hgt_p0, ite_eq_right hgt_p0]
    field_simp [hm.ne']; ring
  have hhon_u : ((twoBidderClinchingMechanism m).outcome θ).utility (fun k => (θ k).val) 1 =
      1 / 4 := by
    dsimp only [Outcome.utility]; rw [hhon_x, hhon_p]
    simp only [θ, Matrix.cons_val_one, Matrix.cons_val_zero]
    field_simp [hm.ne']; norm_num
  have hpe_dev : eqPrice m 1 (1 + Real.log 2) = 2 / m := by
    simp only [eqPrice, entryPrice, add_sub_cancel_left, div_one,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    ring
  have hdev_le : (1 : ℝ) ≤ 1 + Real.log 2 := by linarith
  have hdev_out : (twoBidderClinchingMechanism m).outcome (Function.update θ 1 b') =
      orderedClinching m 1 (1 + Real.log 2) (10 / m) (2 / m) := by
    dsimp only [twoBidderClinchingMechanism, twoBidderClinching]
    simp only [Function.update_self, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1),
      θ, b', Matrix.cons_val_zero]
    rw [ite_eq_left hdev_le]
  have hdev_x : ((twoBidderClinchingMechanism m).outcome (Function.update θ 1 b')).alloc 1 =
      m / 2 := by
    rw [hdev_out]; dsimp only [orderedClinching]
    rw [ite_eq_right hnot_lt, ite_eq_left hlt_v]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, trajX1, hp0, hpe_dev]
    rw [ite_eq_right hgt_p0, ite_eq_left le_rfl]
    field_simp [hm.ne']; ring
  have hdev_p : ((twoBidderClinchingMechanism m).outcome (Function.update θ 1 b')).payment 1 =
      Real.log 2 := by
    rw [hdev_out]; dsimp only [orderedClinching]
    rw [ite_eq_right hnot_lt, ite_eq_left hlt_v]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, trajP1, hp0, hpe_dev]
    rw [ite_eq_right hgt_p0, ite_eq_left le_rfl, one_mul]
    congr 1; field_simp [hm.ne']
  have hdev_u : ((twoBidderClinchingMechanism m).outcome (Function.update θ 1 b')).utility
      (fun k => (θ k).val) 1 = 1 - Real.log 2 := by
    dsimp only [Outcome.utility]; rw [hdev_x, hdev_p]
    simp only [θ, Matrix.cons_val_one, Matrix.cons_val_zero]
    field_simp [hm.ne']
  refine ⟨hpos_θ, hpos_b', hhon_p, hhon_u, hdev_p, ?_, hdev_u, ?_⟩
  · rw [hdev_p]; simp only [θ, Matrix.cons_val_one, Matrix.cons_val_zero]; linarith
  · rw [hhon_u, hdev_u]; linarith

/-- The continuous 2-bidder adaptive clinching auction is **not** private-budget DSIC for any
supply `m > 0`. -/
theorem twoBidderClinching_not_privateBudgetDSIC {m : ℝ} (hm : 0 < m) :
    ¬ (twoBidderClinchingMechanism m).IsPrivateBudgetDSIC := by
  intro hic
  obtain ⟨hpos_θ, hpos_b', _, _, _, hpay_le, _, hlt⟩ :=
    twoBidderClinching_budget_manipulation hm
  have hle := hic ![⟨10 / m, 1⟩, ⟨2 / m, 1⟩] hpos_θ 1 ⟨2 / m, 1 + Real.log 2⟩ hpos_b' hpay_le
  linarith

end Cslib.GameTheory.BudgetedAuction
