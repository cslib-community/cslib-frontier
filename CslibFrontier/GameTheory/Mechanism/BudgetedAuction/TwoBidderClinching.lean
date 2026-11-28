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
  simp [twoBidderClinching, swapOutcome, swap01, not_le.mpr h, h.le]

/-- Phase-0 explicit evaluation: when `B 0 ≤ B 1` and `v 0 < v 1` with `v 0 ≤ B 0 / m`, bidder `1`
receives the full supply `m` at price `v 0`. -/
theorem twoBidderClinching_phase0_lt {m : ℝ} {B v : Fin 2 → ℝ}
    (hm : 0 < m) (hB0 : 0 < B 0) (hB : B 0 ≤ B 1)
    (h1 : v 0 < v 1) (hp : v 0 ≤ B 0 / m) :
    (twoBidderClinching m B v).alloc 0 = 0 ∧ (twoBidderClinching m B v).alloc 1 = m ∧
      (twoBidderClinching m B v).payment 0 = 0 ∧
      (twoBidderClinching m B v).payment 1 = v 0 * m := by
  have hle_e : v 0 ≤ eqPrice m (B 0) (B 1) := hp.trans <|
    le_mul_of_one_le_right (div_pos hB0 hm).le
      (Real.one_le_exp (div_nonneg (sub_nonneg.mpr hB) hB0.le))
  simp only [twoBidderClinching, orderedClinching, hB, h1, trajX0, trajX1, trajP0, trajP1,
    trajSupply, entryPrice, Matrix.cons_val_zero, Matrix.cons_val_one, hle_e, hp, ↓reduceIte,
    zero_add, and_self]

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
    entryPrice m b₁ ≤ eqPrice m b₁ b₂ :=
  le_mul_of_one_le_right (entryPrice_pos hm hb₁).le
    (Real.one_le_exp (div_nonneg (sub_nonneg.mpr hle) hb₁.le))

private theorem eqPrice_pos {m b₁ b₂ : ℝ} (hm : 0 < m) (hb₁ : 0 < b₁) :
    0 < eqPrice m b₁ b₂ :=
  mul_pos (entryPrice_pos hm hb₁) (Real.exp_pos _)

private theorem log_eqPrice {m b₁ b₂ : ℝ} (hm : 0 < m) (hb₁ : 0 < b₁) :
    b₁ * Real.log (eqPrice m b₁ b₂ * m / b₁) = b₂ - b₁ := by
  have heq : eqPrice m b₁ b₂ * m / b₁ = Real.exp ((b₂ - b₁) / b₁) := by
    dsimp only [eqPrice, entryPrice]
    field_simp [hm.ne', hb₁.ne']
  rw [heq, Real.log_exp]
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
    p * (x q - x p) ≤ pay q - pay p ∧ pay q - pay p ≤ q * (x q - x p) :=
  ⟨by linarith [mul_le_mul_of_nonneg_right hpr (sub_nonneg.mpr hxr), h1.1, h2.1],
   by linarith [mul_le_mul_of_nonneg_right hrq (sub_nonneg.mpr hxp), h1.2, h2.2]⟩

private theorem env_glue {x pay : ℝ → ℝ} {a c : ℝ}
    (hL : ∀ ⦃p q⦄, a ≤ p → p ≤ q → q ≤ c →
      x p ≤ x q ∧ p * (x q - x p) ≤ pay q - pay p ∧ pay q - pay p ≤ q * (x q - x p))
    (hR : ∀ ⦃p q⦄, c ≤ p → p ≤ q →
      x p ≤ x q ∧ p * (x q - x p) ≤ pay q - pay p ∧ pay q - pay p ≤ q * (x q - x p)) :
    ∀ ⦃p q⦄, a ≤ p → p ≤ q →
      x p ≤ x q ∧ p * (x q - x p) ≤ pay q - pay p ∧ pay q - pay p ≤ q * (x q - x p) := by
  intro p q hap hpq
  by_cases hp : p ≤ c
  · by_cases hq : q ≤ c
    · exact hL hap hpq hq
    · have hc := hL hap hp le_rfl
      have hr := hR le_rfl (le_of_not_ge hq)
      exact ⟨hc.1.trans hr.1, env_trans hp (le_of_not_ge hq) hc.1 hr.1 hc.2 hr.2⟩
  · exact hR (le_of_not_ge hp) hpq

private theorem phase2_sandwich {b₁ pe p q : ℝ} (hb₁ : 0 < b₁) (hpe : 0 < pe)
    (hp : pe ≤ p) (hpq : p ≤ q) :
    let dx := fun t : ℝ => (b₁ / pe) * (1 - (pe / t) ^ 2) / 2
    let dp := fun t : ℝ => b₁ * (1 - pe / t)
    dx p ≤ dx q ∧
      p * (dx q - dx p) ≤ dp q - dp p ∧ dp q - dp p ≤ q * (dx q - dx p) := by
  intro dx dp
  have hp_pos : 0 < p := hpe.trans_le hp
  have hq_pos : 0 < q := hp_pos.trans_le hpq
  have hqp_nn : 0 ≤ q - p := sub_nonneg.mpr hpq
  have hdiff_x : dx q - dx p = b₁ * pe * (q - p) * (q + p) / (2 * p ^ 2 * q ^ 2) := by
    dsimp only [dx]; field_simp [hpe.ne', hp_pos.ne', hq_pos.ne']; ring
  have hdiff_p : dp q - dp p = b₁ * pe * (q - p) / (p * q) := by
    dsimp only [dp]; field_simp [hp_pos.ne', hq_pos.ne']; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [← sub_nonneg, hdiff_x]; positivity
  · rw [← sub_nonneg, hdiff_x, hdiff_p]
    have : b₁ * pe * (q - p) / (p * q) - p * (b₁ * pe * (q - p) * (q + p) / (2 * p ^ 2 * q ^ 2)) =
        b₁ * pe * (q - p) ^ 2 / (2 * p * q ^ 2) := by field_simp [hp_pos.ne', hq_pos.ne']; ring
    rw [this]; positivity
  · rw [← sub_nonneg, hdiff_x, hdiff_p]
    have : q * (b₁ * pe * (q - p) * (q + p) / (2 * p ^ 2 * q ^ 2)) - b₁ * pe * (q - p) / (p * q) =
        b₁ * pe * (q - p) ^ 2 / (2 * p ^ 2 * q) := by field_simp [hp_pos.ne', hq_pos.ne']; ring
    rw [this]; positivity

private theorem phase1_sandwich {m b₁ p q : ℝ} (hm : 0 < m) (hb₁ : 0 < b₁)
    (hp : 0 < p) (hpq : p ≤ q) :
    let x := fun t : ℝ => m - b₁ / t
    let pay := fun t : ℝ => b₁ * Real.log (t * m / b₁)
    x p ≤ x q ∧
      p * (x q - x p) ≤ pay q - pay p ∧ pay q - pay p ≤ q * (x q - x p) := by
  intro x pay
  have hq : 0 < q := hp.trans_le hpq
  have hratio_pos : 0 < q / p := div_pos hq hp
  have hdp : pay q - pay p = b₁ * Real.log (q / p) := by
    dsimp only [pay]
    rw [← mul_sub, ← Real.log_div (by positivity) (by positivity)]
    congr 2
    field_simp [hm.ne', hb₁.ne', hp.ne']
  have hdx : x q - x p = b₁ * (1 / p - 1 / q) := by
    dsimp only [x]; field_simp [hp.ne', hq.ne']; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [← sub_nonneg, hdx]
    exact mul_nonneg hb₁.le (sub_nonneg.mpr (one_div_le_one_div_of_le hp hpq))
  · have hp_mul : p * (b₁ * (1 / p - 1 / q)) = b₁ * (1 - (q / p)⁻¹) := by
      field_simp [hp.ne', hq.ne']
    rw [hdp, hdx, hp_mul]
    exact mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hratio_pos) hb₁.le
  · have hq_mul : q * (b₁ * (1 / p - 1 / q)) = b₁ * (q / p - 1) := by
      field_simp [hp.ne', hq.ne']
    rw [hdp, hdx, hq_mul]
    exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hratio_pos) hb₁.le

private theorem traj0_isEnvCurve {m b₁ b₂ : ℝ} (hm : 0 < m) (hb₁ : 0 < b₁) :
    IsEnvCurve (trajX0 m b₁ b₂) (trajP0 m b₁ b₂) := by
  let pe := eqPrice m b₁ b₂
  have hpe : 0 < pe := eqPrice_pos hm hb₁
  have eval2 : ∀ t, pe ≤ t →
      trajX0 m b₁ b₂ t = (b₁ / pe) * (1 - (pe / t) ^ 2) / 2 ∧
        trajP0 m b₁ b₂ t = b₁ * (1 - pe / t) := by
    intro t ht
    by_cases hle : t ≤ pe
    · obtain rfl : t = pe := le_antisymm hle ht
      dsimp only [pe] at hpe ⊢
      simp only [trajX0, trajP0, le_rfl, ↓reduceIte, div_self hpe.ne']
      exact ⟨by ring, by ring⟩
    · exact ⟨ite_eq_right hle, ite_eq_right hle⟩
  have h := env_glue (x := trajX0 m b₁ b₂) (pay := trajP0 m b₁ b₂) (a := 0) (c := pe)
    (fun {p q} _ hpq hq => by
      dsimp only [pe] at hq
      simp only [trajX0, trajP0, hpq.trans hq, hq, ↓reduceIte, sub_self, mul_zero, le_rfl,
        and_self])
    (fun {p q} hp hpq => by
      obtain ⟨hxp, hpp⟩ := eval2 p hp
      obtain ⟨hxq, hpq'⟩ := eval2 q (hp.trans hpq)
      rw [hxp, hxq, hpp, hpq']
      exact phase2_sandwich hb₁ hpe hp hpq)
  exact ⟨fun {_ _} hp hpq => (h hp hpq).1, fun {_ _} hp hpq => (h hp hpq).2⟩

private theorem traj1_eval_p0 {m b₁ : ℝ} (hm : 0 < m) (hb₁ : 0 < b₁) :
    m - b₁ / entryPrice m b₁ = 0 ∧
      b₁ * Real.log (entryPrice m b₁ * m / b₁) = 0 := by
  dsimp only [entryPrice]
  have h1 : b₁ / m * m / b₁ = 1 := by field_simp [hm.ne', hb₁.ne']
  refine ⟨by field_simp [hm.ne', hb₁.ne']; ring, ?_⟩
  rw [h1, Real.log_one, mul_zero]

private theorem traj1_isEnvCurve {m b₁ b₂ : ℝ} (hm : 0 < m) (hb₁ : 0 < b₁) (hle : b₁ ≤ b₂) :
    IsEnvCurve (trajX1 m b₁ b₂) (trajP1 m b₁ b₂) := by
  let p₀ := entryPrice m b₁
  let pe := eqPrice m b₁ b₂
  have hp₀_pos : 0 < p₀ := entryPrice_pos hm hb₁
  have hpe_pos : 0 < pe := eqPrice_pos hm hb₁
  have hp₀_le : p₀ ≤ pe := entryPrice_le_eqPrice hm hb₁ hle
  obtain ⟨hx0_eq, hp0_eq⟩ := traj1_eval_p0 hm hb₁
  have hlog_pe : b₁ * Real.log (pe * m / b₁) = b₂ - b₁ := log_eqPrice hm hb₁
  have eval1 : ∀ t, p₀ ≤ t → t ≤ pe →
      trajX1 m b₁ b₂ t = m - b₁ / t ∧ trajP1 m b₁ b₂ t = b₁ * Real.log (t * m / b₁) := by
    intro t ht1 ht2
    by_cases h0 : t ≤ p₀
    · obtain rfl : t = p₀ := le_antisymm h0 ht1
      dsimp only [p₀] at *
      simp only [trajX1, trajP1, le_rfl, ↓reduceIte, hx0_eq, hp0_eq, and_self]
    · dsimp only [p₀, pe] at h0 ht2
      simp only [trajX1, trajP1, h0, ht2, ↓reduceIte, and_self]
  have eval2 : ∀ t, pe ≤ t →
      trajX1 m b₁ b₂ t = (m - b₁ / pe) + (b₁ / pe) * (1 - (pe / t) ^ 2) / 2 ∧
        trajP1 m b₁ b₂ t = (b₂ - b₁) + b₁ * (1 - pe / t) := by
    intro t ht
    by_cases hte : t ≤ pe
    · obtain rfl : t = pe := le_antisymm hte ht
      obtain ⟨hx, hp⟩ := eval1 pe hp₀_le le_rfl
      rw [hx, hp, hlog_pe, div_self hpe_pos.ne']
      exact ⟨by ring, by ring⟩
    · have hnot0 : ¬ t ≤ entryPrice m b₁ := fun h => hte (h.trans hp₀_le)
      dsimp only [pe] at hte ⊢
      simp only [trajX1, trajP1, hnot0, hte, ↓reduceIte, and_self]
  have hge0 := env_glue (x := trajX1 m b₁ b₂) (pay := trajP1 m b₁ b₂) (a := p₀) (c := pe)
    (fun {p q} hp hpq hq => by
      obtain ⟨hxp, hpp⟩ := eval1 p hp (hpq.trans hq)
      obtain ⟨hxq, hpq'⟩ := eval1 q (hp.trans hpq) hq
      rw [hxp, hxq, hpp, hpq']
      exact phase1_sandwich hm hb₁ (hp₀_pos.trans_le hp) hpq)
    (fun {p q} hp hpq => by
      obtain ⟨hxp, hpp⟩ := eval2 p hp
      obtain ⟨hxq, hpq'⟩ := eval2 q (hp.trans hpq)
      simpa only [hxp, hxq, hpp, hpq', add_le_add_iff_left, add_sub_add_left_eq_sub] using
        phase2_sandwich hb₁ hpe_pos hp hpq)
  have hall := env_glue (x := trajX1 m b₁ b₂) (pay := trajP1 m b₁ b₂) (a := 0) (c := p₀)
    (fun {p q} _ hpq hq => by
      dsimp only [p₀] at hq
      simp only [trajX1, trajP1, hpq.trans hq, hq, ↓reduceIte, sub_self, mul_zero, le_rfl,
        and_self])
    hge0
  exact ⟨fun {_ _} hp hpq => (hall hp hpq).1, fun {_ _} hp hpq => (hall hp hpq).2⟩

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
  have hs : ∀ z, 0 ≤ z → v * x z - pay z ≤ v * x v - pay v := fun z hz => by
    rcases le_total z v with h | h
    · linarith [(henv.2 hz h).2]
    · linarith [(henv.2 hv h).1]
  dsimp only [u]
  split_ifs with hbl hvl hvg hbg hvl2 hvg2 hvl3 hvg3
  · exact hs b hb
  · have := mul_le_mul_of_nonneg_right hvg.le (sub_nonneg.mpr (henv.1 hb hbl.le))
    have := mul_nonneg (sub_nonneg.mpr hvg.le) hS0
    linarith [(henv.2 hb hbl.le).2]
  · obtain rfl : v = other := le_antisymm (le_of_not_gt hvg) (le_of_not_gt hvl)
    linarith [hs b hb]
  · have := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hvl2.le) hS0
    linarith [hs other ho]
  · exact le_rfl
  · obtain rfl : v = other := le_antisymm (le_of_not_gt hvg2) (le_of_not_gt hvl2)
    linarith
  · have := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hvl3.le) (div_nonneg hS0 zero_le_two)
    linarith [hs other ho]
  · have := mul_nonneg (sub_nonneg.mpr hvg3.le) (div_nonneg hS0 zero_le_two)
    linarith
  · exact le_rfl

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
  let p₀ := entryPrice m b₁
  let pe := eqPrice m b₁ b₂
  have hp₀_pos : 0 < p₀ := entryPrice_pos hm hb₁
  have hpe_pos : 0 < pe := eqPrice_pos hm hb₁
  have hp₀_le : p₀ ≤ pe := entryPrice_le_eqPrice hm hb₁ hle
  have hb1_eq : b₁ = p₀ * m := (div_mul_cancel₀ b₁ hm.ne').symm
  by_cases h0 : p ≤ entryPrice m b₁
  · have he : p ≤ eqPrice m b₁ b₂ := h0.trans hp₀_le
    have hpm : p * m ≤ b₁ := (mul_le_mul_of_nonneg_right h0 hm.le).trans_eq hb1_eq.symm
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun h => absurd h (not_lt.mpr h0),
      fun h => absurd h (not_lt.mpr he)⟩ <;>
      simp only [trajX0, trajX1, trajP0, trajP1, trajSupply, h0, he, ↓reduceIte] <;>
      first | exact le_rfl | linarith only [hm, hle, hpm]
  · have hp_pos : 0 < p := hp₀_pos.trans (lt_of_not_ge h0)
    by_cases he : p ≤ eqPrice m b₁ b₂
    · have hx1_nn : b₁ / p ≤ m := (div_le_iff₀ hp_pos).mpr (by nlinarith)
      have harg_ge : 1 ≤ p * m / b₁ := (one_le_div hb₁).mpr (by nlinarith)
      have hp1_le : b₁ * Real.log (p * m / b₁) ≤ b₂ - b₁ :=
        (mul_le_mul_of_nonneg_left
          (Real.log_le_log (div_pos (mul_pos hp_pos hm) hb₁)
            (by gcongr)) hb₁.le).trans_eq (log_eqPrice hm hb₁)
      have hsup1 : 0 ≤ b₁ / p := div_nonneg hb₁.le hp_pos.le
      have hlog_nn : 0 ≤ b₁ * Real.log (p * m / b₁) := mul_nonneg hb₁.le (Real.log_nonneg harg_ge)
      have hmul_b : p * (b₁ / p) = b₁ := mul_div_cancel₀ b₁ hp_pos.ne'
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => ?_, fun h => absurd h (not_lt.mpr he)⟩ <;>
        simp only [trajX0, trajX1, trajP0, trajP1, trajSupply, h0, he, ↓reduceIte, hmul_b] <;>
        first | assumption | exact le_rfl | linarith only [hx1_nn, hp1_le]
    · have hfrac_lt : pe / p < 1 := (div_lt_one hp_pos).mpr (lt_of_not_ge he)
      have hsq_le : (pe / p) ^ 2 ≤ 1 := by nlinarith [div_nonneg hpe_pos.le hp_pos.le]
      have hdx_nn : 0 ≤ b₁ / eqPrice m b₁ b₂ * (1 - (eqPrice m b₁ b₂ / p) ^ 2) / 2 :=
        div_nonneg (mul_nonneg (div_nonneg hb₁.le hpe_pos.le) (sub_nonneg.mpr hsq_le)) zero_le_two
      have hsup2 : 0 ≤ b₁ / eqPrice m b₁ b₂ * (eqPrice m b₁ b₂ / p) ^ 2 :=
        mul_nonneg (div_nonneg hb₁.le hpe_pos.le) (sq_nonneg _)
      have hm_ge : b₁ / eqPrice m b₁ b₂ ≤ m := (div_le_iff₀ hpe_pos).mpr (by nlinarith)
      have hdp_nn : 0 ≤ b₁ * (1 - eqPrice m b₁ b₂ / p) :=
        mul_nonneg hb₁.le (sub_nonneg.mpr hfrac_lt.le)
      have hps : p * ((b₁ / eqPrice m b₁ b₂) * (eqPrice m b₁ b₂ / p) ^ 2) =
          b₁ * (eqPrice m b₁ b₂ / p) := by
        field_simp [hpe_pos.ne', hp_pos.ne']
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => ?_, fun _ => ?_⟩ <;>
        simp only [trajX0, trajX1, trajP0, trajP1, trajSupply, h0, he, ↓reduceIte, hps] <;>
        first | assumption | linarith only [hle, hdx_nn, hm_ge, hdp_nn]

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

private theorem orderedProps_of_eq {m b₁ b₂ v₁ v₂ : ℝ} {o : Outcome (Fin 2)}
    (ho : orderedClinching m b₁ b₂ v₁ v₂ = o)
    (hv_nn : ∀ i : Fin 2, 0 ≤ (![v₁, v₂] : Fin 2 → ℝ) i)
    (hfeas : o.IsFeasible m) (hnn : o.HasNonnegPayment)
    (hbf : o.IsBudgetFeasible ![b₁, b₂]) (hir : o.IsIR ![v₁, v₂])
    (hclear : (∃ i : Fin 2, 0 < (![v₁, v₂] : Fin 2 → ℝ) i) →
      (∑ i, o.alloc i = m) ∧ ∀ i, (![v₁, v₂] : Fin 2 → ℝ) i = 0 → o.alloc i = 0)
    (hdom : ∀ i j : Fin 2, 0 < o.alloc i →
      (![v₁, v₂] : Fin 2 → ℝ) i < (![v₁, v₂] : Fin 2 → ℝ) j →
      o.payment j = (![b₁, b₂] : Fin 2 → ℝ) j) :
    OrderedProps m b₁ b₂ v₁ v₂ :=
  ⟨ho ▸ hfeas, ho ▸ hnn, ho ▸ hbf, ho ▸ hir,
   ho ▸ (Outcome.isParetoOptimal_iff hv_nn hfeas hbf).mpr ⟨hclear, hdom⟩⟩

private theorem orderedClinching_props {m b₁ b₂ v₁ v₂ : ℝ} (hm : 0 < m)
    (hb₁ : 0 < b₁) (hle : b₁ ≤ b₂) (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂) :
    OrderedProps m b₁ b₂ v₁ v₂ := by
  have he0 := traj0_isEnvCurve (b₂ := b₂) hm hb₁
  have he1 := traj1_isEnvCurve hm hb₁ hle
  obtain ⟨hzx0, hzp0, hzx1, hzp1⟩ := orderedClinching_zero_vals (b₂ := b₂) hm hb₁
  have hir_p0 : ∀ p, 0 ≤ p → trajP0 m b₁ b₂ p ≤ p * trajX0 m b₁ b₂ p := fun p hp => by
    simpa only [hzx0, hzp0, sub_zero] using (he0.2 le_rfl hp).2
  have hir_p1 : ∀ p, 0 ≤ p → trajP1 m b₁ b₂ p ≤ p * trajX1 m b₁ b₂ p := fun p hp => by
    simpa only [hzx1, hzp1, sub_zero] using (he1.2 le_rfl hp).2
  have hv_nn : ∀ i : Fin 2, 0 ≤ (![v₁, v₂] : Fin 2 → ℝ) i := fun i => by fin_cases i <;> assumption
  have active {p s₀ s₁ : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ v₁) (hp2 : p ≤ v₂)
      (hs₀ : 0 ≤ s₀) (hs₁ : 0 ≤ s₁) (hsum : s₀ + s₁ = trajSupply m b₁ b₂ p)
      (ho : orderedClinching m b₁ b₂ v₁ v₂ =
        ⟨![trajX0 m b₁ b₂ p + s₀, trajX1 m b₁ b₂ p + s₁],
         ![trajP0 m b₁ b₂ p + p * s₀, trajP1 m b₁ b₂ p + p * s₁]⟩)
      (hz : ∀ i : Fin 2, (![v₁, v₂] : Fin 2 → ℝ) i = 0 →
        (![trajX0 m b₁ b₂ p + s₀, trajX1 m b₁ b₂ p + s₁] : Fin 2 → ℝ) i = 0)
      (hdom : ∀ i j : Fin 2,
        0 < (![trajX0 m b₁ b₂ p + s₀, trajX1 m b₁ b₂ p + s₁] : Fin 2 → ℝ) i →
        (![v₁, v₂] : Fin 2 → ℝ) i < (![v₁, v₂] : Fin 2 → ℝ) j →
        (![trajP0 m b₁ b₂ p + p * s₀, trajP1 m b₁ b₂ p + p * s₁] : Fin 2 → ℝ) j =
          (![b₁, b₂] : Fin 2 → ℝ) j) : OrderedProps m b₁ b₂ v₁ v₂ := by
    have inv : TrajInv m b₁ b₂ p := traj_invariants hm hb₁ hle
    have hps : p * s₀ + p * s₁ = p * trajSupply m b₁ b₂ p := by rw [← mul_add, hsum]
    have hclear_sum : ∑ i : Fin 2,
        (![trajX0 m b₁ b₂ p + s₀, trajX1 m b₁ b₂ p + s₁] : Fin 2 → ℝ) i = m := by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      linarith [inv.sum_eq]
    exact orderedProps_of_eq ho hv_nn
      ⟨fun i => by fin_cases i <;> dsimp <;> linarith [inv.x0_nn, inv.x1_nn], hclear_sum.le⟩
      (fun i => by
        fin_cases i <;> dsimp <;>
          linarith [inv.p0_nn, inv.p1_nn, mul_nonneg hp hs₀, mul_nonneg hp hs₁])
      (fun i => by
        fin_cases i <;> dsimp <;>
          linarith [inv.bf0, inv.bf1, mul_nonneg hp hs₀, mul_nonneg hp hs₁])
      (fun i => by
        fin_cases i
        · simp only [Outcome.utility, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
          linarith [hir_p0 p hp, mul_le_mul_of_nonneg_right hp1 (add_nonneg inv.x0_nn hs₀)]
        · simp only [Outcome.utility, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
            Matrix.cons_val_zero]
          linarith [hir_p1 p hp, mul_le_mul_of_nonneg_right hp2 (add_nonneg inv.x1_nn hs₁)])
      (fun _ => ⟨hclear_sum, hz⟩) hdom
  by_cases hlt : v₁ < v₂
  · have inv : TrajInv m b₁ b₂ v₁ := traj_invariants hm hb₁ hle
    refine active hv₁ le_rfl hlt.le le_rfl inv.sup_nn (zero_add _)
      (by simp [orderedClinching, hlt]) (fun i hi => ?_) (fun i j hi hij => ?_)
    · fin_cases i <;> dsimp at hi ⊢
      exacts [by simp [hi, hzx0], by linarith]
    · fin_cases i <;> fin_cases j <;> dsimp at hi hij <;> try linarith
      refine inv.exh1 (by_contra fun hle_pe => ?_)
      have h0 : trajX0 m b₁ b₂ v₁ = 0 := ite_eq_left (not_lt.mp hle_pe)
      linarith
  · by_cases hgt : v₂ < v₁
    · have inv : TrajInv m b₁ b₂ v₂ := traj_invariants hm hb₁ hle
      refine active hv₂ hgt.le le_rfl inv.sup_nn le_rfl (add_zero _)
        (by simp [orderedClinching, hlt, hgt]) (fun i hi => ?_) (fun i j hi hij => ?_)
      · fin_cases i <;> dsimp at hi ⊢
        exacts [by linarith, by simp [hi, hzx1]]
      · fin_cases i <;> fin_cases j <;> dsimp at hi hij <;> try linarith
        refine inv.exh0 (by_contra fun hle_p0 => ?_)
        have h0 : trajX1 m b₁ b₂ v₂ = 0 := ite_eq_left (not_lt.mp hle_p0)
        linarith
    · obtain rfl : v₁ = v₂ := le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
      by_cases hv0 : v₁ = 0
      · subst hv0
        have h00 : orderedClinching m b₁ b₂ 0 0 = ⟨![0, 0], ![0, 0]⟩ := by simp [orderedClinching]
        refine orderedProps_of_eq h00 hv_nn
          ⟨fun i => by fin_cases i <;> simp,
            by simp [Fin.sum_univ_two]; linarith⟩
          (fun i => by fin_cases i <;> simp)
          (fun i => by fin_cases i <;> simp <;> linarith)
          (fun i => by fin_cases i <;> simp [Outcome.utility])
          (fun ⟨i, hi⟩ => by fin_cases i <;> simp at hi)
          (fun i j _ hij => by fin_cases i <;> fin_cases j <;> simp at hij)
      · have hS2 : 0 ≤ trajSupply m b₁ b₂ v₁ / 2 :=
          div_nonneg (traj_invariants hm hb₁ hle).sup_nn zero_le_two
        refine active hv₁ le_rfl le_rfl hS2 hS2 (add_halves _)
          (by simp [orderedClinching, hv0])
          (fun i hi => by fin_cases i <;> exact absurd hi hv0)
          (fun i j _ hij => by fin_cases i <;> fin_cases j <;> simp at hij)

private theorem swapOutcome_pareto {o : Outcome (Fin 2)} {m : ℝ} {v B : Fin 2 → ℝ}
    (h : o.IsParetoOptimal m (fun i => v (swap01 i)) (fun i => B (swap01 i))) :
    (swapOutcome o).IsParetoOptimal m v B := by
  have hsum_eq : ∀ f : Fin 2 → ℝ, (∑ i, f (swap01 i)) = ∑ i, f i := fun f => by
    simp only [Fin.sum_univ_two, swap01_zero, swap01_one]; ring
  refine ⟨⟨fun i => h.1.1 (swap01 i), ?_⟩,
    fun i => by simpa [swapOutcome, swap01_invol] using h.2.1 (swap01 i),
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
    exact ⟨fun i => h.1 (swap01 i), by simpa [swapOutcome, Fin.sum_univ_two, add_comm] using h.2⟩

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
  · simpa only [fin2_vec_eq B] using
      (orderedClinching_props hm (hB 0) hle (hv 0) (hv 1)).bf
  · intro i
    have h := (orderedClinching_props hm (hB 1) (lt_of_not_ge hle).le (hv 1) (hv 0)).bf (swap01 i)
    fin_cases i <;> simpa [swapOutcome, swap01] using h

/-- **Exact Pareto optimality** of the continuous 2-bidder adaptive clinching auction for every
supply `m > 0`, strictly positive public budgets `B`, and nonnegative valuations `v`
([DobzinskiLaviNisan2012], primary PDF not inspected). -/
theorem twoBidderClinching_isParetoOptimal {m : ℝ} (hm : 0 < m) {B v : Fin 2 → ℝ}
    (hB : ∀ i, 0 < B i) (hv : ∀ i, 0 ≤ v i) :
    (twoBidderClinching m B v).IsParetoOptimal m v B := by
  dsimp only [twoBidderClinching]
  split_ifs with hle
  · simpa only [fin2_vec_eq v, fin2_vec_eq B] using
      (orderedClinching_props hm (hB 0) hle (hv 0) (hv 1)).po
  · refine swapOutcome_pareto ?_
    convert (orderedClinching_props hm (hB 1) (lt_of_not_ge hle).le (hv 1) (hv 0)).po using 1 <;>
      ext i <;> fin_cases i <;> rfl

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
  · simpa only [Outcome.utility, fin2_vec_eq b] using
      (orderedClinching_props hm (hB 0) hle (hb 0) (hb 1)).ir i
  · have h := (orderedClinching_props hm (hB 1) (lt_of_not_ge hle).le (hb 1) (hb 0)).ir (swap01 i)
    fin_cases i <;> simpa [Outcome.utility, swapOutcome, swap01] using h

/-- Normalization of `twoBidderClinchingSP`: a bidder bidding `0` pays `0`. -/
theorem twoBidderClinchingSP_isNormalized {m : ℝ} (hm : 0 < m) {B : Fin 2 → ℝ}
    (hB : ∀ i, 0 < B i) :
    (twoBidderClinchingSP m B).IsNormalized := by
  have helper : ∀ {b₁ b₂ v₀ : ℝ}, 0 < b₁ → 0 ≤ v₀ →
      (orderedClinching m b₁ b₂ 0 v₀).payment 0 = 0 ∧
        (orderedClinching m b₁ b₂ v₀ 0).payment 1 = 0 := by
    intro b₁ b₂ v₀ hb₁ hv₀
    obtain ⟨_, hzp0, _, hzp1⟩ := orderedClinching_zero_vals (b₂ := b₂) hm hb₁
    rcases eq_or_lt_of_le hv₀ with rfl | hlt
    · simp [orderedClinching]
    · exact ⟨by simp [orderedClinching, hlt, hzp0],
        by simp [orderedClinching, not_lt.mpr hv₀, hlt, hzp1]⟩
  intro i b hb
  dsimp only [twoBidderClinchingSP, BudgetedMechanism.toSingleParameter,
    twoBidderClinchingMechanism, twoBidderClinching]
  split_ifs with hle
  · fin_cases i
    exacts [(helper (hB 0) (hb 1)).1, (helper (hB 0) (hb 0)).2]
  · fin_cases i
    exacts [(helper (hB 1) (hb 1)).2, (helper (hB 1) (hb 0)).1]

private theorem ordered_dsic_zero_branch {m v b : ℝ} (hm : 0 < m) (hv : 0 ≤ v) :
    (if 0 < b then v * m else 0) ≤ (if 0 < v then v * m else 0) := by
  split_ifs with hzb hzv
  · exact le_rfl
  · obtain rfl : v = 0 := le_antisymm (le_of_not_gt hzv) hv
    simp
  · exact mul_nonneg hv hm.le
  · exact le_rfl

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
          (orderedClinching m b₁ b₂ z 0).payment 0 = if 0 < z then v₁ * m else 0 := fun z hz => by
      rcases eq_or_lt_of_le hz with rfl | hzp
      · simp [orderedClinching]
      · simp [orderedClinching, not_lt.mpr hz, hzp, hzx0, hzp0, hS0]
    rw [eval0 b₁' hb₁', eval0 v₁ hv₁]
    exact ordered_dsic_zero_branch hm hv₁
  · have heval : ∀ z : ℝ,
        v₁ * (orderedClinching m b₁ b₂ z v₂).alloc 0 - (orderedClinching m b₁ b₂ z v₂).payment 0 =
          if z < v₂ then v₁ * trajX0 m b₁ b₂ z - trajP0 m b₁ b₂ z
          else if v₂ < z then
            v₁ * (trajX0 m b₁ b₂ v₂ + trajSupply m b₁ b₂ v₂) -
              (trajP0 m b₁ b₂ v₂ + v₂ * trajSupply m b₁ b₂ v₂)
          else
            v₁ * (trajX0 m b₁ b₂ v₂ + trajSupply m b₁ b₂ v₂ / 2) -
              (trajP0 m b₁ b₂ v₂ + v₂ * (trajSupply m b₁ b₂ v₂ / 2)) := fun z => by
      rcases lt_trichotomy z v₂ with h1 | rfl | h2
      · simp [orderedClinching, h1]
      · simp [orderedClinching, hv₂0]
      · simp [orderedClinching, not_lt.mpr h2.le, h2]
    rw [heval b₁', heval v₁]
    exact env_stop_dsic (traj0_isEnvCurve (b₂ := b₂) hm hb₁)
      (fun t _ => (traj_invariants hm hb₁ hle (p := t)).sup_nn) hv₂ hv₁ hb₁'

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
          (orderedClinching m b₁ b₂ 0 z).payment 1 = if 0 < z then v₂ * m else 0 := fun z hz => by
      rcases eq_or_lt_of_le hz with rfl | hzp
      · simp [orderedClinching]
      · simp [orderedClinching, hzp, hzx1, hzp1, hS0]
    rw [eval0 b₂' hb₂', eval0 v₂ hv₂]
    exact ordered_dsic_zero_branch hm hv₂
  · have heval : ∀ z : ℝ,
        v₂ * (orderedClinching m b₁ b₂ v₁ z).alloc 1 - (orderedClinching m b₁ b₂ v₁ z).payment 1 =
          if z < v₁ then v₂ * trajX1 m b₁ b₂ z - trajP1 m b₁ b₂ z
          else if v₁ < z then
            v₂ * (trajX1 m b₁ b₂ v₁ + trajSupply m b₁ b₂ v₁) -
              (trajP1 m b₁ b₂ v₁ + v₁ * trajSupply m b₁ b₂ v₁)
          else
            v₂ * (trajX1 m b₁ b₂ v₁ + trajSupply m b₁ b₂ v₁ / 2) -
              (trajP1 m b₁ b₂ v₁ + v₁ * (trajSupply m b₁ b₂ v₁ / 2)) := fun z => by
      rcases lt_trichotomy z v₁ with h1 | rfl | h2
      · simp [orderedClinching, h1, not_lt.mpr h1.le]
      · simp [orderedClinching, hv₁0]
      · simp [orderedClinching, not_lt.mpr h2.le, h2]
    rw [heval b₂', heval v₂]
    exact env_stop_dsic (traj1_isEnvCurve hm hb₁ hle)
      (fun t _ => (traj_invariants hm hb₁ hle (p := t)).sup_nn) hv₁ hv₂ hb₂'

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
  have h1 : (23 / 20 : ℝ) ≤ Real.exp (3 / 20) := by linarith [Real.add_one_le_exp (3 / 20 : ℝ)]
  have hpow : (2 : ℝ) < Real.exp (3 / 4) := by
    calc (2 : ℝ) < (23 / 20 : ℝ) ^ 5 := by norm_num
      _ ≤ (Real.exp (3 / 20)) ^ 5 := pow_le_pow_left₀ (by norm_num) h1 5
      _ = Real.exp (3 / 4) := by
        rw [← Real.exp_nat_mul]
        norm_num
  calc Real.log 2
      < Real.log (Real.exp (3 / 4)) := Real.log_lt_log (by norm_num) hpow
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
  have hlt_v : (2 : ℝ) / m < 10 / m := by rw [div_lt_div_iff_of_pos_right hm]; norm_num
  have hnot_lt : ¬ (10 / m < 2 / m) := not_lt.mpr hlt_v.le
  have hpe_hon : eqPrice m 1 1 = 1 / m := by simp [eqPrice, entryPrice]
  have hpe_dev : eqPrice m 1 (1 + Real.log 2) = 2 / m := by
    simp only [eqPrice, entryPrice, add_sub_cancel_left, div_one, Real.exp_log zero_lt_two]
    ring
  have hgt_p0 : ¬ (2 / m ≤ 1 / m) := by rw [not_le, div_lt_div_iff_of_pos_right hm]; norm_num
  have hout1 : ∀ {σ : Fin 2 → BidderType} {b₂ : ℝ},
      σ 0 = ⟨10 / m, 1⟩ → σ 1 = ⟨2 / m, b₂⟩ → 1 ≤ b₂ →
      ((twoBidderClinchingMechanism m).outcome σ).alloc 1 = trajX1 m 1 b₂ (2 / m) ∧
        ((twoBidderClinchingMechanism m).outcome σ).payment 1 = trajP1 m 1 b₂ (2 / m) := by
    intro σ b₂ h0 h1 hle
    simp [twoBidderClinchingMechanism, twoBidderClinching, orderedClinching, h0, h1, hle,
      hnot_lt, hlt_v]
  obtain ⟨hhon_x0, hhon_p0⟩ := hout1 (σ := θ) rfl rfl le_rfl
  have hhon_x : ((twoBidderClinchingMechanism m).outcome θ).alloc 1 = 3 / 8 * m := by
    simp only [hhon_x0, trajX1, entryPrice, hpe_hon, hgt_p0, ↓reduceIte]
    field_simp [hm.ne']; ring
  have hhon_p : ((twoBidderClinchingMechanism m).outcome θ).payment 1 = 1 / 2 := by
    simp only [hhon_p0, trajP1, entryPrice, hpe_hon, hgt_p0, ↓reduceIte]
    field_simp [hm.ne']; ring
  have hhon_u : ((twoBidderClinchingMechanism m).outcome θ).utility (fun k => (θ k).val) 1 =
      1 / 4 := by
    simp only [Outcome.utility, hhon_x, hhon_p, θ, Matrix.cons_val_one, Matrix.cons_val_zero]
    field_simp [hm.ne']; norm_num
  obtain ⟨hdev_x0, hdev_p0⟩ := hout1 (σ := Function.update θ 1 b')
    (Function.update_of_ne (by decide) ..) (Function.update_self ..) (by linarith)
  have hdev_x : ((twoBidderClinchingMechanism m).outcome (Function.update θ 1 b')).alloc 1 =
      m / 2 := by
    simp only [hdev_x0, trajX1, entryPrice, hpe_dev, hgt_p0, le_rfl, ↓reduceIte]
    field_simp [hm.ne']; ring
  have hdev_p : ((twoBidderClinchingMechanism m).outcome (Function.update θ 1 b')).payment 1 =
      Real.log 2 := by
    simp only [hdev_p0, trajP1, entryPrice, hpe_dev, hgt_p0, le_rfl, ↓reduceIte, one_mul]
    exact congrArg Real.log (by field_simp [hm.ne'])
  have hdev_u : ((twoBidderClinchingMechanism m).outcome (Function.update θ 1 b')).utility
      (fun k => (θ k).val) 1 = 1 - Real.log 2 := by
    simp only [Outcome.utility, hdev_x, hdev_p, θ, Matrix.cons_val_one, Matrix.cons_val_zero]
    field_simp [hm.ne']
  refine ⟨fun k => ?_, ⟨div_pos zero_lt_two hm, by linarith⟩, hhon_p, hhon_u, hdev_p,
    hdev_p.trans_le (hlog_lt.le.trans (by norm_num [θ])), hdev_u,
    by linarith [hhon_u, hdev_u]⟩
  fin_cases k <;> exact ⟨div_pos (by norm_num) hm, zero_lt_one⟩

/-- The continuous 2-bidder adaptive clinching auction is **not** private-budget DSIC for any
supply `m > 0`. -/
theorem twoBidderClinching_not_privateBudgetDSIC {m : ℝ} (hm : 0 < m) :
    ¬ (twoBidderClinchingMechanism m).IsPrivateBudgetDSIC := by
  intro hic
  obtain ⟨hpos_θ, hpos_b', _, _, _, hpay_le, _, hlt⟩ :=
    twoBidderClinching_budget_manipulation hm
  linarith [hic ![⟨10 / m, 1⟩, ⟨2 / m, 1⟩] hpos_θ 1 ⟨2 / m, 1 + Real.log 2⟩ hpos_b' hpay_le]

end Cslib.GameTheory.BudgetedAuction
