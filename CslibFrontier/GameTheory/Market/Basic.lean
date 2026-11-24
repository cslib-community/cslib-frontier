/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Exchange and Fisher markets: Walras's law and the First Welfare Theorem

In an **Arrow–Debreu exchange market** (`ExchangeMarket`) a finite set `I` of traders exchanges a
finite set `G` of infinitely divisible goods ([ArrowDebreu1954]; [CodenottiVaradarajan2007],
Section 6.1.1, pp. 136–137). Each trader `i` holds a nonnegative initial endowment bundle
`endowment i : G → ℝ` and evaluates nonnegative consumption bundles by `utility i : (G → ℝ) → ℝ`.
At a price vector `p : G → ℝ`, trader `i`'s budget is the market value `expenditure p (endowment i)`
of their endowment, and their Marshallian **demand set** (`demandSet`) consists of the nonnegative
bundles within that budget maximizing `utility i`. A **competitive equilibrium**
(`ExchangeMarket.IsCompetitiveEquilibrium`) pairs an allocation `x : I → G → ℝ` with nonnegative
prices `p` such that every trader's bundle lies in their demand set, aggregate demand does not
exceed aggregate supply (`excessDemand x g ≤ 0`), and any good in strict excess supply has price
zero (`p g * excessDemand x g = 0`).

In a **Fisher market** (`FisherMarket`) buyers instead arrive with exogenous money budgets
`budget : I → ℝ` to purchase divisible goods of exogenous supply `supply : G → ℝ` ([Vazirani2007],
Section 5.1, pp. 103–104; [CodenottiVaradarajan2007], Section 6.2, p. 141). Both models share the
underlying consumer-choice primitives (`expenditure`, `IsBudgetFeasible`, `demandSet`,
`IsLocallyNonsatiated`, `linearUtility`), and every positive-budget Fisher market embeds into an
exchange market where each buyer holds a budget-proportional share of every good
(`FisherMarket.toExchangeMarket`; [CodenottiVaradarajan2007], Section 6.1.7, p. 140).

## Main definitions

* `Cslib.GameTheory.Market.expenditure`, `Cslib.GameTheory.Market.IsBudgetFeasible`,
  `Cslib.GameTheory.Market.demandSet`, `Cslib.GameTheory.Market.IsLocallyNonsatiated`: bundle cost,
  budget feasibility, Marshallian demand correspondence, and local nonsatiation on nonnegative
  bundles.
* `Cslib.GameTheory.Market.linearUtility`: additive linear utility `∑ g, v g * b g`.
* `Cslib.GameTheory.Market.ExchangeMarket`: Arrow–Debreu exchange economy, with `totalSupply`,
  `income`, `IsBudgetFeasible`, `demandSet`, `IsFeasibleAllocation`, `excessDemand`,
  `IsCompetitiveEquilibrium`, and `IsParetoOptimal`.
* `Cslib.GameTheory.Market.LinearExchangeMarket`: linear Arrow–Debreu exchange economy, bridged to
  `ExchangeMarket` via `LinearExchangeMarket.toExchangeMarket`.
* `Cslib.GameTheory.Market.FisherMarket`: Fisher market with exogenous buyer budgets and good
  supplies, with `totalBudget`, `IsEquilibrium`, `IsParetoOptimal`, and `toExchangeMarket`.

## Main results

* `Cslib.GameTheory.Market.demandSet_smul`: Marshallian demand is homogeneous of degree zero in
  prices and budget (`0 < c`).
* `Cslib.GameTheory.Market.IsLocallyNonsatiated.expenditure_eq_of_mem_demandSet`: locally
  nonsatiated consumers exhaust their budgets at every optimal bundle.
* `Cslib.GameTheory.Market.mem_demandSet_linearUtility_iff`: at positive prices, a locally
  nonsatiated linear consumer demands precisely the budget-exhausting bundles supported on goods of
  maximum bang-per-buck `v g / p g`.
* `Cslib.GameTheory.Market.ExchangeMarket.walras_law`: **Walras's law**
  ([CodenottiVaradarajan2007], Section 6.1.1, p. 137): under local nonsatiation, the market value
  of aggregate excess demand vanishes (`expenditure p (E.excessDemand x) = 0`).
* `Cslib.GameTheory.Market.ExchangeMarket.IsCompetitiveEquilibrium.isParetoOptimal`: **First
  Welfare Theorem** ([ArrowDebreu1954]): under local nonsatiation, every competitive equilibrium
  allocation is Pareto optimal.
* `Cslib.GameTheory.Market.FisherMarket.IsEquilibrium.isParetoOptimal`: every Fisher market
  equilibrium under local nonsatiation is Pareto optimal.
* `Cslib.GameTheory.Market.FisherMarket.isEquilibrium_iff_toExchangeMarket`,
  `Cslib.GameTheory.Market.FisherMarket.isEquilibrium_smul_of_toExchangeMarket`: exact reduction
  from Fisher market equilibrium to Arrow–Debreu competitive equilibrium
  ([CodenottiVaradarajan2007], Section 6.1.7, p. 140).

## References

* [ArrowDebreu1954]
* [CodenottiVaradarajan2007]
* [Vazirani2007]
-/

public section

namespace Cslib.GameTheory.Market

/-! ### Consumer choice, budgets, and demand sets -/

section Consumer

variable {G : Type*} [Fintype G]

/-- Total expenditure `∑ g, p g * b g` of consumption bundle `b` at price vector `p`. -/
def expenditure (p b : G → ℝ) : ℝ :=
  ∑ g : G, p g * b g

theorem expenditure_eq_sum (p b : G → ℝ) : expenditure p b = ∑ g : G, p g * b g := by rfl

@[simp] theorem expenditure_zero_right (p : G → ℝ) : expenditure p 0 = 0 := by
  simp [expenditure]

@[simp] theorem expenditure_zero_left (b : G → ℝ) : expenditure 0 b = 0 := by
  simp [expenditure]

theorem expenditure_add (p b₁ b₂ : G → ℝ) :
    expenditure p (b₁ + b₂) = expenditure p b₁ + expenditure p b₂ := by
  simp only [expenditure, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem expenditure_sub (p b₁ b₂ : G → ℝ) :
    expenditure p (b₁ - b₂) = expenditure p b₁ - expenditure p b₂ := by
  simp only [expenditure, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem expenditure_smul_left (c : ℝ) (p b : G → ℝ) :
    expenditure (c • p) b = c * expenditure p b := by
  simp only [expenditure, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]

theorem expenditure_smul_right (c : ℝ) (p b : G → ℝ) :
    expenditure p (c • b) = c * expenditure p b := by
  simp only [expenditure, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun g _ => by ring

theorem expenditure_nonneg {p b : G → ℝ} (hp : ∀ g, 0 ≤ p g) (hb : ∀ g, 0 ≤ b g) :
    0 ≤ expenditure p b :=
  Finset.sum_nonneg fun g _ => mul_nonneg (hp g) (hb g)

/-- Bundle `b` is **budget-feasible** at prices `p` and scalar budget `m` if it is nonnegative and
its expenditure is at most `m`. -/
@[expose] def IsBudgetFeasible (p : G → ℝ) (m : ℝ) (b : G → ℝ) : Prop :=
  (∀ g, 0 ≤ b g) ∧ expenditure p b ≤ m

theorem IsBudgetFeasible.smul_price_budget {p : G → ℝ} {m c : ℝ} {b : G → ℝ} (hc : 0 < c) :
    IsBudgetFeasible (c • p) (c * m) b ↔ IsBudgetFeasible p m b := by
  simp only [IsBudgetFeasible, expenditure_smul_left, mul_le_mul_iff_right₀ hc]

/-- The **Marshallian demand set** of a consumer with utility `u` and budget `m` at prices `p`:
the set of budget-feasible bundles maximizing `u` ([CodenottiVaradarajan2007], Section 6.1.1,
p. 136). -/
def demandSet (u : (G → ℝ) → ℝ) (p : G → ℝ) (m : ℝ) : Set (G → ℝ) :=
  {b | IsBudgetFeasible p m b ∧ ∀ b', IsBudgetFeasible p m b' → u b' ≤ u b}

@[simp] theorem mem_demandSet {u : (G → ℝ) → ℝ} {p : G → ℝ} {m : ℝ} {b : G → ℝ} :
    b ∈ demandSet u p m ↔
      IsBudgetFeasible p m b ∧ ∀ b', IsBudgetFeasible p m b' → u b' ≤ u b :=
  Iff.rfl

/-- Marshallian demand is homogeneous of degree zero in `(p, m)` for positive scalars `c > 0`
([CodenottiVaradarajan2007], Section 6.1.1, p. 137). -/
theorem demandSet_smul (u : (G → ℝ) → ℝ) (p : G → ℝ) (m : ℝ) {c : ℝ} (hc : 0 < c) :
    demandSet u (c • p) (c * m) = demandSet u p m := by
  ext b
  simp only [mem_demandSet, IsBudgetFeasible.smul_price_budget hc]

/-- A utility function `u : (G → ℝ) → ℝ` is **locally nonsatiated** on nonnegative consumption
bundles if every `ℓ_∞`-neighborhood of every nonnegative bundle contains a strictly preferred
nonnegative bundle ([ArrowDebreu1954]). Note that [CodenottiVaradarajan2007], Section 6.1.1,
p. 136 assumes concavity, global nonsatiation, and monotonicity, whereas we assume local
nonsatiation directly. -/
@[expose] def IsLocallyNonsatiated (u : (G → ℝ) → ℝ) : Prop :=
  ∀ b : G → ℝ, (∀ g, 0 ≤ b g) → ∀ ε : ℝ, 0 < ε →
    ∃ b' : G → ℝ, (∀ g, 0 ≤ b' g) ∧ (∀ g, |b' g - b g| < ε) ∧ u b < u b'

/-- Under local nonsatiation, any nonnegative bundle `b'` weakly preferred to a demanded bundle `b`
costs at least the consumer's budget `m`; otherwise a nearby strictly preferred bundle would also
be affordable. -/
theorem IsLocallyNonsatiated.le_expenditure_of_mem_demandSet {u : (G → ℝ) → ℝ}
    (hlns : IsLocallyNonsatiated u) {p : G → ℝ} {m : ℝ} {b b' : G → ℝ}
    (hb : b ∈ demandSet u p m) (hb'_nn : ∀ g, 0 ≤ b' g) (hub : u b ≤ u b') :
    m ≤ expenditure p b' := by
  by_contra hlt
  push Not at hlt
  set δ : ℝ := m - expenditure p b'
  have hδ : 0 < δ := sub_pos.2 hlt
  set S : ℝ := ∑ g : G, |p g|
  have hS_nn : 0 ≤ S := Finset.sum_nonneg fun g _ => abs_nonneg (p g)
  have hden : 0 < 1 + S := by linarith
  obtain ⟨z, hz_nn, hz_dist, huz⟩ := hlns b' hb'_nn (δ / (1 + S)) (div_pos hδ hden)
  have hz_exp : expenditure p z ≤ m := by
    have hdiff : expenditure p z - expenditure p b' ≤ S * (δ / (1 + S)) := by
      calc
        expenditure p z - expenditure p b'
          = expenditure p (z - b') := (expenditure_sub p z b').symm
        _ ≤ ∑ g : G, |p g| * |z g - b' g| := by
            refine Finset.sum_le_sum fun g _ => ?_
            simp only [Pi.sub_apply, ← abs_mul]
            exact le_abs_self _
        _ ≤ ∑ g : G, |p g| * (δ / (1 + S)) := by
            refine Finset.sum_le_sum fun g _ => ?_
            exact mul_le_mul_of_nonneg_left (hz_dist g).le (abs_nonneg (p g))
        _ = S * (δ / (1 + S)) := by rw [← Finset.sum_mul]
    have hS_le : S * (δ / (1 + S)) ≤ δ := by
      rw [mul_div_assoc', div_le_iff₀ hden]
      nlinarith
    linarith
  have hz_feas : IsBudgetFeasible p m z := ⟨hz_nn, hz_exp⟩
  linarith [hb.2 z hz_feas]

/-- **Budget exhaustion**: a locally nonsatiated consumer spends their entire budget at every
optimal bundle. -/
theorem IsLocallyNonsatiated.expenditure_eq_of_mem_demandSet {u : (G → ℝ) → ℝ}
    (hlns : IsLocallyNonsatiated u) {p : G → ℝ} {m : ℝ} {b : G → ℝ}
    (hb : b ∈ demandSet u p m) : expenditure p b = m :=
  le_antisymm hb.1.2 (hlns.le_expenditure_of_mem_demandSet hb hb.1.1 le_rfl)

/-- Any nonnegative bundle strictly preferred to a demanded bundle strictly exceeds the consumer's
budget (valid without local nonsatiation). -/
theorem lt_expenditure_of_mem_demandSet {u : (G → ℝ) → ℝ} {p : G → ℝ} {m : ℝ} {b b' : G → ℝ}
    (hb : b ∈ demandSet u p m) (hb'_nn : ∀ g, 0 ≤ b' g) (hub : u b < u b') :
    m < expenditure p b' := by
  by_contra hle
  push Not at hle
  exact not_le_of_gt hub (hb.2 b' ⟨hb'_nn, hle⟩)

/-- At nonnegative prices, a locally nonsatiated consumer can have a nonempty demand set only if
at least one good has a strictly positive price. -/
theorem IsLocallyNonsatiated.exists_price_pos_of_mem_demandSet {u : (G → ℝ) → ℝ}
    (hlns : IsLocallyNonsatiated u) {p : G → ℝ} {m : ℝ} {b : G → ℝ}
    (hp : ∀ g, 0 ≤ p g) (hb : b ∈ demandSet u p m) : ∃ g : G, 0 < p g := by
  by_contra hzero
  push Not at hzero
  have hp0 : ∀ g, p g = 0 := fun g => le_antisymm (hzero g) (hp g)
  have hm_nn : 0 ≤ m := by
    calc
      0 ≤ expenditure p b := expenditure_nonneg hp hb.1.1
      _ ≤ m := hb.1.2
  obtain ⟨b', hb'_nn, -, hub⟩ := hlns b hb.1.1 1 one_pos
  have hb'_exp : expenditure p b' = 0 := by simp [expenditure, hp0]
  exact not_le_of_gt hub (hb.2 b' ⟨hb'_nn, by linarith⟩)

/-! ### Linear utilities and bang-per-buck demand -/

/-- Additive **linear utility** `∑ g, v g * b g` with marginal utility vector `v : G → ℝ`
([Vazirani2007], Section 5.2, p. 105; [CodenottiVaradarajan2007], Section 6.1.5, p. 139). -/
def linearUtility (v : G → ℝ) (b : G → ℝ) : ℝ :=
  ∑ g : G, v g * b g

theorem linearUtility_eq_sum (v b : G → ℝ) : linearUtility v b = ∑ g : G, v g * b g := by rfl

/-- A linear utility function `linearUtility v` is locally nonsatiated on nonnegative bundles if
and only if at least one good has strictly positive marginal utility. -/
theorem isLocallyNonsatiated_linearUtility_iff (v : G → ℝ) :
    IsLocallyNonsatiated (linearUtility v) ↔ ∃ g : G, 0 < v g := by
  classical
  constructor
  · intro hlns
    obtain ⟨b', hb'_nn, -, hpos⟩ := hlns 0 (fun _ => le_rfl) 1 one_pos
    simp only [linearUtility, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hpos
    by_contra hall
    push Not at hall
    have hle : ∑ g : G, v g * b' g ≤ 0 :=
      Finset.sum_nonpos fun g _ => mul_nonpos_of_nonpos_of_nonneg (hall g) (hb'_nn g)
    linarith
  · rintro ⟨g₀, hg₀⟩ b hb_nn ε hε
    refine ⟨Function.update b g₀ (b g₀ + ε / 2), ?_, ?_, ?_⟩
    · intro g
      by_cases h : g = g₀
      · subst h
        simp only [Function.update_self]
        linarith [hb_nn g]
      · simp only [Function.update_of_ne h]
        exact hb_nn g
    · intro g
      by_cases h : g = g₀
      · subst h
        simp only [Function.update_self, add_sub_cancel_left, abs_of_pos (half_pos hε)]
        linarith
      · simp only [Function.update_of_ne h, sub_self, abs_zero, hε]
    · have hdiff : linearUtility v (Function.update b g₀ (b g₀ + ε / 2)) - linearUtility v b =
          v g₀ * (ε / 2) := by
        simp only [linearUtility, ← Finset.sum_sub_distrib, ← mul_sub]
        rw [Finset.sum_eq_single g₀]
        · simp
        · intro g _ hne
          simp [Function.update_of_ne hne]
        · intro hmem
          exact False.elim (hmem (Finset.mem_univ g₀))
      nlinarith

/-- If a bundle `b` is optimal for `linearUtility v` at nonnegative prices `p`, every good with
strictly positive marginal utility must have strictly positive price. -/
theorem price_pos_of_mem_demandSet_linearUtility {v p : G → ℝ} {m : ℝ} {b : G → ℝ}
    (hp : ∀ g, 0 ≤ p g) (hb : b ∈ demandSet (linearUtility v) p m) {g : G} (hvg : 0 < v g) :
    0 < p g := by
  classical
  refine lt_of_le_of_ne (hp g) fun hpg => ?_
  have hpg0 : p g = 0 := hpg.symm
  let b' : G → ℝ := Function.update b g (b g + 1)
  have hb'_nn : ∀ g', 0 ≤ b' g' := by
    intro g'
    by_cases h : g' = g
    · subst h
      simp only [b', Function.update_self]
      linarith [hb.1.1 g']
    · simp only [b', Function.update_of_ne h]
      exact hb.1.1 g'
  have hb'_exp : expenditure p b' = expenditure p b := by
    have hdiff : expenditure p b' - expenditure p b = 0 := by
      simp only [expenditure, ← Finset.sum_sub_distrib, ← mul_sub]
      rw [Finset.sum_eq_single g]
      · simp [b', hpg0]
      · intro g' _ hne
        simp [b', Function.update_of_ne hne]
      · intro hmem
        exact False.elim (hmem (Finset.mem_univ g))
    linarith
  have hub : linearUtility v b < linearUtility v b' := by
    have hdiff : linearUtility v b' - linearUtility v b = v g := by
      simp only [linearUtility, ← Finset.sum_sub_distrib, ← mul_sub]
      rw [Finset.sum_eq_single g]
      · simp [b']
      · intro g' _ hne
        simp [b', Function.update_of_ne hne]
      · intro hmem
        exact False.elim (hmem (Finset.mem_univ g))
    linarith
  exact not_le_of_gt hub (hb.2 b' ⟨hb'_nn, by linarith [hb.1.2]⟩)

private theorem sum_mul_update_two_sub [DecidableEq G] (w b : G → ℝ) {g g' : G} (hgg' : g' ≠ g)
    (val : ℝ) :
    ∑ x : G, w x * (Function.update (Function.update b g 0) g' (b g' + val) x - b x) =
      w g' * val - w g * b g := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ g),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hgg', Finset.mem_univ g'⟩)]
  have hrest : ∑ x ∈ (Finset.univ.erase g).erase g',
      w x * (Function.update (Function.update b g 0) g' (b g' + val) x - b x) = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    have hxg' : x ≠ g' := (Finset.mem_erase.1 hx).1
    have hxg : x ≠ g := (Finset.mem_erase.1 (Finset.mem_erase.1 hx).2).1
    simp [Function.update_of_ne hxg', Function.update_of_ne hxg]
  rw [hrest, add_zero]
  simp only [Function.update_of_ne (Ne.symm hgg'), Function.update_self]
  ring

/-- **Bang-per-buck characterization of linear demand** ([Vazirani2007], Section 5.2, pp. 105–106):
at strictly positive prices `p > 0`, a locally nonsatiated linear consumer (`∃ g, 0 < v g`) with
nonnegative marginal utilities `v ≥ 0` and budget `m ≥ 0` demands a bundle `b` if and only if `b`
is nonnegative, exhausts the budget `m`, and places positive weight only on goods maximizing the
utility-per-unit-money ratio `v g / p g`. -/
theorem mem_demandSet_linearUtility_iff {v p : G → ℝ} {m : ℝ} {b : G → ℝ}
    (hv : ∀ g, 0 ≤ v g) (hm : 0 ≤ m) (hp : ∀ g, 0 < p g) (hns : ∃ g, 0 < v g) :
    b ∈ demandSet (linearUtility v) p m ↔
      (∀ g, 0 ≤ b g) ∧ expenditure p b = m ∧
        ∀ g, 0 < b g → ∀ g', v g' / p g' ≤ v g / p g := by
  classical
  have hlns : IsLocallyNonsatiated (linearUtility v) :=
    (isLocallyNonsatiated_linearUtility_iff v).2 hns
  constructor
  · intro hb
    refine ⟨hb.1.1, hlns.expenditure_eq_of_mem_demandSet hb, ?_⟩
    intro g hbg g'
    by_cases hgg' : g' = g
    · subst hgg'
      exact le_rfl
    · have hpg : 0 < p g := hp g
      have hpg' : 0 < p g' := hp g'
      let b' : G → ℝ := Function.update (Function.update b g 0) g' (b g' + p g * b g / p g')
      have hb'_nn : ∀ k, 0 ≤ b' k := by
        intro k
        by_cases hk' : k = g'
        · subst hk'
          simp only [b', Function.update_self]
          exact add_nonneg (hb.1.1 k) (div_nonneg (mul_nonneg hpg.le hbg.le) hpg'.le)
        · by_cases hk : k = g
          · subst hk
            simp [b', Function.update_of_ne hk']
          · simp only [b', Function.update_of_ne hk', Function.update_of_ne hk]
            exact hb.1.1 k
      have hb'_exp : expenditure p b' = expenditure p b := by
        have hdiff : expenditure p b' - expenditure p b = 0 := by
          simp only [expenditure, ← Finset.sum_sub_distrib, ← mul_sub]
          rw [sum_mul_update_two_sub p b hgg' (p g * b g / p g')]
          field_simp [hpg'.ne']
          ring
        linarith
      have hfeas : IsBudgetFeasible p m b' := ⟨hb'_nn, by linarith [hb.1.2]⟩
      have hopt := hb.2 b' hfeas
      have hutil_diff : linearUtility v b' - linearUtility v b =
          v g' * (p g * b g / p g') - v g * b g := by
        simp only [linearUtility, ← Finset.sum_sub_distrib, ← mul_sub]
        exact sum_mul_update_two_sub v b hgg' (p g * b g / p g')
      have hle_mul : v g' * (p g * b g / p g') ≤ v g * b g := by linarith
      rw [div_le_div_iff₀ hpg' hpg]
      have hpos_bg : 0 < b g := hbg
      have hmul : v g' * p g * b g ≤ v g * p g' * b g := by
        have h1 : v g' * (p g * b g) ≤ v g * b g * p g' :=
          (div_le_iff₀ hpg').1 (by simpa only [mul_div_assoc'] using hle_mul)
        linarith
      exact le_of_mul_le_mul_right hmul hpos_bg
  · rintro ⟨hb_nn, hb_exp, hmax⟩
    refine ⟨⟨hb_nn, hb_exp.le⟩, fun b' hb' => ?_⟩
    obtain rfl | hm_pos := hm.eq_or_lt
    · have hb'0 : ∀ g, b' g = 0 := by
        intro g
        by_contra hne
        have hpos : 0 < b' g := lt_of_le_of_ne (hb'.1 g) (Ne.symm hne)
        have hterm : 0 < p g * b' g := mul_pos (hp g) hpos
        have hsum : p g * b' g ≤ expenditure p b' :=
          Finset.single_le_sum (fun k _ => mul_nonneg (hp k).le (hb'.1 k)) (Finset.mem_univ g)
        linarith [hb'.2]
      have hub'0 : linearUtility v b' = 0 := by simp [linearUtility, hb'0]
      rw [hub'0]
      exact Finset.sum_nonneg fun g _ => mul_nonneg (hv g) (hb_nn g)
    · have hex_pos : ∃ g₀ : G, 0 < b g₀ := by
        by_contra hall0
        push Not at hall0
        have hb0 : ∀ g, b g = 0 := fun g => le_antisymm (hall0 g) (hb_nn g)
        have hexp0 : expenditure p b = 0 := by simp [expenditure, hb0]
        linarith
      obtain ⟨g₀, hg₀⟩ := hex_pos
      set α : ℝ := v g₀ / p g₀
      have hα_nn : 0 ≤ α := div_nonneg (hv g₀) (hp g₀).le
      have hv_le : ∀ g', v g' ≤ α * p g' := fun g' =>
        (div_le_iff₀ (hp g')).1 (hmax g₀ hg₀ g')
      have hub_eq : linearUtility v b = α * m := by
        have hterm : ∀ g, v g * b g = α * (p g * b g) := by
          intro g
          rcases (hb_nn g).eq_or_lt with hbg0 | hbg
          · rw [← hbg0]
            simp
          · have h1 : v g / p g ≤ α := hmax g₀ hg₀ g
            have h2 : α ≤ v g / p g := hmax g hbg g₀
            have heq : v g / p g = α := le_antisymm h1 h2
            have hv_eq : v g = α * p g := by
              rw [← heq]
              exact (div_mul_cancel₀ (v g) (hp g).ne').symm
            rw [hv_eq, mul_assoc]
        calc
          linearUtility v b = ∑ g : G, α * (p g * b g) :=
            Finset.sum_congr rfl fun g _ => hterm g
          _ = α * expenditure p b := (Finset.mul_sum _ _ _).symm
          _ = α * m := by rw [hb_exp]
      calc
        linearUtility v b' = ∑ g : G, v g * b' g := rfl
        _ ≤ ∑ g : G, (α * p g) * b' g :=
          Finset.sum_le_sum fun g _ => mul_le_mul_of_nonneg_right (hv_le g) (hb'.1 g)
        _ = α * expenditure p b' := by
          simp only [expenditure, mul_assoc, ← Finset.mul_sum]
        _ ≤ α * m := mul_le_mul_of_nonneg_left hb'.2 hα_nn
        _ = linearUtility v b := hub_eq.symm

/-- Shared consumer-level First Welfare Theorem expenditure argument: if every agent `i` is locally
nonsatiated and chooses an optimal bundle `x i ∈ demandSet (u i) p (budget i)` at nonnegative prices
`p`, and total budget equals the market value of total supply (`∑ i, budget i = expenditure p
supply`), then no nonnegative allocation `y` respecting `supply` can Pareto-dominate `x`. -/
theorem not_exists_paretoImprovement {I : Type*} [Fintype I]
    {u : I → (G → ℝ) → ℝ} {budget : I → ℝ} {supply p : G → ℝ} {x : I → G → ℝ}
    (hp : ∀ g, 0 ≤ p g)
    (hdem : ∀ i, x i ∈ demandSet (u i) p (budget i))
    (hlns : ∀ i, IsLocallyNonsatiated (u i))
    (hbudget : ∑ i : I, budget i = expenditure p supply) :
    ¬ ∃ y : I → G → ℝ,
      ((∀ i g, 0 ≤ y i g) ∧ ∀ g : G, ∑ i : I, y i g ≤ supply g) ∧
      (∀ i, u i (x i) ≤ u i (y i)) ∧
      ∃ i, u i (x i) < u i (y i) := by
  rintro ⟨y, hy_feas, hy_le, ⟨i₀, hi₀⟩⟩
  have h_all : ∀ i ∈ (Finset.univ : Finset I), budget i ≤ expenditure p (y i) :=
    fun i _ => (hlns i).le_expenditure_of_mem_demandSet (hdem i) (hy_feas.1 i) (hy_le i)
  have h_strict : budget i₀ < expenditure p (y i₀) :=
    lt_expenditure_of_mem_demandSet (hdem i₀) (hy_feas.1 i₀) hi₀
  have hsum_lt : ∑ i : I, budget i < ∑ i : I, expenditure p (y i) :=
    Finset.sum_lt_sum h_all ⟨i₀, Finset.mem_univ i₀, h_strict⟩
  have hsum_le : ∑ i : I, expenditure p (y i) ≤ expenditure p supply := by
    calc
      ∑ i : I, expenditure p (y i)
        = ∑ g : G, p g * ∑ i : I, y i g := by
            simp only [expenditure, Finset.mul_sum]
            exact Finset.sum_comm
      _ ≤ ∑ g : G, p g * supply g :=
            Finset.sum_le_sum fun g _ => mul_le_mul_of_nonneg_left (hy_feas.2 g) (hp g)
      _ = expenditure p supply := rfl
  linarith

end Consumer

/-! ### Arrow–Debreu exchange markets -/

/-- An **Arrow–Debreu exchange market** ([ArrowDebreu1954]; [CodenottiVaradarajan2007],
Section 6.1.1, pp. 136–137) with traders `I` and divisible goods `G`: each trader `i` starts with a
nonnegative endowment `endowment i : G → ℝ` and evaluates consumption bundles via
`utility i : (G → ℝ) → ℝ`. -/
@[ext]
structure ExchangeMarket (I G : Type*) where
  /-- Initial endowment `endowment i g` of good `g` held by trader `i`. -/
  endowment : I → G → ℝ
  /-- Utility `utility i b` derived by trader `i` from consumption bundle `b : G → ℝ`. -/
  utility : I → (G → ℝ) → ℝ
  /-- Initial endowments are nonnegative. -/
  endowment_nonneg : ∀ (i : I) (g : G), 0 ≤ endowment i g

namespace ExchangeMarket

section Basic

variable {I G : Type*} [Fintype I] [Fintype G] (E : ExchangeMarket I G)

/-- Aggregate market supply `∑ i, endowment i g` of good `g`. -/
def totalSupply (g : G) : ℝ :=
  ∑ i : I, E.endowment i g

omit [Fintype G] in
theorem totalSupply_eq_sum (g : G) : E.totalSupply g = ∑ i : I, E.endowment i g := by rfl

omit [Fintype G] in
theorem totalSupply_nonneg (g : G) : 0 ≤ E.totalSupply g :=
  Finset.sum_nonneg fun i _ => E.endowment_nonneg i g

/-- Trader `i`'s endowment income `expenditure p (E.endowment i)` at prices `p`. -/
def income (p : G → ℝ) (i : I) : ℝ :=
  expenditure p (E.endowment i)

omit [Fintype I] in
theorem income_eq (p : G → ℝ) (i : I) : E.income p i = expenditure p (E.endowment i) := by rfl

omit [Fintype I] in
theorem income_nonneg {p : G → ℝ} (hp : ∀ g, 0 ≤ p g) (i : I) : 0 ≤ E.income p i :=
  expenditure_nonneg hp (E.endowment_nonneg i)

theorem sum_income (p : G → ℝ) : ∑ i : I, E.income p i = expenditure p E.totalSupply := by
  simp only [income, expenditure, totalSupply, Finset.mul_sum]
  exact Finset.sum_comm

/-- Bundle `b` is budget-feasible for trader `i` at prices `p`. -/
@[expose] def IsBudgetFeasible (p : G → ℝ) (i : I) (b : G → ℝ) : Prop :=
  Market.IsBudgetFeasible p (E.income p i) b

/-- Trader `i`'s Marshallian demand set at prices `p`. -/
def demandSet (p : G → ℝ) (i : I) : Set (G → ℝ) :=
  Market.demandSet (E.utility i) p (E.income p i)

omit [Fintype I] in
@[simp] theorem mem_demandSet {p : G → ℝ} {i : I} {b : G → ℝ} :
    b ∈ E.demandSet p i ↔ b ∈ Market.demandSet (E.utility i) p (E.income p i) :=
  Iff.rfl

omit [Fintype I] in
theorem demandSet_smul (p : G → ℝ) (i : I) {c : ℝ} (hc : 0 < c) :
    E.demandSet (c • p) i = E.demandSet p i := by
  simp only [demandSet, income, expenditure_smul_left]
  exact Market.demandSet_smul (E.utility i) p (expenditure p (E.endowment i)) hc

/-- An allocation `x : I → G → ℝ` is **feasible** (with free disposal) if every bundle is
nonnegative and aggregate consumption of each good does not exceed `E.totalSupply g`. -/
@[expose] def IsFeasibleAllocation (x : I → G → ℝ) : Prop :=
  (∀ (i : I) (g : G), 0 ≤ x i g) ∧ ∀ g : G, ∑ i : I, x i g ≤ E.totalSupply g

/-- Aggregate **excess demand** `(∑ i, x i g) - E.totalSupply g` for good `g` under allocation `x`
([CodenottiVaradarajan2007], Section 6.1.1, p. 137). -/
def excessDemand (x : I → G → ℝ) (g : G) : ℝ :=
  (∑ i : I, x i g) - E.totalSupply g

omit [Fintype G] in
theorem excessDemand_eq (x : I → G → ℝ) (g : G) :
    E.excessDemand x g = (∑ i : I, x i g) - E.totalSupply g := by rfl

theorem expenditure_excessDemand (p : G → ℝ) (x : I → G → ℝ) :
    expenditure p (E.excessDemand x) = ∑ i : I, (expenditure p (x i) - E.income p i) := by
  calc
    expenditure p (E.excessDemand x)
      = (∑ g : G, p g * ∑ i : I, x i g) - expenditure p E.totalSupply := by
          simp only [expenditure, excessDemand, mul_sub, Finset.sum_sub_distrib]
    _ = (∑ i : I, expenditure p (x i)) - ∑ i : I, E.income p i := by
          rw [E.sum_income p]
          congr 1
          simp only [expenditure, Finset.mul_sum]
          exact Finset.sum_comm
    _ = ∑ i : I, (expenditure p (x i) - E.income p i) :=
          (Finset.sum_sub_distrib _ _).symm

/-- **Weak Walras inequality**: if every trader chooses a budget-feasible bundle at prices `p`,
the market value of aggregate excess demand is nonpositive. -/
theorem expenditure_excessDemand_le_zero {p : G → ℝ} {x : I → G → ℝ}
    (hfeas : ∀ i, E.IsBudgetFeasible p i (x i)) :
    expenditure p (E.excessDemand x) ≤ 0 := by
  rw [E.expenditure_excessDemand]
  exact Finset.sum_nonpos fun i _ => sub_nonpos.2 (hfeas i).2

/-- **Walras's law** ([CodenottiVaradarajan2007], Section 6.1.1, p. 137): if every trader is
locally nonsatiated and selects an optimal bundle `x i ∈ E.demandSet p i`, then the total value of
excess demand vanishes (`expenditure p (E.excessDemand x) = 0`) at any price vector `p`. -/
theorem walras_law {p : G → ℝ} {x : I → G → ℝ}
    (hlns : ∀ i, IsLocallyNonsatiated (E.utility i))
    (hdem : ∀ i, x i ∈ E.demandSet p i) :
    expenditure p (E.excessDemand x) = 0 := by
  rw [E.expenditure_excessDemand]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [(hlns i).expenditure_eq_of_mem_demandSet (hdem i), sub_self]

/-- Consequence of Walras's law: if `expenditure p (E.excessDemand x) = 0`, good `g₀` has a
strictly positive price, and all other goods clear (`excessDemand x g = 0` for `g ≠ g₀`), then the
market for `g₀` also clears (`excessDemand x g₀ = 0`). -/
theorem excessDemand_eq_zero_of_other_goods {p : G → ℝ} {x : I → G → ℝ} {g₀ : G}
    (hwalras : expenditure p (E.excessDemand x) = 0) (hp₀ : 0 < p g₀)
    (hother : ∀ g, g ≠ g₀ → E.excessDemand x g = 0) :
    E.excessDemand x g₀ = 0 := by
  classical
  have hsingle : expenditure p (E.excessDemand x) = p g₀ * E.excessDemand x g₀ := by
    simp only [expenditure]
    refine Finset.sum_eq_single g₀ (fun g _ hne => ?_) (fun hmem => ?_)
    · rw [hother g hne, mul_zero]
    · exact False.elim (hmem (Finset.mem_univ g₀))
  rw [hsingle] at hwalras
  exact (mul_eq_zero.1 hwalras).resolve_left hp₀.ne'

/-- A **competitive (Walrasian) equilibrium** ([ArrowDebreu1954]; [CodenottiVaradarajan2007],
Section 6.1.1, p. 136) consists of an allocation `x` and nonnegative prices `p` such that every
trader maximizes utility within their endowment budget, no good is over-demanded
(`excessDemand x g ≤ 0`), and any good in strict excess supply has price zero
(`p g * excessDemand x g = 0`). -/
@[expose] def IsCompetitiveEquilibrium (x : I → G → ℝ) (p : G → ℝ) : Prop :=
  (∀ g, 0 ≤ p g) ∧ (∀ i, x i ∈ E.demandSet p i) ∧
    (∀ g, E.excessDemand x g ≤ 0) ∧ ∀ g, p g * E.excessDemand x g = 0

theorem IsCompetitiveEquilibrium.isFeasibleAllocation {E : ExchangeMarket I G}
    {x : I → G → ℝ} {p : G → ℝ} (heq : E.IsCompetitiveEquilibrium x p) :
    E.IsFeasibleAllocation x :=
  ⟨fun i g => (heq.2.1 i).1.1 g, fun g => sub_nonpos.1 (heq.2.2.1 g)⟩

/-- Scaling equilibrium prices by any positive constant preserves competitive equilibrium. -/
theorem IsCompetitiveEquilibrium.smul {E : ExchangeMarket I G}
    {x : I → G → ℝ} {p : G → ℝ} (heq : E.IsCompetitiveEquilibrium x p) {c : ℝ} (hc : 0 < c) :
    E.IsCompetitiveEquilibrium x (c • p) := by
  refine ⟨fun g => mul_nonneg hc.le (heq.1 g), fun i => ?_, heq.2.2.1, fun g => ?_⟩
  · rw [E.demandSet_smul p i hc]
    exact heq.2.1 i
  · simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, heq.2.2.2 g, mul_zero]

/-- Under local nonsatiation, Walras's law implies that `0 ≤ p`, individual demand optimality, and
nonpositive excess demand `excessDemand x g ≤ 0` automatically enforce complementary slackness
`p g * excessDemand x g = 0`. -/
theorem IsCompetitiveEquilibrium.of_locallyNonsatiated {E : ExchangeMarket I G}
    {x : I → G → ℝ} {p : G → ℝ}
    (hlns : ∀ i, IsLocallyNonsatiated (E.utility i))
    (hp : ∀ g, 0 ≤ p g) (hdem : ∀ i, x i ∈ E.demandSet p i)
    (hclear : ∀ g, E.excessDemand x g ≤ 0) :
    E.IsCompetitiveEquilibrium x p := by
  classical
  refine ⟨hp, hdem, hclear, fun g => ?_⟩
  have hwalras := E.walras_law hlns hdem
  have hnonpos : ∀ g' ∈ (Finset.univ : Finset G), p g' * E.excessDemand x g' ≤ 0 :=
    fun g' _ => mul_nonpos_of_nonneg_of_nonpos (hp g') (hclear g')
  have hrest : ∑ k ∈ Finset.univ.erase g, p k * E.excessDemand x k ≤ 0 :=
    Finset.sum_nonpos fun k _ => hnonpos k (Finset.mem_univ k)
  have hsplit := Finset.add_sum_erase Finset.univ (fun k => p k * E.excessDemand x k)
    (Finset.mem_univ g)
  have hsum0 : ∑ k : G, p k * E.excessDemand x k = 0 := hwalras
  linarith [hnonpos g (Finset.mem_univ g)]

/-- Every positively priced good clears with exact equality (`∑ i, x i g = E.totalSupply g`) in a
competitive equilibrium. -/
theorem IsCompetitiveEquilibrium.sum_eq_totalSupply_of_price_pos {E : ExchangeMarket I G}
    {x : I → G → ℝ} {p : G → ℝ} (heq : E.IsCompetitiveEquilibrium x p) {g : G} (hpg : 0 < p g) :
    ∑ i : I, x i g = E.totalSupply g := by
  have hz : E.excessDemand x g = 0 := (mul_eq_zero.1 (heq.2.2.2 g)).resolve_left hpg.ne'
  linarith [show E.excessDemand x g = (∑ i : I, x i g) - E.totalSupply g from rfl]

/-- A feasible allocation `x` is **Pareto optimal** if no feasible allocation `y` makes every
trader weakly better off and at least one trader strictly better off ([ArrowDebreu1954]). -/
@[expose] def IsParetoOptimal (x : I → G → ℝ) : Prop :=
  E.IsFeasibleAllocation x ∧
    ¬ ∃ y : I → G → ℝ, E.IsFeasibleAllocation y ∧
      (∀ i, E.utility i (x i) ≤ E.utility i (y i)) ∧
      ∃ i, E.utility i (x i) < E.utility i (y i)

/-- **First Welfare Theorem** ([ArrowDebreu1954]): in an exchange market where every trader's
utility function is locally nonsatiated, every competitive equilibrium allocation is Pareto
optimal. -/
theorem IsCompetitiveEquilibrium.isParetoOptimal {E : ExchangeMarket I G}
    {x : I → G → ℝ} {p : G → ℝ}
    (heq : E.IsCompetitiveEquilibrium x p)
    (hlns : ∀ i, IsLocallyNonsatiated (E.utility i)) :
    E.IsParetoOptimal x :=
  ⟨heq.isFeasibleAllocation,
    not_exists_paretoImprovement heq.1 heq.2.1 hlns (E.sum_income p)⟩

end Basic

end ExchangeMarket

/-! ### Linear Arrow–Debreu exchange markets -/

/-- A **linear Arrow–Debreu exchange market** ([Vazirani2007], Section 5.11, p. 122;
[CodenottiVaradarajan2007], Section 6.1.5 and Section 6.4.1, pp. 139, 147): each trader `i` has
nonnegative endowment `endowment i : G → ℝ` and nonnegative marginal utilities `utility i : G → ℝ`
inducing additive utility `linearUtility (utility i)`. -/
structure LinearExchangeMarket (I G : Type*) where
  /-- Initial endowment `endowment i g` of good `g` held by trader `i`. -/
  endowment : I → G → ℝ
  /-- Marginal utility `utility i g` derived by trader `i` per unit of good `g`. -/
  utility : I → G → ℝ
  /-- Initial endowments are nonnegative. -/
  endowment_nonneg : ∀ (i : I) (g : G), 0 ≤ endowment i g
  /-- Marginal utilities are nonnegative. -/
  utility_nonneg : ∀ (i : I) (g : G), 0 ≤ utility i g

namespace LinearExchangeMarket

variable {I G : Type*} [Fintype I] [Fintype G] (E : LinearExchangeMarket I G)

/-- View a `LinearExchangeMarket` as a general `ExchangeMarket` with `linearUtility`. -/
def toExchangeMarket : ExchangeMarket I G where
  endowment := E.endowment
  utility i := linearUtility (E.utility i)
  endowment_nonneg := E.endowment_nonneg

omit [Fintype I] in
@[simp] theorem toExchangeMarket_endowment : E.toExchangeMarket.endowment = E.endowment := by rfl

omit [Fintype I] in
@[simp] theorem toExchangeMarket_utility (i : I) :
    E.toExchangeMarket.utility i = linearUtility (E.utility i) := by rfl

/-- Competitive equilibrium of a linear exchange market. -/
@[expose] def IsCompetitiveEquilibrium (x : I → G → ℝ) (p : G → ℝ) : Prop :=
  E.toExchangeMarket.IsCompetitiveEquilibrium x p

/-- Pareto optimality in a linear exchange market. -/
@[expose] def IsParetoOptimal (x : I → G → ℝ) : Prop :=
  E.toExchangeMarket.IsParetoOptimal x

/-- **Walras's law for linear exchange markets**: when every trader desires at least one good,
every optimal demand profile satisfies `expenditure p (E.toExchangeMarket.excessDemand x) = 0`. -/
theorem walras_law {p : G → ℝ} {x : I → G → ℝ}
    (hns : ∀ i, ∃ g, 0 < E.utility i g)
    (hdem : ∀ i, x i ∈ E.toExchangeMarket.demandSet p i) :
    expenditure p (E.toExchangeMarket.excessDemand x) = 0 :=
  E.toExchangeMarket.walras_law
    (fun i => (isLocallyNonsatiated_linearUtility_iff (E.utility i)).2 (hns i)) hdem

/-- **First Welfare Theorem for linear exchange markets**: when every trader desires at least one
good, every competitive equilibrium allocation is Pareto optimal. -/
theorem IsCompetitiveEquilibrium.isParetoOptimal {E : LinearExchangeMarket I G}
    {x : I → G → ℝ} {p : G → ℝ}
    (heq : E.IsCompetitiveEquilibrium x p)
    (hns : ∀ i, ∃ g, 0 < E.utility i g) :
    E.IsParetoOptimal x :=
  ExchangeMarket.IsCompetitiveEquilibrium.isParetoOptimal heq
    (fun i => (isLocallyNonsatiated_linearUtility_iff (E.utility i)).2 (hns i))

/-- **Bang-per-buck characterization of linear Arrow–Debreu equilibrium** ([Vazirani2007],
Section 5.11, p. 122): at strictly positive prices `p > 0`, when every trader desires at least one
good, `(x, p)` is a competitive equilibrium if and only if `x` is nonnegative, clears every good's
total supply, exhausts every trader's endowment income, and allocates each trader only goods of
maximum marginal-utility-to-price ratio `E.utility i g / p g`. -/
theorem isCompetitiveEquilibrium_iff_bangPerBuck {x : I → G → ℝ} {p : G → ℝ}
    (hp : ∀ g, 0 < p g) (hns : ∀ i, ∃ g, 0 < E.utility i g) :
    E.IsCompetitiveEquilibrium x p ↔
      (∀ i g, 0 ≤ x i g) ∧
      (∀ g, ∑ i : I, x i g = E.toExchangeMarket.totalSupply g) ∧
      (∀ i, expenditure p (x i) = E.toExchangeMarket.income p i) ∧
      ∀ i g, 0 < x i g → ∀ g', E.utility i g' / p g' ≤ E.utility i g / p g := by
  have hp_nn : ∀ g, 0 ≤ p g := fun g => (hp g).le
  have hlns : ∀ i, IsLocallyNonsatiated (E.toExchangeMarket.utility i) :=
    fun i => (isLocallyNonsatiated_linearUtility_iff (E.utility i)).2 (hns i)
  constructor
  · intro heq
    refine ⟨fun i g => (heq.2.1 i).1.1 g,
      fun g => heq.sum_eq_totalSupply_of_price_pos (hp g),
      fun i => (hlns i).expenditure_eq_of_mem_demandSet (heq.2.1 i), ?_⟩
    intro i g hxg g'
    have hmem := (mem_demandSet_linearUtility_iff (E.utility_nonneg i)
      (E.toExchangeMarket.income_nonneg hp_nn i) hp (hns i)).1 (heq.2.1 i)
    exact hmem.2.2 g hxg g'
  · rintro ⟨hx_nn, hclear, hexp, hmax⟩
    have hdem : ∀ i, x i ∈ E.toExchangeMarket.demandSet p i := fun i =>
      (mem_demandSet_linearUtility_iff (E.utility_nonneg i)
        (E.toExchangeMarket.income_nonneg hp_nn i) hp (hns i)).2 ⟨hx_nn i, hexp i, hmax i⟩
    exact ExchangeMarket.IsCompetitiveEquilibrium.of_locallyNonsatiated hlns hp_nn hdem fun g => by
      simp [ExchangeMarket.excessDemand, hclear g]

end LinearExchangeMarket

/-! ### Fisher markets and reduction to Arrow–Debreu exchange -/

/-- A **Fisher market** ([Vazirani2007], Section 5.1, pp. 103–104; [CodenottiVaradarajan2007],
Section 6.2, p. 141) with buyers `I` and divisible goods `G`: each buyer `i` has an exogenous money
budget `budget i ≥ 0` and utility `utility i : (G → ℝ) → ℝ`, and each good `g` has supply
`supply g ≥ 0`. -/
structure FisherMarket (I G : Type*) where
  /-- Exogenous money budget `budget i` of buyer `i`. -/
  budget : I → ℝ
  /-- Available supply `supply g` of good `g`. -/
  supply : G → ℝ
  /-- Utility `utility i b` derived by buyer `i` from bundle `b : G → ℝ`. -/
  utility : I → (G → ℝ) → ℝ
  /-- Buyer budgets are nonnegative. -/
  budget_nonneg : ∀ i : I, 0 ≤ budget i
  /-- Good supplies are nonnegative. -/
  supply_nonneg : ∀ g : G, 0 ≤ supply g

namespace FisherMarket

variable {I G : Type*} [Fintype I] [Fintype G] (M : FisherMarket I G)

/-- Aggregate money budget `∑ i, M.budget i` of all buyers. -/
def totalBudget : ℝ :=
  ∑ i : I, M.budget i

omit [Fintype G] in
theorem totalBudget_eq_sum : M.totalBudget = ∑ i : I, M.budget i := by rfl

omit [Fintype G] in
theorem totalBudget_nonneg : 0 ≤ M.totalBudget :=
  Finset.sum_nonneg fun i _ => M.budget_nonneg i

/-- Buyer `i`'s Marshallian demand set at prices `p`. -/
def demandSet (p : G → ℝ) (i : I) : Set (G → ℝ) :=
  Market.demandSet (M.utility i) p (M.budget i)

omit [Fintype I] in
@[simp] theorem mem_demandSet {p : G → ℝ} {i : I} {b : G → ℝ} :
    b ∈ M.demandSet p i ↔ b ∈ Market.demandSet (M.utility i) p (M.budget i) :=
  Iff.rfl

/-- An allocation `x : I → G → ℝ` is **feasible** in Fisher market `M` if bundles are nonnegative
and aggregate consumption of each good `g` is at most `M.supply g`. -/
@[expose] def IsFeasibleAllocation (x : I → G → ℝ) : Prop :=
  (∀ (i : I) (g : G), 0 ≤ x i g) ∧ ∀ g : G, ∑ i : I, x i g ≤ M.supply g

/-- A **market equilibrium** of Fisher market `M` ([Vazirani2007], Section 5.1, p. 104;
[CodenottiVaradarajan2007], Section 6.2, p. 141): nonnegative prices `p` and an allocation `x`
such that every buyer chooses an optimal bundle in their budget, no good's supply is exceeded, and
every positively priced good is completely sold (`p g * (supply g - ∑ i, x i g) = 0`). -/
@[expose] def IsEquilibrium (x : I → G → ℝ) (p : G → ℝ) : Prop :=
  (∀ g, 0 ≤ p g) ∧ (∀ i, x i ∈ M.demandSet p i) ∧
    (∀ g, ∑ i : I, x i g ≤ M.supply g) ∧ ∀ g, p g * (M.supply g - ∑ i : I, x i g) = 0

theorem IsEquilibrium.isFeasibleAllocation {M : FisherMarket I G} {x : I → G → ℝ} {p : G → ℝ}
    (heq : M.IsEquilibrium x p) : M.IsFeasibleAllocation x :=
  ⟨fun i g => (heq.2.1 i).1.1 g, heq.2.2.1⟩

theorem IsEquilibrium.sum_eq_supply_of_price_pos {M : FisherMarket I G}
    {x : I → G → ℝ} {p : G → ℝ} (heq : M.IsEquilibrium x p) {g : G} (hpg : 0 < p g) :
    ∑ i : I, x i g = M.supply g := by
  have hz : M.supply g - ∑ i : I, x i g = 0 := (mul_eq_zero.1 (heq.2.2.2 g)).resolve_left hpg.ne'
  linarith

/-- **Fisher market Walras identity**: in any Fisher market equilibrium under local nonsatiation,
the total market value of all supplies equals the aggregate buyer budget (`expenditure p M.supply =
M.totalBudget`). -/
theorem IsEquilibrium.expenditure_supply_eq_totalBudget {M : FisherMarket I G}
    {x : I → G → ℝ} {p : G → ℝ} (heq : M.IsEquilibrium x p)
    (hlns : ∀ i, IsLocallyNonsatiated (M.utility i)) :
    expenditure p M.supply = M.totalBudget := by
  calc
    expenditure p M.supply
      = ∑ g : G, p g * ∑ i : I, x i g := by
          refine Finset.sum_congr rfl fun g _ => ?_
          linarith [heq.2.2.2 g]
    _ = ∑ i : I, expenditure p (x i) := by
          simp only [expenditure, Finset.mul_sum]
          exact Finset.sum_comm
    _ = M.totalBudget :=
          Finset.sum_congr rfl fun i _ => (hlns i).expenditure_eq_of_mem_demandSet (heq.2.1 i)

/-- A feasible allocation `x` in Fisher market `M` is **Pareto optimal** if no feasible allocation
makes every buyer weakly better off and at least one buyer strictly better off. -/
@[expose] def IsParetoOptimal (x : I → G → ℝ) : Prop :=
  M.IsFeasibleAllocation x ∧
    ¬ ∃ y : I → G → ℝ, M.IsFeasibleAllocation y ∧
      (∀ i, M.utility i (x i) ≤ M.utility i (y i)) ∧
      ∃ i, M.utility i (x i) < M.utility i (y i)

/-- **First Welfare Theorem for Fisher markets**: under local nonsatiation, every Fisher market
equilibrium allocation is Pareto optimal. -/
theorem IsEquilibrium.isParetoOptimal {M : FisherMarket I G} {x : I → G → ℝ} {p : G → ℝ}
    (heq : M.IsEquilibrium x p) (hlns : ∀ i, IsLocallyNonsatiated (M.utility i)) :
    M.IsParetoOptimal x :=
  ⟨heq.isFeasibleAllocation,
    not_exists_paretoImprovement heq.1 heq.2.1 hlns
      (heq.expenditure_supply_eq_totalBudget hlns).symm⟩

/-- **Fisher-to-Arrow–Debreu proportional-endowment embedding** ([CodenottiVaradarajan2007],
Section 6.1.7, p. 140; see also Section 6.2, p. 141): embed Fisher market `M` into an
`ExchangeMarket` by giving each buyer `i` fraction `M.budget i / M.totalBudget` of the supply of
every good `g`. -/
noncomputable def toExchangeMarket : ExchangeMarket I G where
  endowment i g := (M.budget i / M.totalBudget) * M.supply g
  utility := M.utility
  endowment_nonneg i g :=
    mul_nonneg (div_nonneg (M.budget_nonneg i) M.totalBudget_nonneg) (M.supply_nonneg g)

omit [Fintype G] in
@[simp] theorem toExchangeMarket_endowment (i : I) (g : G) :
    M.toExchangeMarket.endowment i g = (M.budget i / M.totalBudget) * M.supply g := by rfl

omit [Fintype G] in
@[simp] theorem toExchangeMarket_utility : M.toExchangeMarket.utility = M.utility := by rfl

omit [Fintype G] in
theorem toExchangeMarket_totalSupply (hB : 0 < M.totalBudget) (g : G) :
    M.toExchangeMarket.totalSupply g = M.supply g := by
  simp only [ExchangeMarket.totalSupply, toExchangeMarket, div_eq_mul_inv, ← Finset.sum_mul]
  change (M.totalBudget * M.totalBudget⁻¹) * M.supply g = M.supply g
  rw [mul_inv_cancel₀ hB.ne', one_mul]

theorem toExchangeMarket_income (p : G → ℝ) (i : I) :
    M.toExchangeMarket.income p i = (M.budget i / M.totalBudget) * expenditure p M.supply := by
  simp only [ExchangeMarket.income, toExchangeMarket, expenditure, mul_left_comm (p _),
    ← Finset.mul_sum]

/-- Under local nonsatiation and positive aggregate budget `0 < M.totalBudget`, `(x, p)` is a
Fisher equilibrium of `M` if and only if `expenditure p M.supply = M.totalBudget` and `(x, p)` is a
competitive equilibrium of `M.toExchangeMarket` ([CodenottiVaradarajan2007], Section 6.1.7,
p. 140). -/
theorem isEquilibrium_iff_toExchangeMarket {x : I → G → ℝ} {p : G → ℝ}
    (hB : 0 < M.totalBudget) (hlns : ∀ i, IsLocallyNonsatiated (M.utility i)) :
    M.IsEquilibrium x p ↔
      expenditure p M.supply = M.totalBudget ∧ M.toExchangeMarket.IsCompetitiveEquilibrium x p := by
  have hsup : ∀ g, M.toExchangeMarket.totalSupply g = M.supply g :=
    M.toExchangeMarket_totalSupply hB
  constructor
  · intro heq
    have hval := heq.expenditure_supply_eq_totalBudget hlns
    refine ⟨hval, heq.1, fun i => ?_, fun g => ?_, fun g => ?_⟩
    · have hinc : M.toExchangeMarket.income p i = M.budget i := by
        rw [M.toExchangeMarket_income, hval, div_mul_cancel₀ _ hB.ne']
      have hd : M.toExchangeMarket.demandSet p i = M.demandSet p i := by
        simp only [ExchangeMarket.demandSet, FisherMarket.demandSet, hinc]
        rfl
      rw [hd]
      exact heq.2.1 i
    · simp only [ExchangeMarket.excessDemand, hsup g]
      linarith [heq.2.2.1 g]
    · simp only [ExchangeMarket.excessDemand, hsup g]
      linarith [heq.2.2.2 g]
  · rintro ⟨hval, heq⟩
    refine ⟨heq.1, fun i => ?_, fun g => ?_, fun g => ?_⟩
    · have hinc : M.toExchangeMarket.income p i = M.budget i := by
        rw [M.toExchangeMarket_income, hval, div_mul_cancel₀ _ hB.ne']
      have hd : M.toExchangeMarket.demandSet p i = M.demandSet p i := by
        simp only [ExchangeMarket.demandSet, FisherMarket.demandSet, hinc]
        rfl
      rw [← hd]
      exact heq.2.1 i
    · have hle := heq.2.2.1 g
      simp only [ExchangeMarket.excessDemand, hsup g] at hle
      linarith
    · have hz := heq.2.2.2 g
      simp only [ExchangeMarket.excessDemand, hsup g] at hz
      linarith

/-- **Rescaling recovery** ([CodenottiVaradarajan2007], Section 6.1.7, p. 140): any competitive
equilibrium `(x, p)` of `M.toExchangeMarket` with positive aggregate supply value
`0 < expenditure p M.supply` rescales to an exact Fisher market equilibrium
`(x, (M.totalBudget / expenditure p M.supply) • p)` of `M`. -/
theorem isEquilibrium_smul_of_toExchangeMarket {x : I → G → ℝ} {p : G → ℝ}
    (hB : 0 < M.totalBudget) (hlns : ∀ i, IsLocallyNonsatiated (M.utility i))
    (heq : M.toExchangeMarket.IsCompetitiveEquilibrium x p)
    (hval : 0 < expenditure p M.supply) :
    M.IsEquilibrium x ((M.totalBudget / expenditure p M.supply) • p) := by
  rw [M.isEquilibrium_iff_toExchangeMarket hB hlns]
  refine ⟨?_, heq.smul (div_pos hB hval)⟩
  rw [expenditure_smul_left, div_mul_cancel₀ _ hval.ne']

end FisherMarket

end Cslib.GameTheory.Market
