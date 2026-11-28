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

* `Cslib.GameTheory.Market.IsBudgetFeasibleOn`, `Cslib.GameTheory.Market.demandSetOn`,
  `Cslib.GameTheory.Market.IsLocallyNonsatiatedOn`: general consumption-set (`X : Set (G → ℝ)`)
  versions of budget feasibility, Marshallian demand, and local nonsatiation, with specializations
  `Cslib.GameTheory.Market.expenditure`, `Cslib.GameTheory.Market.IsBudgetFeasible`,
  `Cslib.GameTheory.Market.demandSet`, `Cslib.GameTheory.Market.IsLocallyNonsatiated` on
  nonnegative bundles.
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
* `Cslib.GameTheory.Market.not_exists_paretoImprovementOn`,
  `Cslib.GameTheory.Market.not_exists_strictParetoImprovementOn`: shared consumer-level
  expenditure contradictions on general consumption sets (used by both exchange and production
  welfare theorems).
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

/-- Bundle `b` is **budget-feasible on `X`** at prices `p` and scalar budget `m` if `b ∈ X` and
its expenditure is at most `m`. -/
@[expose] def IsBudgetFeasibleOn (X : Set (G → ℝ)) (p : G → ℝ) (m : ℝ) (b : G → ℝ) : Prop :=
  b ∈ X ∧ expenditure p b ≤ m

theorem IsBudgetFeasibleOn.smul_price_budget {X : Set (G → ℝ)} {p : G → ℝ} {m c : ℝ}
    {b : G → ℝ} (hc : 0 < c) :
    IsBudgetFeasibleOn X (c • p) (c * m) b ↔ IsBudgetFeasibleOn X p m b := by
  simp only [IsBudgetFeasibleOn, expenditure_smul_left, mul_le_mul_iff_right₀ hc]

/-- Bundle `b` is **budget-feasible** at prices `p` and scalar budget `m` if it is nonnegative and
its expenditure is at most `m`. -/
@[expose] def IsBudgetFeasible (p : G → ℝ) (m : ℝ) (b : G → ℝ) : Prop :=
  (∀ g, 0 ≤ b g) ∧ expenditure p b ≤ m

theorem IsBudgetFeasible.smul_price_budget {p : G → ℝ} {m c : ℝ} {b : G → ℝ} (hc : 0 < c) :
    IsBudgetFeasible (c • p) (c * m) b ↔ IsBudgetFeasible p m b := by
  simp only [IsBudgetFeasible, expenditure_smul_left, mul_le_mul_iff_right₀ hc]

/-- The **Marshallian demand set on `X`** of a consumer with consumption set `X`, utility `u`,
and budget `m` at prices `p`. -/
def demandSetOn (X : Set (G → ℝ)) (u : (G → ℝ) → ℝ) (p : G → ℝ) (m : ℝ) : Set (G → ℝ) :=
  {b | IsBudgetFeasibleOn X p m b ∧ ∀ b', IsBudgetFeasibleOn X p m b' → u b' ≤ u b}

@[simp] theorem mem_demandSetOn {X : Set (G → ℝ)} {u : (G → ℝ) → ℝ} {p : G → ℝ} {m : ℝ}
    {b : G → ℝ} :
    b ∈ demandSetOn X u p m ↔
      IsBudgetFeasibleOn X p m b ∧ ∀ b', IsBudgetFeasibleOn X p m b' → u b' ≤ u b :=
  Iff.rfl

theorem demandSetOn_smul (X : Set (G → ℝ)) (u : (G → ℝ) → ℝ) (p : G → ℝ) (m : ℝ) {c : ℝ}
    (hc : 0 < c) :
    demandSetOn X u (c • p) (c * m) = demandSetOn X u p m := by
  ext b
  simp only [mem_demandSetOn, IsBudgetFeasibleOn.smul_price_budget hc]

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

/-- A utility function `u : (G → ℝ) → ℝ` is **locally nonsatiated on `X`** if every
`ℓ_∞`-neighborhood of every bundle `b ∈ X` contains a strictly preferred bundle `b' ∈ X`
([ArrowDebreu1954]). -/
@[expose] def IsLocallyNonsatiatedOn (X : Set (G → ℝ)) (u : (G → ℝ) → ℝ) : Prop :=
  ∀ b ∈ X, ∀ ε : ℝ, 0 < ε →
    ∃ b' ∈ X, (∀ g, |b' g - b g| < ε) ∧ u b < u b'

/-- A utility function `u : (G → ℝ) → ℝ` is **locally nonsatiated** on nonnegative consumption
bundles if every `ℓ_∞`-neighborhood of every nonnegative bundle contains a strictly preferred
nonnegative bundle ([ArrowDebreu1954]). Note that [CodenottiVaradarajan2007], Section 6.1.1,
p. 136 assumes concavity, global nonsatiation, and monotonicity, whereas we assume local
nonsatiation directly. -/
@[expose] def IsLocallyNonsatiated (u : (G → ℝ) → ℝ) : Prop :=
  ∀ b : G → ℝ, (∀ g, 0 ≤ b g) → ∀ ε : ℝ, 0 < ε →
    ∃ b' : G → ℝ, (∀ g, 0 ≤ b' g) ∧ (∀ g, |b' g - b g| < ε) ∧ u b < u b'

/-- Under local nonsatiation on `X`, any bundle `b' ∈ X` weakly preferred to a demanded bundle
`b ∈ demandSetOn X u p m` costs at least `m`. -/
theorem IsLocallyNonsatiatedOn.le_expenditure_of_mem_demandSetOn {X : Set (G → ℝ)}
    {u : (G → ℝ) → ℝ} (hlns : IsLocallyNonsatiatedOn X u) {p : G → ℝ} {m : ℝ} {b b' : G → ℝ}
    (hb : b ∈ demandSetOn X u p m) (hb'_mem : b' ∈ X) (hub : u b ≤ u b') :
    m ≤ expenditure p b' := by
  refine le_of_not_gt fun hlt => ?_
  set δ : ℝ := m - expenditure p b'
  have hδ : 0 < δ := sub_pos.2 hlt
  set S : ℝ := ∑ g : G, |p g|
  have hS_nn : 0 ≤ S := Finset.sum_nonneg fun g _ => abs_nonneg (p g)
  have hden : 0 < 1 + S := by linarith
  obtain ⟨z, hz_mem, hz_dist, huz⟩ := hlns b' hb'_mem (δ / (1 + S)) (div_pos hδ hden)
  have hz_exp : expenditure p z ≤ m := by
    have hdiff : expenditure p z - expenditure p b' ≤ S * (δ / (1 + S)) := by
      calc
        expenditure p z - expenditure p b'
          = expenditure p (z - b') := (expenditure_sub p z b').symm
        _ ≤ ∑ g : G, |p g| * (δ / (1 + S)) := by
            refine Finset.sum_le_sum fun g _ => (le_abs_self _).trans ?_
            rw [Pi.sub_apply, abs_mul]
            exact mul_le_mul_of_nonneg_left (hz_dist g).le (abs_nonneg (p g))
        _ = S * (δ / (1 + S)) := by rw [← Finset.sum_mul]
    have hS_le : S * (δ / (1 + S)) ≤ δ := by rw [mul_div_assoc', div_le_iff₀ hden]; nlinarith
    linarith
  linarith [hb.2 z ⟨hz_mem, hz_exp⟩]

/-- Budget exhaustion on general consumption sets `X`. -/
theorem IsLocallyNonsatiatedOn.expenditure_eq_of_mem_demandSetOn {X : Set (G → ℝ)}
    {u : (G → ℝ) → ℝ} (hlns : IsLocallyNonsatiatedOn X u) {p : G → ℝ} {m : ℝ} {b : G → ℝ}
    (hb : b ∈ demandSetOn X u p m) : expenditure p b = m :=
  le_antisymm hb.1.2 (hlns.le_expenditure_of_mem_demandSetOn hb hb.1.1 le_rfl)

/-- Any bundle `b' ∈ X` strictly preferred to a demanded bundle on `X` strictly exceeds the
consumer's budget (valid without local nonsatiation). -/
theorem lt_expenditure_of_mem_demandSetOn {X : Set (G → ℝ)} {u : (G → ℝ) → ℝ}
    {p : G → ℝ} {m : ℝ} {b b' : G → ℝ}
    (hb : b ∈ demandSetOn X u p m) (hb'_mem : b' ∈ X) (hub : u b < u b') :
    m < expenditure p b' :=
  lt_of_not_ge fun hle => not_le_of_gt hub (hb.2 b' ⟨hb'_mem, hle⟩)

/-- Under local nonsatiation, any nonnegative bundle `b'` weakly preferred to a demanded bundle `b`
costs at least the consumer's budget `m`; otherwise a nearby strictly preferred bundle would also
be affordable. -/
theorem IsLocallyNonsatiated.le_expenditure_of_mem_demandSet {u : (G → ℝ) → ℝ}
    (hlns : IsLocallyNonsatiated u) {p : G → ℝ} {m : ℝ} {b b' : G → ℝ}
    (hb : b ∈ demandSet u p m) (hb'_nn : ∀ g, 0 ≤ b' g) (hub : u b ≤ u b') :
    m ≤ expenditure p b' :=
  IsLocallyNonsatiatedOn.le_expenditure_of_mem_demandSetOn (X := {b | ∀ g, 0 ≤ b g})
    hlns hb hb'_nn hub

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
    m < expenditure p b' :=
  lt_expenditure_of_mem_demandSetOn (X := {b | ∀ g, 0 ≤ b g}) hb hb'_nn hub

/-- At nonnegative prices, a locally nonsatiated consumer can have a nonempty demand set only if
at least one good has a strictly positive price. -/
theorem IsLocallyNonsatiated.exists_price_pos_of_mem_demandSet {u : (G → ℝ) → ℝ}
    (hlns : IsLocallyNonsatiated u) {p : G → ℝ} {m : ℝ} {b : G → ℝ}
    (hp : ∀ g, 0 ≤ p g) (hb : b ∈ demandSet u p m) : ∃ g : G, 0 < p g := by
  by_contra hzero
  have hp0 : ∀ g, p g = 0 := fun g => le_antisymm (not_lt.mp fun h => hzero ⟨g, h⟩) (hp g)
  have hm_nn : 0 ≤ m := (expenditure_nonneg hp hb.1.1).trans hb.1.2
  obtain ⟨b', hb'_nn, -, hub⟩ := hlns b hb.1.1 1 one_pos
  exact not_le_of_gt hub (hb.2 b' ⟨hb'_nn, by simp [expenditure, hp0, hm_nn]⟩)

/-! ### Linear utilities and bang-per-buck demand -/

/-- Additive **linear utility** `∑ g, v g * b g` with marginal utility vector `v : G → ℝ`
([Vazirani2007], Section 5.2, p. 105; [CodenottiVaradarajan2007], Section 6.1.5, p. 139). -/
def linearUtility (v : G → ℝ) (b : G → ℝ) : ℝ :=
  ∑ g : G, v g * b g

theorem linearUtility_eq_sum (v b : G → ℝ) : linearUtility v b = ∑ g : G, v g * b g := by rfl

private theorem sum_mul_update_sub [DecidableEq G] (w b : G → ℝ) (g : G) (c : ℝ) :
    ∑ x : G, w x * (Function.update b g c x - b x) = w g * (c - b g) := by
  rw [Finset.sum_eq_single g (fun x _ hx => by simp [Function.update_of_ne hx]) (by simp)]
  simp

/-- A linear utility function `linearUtility v` is locally nonsatiated on nonnegative bundles if
and only if at least one good has strictly positive marginal utility. -/
theorem isLocallyNonsatiated_linearUtility_iff (v : G → ℝ) :
    IsLocallyNonsatiated (linearUtility v) ↔ ∃ g : G, 0 < v g := by
  classical
  constructor
  · intro hlns
    obtain ⟨b', hb'_nn, -, hpos⟩ := hlns 0 (fun _ => le_rfl) 1 one_pos
    obtain ⟨g, -, hg⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ) (f := fun _ => (0 : ℝ))
      (g := fun g => v g * b' g) (by simpa [linearUtility] using hpos)
    exact ⟨g, pos_of_mul_pos_left hg (hb'_nn g)⟩
  · rintro ⟨g₀, hg₀⟩ b hb_nn ε hε
    refine ⟨Function.update b g₀ (b g₀ + ε / 2),
      le_update_iff.2 ⟨by linarith [hb_nn g₀], fun j _ => hb_nn j⟩, fun g => ?_, ?_⟩
    · by_cases h : g = g₀ <;> simp [h, abs_of_pos (half_pos hε), half_lt_self hε, hε]
    · rw [← sub_pos]
      simpa [linearUtility, ← Finset.sum_sub_distrib, ← mul_sub, sum_mul_update_sub] using
        mul_pos hg₀ (half_pos hε)

/-- If a bundle `b` is optimal for `linearUtility v` at nonnegative prices `p`, every good with
strictly positive marginal utility must have strictly positive price. -/
theorem price_pos_of_mem_demandSet_linearUtility {v p : G → ℝ} {m : ℝ} {b : G → ℝ}
    (hp : ∀ g, 0 ≤ p g) (hb : b ∈ demandSet (linearUtility v) p m) {g : G} (hvg : 0 < v g) :
    0 < p g := by
  classical
  refine lt_of_le_of_ne (hp g) fun hpg => ?_
  let b' : G → ℝ := Function.update b g (b g + 1)
  have hb'_nn : ∀ g', 0 ≤ b' g' :=
    le_update_iff.2 ⟨by linarith [hb.1.1 g], fun j _ => hb.1.1 j⟩
  have hb'_exp : expenditure p b' = expenditure p b := by
    simp [← sub_eq_zero, b', expenditure, ← Finset.sum_sub_distrib, ← mul_sub,
      sum_mul_update_sub, hpg.symm]
  have hdiff : linearUtility v b' - linearUtility v b = v g := by
    simp [b', linearUtility, ← Finset.sum_sub_distrib, ← mul_sub, sum_mul_update_sub]
  exact not_le_of_gt (by linarith) (hb.2 b' ⟨hb'_nn, hb'_exp.symm ▸ hb.1.2⟩)

private theorem sum_mul_update_two_sub [DecidableEq G] (w b : G → ℝ) {g g' : G} (hgg' : g' ≠ g)
    (val : ℝ) :
    ∑ x : G, w x * (Function.update (Function.update b g 0) g' (b g' + val) x - b x) =
      w g' * val - w g * b g := by
  let u := Function.update b g 0
  have hsplit (x : G) : w x * (Function.update u g' (b g' + val) x - b x) =
      w x * (Function.update u g' (b g' + val) x - u x) + w x * (u x - b x) := by ring
  simp only [hsplit, Finset.sum_add_distrib, sum_mul_update_sub, u, Function.update_of_ne hgg']
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
  refine ⟨fun hb => ⟨hb.1.1, hlns.expenditure_eq_of_mem_demandSet hb, fun g hbg g' => ?_⟩, ?_⟩
  · obtain rfl | hgg' := eq_or_ne g' g
    · exact le_rfl
    · let b' : G → ℝ := Function.update (Function.update b g 0) g' (b g' + p g * b g / p g')
      have hb'_nn (k : G) : 0 ≤ b' k := by
        simp only [b', Function.update_apply]
        split_ifs
        exacts [add_nonneg (hb.1.1 _) (div_nonneg (mul_nonneg (hp g).le hbg.le) (hp g').le),
          le_rfl, hb.1.1 k]
      have hb'_exp : expenditure p b' = expenditure p b := by
        simp [← sub_eq_zero, b', expenditure, ← Finset.sum_sub_distrib, ← mul_sub,
          sum_mul_update_two_sub p b hgg', mul_div_cancel₀ _ (hp g').ne']
      have hutil_diff : linearUtility v b' - linearUtility v b =
          v g' * (p g * b g / p g') - v g * b g := by
        simp only [b', linearUtility, ← Finset.sum_sub_distrib, ← mul_sub,
          sum_mul_update_two_sub v b hgg']
      have hle_mul : v g' * (p g * b g / p g') ≤ v g * b g := by
        linarith [hb.2 b' ⟨hb'_nn, hb'_exp.trans_le hb.1.2⟩]
      rw [mul_div_assoc', div_le_iff₀ (hp g')] at hle_mul
      exact (div_le_div_iff₀ (hp g') (hp g)).2 (le_of_mul_le_mul_right (by linarith) hbg)
  · rintro ⟨hb_nn, hb_exp, hmax⟩
    refine ⟨⟨hb_nn, hb_exp.le⟩, fun b' hb' => ?_⟩
    obtain rfl | hm_pos := hm.eq_or_lt
    · have hb'0 (g : G) : b' g = 0 := by
        nlinarith [(Finset.single_le_sum (fun k _ => mul_nonneg (hp k).le (hb'.1 k))
          (Finset.mem_univ g)).trans hb'.2, hp g, hb'.1 g]
      simpa only [linearUtility, hb'0, mul_zero, Finset.sum_const_zero] using
        Finset.sum_nonneg fun g _ => mul_nonneg (hv g) (hb_nn g)
    · obtain ⟨g₀, -, hpb⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ)
        (f := fun _ => (0 : ℝ)) (g := fun g => p g * b g)
        (by rw [Finset.sum_const_zero, ← expenditure_eq_sum, hb_exp]; exact hm_pos)
      have hg₀ : 0 < b g₀ := pos_of_mul_pos_right hpb (hp g₀).le
      set α : ℝ := v g₀ / p g₀
      have hα_nn : 0 ≤ α := div_nonneg (hv g₀) (hp g₀).le
      have hv_le : ∀ g', v g' ≤ α * p g' := fun g' =>
        (div_le_iff₀ (hp g')).1 (hmax g₀ hg₀ g')
      have hub_eq : linearUtility v b = α * m := by
        rw [← hb_exp, expenditure, Finset.mul_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        rcases (hb_nn g).eq_or_lt with hbg0 | hbg
        · simp [← hbg0]
        · rw [← (le_antisymm (hmax g₀ hg₀ g) (hmax g hbg g₀) : v g / p g = α), ← mul_assoc,
            div_mul_cancel₀ _ (hp g).ne']
      calc
        linearUtility v b' ≤ ∑ g : G, (α * p g) * b' g :=
          Finset.sum_le_sum fun g _ => mul_le_mul_of_nonneg_right (hv_le g) (hb'.1 g)
        _ = α * expenditure p b' := by
          simp only [expenditure, mul_assoc, ← Finset.mul_sum]
        _ ≤ α * m := mul_le_mul_of_nonneg_left hb'.2 hα_nn
        _ = linearUtility v b := hub_eq.symm

/-- Shared consumer-level First Welfare Theorem expenditure argument on general consumption sets
and arbitrary coalitions `S : Finset I`: if every member `i ∈ S` is locally nonsatiated on `X i`
and demands `x i ∈ demandSetOn (X i) (u i) p (budget i)`, then no consumption profile
`y i ∈ X i` costing at most `∑ i ∈ S, budget i` can Pareto-dominate `x` on `S`. -/
theorem not_exists_paretoImprovementOn {I : Type*}
    {X : I → Set (G → ℝ)} {u : I → (G → ℝ) → ℝ} {budget : I → ℝ} {p : G → ℝ}
    {x y : I → G → ℝ} {S : Finset I}
    (hdem : ∀ i ∈ S, x i ∈ demandSetOn (X i) (u i) p (budget i))
    (hlns : ∀ i ∈ S, IsLocallyNonsatiatedOn (X i) (u i))
    (hy_mem : ∀ i ∈ S, y i ∈ X i)
    (hy_cost : ∑ i ∈ S, expenditure p (y i) ≤ ∑ i ∈ S, budget i) :
    ¬ ((∀ i ∈ S, u i (x i) ≤ u i (y i)) ∧ ∃ i ∈ S, u i (x i) < u i (y i)) := by
  rintro ⟨hy_le, i₀, hi₀S, hi₀⟩
  have hsum_lt : ∑ i ∈ S, budget i < ∑ i ∈ S, expenditure p (y i) :=
    Finset.sum_lt_sum
      (fun i hi => (hlns i hi).le_expenditure_of_mem_demandSetOn
        (hdem i hi) (hy_mem i hi) (hy_le i hi))
      ⟨i₀, hi₀S, lt_expenditure_of_mem_demandSetOn (hdem i₀ hi₀S) (hy_mem i₀ hi₀S) hi₀⟩
  linarith

/-- Local-nonsatiation-free strict Pareto expenditure argument on general consumption sets: if `S`
is nonempty and every `i ∈ S` demands `x i`, then no profile `y i ∈ X i` costing at most
`∑ i ∈ S, budget i` can make every `i ∈ S` strictly better off. -/
theorem not_exists_strictParetoImprovementOn {I : Type*}
    {X : I → Set (G → ℝ)} {u : I → (G → ℝ) → ℝ} {budget : I → ℝ} {p : G → ℝ}
    {x y : I → G → ℝ} {S : Finset I} (hS : S.Nonempty)
    (hdem : ∀ i ∈ S, x i ∈ demandSetOn (X i) (u i) p (budget i))
    (hy_mem : ∀ i ∈ S, y i ∈ X i)
    (hy_cost : ∑ i ∈ S, expenditure p (y i) ≤ ∑ i ∈ S, budget i) :
    ¬ ∀ i ∈ S, u i (x i) < u i (y i) := by
  intro hlt
  obtain ⟨i₀, hi₀⟩ := hS
  have hsum_lt : ∑ i ∈ S, budget i < ∑ i ∈ S, expenditure p (y i) :=
    Finset.sum_lt_sum
      (fun i hi => (lt_expenditure_of_mem_demandSetOn (hdem i hi) (hy_mem i hi) (hlt i hi)).le)
      ⟨i₀, hi₀, lt_expenditure_of_mem_demandSetOn (hdem i₀ hi₀) (hy_mem i₀ hi₀) (hlt i₀ hi₀)⟩
  linarith

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
  rintro ⟨y, hy_feas, hy_le, hi_lt⟩
  have hsum_le : ∑ i : I, expenditure p (y i) ≤ ∑ i : I, budget i := by
    calc
      ∑ i : I, expenditure p (y i)
        = ∑ g : G, p g * ∑ i : I, y i g := by
            simp only [expenditure, Finset.mul_sum]
            exact Finset.sum_comm
      _ ≤ ∑ g : G, p g * supply g :=
            Finset.sum_le_sum fun g _ => mul_le_mul_of_nonneg_left (hy_feas.2 g) (hp g)
      _ = ∑ i : I, budget i := hbudget.symm
  exact not_exists_paretoImprovementOn (X := fun _ => {b | ∀ g, 0 ≤ b g})
    (fun i _ => hdem i) (fun i _ => hlns i) (fun i _ => hy_feas.1 i) hsum_le
    ⟨fun i _ => hy_le i, let ⟨i₀, hi₀⟩ := hi_lt; ⟨i₀, Finset.mem_univ i₀, hi₀⟩⟩

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
  have hsingle : expenditure p (E.excessDemand x) = p g₀ * E.excessDemand x g₀ :=
    Finset.sum_eq_single g₀ (fun g _ hne => by rw [hother g hne, mul_zero]) (by simp)
  exact (mul_eq_zero.1 (hsingle ▸ hwalras)).resolve_left hp₀.ne'

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
    E.IsCompetitiveEquilibrium x (c • p) :=
  ⟨fun g => mul_nonneg hc.le (heq.1 g), fun i => (E.demandSet_smul p i hc).symm ▸ heq.2.1 i,
    heq.2.2.1, fun g => by simp [smul_eq_mul, mul_assoc, heq.2.2.2 g]⟩

/-- Under local nonsatiation, Walras's law implies that `0 ≤ p`, individual demand optimality, and
nonpositive excess demand `excessDemand x g ≤ 0` automatically enforce complementary slackness
`p g * excessDemand x g = 0`. -/
theorem IsCompetitiveEquilibrium.of_locallyNonsatiated {E : ExchangeMarket I G}
    {x : I → G → ℝ} {p : G → ℝ}
    (hlns : ∀ i, IsLocallyNonsatiated (E.utility i))
    (hp : ∀ g, 0 ≤ p g) (hdem : ∀ i, x i ∈ E.demandSet p i)
    (hclear : ∀ g, E.excessDemand x g ≤ 0) :
    E.IsCompetitiveEquilibrium x p := by
  refine ⟨hp, hdem, hclear, fun g => ?_⟩
  exact (Finset.sum_eq_zero_iff_of_nonpos fun k _ =>
    mul_nonpos_of_nonneg_of_nonpos (hp k) (hclear k)).1 (E.walras_law hlns hdem) g
    (Finset.mem_univ g)

/-- Every positively priced good clears with exact equality (`∑ i, x i g = E.totalSupply g`) in a
competitive equilibrium. -/
theorem IsCompetitiveEquilibrium.sum_eq_totalSupply_of_price_pos {E : ExchangeMarket I G}
    {x : I → G → ℝ} {p : G → ℝ} (heq : E.IsCompetitiveEquilibrium x p) {g : G} (hpg : 0 < p g) :
    ∑ i : I, x i g = E.totalSupply g := by
  exact sub_eq_zero.1 ((mul_eq_zero.1 (heq.2.2.2 g)).resolve_left hpg.ne')

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
    exact ⟨fun i g => (heq.2.1 i).1.1 g,
      fun g => heq.sum_eq_totalSupply_of_price_pos (hp g),
      fun i => (hlns i).expenditure_eq_of_mem_demandSet (heq.2.1 i), fun i =>
        ((mem_demandSet_linearUtility_iff (E.utility_nonneg i)
          (E.toExchangeMarket.income_nonneg hp_nn i) hp (hns i)).1 (heq.2.1 i)).2.2⟩
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
  exact (sub_eq_zero.1 ((mul_eq_zero.1 (heq.2.2.2 g)).resolve_left hpg.ne')).symm

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
  simp only [ExchangeMarket.totalSupply, toExchangeMarket, div_eq_mul_inv, ← Finset.sum_mul,
    ← M.totalBudget_eq_sum, mul_inv_cancel₀ hB.ne', one_mul]

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
  have hsup := M.toExchangeMarket_totalSupply hB
  have hd (hval : expenditure p M.supply = M.totalBudget) (i : I) :
      M.toExchangeMarket.demandSet p i = M.demandSet p i := by
    simp only [ExchangeMarket.demandSet, FisherMarket.demandSet, M.toExchangeMarket_income, hval,
      div_mul_cancel₀ _ hB.ne', toExchangeMarket_utility]
  have hcs (g : G) : p g * M.toExchangeMarket.excessDemand x g = 0 ↔
      p g * (M.supply g - ∑ i, x i g) = 0 := by
    rw [ExchangeMarket.excessDemand, hsup g, ← neg_sub, mul_neg, neg_eq_zero]
  refine ⟨fun heq => ?_, fun ⟨hval, heq⟩ =>
    ⟨heq.1, fun i => hd hval i ▸ heq.2.1 i, fun g => hsup g ▸ sub_nonpos.1 (heq.2.2.1 g),
      fun g => (hcs g).1 (heq.2.2.2 g)⟩⟩
  have hval := heq.expenditure_supply_eq_totalBudget hlns
  exact ⟨hval, heq.1, fun i => hd hval i ▸ heq.2.1 i,
    fun g => sub_nonpos.2 (hsup g ▸ heq.2.2.1 g), fun g => (hcs g).2 (heq.2.2.2 g)⟩

/-- **Rescaling recovery** ([CodenottiVaradarajan2007], Section 6.1.7, p. 140): any competitive
equilibrium `(x, p)` of `M.toExchangeMarket` with positive aggregate supply value
`0 < expenditure p M.supply` rescales to an exact Fisher market equilibrium
`(x, (M.totalBudget / expenditure p M.supply) • p)` of `M`. -/
theorem isEquilibrium_smul_of_toExchangeMarket {x : I → G → ℝ} {p : G → ℝ}
    (hB : 0 < M.totalBudget) (hlns : ∀ i, IsLocallyNonsatiated (M.utility i))
    (heq : M.toExchangeMarket.IsCompetitiveEquilibrium x p)
    (hval : 0 < expenditure p M.supply) :
    M.IsEquilibrium x ((M.totalBudget / expenditure p M.supply) • p) := by
  exact (M.isEquilibrium_iff_toExchangeMarket hB hlns).2
    ⟨by rw [expenditure_smul_left, div_mul_cancel₀ _ hval.ne'], heq.smul (div_pos hB hval)⟩

end FisherMarket

end Cslib.GameTheory.Market
