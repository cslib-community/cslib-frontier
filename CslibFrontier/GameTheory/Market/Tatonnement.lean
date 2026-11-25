/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Market.GrossSubstitutes
public import Mathlib.Analysis.Convex.Function
import CslibFrontier.Foundations.Analysis.Brouwer.Simplex
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Monoid

/-!
# Market regularization and projected discrete tâtonnement for WGS economies

In general WGS exchange markets exact equilibrium prices can be irrational, so polynomial-time
algorithms target multiplicative approximate equilibria ([CodenottiVaradarajan2007], Section 6.1.3,
Definition 6.1, p. 138). Following Codenotti, McCune, and Varadarajan
[CodenottiMcCuneVaradarajan2005] as presented in [CodenottiVaradarajan2007], Section 6.3.1,
pp. 143–148 and Exercises 6.4–6.5, p. 158, this module formalizes the complete regularization and
discrete-tâtonnement pipeline:

1. **Approximate demand and approximate equilibria (`Definition 6.1`, p. 138; `Exercise 6.5`,
   p. 158):** `IsApproxDemand`, `ExchangeMarket.IsStrongApproxEquilibrium`,
   `ExchangeMarket.IsWeakApproxEquilibrium`, and the relative price-spread guarantee
   `ExchangeMarket.isWeakApproxEquilibrium_of_priceRatio_le` (**Exercise 6.5**).
2. **Unit-supply rescaling `M → M'` (`Lemma 6.5`, p. 143):** `ExchangeMarket.unitRescale` normalizes
   every good's aggregate supply to `1` while preserving `μ`-approximate demands, weak
   `μ`-approximate equilibria, and weak gross substitutability.
3. **Phantom Cobb–Douglas regularization `M' → M̂` (`Lemma 6.6`, pp. 143–144; `Exercise 6.4`,
   p. 158):** adjoining an extra trader `none` with uniform endowment `(η, …, η)` (`0 < η ≤ 1`) and
   uniform Cobb–Douglas utility guarantees:
   * `(1)` existence of a positive Walrasian equilibrium in `Δ = [η/(2n), 1]^G` via Brouwer's
     fixed-point theorem on a trimmed price simplex
     (`exists_mem_tatonnementBox_isWalrasianEquilibrium`),
   * `(2)` equilibrium price-ratio bound `p j / p k ≤ 2n / η`
     (`priceRatio_le_of_isWalrasianEquilibrium_phantomExcessDemand`),
   * `(3)` transfer of weak `μ`-approximate equilibria on `M̂` to weak `μ(1 + η)`-approximate
     equilibria on `M'` (`isWeakApproxEquilibrium_of_withPhantomTrader`), and
   * `(4)` preservation of WGS (`isWeakGrossSubstitutes_phantomExcessDemand`).
   (Note the printed typo in Exercise 6.4 on p. 158 referring to "Lemma 6.5" instead of Lemma 6.6;
   p. 144 explicitly defers parts `(2)`–`(4)` of Lemma 6.6 to Exercise 6.4.)
4. **Quantitative separating hyperplane and `ℓ_2` bound (`Lemma 6.7` & `Lemma 6.8`, pp. 145–147):**
   for `0 < ε ≤ 1` and `p ∈ Δ⁺ = [η/(4n), 1 + η/(4n)]^G` not a weak `(1 + ε)`-approximate
   equilibrium of `M̂`, every equilibrium `p̂ ∈ Δ` satisfies
   `expenditure p̂ (Z p) ≥ δ = ε^2 η^2 / (144 n^4)` (`expenditure_phantomExcessDemand_ge_delta`),
   and `∑ g, (Z p g)^2 ≤ (12 n^2 / η)^2` (`sum_sq_phantomExcessDemand_le`).
5. **Projected discrete tâtonnement convergence (`Theorem 6.9` & `Theorem 6.10`, pp. 147–148):**
   iterating `tatonnementStep` from any `p₀ ∈ Δ` decreases `∑ g, (p*_g - p_g)^2` by at least
   `μ = min((δ / (12 n^2 / η))^2, (η / (4n))^2)` at every non-equilibrium step, visiting `Δ⁺` at a
   weak `(1 + ε)`-approximate equilibrium of `M̂` within `⌊n / μ⌋` iterations
   (`exists_le_tatonnementIter_isWeakApproxEquilibrium`), and transferring back via `η = ε / 3` to
   the original WGS market `M` (`exists_weakApproxEquilibrium_of_wgs_oracle`).

## Main definitions

* `Cslib.GameTheory.Market.IsApproxDemand`,
  `Cslib.GameTheory.Market.ExchangeMarket.IsStrongApproxEquilibrium`,
  `Cslib.GameTheory.Market.ExchangeMarket.IsWeakApproxEquilibrium`: multiplicative `μ ≥ 1`
  approximate demand and market equilibria ([CodenottiVaradarajan2007], Definition 6.1, p. 138).
* `Cslib.GameTheory.Market.ExchangeMarket.unitRescale`,
  `Cslib.GameTheory.Market.ExchangeMarket.withPhantomTrader`,
  `Cslib.GameTheory.Market.phantomDemand`, `Cslib.GameTheory.Market.phantomExcessDemand`:
  market normalizations `M → M' → M̂` ([CodenottiVaradarajan2007], Section 6.3.1, pp. 143–144).
* `Cslib.GameTheory.Market.tatonnementBox`, `Cslib.GameTheory.Market.tatonnementOuterBox`,
  `Cslib.GameTheory.Market.projectTatonnementBox`, `Cslib.GameTheory.Market.tatonnementStep`,
  `Cslib.GameTheory.Market.tatonnementIter`: price boxes `Δ`, `Δ⁺` and projected discrete
  tâtonnement dynamics ([CodenottiVaradarajan2007], p. 144).

## Main results

* `Cslib.GameTheory.Market.ExchangeMarket.isWeakApproxEquilibrium_of_priceRatio_le`:
  **Exercise 6.5** (bounded relative price spread implies weak `(1 + ε)`-approximate equilibrium).
* `Cslib.GameTheory.Market.ExchangeMarket.isApproxDemand_unitRescale_iff`,
  `Cslib.GameTheory.Market.ExchangeMarket.isWeakApproxEquilibrium_unitRescale_iff`,
  `Cslib.GameTheory.Market.isWeakGrossSubstitutes_unitRescale`: **Lemma 6.5** `(i)`–`(iii)`.
* `Cslib.GameTheory.Market.exists_mem_tatonnementBox_isWalrasianEquilibrium`,
  `Cslib.GameTheory.Market.priceRatio_le_of_isWalrasianEquilibrium_phantomExcessDemand`,
  `Cslib.GameTheory.Market.ExchangeMarket.isWeakApproxEquilibrium_of_withPhantomTrader`,
  `Cslib.GameTheory.Market.isWeakGrossSubstitutes_phantomExcessDemand`: **Lemma 6.6** `(1)`–`(4)`
  and **Exercise 6.4**.
* `Cslib.GameTheory.Market.expenditure_phantomExcessDemand_ge_delta`: **Lemma 6.7**.
* `Cslib.GameTheory.Market.sum_sq_phantomExcessDemand_le`: **Lemma 6.8**.
* `Cslib.GameTheory.Market.exists_le_tatonnementIter_sep_lt`,
  `Cslib.GameTheory.Market.exists_le_tatonnementIter_isWeakApproxEquilibrium`,
  `Cslib.GameTheory.Market.exists_weakApproxEquilibrium_of_wgs_oracle`,
  `Cslib.GameTheory.Market.CobbDouglasExchangeMarket.exists_weakApproxEquilibrium_tatonnement`:
  **Theorem 6.9**, the excess-demand oracle iteration guarantee of **Theorem 6.10**, and its
  direct specialization to Cobb–Douglas exchange markets.

## References

* [CodenottiMcCuneVaradarajan2005] (primary PDF unverified; cited via [CodenottiVaradarajan2007])
* [CodenottiVaradarajan2007], Sections 6.1.3, 6.3.1, 6.7, and Exercises 6.4–6.5, pp. 138,
  143–148, 156, 158
-/

public section

namespace Cslib.GameTheory.Market

open Finset
open scoped BigOperators

/-! ### Multiplicative `μ`-approximate demand and approximate equilibria (`Definition 6.1`) -/

section ApproxEquilibrium

variable {I G : Type*} [Fintype G]

/-- Bundle `x` is a **`μ`-approximate demand** (`μ ≥ 1`) of a trader with utility `u` and endowment
`w` at prices `p` ([CodenottiVaradarajan2007], Definition 6.1, p. 138) if `x ≥ 0`,
`expenditure p x ≤ μ * expenditure p w`, and `u y ≤ μ * u x` for every bundle `y ≥ 0` affordable
within `expenditure p w` (equivalent to `u x ≥ (1 / μ) u*` whenever the maximum utility `u*` is
attained). -/
@[expose] def IsApproxDemand (u : (G → ℝ) → ℝ) (μ : ℝ) (p w x : G → ℝ) : Prop :=
  1 ≤ μ ∧ (∀ g, 0 ≤ x g) ∧ expenditure p x ≤ μ * expenditure p w ∧
    ∀ y : G → ℝ, IsBudgetFeasible p (expenditure p w) y → u y ≤ μ * u x

private theorem expenditure_le_mul_of_le {G : Type*} [Fintype G] {p q x : G → ℝ} {c : ℝ}
    (hpq : ∀ g, p g ≤ c * q g) (hx : ∀ g, 0 ≤ x g) :
    expenditure p x ≤ c * expenditure q x := by
  simp only [expenditure_eq_sum, mul_sum]
  refine sum_le_sum fun g _ => ?_
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hpq g) (hx g)

private theorem mul_expenditure_le_of_le {G : Type*} [Fintype G] {p q x : G → ℝ} {c : ℝ}
    (hpq : ∀ g, c * q g ≤ p g) (hx : ∀ g, 0 ≤ x g) :
    c * expenditure q x ≤ expenditure p x := by
  simp only [expenditure_eq_sum, mul_sum]
  refine sum_le_sum fun g _ => ?_
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hpq g) (hx g)

private theorem expenditure_div_mul_self {G : Type*} [Fintype G] {W p z : G → ℝ}
    (hW : ∀ g, 0 < W g) :
    expenditure (fun g => p g / W g) (fun g => W g * z g) = expenditure p z := by
  simp only [expenditure_eq_sum]
  exact sum_congr rfl fun g _ => by field_simp [(hW g).ne']

/-- When an exact Marshallian demand bundle `xStar ∈ demandSet u p (expenditure p w)` exists,
`IsApproxDemand` matches the `u x ≥ (1 / μ) u(xStar)` formulation of [CodenottiVaradarajan2007],
Definition 6.1, p. 138. -/
theorem isApproxDemand_iff_of_mem_demandSet {u : (G → ℝ) → ℝ} {μ : ℝ} {p w x xStar : G → ℝ}
    (hxStar : xStar ∈ demandSet u p (expenditure p w)) :
    IsApproxDemand u μ p w x ↔
      1 ≤ μ ∧ (∀ g, 0 ≤ x g) ∧ expenditure p x ≤ μ * expenditure p w ∧
        (1 / μ) * u xStar ≤ u x := by
  rw [mem_demandSet] at hxStar
  refine ⟨fun ⟨hμ, hx_nn, hexp, hopt⟩ => ⟨hμ, hx_nn, hexp, ?_⟩,
    fun ⟨hμ, hx_nn, hexp, hge⟩ => ⟨hμ, hx_nn, hexp, fun y hy => ?_⟩⟩
  · rw [one_div]
    exact (inv_mul_le_iff₀ (by linarith)).2 (hopt xStar hxStar.1)
  · rw [one_div] at hge
    exact (hxStar.2 y hy).trans ((inv_mul_le_iff₀ (by linarith)).1 hge)

theorem IsApproxDemand.of_mem_demandSet {u : (G → ℝ) → ℝ} {p w x : G → ℝ}
    (hx : x ∈ demandSet u p (expenditure p w)) :
    IsApproxDemand u 1 p w x := by
  rw [mem_demandSet] at hx
  exact ⟨le_rfl, hx.1.1, by simpa only [one_mul] using hx.1.2,
    fun y hy => by simpa only [one_mul] using hx.2 y hy⟩

theorem IsApproxDemand.mono {u : (G → ℝ) → ℝ} {μ μ' : ℝ} {p w x : G → ℝ}
    (h : IsApproxDemand u μ p w x) (hμμ' : μ ≤ μ')
    (hp : ∀ g, 0 ≤ p g) (hw : ∀ g, 0 ≤ w g) (hux : 0 ≤ u x) :
    IsApproxDemand u μ' p w x := by
  refine ⟨h.1.trans hμμ', h.2.1, ?_, fun y hy => ?_⟩
  · exact h.2.2.1.trans (mul_le_mul_of_nonneg_right hμμ' (expenditure_nonneg hp hw))
  · exact (h.2.2.2 y hy).trans (mul_le_mul_of_nonneg_right hμμ' hux)

/-- Utility function `u` is **subhomogeneous from `0`** on `ℝ_+^G` if scaling down any nonnegative
bundle by `c ∈ (0, 1]` scales utility by at least `c` (`c * u b ≤ u (c • b)`). Every concave
function on `ℝ_+^G` with `0 ≤ u 0` (the standing assumption of [CodenottiVaradarajan2007],
Section 6.1.1, p. 136) and every homogeneous-of-degree-`1` function (such as `cobbDouglasUtility`)
satisfies this property. -/
@[expose] def IsRayConcave (u : (G → ℝ) → ℝ) : Prop :=
  ∀ ⦃b : G → ℝ⦄, (∀ g, 0 ≤ b g) → ∀ ⦃c : ℝ⦄, 0 < c → c ≤ 1 → c * u b ≤ u (c • b)

omit [Fintype G] in
theorem IsRayConcave.of_concaveOn {u : (G → ℝ) → ℝ}
    (hconc : ConcaveOn ℝ {b : G → ℝ | ∀ g, 0 ≤ b g} u) (hu0 : 0 ≤ u 0) :
    IsRayConcave u := by
  intro b hb c hc0 hc1
  have hcomb := hconc.2 hb (show (0 : G → ℝ) ∈ _ from fun _ => le_rfl)
    hc0.le (sub_nonneg.2 hc1) (by ring)
  simp only [smul_zero, add_zero, smul_eq_mul] at hcomb
  nlinarith

theorem isRayConcave_cobbDouglasUtility {α : G → ℝ} (hα_sum : ∑ g : G, α g = 1) :
    IsRayConcave (cobbDouglasUtility α) := by
  intro b hb c hc0 _
  rw [cobbDouglasUtility_smul hα_sum hb hc0]

namespace ExchangeMarket

variable [Fintype I] (E : ExchangeMarket I G)

/-- A price vector `p` is a **strong `μ`-approximate equilibrium** (`μ ≥ 1`) of `E`
([CodenottiVaradarajan2007], Definition 6.1, p. 138) if every trader receives an exact Marshallian
demand bundle at `p` and aggregate demand of each good is at most `μ * E.totalSupply g`. -/
@[expose] def IsStrongApproxEquilibrium (μ : ℝ) (p : G → ℝ) : Prop :=
  1 ≤ μ ∧ (∀ g, 0 ≤ p g) ∧ ∃ x : I → G → ℝ,
    (∀ i, x i ∈ E.demandSet p i) ∧ ∀ g : G, ∑ i : I, x i g ≤ μ * E.totalSupply g

/-- A price vector `p` is a **weak `μ`-approximate equilibrium** (`μ ≥ 1`) of `E`
([CodenottiVaradarajan2007], Definition 6.1, p. 138) if every trader receives a `μ`-approximate
demand bundle at `p` and aggregate demand of each good is at most `μ * E.totalSupply g`. -/
@[expose] def IsWeakApproxEquilibrium (μ : ℝ) (p : G → ℝ) : Prop :=
  1 ≤ μ ∧ (∀ g, 0 ≤ p g) ∧ ∃ x : I → G → ℝ,
    (∀ i, IsApproxDemand (E.utility i) μ p (E.endowment i) (x i)) ∧
      ∀ g : G, ∑ i : I, x i g ≤ μ * E.totalSupply g

theorem IsStrongApproxEquilibrium.isWeakApproxEquilibrium {E : ExchangeMarket I G}
    {μ : ℝ} {p : G → ℝ} (h : E.IsStrongApproxEquilibrium μ p)
    (hu_nn : ∀ i b, (∀ g, 0 ≤ b g) → 0 ≤ E.utility i b) :
    E.IsWeakApproxEquilibrium μ p := by
  obtain ⟨hμ, hp, x, hdem, hsup⟩ := h
  refine ⟨hμ, hp, x, fun i => ?_, hsup⟩
  have h1 := IsApproxDemand.of_mem_demandSet (E.income_eq _ _ ▸ (E.mem_demandSet).1 (hdem i))
  exact h1.mono hμ hp (E.endowment_nonneg i) (hu_nn i (x i) h1.2.1)

theorem IsWeakApproxEquilibrium.mono {E : ExchangeMarket I G} {μ μ' : ℝ} {p : G → ℝ}
    (h : E.IsWeakApproxEquilibrium μ p) (hμμ' : μ ≤ μ')
    (hu_nn : ∀ i b, (∀ g, 0 ≤ b g) → 0 ≤ E.utility i b) :
    E.IsWeakApproxEquilibrium μ' p := by
  obtain ⟨hμ, hp, x, hdem, hsup⟩ := h
  refine ⟨hμ.trans hμμ', hp, x, fun i => ?_, fun g => ?_⟩
  · exact (hdem i).mono hμμ' hp (E.endowment_nonneg i) (hu_nn i (x i) (hdem i).2.1)
  · exact (hsup g).trans (mul_le_mul_of_nonneg_right hμμ' (E.totalSupply_nonneg g))

/-- **NRTV Exercise 6.5** ([CodenottiVaradarajan2007], p. 158; used in Lemma 6.7, p. 146): if
`(xHat, pHat)` is a positive competitive equilibrium of `E` (`pHat > 0`), `p > 0`, `0 ≤ ε`, and all
pairwise relative price ratios satisfy `p j / pHat j ≤ (1 + ε / 3) * (p k / pHat k)`, then `p` is a
weak `(1 + ε)`-approximate equilibrium of `E` (in fact weak `(1 + ε / 3)`-approximate). -/
theorem isWeakApproxEquilibrium_of_priceRatio_le {xHat : I → G → ℝ} {pHat p : G → ℝ} {ε : ℝ}
    (hray : ∀ i, IsRayConcave (E.utility i))
    (hu_nn : ∀ i b, (∀ g, 0 ≤ b g) → 0 ≤ E.utility i b)
    (heq : E.IsCompetitiveEquilibrium xHat pHat)
    (hpHat : ∀ g, 0 < pHat g) (hp : ∀ g, 0 < p g) (hε : 0 ≤ ε)
    (hratio : ∀ j k : G, p j / pHat j ≤ (1 + ε / 3) * (p k / pHat k)) :
    E.IsWeakApproxEquilibrium (1 + ε) p := by
  suffices h3 : E.IsWeakApproxEquilibrium (1 + ε / 3) p from
    h3.mono (by linarith) hu_nn
  have hμ : 1 ≤ 1 + ε / 3 := by linarith
  have hp_nn : ∀ g, 0 ≤ p g := fun g => (hp g).le
  rcases isEmpty_or_nonempty G with hEmpty | hNonempty
  · refine ⟨hμ, hp_nn, xHat, fun i => ⟨hμ, fun g => isEmptyElim g, by simp [expenditure_eq_sum],
      fun y _ => ?_⟩, fun g => isEmptyElim g⟩
    rw [show y = xHat i from funext fun g => isEmptyElim g]
    nlinarith [hu_nn i (xHat i) fun g => isEmptyElim g]
  · obtain ⟨gMin, -, hgMin⟩ := exists_min_image univ (fun g => p g / pHat g) univ_nonempty
    obtain ⟨gMax, -, hgMax⟩ := exists_max_image univ (fun g => p g / pHat g) univ_nonempty
    set αMin := p gMin / pHat gMin
    set αMax := p gMax / pHat gMax
    have hαMin_pos : 0 < αMin := div_pos (hp gMin) (hpHat gMin)
    set r := αMax / αMin
    have hr_ge_1 : 1 ≤ r := (one_le_div hαMin_pos).2 (hgMin gMax (mem_univ gMax))
    have hr_pos : 0 < r := by linarith
    have hr_le : r ≤ 1 + ε / 3 := (div_le_iff₀ hαMin_pos).2 (hratio gMax gMin)
    have hp_le_max : ∀ g, p g ≤ αMax * pHat g :=
      fun g => (div_le_iff₀ (hpHat g)).1 (hgMax g (mem_univ g))
    have hp_ge_min : ∀ g, αMin * pHat g ≤ p g :=
      fun g => (le_div_iff₀ (hpHat g)).1 (hgMin g (mem_univ g))
    refine ⟨hμ, hp_nn, xHat, fun i => ?_, fun g => ?_⟩
    swap
    · nlinarith [heq.isFeasibleAllocation.2 g, E.totalSupply_nonneg g]
    have hdem_i := (E.mem_demandSet).1 (heq.2.1 i)
    rw [E.income_eq, Market.mem_demandSet] at hdem_i
    have hx_nn : ∀ g, 0 ≤ xHat i g := hdem_i.1.1
    have hexp_p : expenditure p (xHat i) ≤ (1 + ε / 3) * expenditure p (E.endowment i) := by
      have h1 := expenditure_le_mul_of_le hp_le_max hx_nn
      have h2 := mul_expenditure_le_of_le hp_ge_min (E.endowment_nonneg i)
      have hr_eq : αMax = r * αMin := (div_mul_cancel₀ αMax hαMin_pos.ne').symm
      calc expenditure p (xHat i)
          ≤ r * (αMin * expenditure pHat (xHat i)) := by
            rw [← mul_assoc, ← hr_eq]
            exact h1
        _ ≤ r * (αMin * expenditure pHat (E.endowment i)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdem_i.1.2 hαMin_pos.le) hr_pos.le
        _ ≤ r * expenditure p (E.endowment i) := mul_le_mul_of_nonneg_left h2 hr_pos.le
        _ ≤ (1 + ε / 3) * expenditure p (E.endowment i) :=
            mul_le_mul_of_nonneg_right hr_le (expenditure_nonneg hp_nn (E.endowment_nonneg i))
    refine ⟨hμ, hx_nn, hexp_p, fun y hy => ?_⟩
    -- Scale `y` by `r⁻¹ ∈ (0, 1]` so it becomes affordable under `pHat`.
    have hy_scaled_feas :
        Market.IsBudgetFeasible pHat (expenditure pHat (E.endowment i)) (r⁻¹ • y) := by
      refine ⟨fun g => mul_nonneg (inv_pos.2 hr_pos).le (hy.1 g), ?_⟩
      rw [expenditure_smul_right]
      have h_chain := (mul_expenditure_le_of_le hp_ge_min hy.1).trans
        (hy.2.trans (expenditure_le_mul_of_le hp_le_max (E.endowment_nonneg i)))
      exact (inv_mul_le_iff₀ hr_pos).2 <| by
        dsimp only [r]
        rw [div_mul_eq_mul_div]
        exact (le_div_iff₀' hαMin_pos).2 h_chain
    have huy_le_r : E.utility i y ≤ r * E.utility i (xHat i) :=
      (inv_mul_le_iff₀ hr_pos).1
        ((hray i hy.1 (inv_pos.2 hr_pos) (inv_le_one_of_one_le₀ hr_ge_1)).trans
          (hdem_i.2 _ hy_scaled_feas))
    exact huy_le_r.trans (mul_le_mul_of_nonneg_right hr_le (hu_nn i (xHat i) hx_nn))

end ExchangeMarket

end ApproxEquilibrium

/-! ### Unit-supply market rescaling `M → M'` (`Lemma 6.5`) -/

section UnitRescale

variable {I G : Type*} [Fintype I] [Fintype G]

namespace ExchangeMarket

/-- **Unit-supply rescaling `M → M'`** ([CodenottiVaradarajan2007], Section 6.3.1, p. 143):
normalizes trader endowments by `W_g = E.totalSupply g` and rescales bundle coordinates in each
trader's utility function by `W_g` so that `totalSupply g = 1` for positively supplied goods. -/
noncomputable def unitRescale (E : ExchangeMarket I G) : ExchangeMarket I G where
  endowment i g := E.endowment i g / E.totalSupply g
  utility i b := E.utility i (fun g => E.totalSupply g * b g)
  endowment_nonneg i g := div_nonneg (E.endowment_nonneg i g) (E.totalSupply_nonneg g)

omit [Fintype G] in
@[simp] theorem unitRescale_endowment (E : ExchangeMarket I G) (i : I) (g : G) :
    E.unitRescale.endowment i g = E.endowment i g / E.totalSupply g := by rfl

omit [Fintype G] in
@[simp] theorem unitRescale_utility (E : ExchangeMarket I G) (i : I) (b : G → ℝ) :
    E.unitRescale.utility i b = E.utility i (fun g => E.totalSupply g * b g) := by rfl

omit [Fintype G] in
theorem unitRescale_totalSupply (E : ExchangeMarket I G) {g : G} (hW : 0 < E.totalSupply g) :
    E.unitRescale.totalSupply g = 1 := by
  rw [totalSupply_eq_sum]
  simp only [unitRescale_endowment, ← sum_div]
  rw [← totalSupply_eq_sum]
  exact div_self hW.ne'

/-- **Lemma 6.5 (i)** ([CodenottiVaradarajan2007], p. 143): `b` is a `μ`-approximate demand at
prices `p` for trader `i` in `E.unitRescale` if and only if `(fun g => E.totalSupply g * b g)` is a
`μ`-approximate demand at prices `(fun g => p g / E.totalSupply g)` in `E`. -/
theorem isApproxDemand_unitRescale_iff (E : ExchangeMarket I G)
    (hW : ∀ g, 0 < E.totalSupply g) (μ : ℝ) (p : G → ℝ) (i : I) (b : G → ℝ) :
    IsApproxDemand (E.unitRescale.utility i) μ p (E.unitRescale.endowment i) b ↔
      IsApproxDemand (E.utility i) μ (fun g => p g / E.totalSupply g) (E.endowment i)
        (fun g => E.totalSupply g * b g) := by
  have hexp_endow : expenditure (fun g => p g / E.totalSupply g) (E.endowment i) =
      expenditure p (E.unitRescale.endowment i) := by
    simp only [expenditure_eq_sum, unitRescale_endowment]
    exact sum_congr rfl fun g _ => by ring
  have hnn_iff : (∀ g, 0 ≤ b g) ↔ ∀ g, 0 ≤ E.totalSupply g * b g :=
    ⟨fun hb g => mul_nonneg (hW g).le (hb g),
      fun hb g => nonneg_of_mul_nonneg_right (hb g) (hW g)⟩
  constructor
  · rintro ⟨hμ, hb_nn, hexp, hopt⟩
    refine ⟨hμ, hnn_iff.1 hb_nn, by rwa [expenditure_div_mul_self hW, hexp_endow], fun y hy => ?_⟩
    let y' : G → ℝ := fun g => y g / E.totalSupply g
    have hy_rec : (fun g => E.totalSupply g * y' g) = y :=
      funext fun g => mul_div_cancel₀ _ (hW g).ne'
    have hy'_feas : Market.IsBudgetFeasible p (expenditure p (E.unitRescale.endowment i)) y' :=
      ⟨fun g => div_nonneg (hy.1 g) (hW g).le, by
        rw [← expenditure_div_mul_self hW, hy_rec, ← hexp_endow]
        exact hy.2⟩
    simpa only [unitRescale_utility, hy_rec] using hopt y' hy'_feas
  · rintro ⟨hμ, hb_nn, hexp, hopt⟩
    refine ⟨hμ, hnn_iff.2 hb_nn, by rwa [← expenditure_div_mul_self hW, ← hexp_endow],
      fun y' hy' => ?_⟩
    exact hopt (fun g => E.totalSupply g * y' g)
      ⟨fun g => mul_nonneg (hW g).le (hy'.1 g), by
        rw [expenditure_div_mul_self hW, hexp_endow]
        exact hy'.2⟩

/-- **Lemma 6.5 (ii)** ([CodenottiVaradarajan2007], p. 143): `p` is a weak `μ`-approximate
equilibrium for `E.unitRescale` if and only if `(fun g => p g / E.totalSupply g)` is a weak
`μ`-approximate equilibrium for `E`. -/
theorem isWeakApproxEquilibrium_unitRescale_iff (E : ExchangeMarket I G)
    (hW : ∀ g, 0 < E.totalSupply g) (μ : ℝ) (p : G → ℝ) :
    E.unitRescale.IsWeakApproxEquilibrium μ p ↔
      E.IsWeakApproxEquilibrium μ (fun g => p g / E.totalSupply g) := by
  have hp_iff : (∀ g, 0 ≤ p g) ↔ ∀ g, 0 ≤ p g / E.totalSupply g :=
    ⟨fun hp g => div_nonneg (hp g) (hW g).le,
      fun hp g => by simpa only [div_mul_cancel₀ _ (hW g).ne'] using mul_nonneg (hp g) (hW g).le⟩
  constructor
  · rintro ⟨hμ, hp, x, hdem, hsup⟩
    refine ⟨hμ, hp_iff.1 hp, fun i g => E.totalSupply g * x i g,
      fun i => (E.isApproxDemand_unitRescale_iff hW μ p i (x i)).1 (hdem i), fun g => ?_⟩
    rw [← mul_sum]
    nlinarith [hW g, E.unitRescale_totalSupply (hW g) ▸ hsup g]
  · rintro ⟨hμ, hp, y, hdem, hsup⟩
    refine ⟨hμ, hp_iff.2 hp, fun i g => y i g / E.totalSupply g, fun i => ?_, fun g => ?_⟩
    · refine (E.isApproxDemand_unitRescale_iff hW μ p i _).2 ?_
      exact (funext fun g => mul_div_cancel₀ (y i g) (hW g).ne').symm ▸ hdem i
    · rw [E.unitRescale_totalSupply (hW g), mul_one, ← sum_div]
      exact (div_le_iff₀ (hW g)).2 (by linarith [hsup g])

end ExchangeMarket

omit [Fintype G] in
/-- **Lemma 6.5 (iii)** ([CodenottiVaradarajan2007], p. 143): rescaling prices and excess demands by
strictly positive total supplies `W > 0` preserves weak gross substitutability. -/
theorem isWeakGrossSubstitutes_unitRescale {Z : (G → ℝ) → G → ℝ} {W : G → ℝ}
    (hW : ∀ g, 0 < W g) (hWGS : IsWeakGrossSubstitutes Z) :
    IsWeakGrossSubstitutes (fun p g => Z (fun k => p k / W k) g / W g) := by
  intro p p' hp hle g hfg
  have hp_div : ∀ k, 0 < p k / W k := fun k => div_pos (hp k) (hW k)
  have hle_div : ∀ k, p k / W k ≤ p' k / W k :=
    fun k => div_le_div_of_nonneg_right (hle k) (hW k).le
  have hfg_div : p' g / W g = p g / W g := by rw [hfg]
  exact div_le_div_of_nonneg_right (hWGS hp_div hle_div g hfg_div) (hW g).le

end UnitRescale

/-! ### Phantom Cobb–Douglas regularization `M' → M̂` (`Lemma 6.6` and `Exercise 6.4`) -/

section PhantomRegularization

variable {I G : Type*} [Fintype I] [Fintype G]

/-- Price box `Δ = {p | ∀ g, η / (2 |G|) ≤ p g ≤ 1}` containing normalized equilibria of the
regularized market `M̂` ([CodenottiVaradarajan2007], Section 6.3.1, p. 144). -/
def tatonnementBox (G : Type*) [Fintype G] (η : ℝ) : Set (G → ℝ) :=
  {p | ∀ g : G, η / (2 * (Fintype.card G : ℝ)) ≤ p g ∧ p g ≤ 1}

@[simp] theorem mem_tatonnementBox {η : ℝ} {p : G → ℝ} :
    p ∈ tatonnementBox G η ↔ ∀ g : G, η / (2 * (Fintype.card G : ℝ)) ≤ p g ∧ p g ≤ 1 := by rfl

/-- Expanded price box `Δ⁺ = {p | ∀ g, η / (4 |G|) ≤ p g ≤ 1 + η / (4 |G|)}` on which excess-demand
steps are taken during discrete tâtonnement ([CodenottiVaradarajan2007], Section 6.3.1, p. 144). -/
def tatonnementOuterBox (G : Type*) [Fintype G] (η : ℝ) : Set (G → ℝ) :=
  {p | ∀ g : G,
    η / (4 * (Fintype.card G : ℝ)) ≤ p g ∧ p g ≤ 1 + η / (4 * (Fintype.card G : ℝ))}

@[simp] theorem mem_tatonnementOuterBox {η : ℝ} {p : G → ℝ} :
    p ∈ tatonnementOuterBox G η ↔
      ∀ g : G,
        η / (4 * (Fintype.card G : ℝ)) ≤ p g ∧ p g ≤ 1 + η / (4 * (Fintype.card G : ℝ)) := by rfl

theorem tatonnementBox_subset_outerBox {η : ℝ} (hη : 0 ≤ η) :
    tatonnementBox G η ⊆ tatonnementOuterBox G η := by
  intro p hp g
  have hquarter_le_half :
      η / (4 * (Fintype.card G : ℝ)) ≤ η / (2 * (Fintype.card G : ℝ)) := by
    rcases eq_or_lt_of_le (Nat.cast_nonneg (α := ℝ) (Fintype.card G)) with h0 | hpos
    · simp [← h0]
    · exact div_le_div_of_nonneg_left hη (by positivity) (by linarith)
  have : 0 ≤ η / (4 * (Fintype.card G : ℝ)) := by positivity
  exact ⟨hquarter_le_half.trans (hp g).1, (hp g).2.trans (by linarith)⟩

theorem priceRatio_le_of_mem_tatonnementOuterBox [Nonempty G] {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    {p : G → ℝ} (hp : p ∈ tatonnementOuterBox G η) (j k : G) :
    p j / p k ≤ 5 * (Fintype.card G : ℝ) / η := by
  set n : ℝ := (Fintype.card G : ℝ)
  have hn_ge_1 : 1 ≤ n := Nat.one_le_cast.2 Fintype.card_pos
  have hn_pos : 0 < n := by linarith
  calc p j / p k
      ≤ (1 + η / (4 * n)) / (η / (4 * n)) :=
        div_le_div₀ (by positivity) (hp j).2 (by positivity) (hp k).1
    _ = (4 * n + η) / η := by field_simp [hη0.ne', hn_pos.ne']
    _ ≤ 5 * n / η := div_le_div_of_nonneg_right (by linarith) hη0.le

/-- Uniform Cobb–Douglas demand `cobbDouglasDemand (1 / |G|) p (expenditure p (const η))` of the
extra `(m + 1)`-st phantom trader in `M̂` ([CodenottiVaradarajan2007], Section 6.3.1, p. 143). -/
noncomputable def phantomDemand (η : ℝ) (p : G → ℝ) (g : G) : ℝ :=
  cobbDouglasDemand (fun _ => 1 / (Fintype.card G : ℝ)) p (expenditure p (fun _ => η)) g

@[simp] theorem phantomDemand_apply (η : ℝ) (p : G → ℝ) (g : G) :
    phantomDemand η p g =
      (1 / (Fintype.card G : ℝ)) * expenditure p (fun _ => η) / p g := by
  unfold phantomDemand
  rw [cobbDouglasDemand_apply]

/-- Aggregate excess-demand function `Z_{M̂}(p) = Z'(p) + (phantomDemand η p - η)` of the
regularized market `M̂` ([CodenottiVaradarajan2007], p. 144). -/
noncomputable def phantomExcessDemand (Z' : (G → ℝ) → G → ℝ) (η : ℝ) (p : G → ℝ) (g : G) : ℝ :=
  Z' p g + (phantomDemand η p g - η)

@[simp] theorem phantomExcessDemand_apply (Z' : (G → ℝ) → G → ℝ) (η : ℝ) (p : G → ℝ) (g : G) :
    phantomExcessDemand Z' η p g = Z' p g + (phantomDemand η p g - η) := by rfl

private theorem sum_uniformWeight [Nonempty G] :
    ∑ _g : G, (1 / (Fintype.card G : ℝ)) = 1 := by
  have hn : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp [hn]

private theorem neg_one_add_le_phantomExcessDemand {Z' : (G → ℝ) → G → ℝ} {η : ℝ} (hη : 0 ≤ η)
    (hX_nn : ∀ ⦃q : G → ℝ⦄, (∀ g, 0 < q g) → ∀ g, -1 ≤ Z' q g)
    {p : G → ℝ} (hp : ∀ g, 0 < p g) (k : G) :
    -(1 + η) ≤ phantomExcessDemand Z' η p k := by
  rw [phantomExcessDemand_apply, phantomDemand_apply]
  have hph_nn : 0 ≤ (1 / (Fintype.card G : ℝ)) * expenditure p (fun _ => η) / p k :=
    div_nonneg (mul_nonneg (by positivity)
      (expenditure_nonneg (fun l => (hp l).le) fun _ => hη)) (hp k).le
  linarith [hX_nn hp k]

theorem isHomogeneousDegZero_phantomExcessDemand {Z' : (G → ℝ) → G → ℝ}
    (hH : IsHomogeneousDegZero Z') (η : ℝ) :
    IsHomogeneousDegZero (phantomExcessDemand Z' η) := by
  intro c hc p hp
  funext g
  simp only [phantomExcessDemand_apply, hH hc hp, phantomDemand_apply, expenditure_smul_left,
    Pi.smul_apply, smul_eq_mul]
  congr 2
  field_simp [hc.ne', (hp g).ne']

theorem satisfiesWalrasLaw_phantomExcessDemand [Nonempty G] {Z' : (G → ℝ) → G → ℝ}
    (hW : SatisfiesWalrasLaw Z') (η : ℝ) :
    SatisfiesWalrasLaw (phantomExcessDemand Z' η) := by
  intro p hp
  have hw' := hW hp
  have hexp_ph : expenditure p (phantomDemand η p) = expenditure p (fun _ => η) :=
    expenditure_cobbDouglasDemand sum_uniformWeight hp (expenditure p (fun _ => η))
  have hsplit : expenditure p (phantomExcessDemand Z' η p) =
      expenditure p (Z' p) + (expenditure p (phantomDemand η p) - expenditure p (fun _ => η)) := by
    simp only [expenditure_eq_sum, phantomExcessDemand_apply, mul_add, mul_sub, sum_add_distrib,
      sum_sub_distrib]
  linarith

/-- **Lemma 6.6 (4) / Exercise 6.4** ([CodenottiVaradarajan2007], pp. 144, 158): adding the phantom
Cobb–Douglas trader preserves weak gross substitutability. -/
theorem isWeakGrossSubstitutes_phantomExcessDemand {Z' : (G → ℝ) → G → ℝ} {η : ℝ}
    (hη : 0 ≤ η) (hWGS : IsWeakGrossSubstitutes Z') :
    IsWeakGrossSubstitutes (phantomExcessDemand Z' η) := by
  intro p p' hp hle g hfg
  simp only [phantomExcessDemand_apply]
  have h1 := hWGS hp hle g hfg
  have h2 := isWeakGrossSubstitutes_cobbDouglasExcessDemand
    (α := fun _ => 1 / (Fintype.card G : ℝ)) (w := fun _ => η)
    (fun _ => by positivity) (fun _ => hη) hp hle g hfg
  simp only [phantomDemand_apply, cobbDouglasDemand_apply] at h2 ⊢
  linarith

/-- **Lemma 6.6 (2) / Exercise 6.4** ([CodenottiVaradarajan2007], pp. 144, 158): when original
aggregate demand is nonnegative (`∀ g, -1 ≤ Z' p g`), every positive Walrasian equilibrium `p` of
`phantomExcessDemand Z' η` (`0 < η ≤ 1`) satisfies `p j / p k ≤ 2 |G| / η`. -/
theorem priceRatio_le_of_isWalrasianEquilibrium_phantomExcessDemand [Nonempty G]
    {Z' : (G → ℝ) → G → ℝ} {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hX_nn : ∀ ⦃p : G → ℝ⦄, (∀ g, 0 < p g) → ∀ g, -1 ≤ Z' p g)
    {p : G → ℝ} (heq : IsWalrasianEquilibrium (phantomExcessDemand Z' η) p) (j k : G) :
    p j / p k ≤ 2 * (Fintype.card G : ℝ) / η := by
  set n : ℝ := (Fintype.card G : ℝ)
  have hn_pos : 0 < n := Nat.cast_pos.2 Fintype.card_pos
  have hph_le : phantomDemand η p k ≤ 1 + η := by
    have := heq.2 k
    rw [phantomExcessDemand_apply] at this
    linarith [hX_nn heq.1 k]
  have hexp_ge : η * p j ≤ expenditure p (fun _ => η) := by
    rw [expenditure_eq_sum]
    have := single_le_sum (f := fun l => p l * η)
      (fun l _ => mul_nonneg (heq.1 l).le hη0.le) (mem_univ j)
    linarith
  have hph_ge : η * (p j / p k) / n ≤ phantomDemand η p k := by
    rw [phantomDemand_apply]
    calc η * (p j / p k) / n = (1 / n) * (η * p j) / p k := by ring
      _ ≤ (1 / n) * expenditure p (fun _ => η) / p k :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hexp_ge (by positivity)) (heq.1 k).le
  have hmul : η * (p j / p k) ≤ (1 + η) * n := (div_le_iff₀ hn_pos).1 (hph_ge.trans hph_le)
  exact (le_div_iff₀' hη0).2 (hmul.trans (by nlinarith))

/-- Normalizing any positive Walrasian equilibrium of `phantomExcessDemand Z' η` by its maximum
coordinate produces a Walrasian equilibrium inside `tatonnementBox G η` (`Δ`). -/
theorem mem_tatonnementBox_smul_of_isWalrasianEquilibrium [Nonempty G]
    {Z' : (G → ℝ) → G → ℝ} {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hH : IsHomogeneousDegZero Z')
    (hX_nn : ∀ ⦃p : G → ℝ⦄, (∀ g, 0 < p g) → ∀ g, -1 ≤ Z' p g)
    {p : G → ℝ} (heq : IsWalrasianEquilibrium (phantomExcessDemand Z' η) p) :
    ∃ pStar ∈ tatonnementBox G η,
      IsWalrasianEquilibrium (phantomExcessDemand Z' η) pStar := by
  obtain ⟨gMax, -, hgMax⟩ := exists_max_image univ p univ_nonempty
  have hpMax : 0 < p gMax := heq.1 gMax
  refine ⟨(p gMax)⁻¹ • p, fun g => ?_,
    (isHomogeneousDegZero_phantomExcessDemand hH η).isWalrasianEquilibrium_smul
      heq (inv_pos.2 hpMax)⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  refine ⟨?_, by simpa only [inv_mul_eq_div] using (div_le_one hpMax).2 (hgMax g (mem_univ g))⟩
  have hrat := priceRatio_le_of_isWalrasianEquilibrium_phantomExcessDemand
    hη0 hη1 hX_nn heq gMax g
  have hn_pos : (0 : ℝ) < Fintype.card G := Nat.cast_pos.2 Fintype.card_pos
  have h2n_pos : (0 : ℝ) < 2 * Fintype.card G := by positivity
  have h1 := (div_le_div_iff₀ (heq.1 g) hη0).1 hrat
  simpa only [div_eq_inv_mul] using (div_le_div_iff₀ h2n_pos hpMax).2 (by linarith)

/-- **Lemma 6.6 (1)** ([CodenottiVaradarajan2007], p. 144): if `Z'` is homogeneous of degree `0`,
satisfies Walras's law, has nonnegative underlying demand (`∀ g, -1 ≤ Z' p g`), and is continuous on
strictly positive price vectors, then `phantomExcessDemand Z' η` (`0 < η ≤ 1`) admits a Walrasian
equilibrium `pStar ∈ tatonnementBox G η`. Proved directly from
`Cslib.Brouwer.exists_isFixedPt_pi_simplex` via Gale–Nikaido price adjustment on the trimmed simplex
`{p | ∑ g, p g = 1 ∧ ∀ g, δ ≤ p g}` with `δ = η / (8 |G|^2)`. -/
theorem exists_mem_tatonnementBox_isWalrasianEquilibrium [Nonempty G]
    {Z' : (G → ℝ) → G → ℝ} {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hH : IsHomogeneousDegZero Z') (hW : SatisfiesWalrasLaw Z')
    (hX_nn : ∀ ⦃p : G → ℝ⦄, (∀ g, 0 < p g) → ∀ g, -1 ≤ Z' p g)
    (hcont : ContinuousOn Z' {p : G → ℝ | ∀ g, 0 < p g}) :
    ∃ pStar ∈ tatonnementBox G η,
      IsWalrasianEquilibrium (phantomExcessDemand Z' η) pStar := by
  set n : ℝ := (Fintype.card G : ℝ)
  have hn_ge_1 : 1 ≤ n := Nat.one_le_cast.2 Fintype.card_pos
  have hn_pos : 0 < n := by linarith
  set Z := phantomExcessDemand Z' η
  have hWZ : SatisfiesWalrasLaw Z := satisfiesWalrasLaw_phantomExcessDemand hW η
  set δ : ℝ := η / (8 * n ^ 2)
  have hδ_pos : 0 < δ := by positivity
  have hnδ_eq : n * δ = η / (8 * n) := by dsimp only [δ]; field_simp [hn_pos.ne']
  have h1_sub_pos : 0 < 1 - n * δ := by
    rw [sub_pos, hnδ_eq, div_lt_one (by positivity)]
    linarith
  set τ : ℝ := δ / 2
  have hτ_pos : 0 < τ := half_pos hδ_pos
  -- Affine bijection between the standard simplex on `G` and the trimmed simplex `S_δ`.
  let toTrimmed : (G → ℝ) → G → ℝ := fun y g => δ + (1 - n * δ) * y g
  let fromTrimmed : (G → ℝ) → G → ℝ := fun p g => (p g - δ) / (1 - n * δ)
  let posPart : (G → ℝ) → G → ℝ := fun p g => max 0 (Z p g)
  let gnMap : (G → ℝ) → G → ℝ := fun p g =>
    (p g + τ * posPart p g) / (1 + τ * ∑ k : G, posPart p k)
  -- Key invariance: `gnMap` maps `{p | (∀ g, δ ≤ p g) ∧ ∑ g, p g = 1}` into itself.
  have hgn_maps : ∀ p : G → ℝ, (∀ g, δ ≤ p g) → ∑ g : G, p g = 1 →
      (∀ g, δ ≤ gnMap p g) ∧ ∑ g : G, gnMap p g = 1 := by
    intro p hp_low hp_sum
    have hp_pos : ∀ g, 0 < p g := fun g => hδ_pos.trans_le (hp_low g)
    have hsum_pos_nn : 0 ≤ ∑ k : G, posPart p k := sum_nonneg fun k _ => le_max_left 0 _
    have hden_pos : 0 < 1 + τ * ∑ k : G, posPart p k := by positivity
    -- Upper bound `∑ k, posPart p k ≤ 2 / δ`:
    have hZ_lower : ∀ k, -(1 + η) ≤ Z p k :=
      neg_one_add_le_phantomExcessDemand hη0.le hX_nn hp_pos
    have hpos_le_X : ∑ k : G, posPart p k ≤ 2 / δ := by
      have hmul_le : δ * ∑ k : G, (Z p k + (1 + η)) ≤ ∑ k : G, p k * (Z p k + (1 + η)) := by
        rw [mul_sum]
        exact sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_right (hp_low k) (by linarith [hZ_lower k])
      have hwal : ∑ k : G, p k * (Z p k + (1 + η)) = 1 + η := by
        have hw0 : ∑ k : G, p k * Z p k = 0 := by
          rw [← expenditure_eq_sum]
          exact hWZ hp_pos
        calc
          ∑ k : G, p k * (Z p k + (1 + η)) =
              (∑ k : G, p k * Z p k) + (∑ k : G, p k) * (1 + η) := by
            simp only [mul_add, sum_add_distrib, ← sum_mul]
          _ = 1 + η := by rw [hw0, hp_sum, zero_add, one_mul]
      calc ∑ k : G, posPart p k
          ≤ ∑ k : G, (Z p k + (1 + η)) := by
            refine sum_le_sum fun k _ => ?_
            exact max_le (by linarith [hZ_lower k]) (by linarith)
        _ ≤ 2 / δ := (le_div_iff₀' hδ_pos).2 (hmul_le.trans (by linarith))
    have hden_le_2 : 1 + τ * ∑ k : G, posPart p k ≤ 2 := by
      have := mul_le_mul_of_nonneg_left hpos_le_X hτ_pos.le
      have h1 : τ * (2 / δ) = 1 := by dsimp only [τ]; field_simp [hδ_pos.ne']
      linarith
    refine ⟨fun g => ?_, ?_⟩
    · dsimp only [gnMap]
      by_cases hpg2 : 2 * δ ≤ p g
      · have hnum : 2 * δ ≤ p g + τ * posPart p g := by
          linarith [mul_nonneg hτ_pos.le (le_max_left 0 (Z p g))]
        calc
          δ = (2 * δ) / 2 := by ring
          _ ≤ (p g + τ * posPart p g) / 2 := by linarith
          _ ≤ (p g + τ * posPart p g) / (1 + τ * ∑ k : G, posPart p k) :=
            div_le_div_of_nonneg_left (by linarith) hden_pos hden_le_2
      · push Not at hpg2
        -- Note `n ≥ 2` since if `Fintype.card G = 1`, `p g = 1 > 2 * δ`.
        have hn_ge_2 : 2 ≤ n := by
          rcases Nat.eq_or_lt_of_le (Fintype.card_pos (α := G)) with hcard1 | hcard2
          · exfalso
            have hsub := Fintype.card_le_one_iff_subsingleton.1 hcard1.symm.le
            have hpg1 : p g = 1 := by
              rw [← hp_sum, sum_eq_single g (fun k _ hne => (hne (Subsingleton.elim k g)).elim)
                (fun h => (h (mem_univ g)).elim)]
            have : n * δ ≤ 1 / 8 := by
              rw [hnδ_eq]
              exact div_le_div₀ zero_le_one hη1 (by positivity) (by linarith)
            have : δ ≤ n * δ := le_mul_of_one_le_left hδ_pos.le hn_ge_1
            linarith
          · exact Nat.ofNat_le_cast.2 (Nat.succ_le_of_lt hcard2)
        have hexp_η : expenditure p (fun _ => η) = η := by
          rw [expenditure_eq_sum, ← sum_mul, hp_sum, one_mul]
        have hph_gt : 4 * n < phantomDemand η p g := by
          rw [phantomDemand_apply, hexp_η]
          have hpg_lt : p g < η / (4 * n ^ 2) := hpg2.trans_eq (by
            dsimp only [δ]
            ring)
          calc 4 * n = ((1 / n) * η) / (η / (4 * n ^ 2)) := by field_simp [hη0.ne', hn_pos.ne']
            _ < (1 / n) * η / p g := div_lt_div_of_pos_left (by positivity) (hp_pos g) hpg_lt
        have hZg_ge_2 : 2 ≤ posPart p g := by
          refine le_trans ?_ (le_max_right 0 (Z p g))
          simp only [Z, phantomExcessDemand_apply]
          linarith [hX_nn hp_pos g]
        have hnum : 2 * δ ≤ p g + τ * posPart p g := by
          dsimp only [τ]
          nlinarith [hp_low g]
        calc
          δ = (2 * δ) / 2 := by ring
          _ ≤ (p g + τ * posPart p g) / 2 := by linarith
          _ ≤ (p g + τ * posPart p g) / (1 + τ * ∑ k : G, posPart p k) :=
            div_le_div_of_nonneg_left (by linarith) hden_pos hden_le_2
    · dsimp only [gnMap]
      rw [← sum_div, sum_add_distrib, hp_sum, ← mul_sum]
      exact div_self hden_pos.ne'
  -- Compose onto `Unit → G → ℝ` and apply `Cslib.Brouwer.exists_isFixedPt_pi_simplex`.
  let F : (Unit → G → ℝ) → Unit → G → ℝ :=
    fun y _ => fromTrimmed (gnMap (toTrimmed (y ())))
  have htoTrimmed : ∀ y : G → ℝ, (∀ g, 0 ≤ y g) → ∑ g : G, y g = 1 →
      (∀ g, δ ≤ toTrimmed y g) ∧ ∑ g : G, toTrimmed y g = 1 := fun y hy0 hy1 => by
    refine ⟨fun g => ?_, ?_⟩
    · dsimp only [toTrimmed]
      nlinarith [hy0 g]
    · simp only [toTrimmed, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ← mul_sum, hy1,
        mul_one]
      change n * δ + (1 - n * δ) = 1
      ring
  have hF_maps : Set.MapsTo F
      {y | ∀ i : Unit, (∀ g, 0 ≤ y i g) ∧ ∑ g, y i g = 1}
      {y | ∀ i : Unit, (∀ g, 0 ≤ y i g) ∧ ∑ g, y i g = 1} := fun y hy _ => by
    have ht := htoTrimmed (y ()) (hy ()).1 (hy ()).2
    have hg := hgn_maps (toTrimmed (y ())) ht.1 ht.2
    refine ⟨fun g => div_nonneg (sub_nonneg.2 (hg.1 g)) h1_sub_pos.le, ?_⟩
    simp only [F, fromTrimmed, ← sum_div, sum_sub_distrib, hg.2, sum_const, card_univ, nsmul_eq_mul]
    exact div_self h1_sub_pos.ne'
  have hcont_Z : ContinuousOn Z {p : G → ℝ | ∀ g, 0 < p g} := by
    refine continuousOn_pi.2 fun g => ?_
    simp_rw [Z, phantomExcessDemand_apply, phantomDemand_apply]
    have hnum_cont : Continuous fun p : G → ℝ =>
        (1 / (Fintype.card G : ℝ)) * expenditure p (fun _ => η) := by
      simp only [expenditure_eq_sum]
      exact continuous_const.mul
        (continuous_finsetSum univ fun k _ => (continuous_apply k).mul continuous_const)
    exact ((continuous_apply g).comp_continuousOn hcont).add
      (((hnum_cont.continuousOn.div₀ (continuous_apply g).continuousOn fun p hp => (hp g).ne')).sub
        continuousOn_const)
  have hcont_gn : ContinuousOn gnMap {p : G → ℝ | ∀ g, 0 < p g} := by
    have hcont_pos : ∀ k : G, ContinuousOn (fun p : G → ℝ => posPart p k)
        {p : G → ℝ | ∀ g, 0 < p g} := fun k =>
      (continuous_const.max (continuous_apply k)).comp_continuousOn hcont_Z
    refine continuousOn_pi.2 fun g =>
      ((continuous_apply g).continuousOn.add (continuousOn_const.mul (hcont_pos g))).div₀
        (continuousOn_const.add (continuousOn_const.mul
          (continuousOn_finsetSum univ fun k _ => hcont_pos k)))
        fun p _ => by
          have : 0 ≤ ∑ k : G, posPart p k := sum_nonneg fun k _ => le_max_left 0 _
          positivity
  have hF_cont : ContinuousOn F {y | ∀ i : Unit, (∀ g, 0 ≤ y i g) ∧ ∑ g, y i g = 1} := by
    have hto_cont : Continuous (fun y : Unit → G → ℝ => toTrimmed (y ())) :=
      continuous_pi fun g => continuous_const.add
        (continuous_const.mul ((continuous_apply g).comp (continuous_apply ())))
    have hfrom_cont : Continuous fromTrimmed :=
      continuous_pi fun g => ((continuous_apply g).sub continuous_const).div_const _
    have hto_maps : Set.MapsTo (fun y : Unit → G → ℝ => toTrimmed (y ()))
        {y | ∀ i : Unit, (∀ g, 0 ≤ y i g) ∧ ∑ g, y i g = 1}
        {p : G → ℝ | ∀ g, 0 < p g} := fun y hy g =>
      hδ_pos.trans_le ((htoTrimmed (y ()) (hy ()).1 (hy ()).2).1 g)
    have hcomp := hfrom_cont.comp_continuousOn (hcont_gn.comp hto_cont.continuousOn hto_maps)
    exact continuous_pi (fun _ => continuous_id) |>.comp_continuousOn hcomp
  obtain ⟨yFix, hyFix_mem, hyFix_pt⟩ := Cslib.Brouwer.exists_isFixedPt_pi_simplex hF_maps hF_cont
  set pFix := toTrimmed (yFix ())
  -- Deduce `Z pFix g ≤ 0` for all `g` from `gnMap pFix = pFix` and Walras's law `hWZ`.
  have hpFix_pos : ∀ g, 0 < pFix g := fun g =>
    hδ_pos.trans_le ((htoTrimmed (yFix ()) (hyFix_mem ()).1 (hyFix_mem ()).2).1 g)
  have hgn_fix : gnMap pFix = pFix := funext fun g => by
    have hfg := congrFun (congrFun hyFix_pt ()) g
    dsimp only [F, fromTrimmed, pFix, toTrimmed] at hfg ⊢
    linarith [(div_eq_iff h1_sub_pos.ne').1 hfg]
  have hpFix_eq : IsWalrasianEquilibrium Z pFix := by
    refine ⟨hpFix_pos, fun g => ?_⟩
    set S := ∑ k : G, posPart pFix k
    have hS_nn : 0 ≤ S := sum_nonneg fun k _ => le_max_left 0 _
    have hden_pos : 0 < 1 + τ * S := by positivity
    have hcoord : ∀ k : G, posPart pFix k = pFix k * S := fun k => by
      have hk := (div_eq_iff hden_pos.ne').1 (congrFun hgn_fix k)
      exact mul_left_cancel₀ hτ_pos.ne' (by linarith)
    have hsq0 : ∑ k : G, (posPart pFix k) ^ 2 = 0 := by
      have hterm : ∀ k : G, (posPart pFix k) ^ 2 = Z pFix k * posPart pFix k := fun k => by
        dsimp only [posPart]
        rcases le_total (Z pFix k) 0 with hle | hge
        · rw [max_eq_left hle]; ring
        · rw [max_eq_right hge]; ring
      calc ∑ k : G, (posPart pFix k) ^ 2
          = (∑ k : G, pFix k * Z pFix k) * S := by
            rw [sum_mul]
            refine sum_congr rfl fun k _ => ?_
            rw [hterm k, hcoord k]
            ring
        _ = 0 := by rw [← expenditure_eq_sum, hWZ hpFix_pos, zero_mul]
    have hpos0 : posPart pFix g = 0 := sq_eq_zero_iff.1 <|
      (sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg (posPart pFix k)).1 hsq0 g (mem_univ g)
    linarith [le_max_right 0 (Z pFix g)]
  exact mem_tatonnementBox_smul_of_isWalrasianEquilibrium hη0 hη1 hH hX_nn hpFix_eq

namespace ExchangeMarket

/-- Adjoin the `(m + 1)`-st phantom Cobb–Douglas trader `none` with uniform endowment `(η, …, η)`
(`M' → M̂`, [CodenottiVaradarajan2007], Section 6.3.1, p. 143). -/
noncomputable def withPhantomTrader (E : ExchangeMarket I G) (η : ℝ) (hη : 0 ≤ η) :
    ExchangeMarket (Option I) G where
  endowment
    | some i, g => E.endowment i g
    | none, _ => η
  utility
    | some i => E.utility i
    | none => cobbDouglasUtility (fun _ => 1 / (Fintype.card G : ℝ))
  endowment_nonneg
    | some i, g => E.endowment_nonneg i g
    | none, _ => hη

omit [Fintype I] in
@[simp] theorem withPhantomTrader_endowment_some (E : ExchangeMarket I G) (η : ℝ) (hη : 0 ≤ η)
    (i : I) : (E.withPhantomTrader η hη).endowment (some i) = E.endowment i := by rfl

omit [Fintype I] in
@[simp] theorem withPhantomTrader_endowment_none (E : ExchangeMarket I G) (η : ℝ) (hη : 0 ≤ η) :
    (E.withPhantomTrader η hη).endowment none = fun _ => η := by rfl

omit [Fintype I] in
@[simp] theorem withPhantomTrader_utility_some (E : ExchangeMarket I G) (η : ℝ) (hη : 0 ≤ η)
    (i : I) : (E.withPhantomTrader η hη).utility (some i) = E.utility i := by rfl

omit [Fintype I] in
@[simp] theorem withPhantomTrader_utility_none (E : ExchangeMarket I G) (η : ℝ) (hη : 0 ≤ η) :
    (E.withPhantomTrader η hη).utility none =
      cobbDouglasUtility (fun _ => 1 / (Fintype.card G : ℝ)) := by rfl

theorem withPhantomTrader_totalSupply (E : ExchangeMarket I G) (η : ℝ) (hη : 0 ≤ η) (g : G) :
    (E.withPhantomTrader η hη).totalSupply g = E.totalSupply g + η := by
  rw [totalSupply_eq_sum, Fintype.sum_option]
  simp only [withPhantomTrader_endowment_none, withPhantomTrader_endowment_some,
    ← totalSupply_eq_sum]
  ring

/-- **Lemma 6.6 (3) / Exercise 6.4** ([CodenottiVaradarajan2007], pp. 144, 158): in a unit-supply
market `E` (`∀ g, E.totalSupply g = 1`), any weak `μ`-approximate equilibrium `p` of
`E.withPhantomTrader η hη` is a weak `μ * (1 + η)`-approximate equilibrium of `E`. -/
theorem isWeakApproxEquilibrium_of_withPhantomTrader (E : ExchangeMarket I G)
    (hsup : ∀ g, E.totalSupply g = 1)
    (hu_nn : ∀ i b, (∀ g, 0 ≤ b g) → 0 ≤ E.utility i b)
    {η μ : ℝ} (hη : 0 ≤ η)
    {p : G → ℝ} (h : (E.withPhantomTrader η hη).IsWeakApproxEquilibrium μ p) :
    E.IsWeakApproxEquilibrium (μ * (1 + η)) p := by
  obtain ⟨hμ, hp, x, hdem, hclear⟩ := h
  have hμμ' : μ ≤ μ * (1 + η) := by nlinarith
  refine ⟨by nlinarith, hp, fun i => x (some i), fun i => ?_, fun g => ?_⟩
  · have hdem_i : IsApproxDemand (E.utility i) μ p (E.endowment i) (x (some i)) := by
      simpa only [withPhantomTrader_utility_some, withPhantomTrader_endowment_some] using
        hdem (some i)
    exact hdem_i.mono hμμ' hp (E.endowment_nonneg i) (hu_nn i (x (some i)) hdem_i.2.1)
  · have hnone_nn : 0 ≤ x none g := (hdem none).2.1 g
    have htot := hclear g
    rw [Fintype.sum_option, E.withPhantomTrader_totalSupply η hη g, hsup g] at htot
    rw [hsup g, mul_one]
    linarith

end ExchangeMarket

end PhantomRegularization

/-! ### Quantitative separation (`Lemma 6.7`), `ℓ_2` bound (`Lemma 6.8`), and `Theorem 6.9` -/

section DiscreteTatonnement

variable {I G : Type*} [Fintype I] [Fintype G]

/-- Explicit polynomial separation constant `δ(n, ε, η) = ε^2 η^2 / (144 n^4)` of
[CodenottiVaradarajan2007], Lemma 6.7, p. 146. -/
noncomputable def tatonnementDelta (n : ℕ) (ε η : ℝ) : ℝ :=
  ε ^ 2 * η ^ 2 / (144 * (n : ℝ) ^ 4)

@[simp] theorem tatonnementDelta_eq (n : ℕ) (ε η : ℝ) :
    tatonnementDelta n ε η = ε ^ 2 * η ^ 2 / (144 * (n : ℝ) ^ 4) := by rfl

/-- Explicit `ℓ_2` excess-demand upper bound `L(n, η) = 12 n^2 / η` of
[CodenottiVaradarajan2007], Lemma 6.8, p. 146. -/
noncomputable def tatonnementBoundL (n : ℕ) (η : ℝ) : ℝ :=
  12 * (n : ℝ) ^ 2 / η

@[simp] theorem tatonnementBoundL_eq (n : ℕ) (η : ℝ) :
    tatonnementBoundL n η = 12 * (n : ℝ) ^ 2 / η := by rfl

/-- Per-iteration squared-distance decrease `μ = min((δ / (12 n^2 / η))^2, (η / (4n))^2)` of
[CodenottiVaradarajan2007], Theorem 6.9, p. 147. -/
noncomputable def tatonnementMu (n : ℕ) (η δ : ℝ) : ℝ :=
  min ((δ / tatonnementBoundL n η) ^ 2) ((η / (4 * (n : ℝ))) ^ 2)

@[simp] theorem tatonnementMu_eq (n : ℕ) (η δ : ℝ) :
    tatonnementMu n η δ = min ((δ / tatonnementBoundL n η) ^ 2) ((η / (4 * (n : ℝ))) ^ 2) := by
  rfl

private theorem pow_one_add_div_six_lt {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (1 + ε / (6 * (n : ℝ))) ^ (n - 1) < 1 + ε / 3 := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  -- Prove by induction on `k ≤ n` that `(1 + ε / (6n))^k ≤ 1 + k * (ε / (3n))`.
  have hind : ∀ k : ℕ, k ≤ n →
      (1 + ε / (6 * (n : ℝ))) ^ k ≤ 1 + (k : ℝ) * (ε / (3 * (n : ℝ))) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk_succ
      have hprev := ih (by omega)
      have hk_cast : (k : ℝ) ≤ n := by exact_mod_cast (by omega : k ≤ n)
      have hsq : ε ^ 2 ≤ ε := by nlinarith
      have hk_eps : (k : ℝ) * ε ^ 2 ≤ (n : ℝ) * ε :=
        calc (k : ℝ) * ε ^ 2
            ≤ (n : ℝ) * ε ^ 2 := mul_le_mul_of_nonneg_right hk_cast (sq_nonneg ε)
          _ ≤ (n : ℝ) * ε := mul_le_mul_of_nonneg_left hsq hn_pos.le
      have hquad : ((k : ℝ) * ε ^ 2) / (18 * (n : ℝ) ^ 2) ≤ ε / (6 * (n : ℝ)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hk_eps]
      calc (1 + ε / (6 * (n : ℝ))) ^ (k + 1)
          = (1 + ε / (6 * (n : ℝ))) ^ k * (1 + ε / (6 * (n : ℝ))) := pow_succ _ _
        _ ≤ (1 + (k : ℝ) * (ε / (3 * (n : ℝ)))) * (1 + ε / (6 * (n : ℝ))) :=
            mul_le_mul_of_nonneg_right hprev (by positivity)
        _ = 1 + (k : ℝ) * (ε / (3 * (n : ℝ))) + ε / (6 * (n : ℝ)) +
              ((k : ℝ) * ε ^ 2) / (18 * (n : ℝ) ^ 2) := by ring
        _ ≤ 1 + ((k + 1 : ℕ) : ℝ) * (ε / (3 * (n : ℝ))) := by
            have : ((k : ℝ) + 1) * (ε / (3 * (n : ℝ))) =
                (k : ℝ) * (ε / (3 * (n : ℝ))) + 2 * (ε / (6 * (n : ℝ))) := by ring
            push_cast; linarith
  have h1 := hind (n - 1) (by omega)
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hlt : ((n - 1 : ℕ) : ℝ) * (ε / (3 * (n : ℝ))) = ε / 3 - ε / (3 * (n : ℝ)) := by
    rw [hcast]; field_simp [hn_pos.ne']
  have : 0 < ε / (3 * (n : ℝ)) := by positivity
  linarith

/-- **Lemma 6.7** ([CodenottiVaradarajan2007], Section 6.3.1, pp. 145–146): suppose `E` is a
unit-supply market (`∀ g, E.totalSupply g = 1`) with ray-concave nonnegative utilities whose
excess-demand map `Z'` comes from trader Marshallian demands `d i p ∈ E.demandSet p i` and satisfies
degree-`0` homogeneity, Walras's law, and WGS. For `0 < η`, `0 < ε ≤ 1`, any equilibrium `pHat ∈
tatonnementBox G η` of `phantomExcessDemand Z' η`, and any `p ∈ tatonnementOuterBox G η` that is
**not** a weak `(1 + ε)`-approximate equilibrium of `E.withPhantomTrader η hη0.le`,
`tatonnementDelta (Fintype.card G) ε η ≤ expenditure pHat (phantomExcessDemand Z' η p)`.
(Note the minor typo on p. 146 line 3 of [CodenottiVaradarajan2007] writing "weak `ε`-approximate
equilibrium" in the proof body for the statement's "weak `(1 + ε)`-approximate equilibrium".) -/
theorem expenditure_phantomExcessDemand_ge_delta [Nonempty G]
    {E : ExchangeMarket I G} (hray : ∀ i, IsRayConcave (E.utility i))
    (hu_nn : ∀ i b, (∀ g, 0 ≤ b g) → 0 ≤ E.utility i b)
    {d : I → (G → ℝ) → G → ℝ}
    (hd : ∀ ⦃q : G → ℝ⦄, (∀ g, 0 < q g) → ∀ i, d i q ∈ E.demandSet q i)
    {Z' : (G → ℝ) → G → ℝ}
    (hZ'_eq : ∀ ⦃q : G → ℝ⦄, (∀ g, 0 < q g) → ∀ g, Z' q g = (∑ i : I, d i q g) - E.totalSupply g)
    (hH' : IsHomogeneousDegZero Z') (hW' : SatisfiesWalrasLaw Z')
    (hWGS' : IsWeakGrossSubstitutes Z')
    {η ε : ℝ} (hη0 : 0 < η) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {pHat p : G → ℝ} (hpHat_box : pHat ∈ tatonnementBox G η)
    (heqHat : IsWalrasianEquilibrium (phantomExcessDemand Z' η) pHat)
    (hp_box : p ∈ tatonnementOuterBox G η)
    (hnot : ¬ (E.withPhantomTrader η hη0.le).IsWeakApproxEquilibrium (1 + ε) p) :
    tatonnementDelta (Fintype.card G) ε η ≤
      expenditure pHat (phantomExcessDemand Z' η p) := by
  set n := Fintype.card G
  have hn_pos : 0 < n := Fintype.card_pos
  have hn_rpos : (0 : ℝ) < n := Nat.cast_pos.2 hn_pos
  set Z := phantomExcessDemand Z' η
  have hHZ : IsHomogeneousDegZero Z := isHomogeneousDegZero_phantomExcessDemand hH' η
  have hWZ : SatisfiesWalrasLaw Z := satisfiesWalrasLaw_phantomExcessDemand hW' η
  have hWGSZ : IsWeakGrossSubstitutes Z := isWeakGrossSubstitutes_phantomExcessDemand hη0.le hWGS'
  have hpHat_pos : ∀ g, 0 < pHat g := heqHat.1
  have hp_pos : ∀ g, 0 < p g := fun g =>
    lt_of_lt_of_le (by positivity : 0 < η / (4 * (n : ℝ))) (hp_box g).1
  -- Construct the exact competitive equilibrium `(xHat, pHat)` of `M̂ = E.withPhantomTrader η`.
  let xHat : Option I → G → ℝ
    | some i => d i pHat
    | none => phantomDemand η pHat
  have hMhat_eq : (E.withPhantomTrader η hη0.le).IsCompetitiveEquilibrium xHat pHat := by
    have hz0 := hWZ.eq_zero_of_isWalrasianEquilibrium heqHat
    have hex_eq : ∀ g : G, (E.withPhantomTrader η hη0.le).excessDemand xHat g = Z pHat g :=
      fun g => by
        rw [ExchangeMarket.excessDemand_eq, Fintype.sum_option,
          E.withPhantomTrader_totalSupply η hη0.le g]
        simp only [xHat, Z, phantomExcessDemand_apply, hZ'_eq hpHat_pos g]; ring
    refine ⟨fun g => (hpHat_pos g).le, ?_, fun g => ?_,
      fun g => by rw [hex_eq, hz0, Pi.zero_apply, mul_zero]⟩
    · rintro (rfl | i)
      · rw [ExchangeMarket.mem_demandSet, ExchangeMarket.withPhantomTrader_utility_none,
          ExchangeMarket.income_eq]
        exact cobbDouglasDemand_mem_demandSet (fun _ => by positivity) sum_uniformWeight
          hpHat_pos (expenditure_nonneg (fun g => (hpHat_pos g).le) fun _ => hη0.le)
      · rw [ExchangeMarket.mem_demandSet, ExchangeMarket.withPhantomTrader_utility_some,
          ExchangeMarket.income_eq]
        have hmem := (E.mem_demandSet).1 (hd hpHat_pos i)
        rwa [E.income_eq] at hmem
    · rw [hex_eq, hz0]
      exact le_rfl
  -- Contrapositive of Exercise 6.5 gives a pair of goods violating `(1 + ε / 3)`.
  have hspread : ∃ j l : G, (1 + ε / 3) * (p l / pHat l) < p j / pHat j := by
    by_contra hall
    push Not at hall
    exact hnot ((E.withPhantomTrader η hη0.le).isWeakApproxEquilibrium_of_priceRatio_le
      (fun | some i => hray i | none => isRayConcave_cobbDouglasUtility sum_uniformWeight)
      (fun | some i, b, hb => hu_nn i b hb | none, b, hb => cobbDouglasUtility_nonneg hb)
      hMhat_eq hpHat_pos hp_pos hε0.le hall)
  set σ := sortedPriceRatioEquiv pHat p
  set α := fun t : Fin n => p (σ t) / pHat (σ t)
  set q := fun t : Fin n => hybridPrice pHat p (α t)
  set sFirst : Fin n := ⟨0, hn_pos⟩
  set sLast : Fin n := ⟨n - 1, Nat.sub_lt hn_pos Nat.zero_lt_one⟩
  have hα_spread : (1 + ε / 3) * α sFirst < α sLast := by
    obtain ⟨j, l, hjl⟩ := hspread
    obtain ⟨tj, rfl⟩ := σ.surjective j
    obtain ⟨tl, rfl⟩ := σ.surjective l
    have h1 := mul_le_mul_of_nonneg_left
      (monotone_sortedPriceRatio pHat p (show sFirst ≤ tl from Nat.zero_le tl.val))
      (by positivity : 0 ≤ 1 + ε / 3)
    have h2 : α tj ≤ α sLast := monotone_sortedPriceRatio pHat p (Nat.le_sub_one_of_lt tj.isLt)
    linarith
  have hn_ge_2 : 2 ≤ n := by
    by_contra hlt2
    have heq_idx : sFirst = sLast := Fin.ext (by simp [sFirst, sLast]; omega)
    rw [heq_idx] at hα_spread
    nlinarith [div_pos (hp_pos (σ sLast)) (hpHat_pos (σ sLast))]
  -- Find consecutive sorted indices `k, k + 1` with `(1 + ε / (6n)) * α_k ≤ α_{k+1}`.
  have hex_gap : ∃ k : Fin (n - 1),
      (1 + ε / (6 * (n : ℝ))) * α ⟨k.val, by omega⟩ ≤ α ⟨k.val + 1, by omega⟩ := by
    by_contra hall
    push Not at hall
    have hind : ∀ (m : ℕ) (hm : m < n),
        α ⟨m, hm⟩ ≤ (1 + ε / (6 * (n : ℝ))) ^ m * α sFirst := by
      intro m
      induction m with
      | zero => intro _; simp [sFirst]
      | succ k ih =>
        intro hk
        calc α ⟨k + 1, hk⟩
            ≤ (1 + ε / (6 * (n : ℝ))) * α ⟨k, by omega⟩ := (hall ⟨k, by omega⟩).le
          _ ≤ (1 + ε / (6 * (n : ℝ))) * ((1 + ε / (6 * (n : ℝ))) ^ k * α sFirst) :=
              mul_le_mul_of_nonneg_left (ih (by omega)) (by positivity)
          _ = (1 + ε / (6 * (n : ℝ))) ^ (k + 1) * α sFirst := by rw [pow_succ']; ring
    have hlast_le := hind (n - 1) (Nat.sub_lt hn_pos Nat.zero_lt_one)
    have hlt := mul_lt_mul_of_pos_right (pow_one_add_div_six_lt hn_ge_2 hε0 hε1)
      (div_pos (hp_pos (σ sFirst)) (hpHat_pos (σ sFirst)))
    linarith
  obtain ⟨kGap, hkGap⟩ := hex_gap
  set s : Fin n := ⟨kGap.val, by omega⟩
  set s' : Fin n := ⟨kGap.val + 1, by omega⟩
  have hss' : s ≤ s' := Nat.le_succ kGap.val
  have hαs_pos : 0 < α s := div_pos (hp_pos _) (hpHat_pos _)
  have hαs'_pos : 0 < α s' := div_pos (hp_pos _) (hpHat_pos _)
  have hα0_pos : 0 < α sFirst := div_pos (hp_pos _) (hpHat_pos _)
  -- Bound `1 - α s / α s' ≥ ε / (12 n)`.
  have h1_sub_ge : ε / (12 * (n : ℝ)) ≤ 1 - α s / α s' := by
    have hdiv_le : α s / α s' ≤ 1 / (1 + ε / (6 * (n : ℝ))) := by
      rw [div_le_div_iff₀ hαs'_pos (by positivity), one_mul]; linarith
    have h6n_le_2 : 1 + ε / (6 * (n : ℝ)) ≤ 2 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn_pos
      have hdiv1 : ε / (6 * (n : ℝ)) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
      linarith
    calc ε / (12 * (n : ℝ))
        = (ε / (6 * (n : ℝ))) / 2 := by ring
      _ ≤ (ε / (6 * (n : ℝ))) / (1 + ε / (6 * (n : ℝ))) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) h6n_le_2
      _ = 1 - 1 / (1 + ε / (6 * (n : ℝ))) := by
          have : 1 + ε / (6 * (n : ℝ)) ≠ 0 := by positivity
          field_simp; ring
      _ ≤ 1 - α s / α s' := by linarith
  -- Bound the phantom trader's income jump and demand jump on `g₀ = σ sFirst`.
  have hinc_jump : (ε / (6 * (n : ℝ))) * α s * pHat (σ sLast) * η ≤
      expenditure (q s') (fun _ => η) - expenditure (q s) (fun _ => η) := by
    have hqs_le := hybridPrice_mono pHat p (monotone_sortedPriceRatio pHat p hss')
      fun g => (hpHat_pos g).le
    rw [expenditure_eq_sum, expenditure_eq_sum, ← sum_sub_distrib]
    simp_rw [← sub_mul]
    have hsingle := single_le_sum (f := fun g => (q s' g - q s g) * η)
      (fun g _ => mul_nonneg (sub_nonneg.2 (hqs_le g)) hη0.le) (mem_univ (σ sLast))
    have hs'_last : s' ≤ sLast := Nat.succ_le_of_lt kGap.isLt
    have hq_s'_last : q s' (σ sLast) = α s' * pHat (σ sLast) :=
      hybridPrice_sorted_of_ge hpHat_pos hs'_last
    have hq_s_last : q s (σ sLast) = α s * pHat (σ sLast) :=
      hybridPrice_sorted_of_ge hpHat_pos (hss'.trans hs'_last)
    rw [hq_s'_last, hq_s_last] at hsingle
    have := mul_le_mul_of_nonneg_right (show ε / (6 * (n : ℝ)) * α s ≤ α s' - α s by linarith)
      (mul_nonneg (hpHat_pos (σ sLast)).le hη0.le)
    linarith
  have hZ_jump_g0 :
      (ε * α s * pHat (σ sLast) * η) / (6 * (n : ℝ) ^ 2 * p (σ sFirst)) ≤
        Z (q s') (σ sFirst) - Z (q s) (σ sFirst) := by
    have h0_le_s : sFirst ≤ s := Nat.zero_le _
    have hZ'_nn := sub_nonneg.2
      (excessDemand_hybridPrice_le_succ_of_le hWGS' hpHat_pos hp_pos hss' h0_le_s)
    have hqs'_0 : q s' (σ sFirst) = p (σ sFirst) :=
      hybridPrice_sorted_of_le hpHat_pos (h0_le_s.trans hss')
    have hqs_0 : q s (σ sFirst) = p (σ sFirst) :=
      hybridPrice_sorted_of_le hpHat_pos h0_le_s
    have hph_diff : phantomDemand η (q s') (σ sFirst) - phantomDemand η (q s) (σ sFirst) =
        (1 / (n : ℝ)) * (expenditure (q s') (fun _ => η) - expenditure (q s) (fun _ => η)) /
          p (σ sFirst) := by
      simp only [phantomDemand_apply, hqs'_0, hqs_0]
      ring
    have hp0_pos := hp_pos (σ sFirst)
    have hph_ge : (ε * α s * pHat (σ sLast) * η) / (6 * (n : ℝ) ^ 2 * p (σ sFirst)) ≤
        phantomDemand η (q s') (σ sFirst) - phantomDemand η (q s) (σ sFirst) := by
      rw [hph_diff]
      calc (ε * α s * pHat (σ sLast) * η) / (6 * (n : ℝ) ^ 2 * p (σ sFirst))
          = (1 / (n : ℝ)) * ((ε / (6 * (n : ℝ))) * α s * pHat (σ sLast) * η) / p (σ sFirst) := by
            field_simp [hn_rpos.ne', hp0_pos.ne']
        _ ≤ _ := div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hinc_jump (by positivity)) hp0_pos.le
    simp only [Z, phantomExcessDemand_apply]; linarith
  -- Plug `t = sFirst` into Equation `(6.5)` (`expenditure_hybridPrice_step_ge`) at `kGap`.
  have hstep_k : tatonnementDelta n ε η ≤
      expenditure pHat (Z (q s')) - expenditure pHat (Z (q s)) := by
    have hge65 :=
      expenditure_hybridPrice_step_ge hHZ hWZ hWGSZ heqHat hp_pos (s := s) (s' := s') rfl
    have hsum_ge := single_le_sum
      (f := fun t => pHat (σ t) * (Z (q s') (σ t) - Z (q s) (σ t)))
      (fun t ht => mul_nonneg (hpHat_pos (σ t)).le
        (sub_nonneg.2 (excessDemand_hybridPrice_le_succ_of_le hWGSZ hpHat_pos hp_pos hss'
          (mem_filter.1 ht).2)))
      (mem_filter.2 ⟨mem_univ sFirst, Nat.zero_le _⟩)
    have hratio_ge_1 : 1 ≤ pHat (σ sFirst) * α s / p (σ sFirst) := by
      have hp0_eq : p (σ sFirst) = α sFirst * pHat (σ sFirst) :=
        (div_mul_cancel₀ _ (hpHat_pos (σ sFirst)).ne').symm
      rw [hp0_eq, mul_comm (pHat _), mul_div_mul_right _ _ (hpHat_pos (σ sFirst)).ne']
      exact (one_le_div hα0_pos).2 (monotone_sortedPriceRatio pHat p (Nat.zero_le _))
    have hp0_pos := hp_pos (σ sFirst)
    have hpHat0_pos := hpHat_pos (σ sFirst)
    have hpHatL_pos := hpHat_pos (σ sLast)
    have hterm_ge : ε ^ 2 * η ^ 2 / (144 * (n : ℝ) ^ 4) ≤
        (ε / (12 * (n : ℝ))) * (pHat (σ sFirst) *
          ((ε * α s * pHat (σ sLast) * η) / (6 * (n : ℝ) ^ 2 * p (σ sFirst)))) := by
      calc ε ^ 2 * η ^ 2 / (144 * (n : ℝ) ^ 4)
          = (ε / (12 * (n : ℝ))) *
              (1 * ((ε * (η / (2 * (n : ℝ))) * η) / (6 * (n : ℝ) ^ 2))) := by
            field_simp [hn_rpos.ne']; ring
        _ ≤ (ε / (12 * (n : ℝ))) * ((pHat (σ sFirst) * α s / p (σ sFirst)) *
              ((ε * pHat (σ sLast) * η) / (6 * (n : ℝ) ^ 2))) := by
            gcongr
            exact (hpHat_box (σ sLast)).1
        _ = _ := by field_simp [hn_rpos.ne', hp0_pos.ne']
    have hε12_pos : 0 < ε / (12 * (n : ℝ)) := by positivity
    have hprod_ge := mul_le_mul h1_sub_ge
      ((mul_le_mul_of_nonneg_left hZ_jump_g0 hpHat0_pos.le).trans hsum_ge)
      (by positivity) (by linarith)
    rw [tatonnementDelta_eq]
    exact hterm_ge.trans (hprod_ge.trans hge65)
  -- Sum over all `k : Fin (n - 1)`: all steps are `≥ 0` and step `kGap` is `≥ δ`.
  rw [expenditure_eq_sum_hybridPrice_steps hHZ hWZ heqHat hp_pos hn_pos]
  exact hstep_k.trans (single_le_sum (fun k _ =>
    expenditure_hybridPrice_step_nonneg hHZ hWZ hWGSZ heqHat hp_pos
      (s := ⟨k.val, by omega⟩) (s' := ⟨k.val + 1, by omega⟩) rfl) (mem_univ kGap))

/-- **Lemma 6.8** ([CodenottiVaradarajan2007], Section 6.3.1, pp. 146–147): for any
`p ∈ tatonnementOuterBox G η` (`0 < η ≤ 1`), when `Z'` satisfies Walras's law and `∀ g, -1 ≤ Z' p g`
(nonnegative original demand against unit supplies), the `ℓ_1` and squared `ℓ_2` norms of
`phantomExcessDemand Z' η p` satisfy `∑ g, |Z p g| ≤ 12 |G|^2 / η` and
`∑ g, (Z p g)^2 ≤ (12 |G|^2 / η)^2`. -/
theorem sum_sq_phantomExcessDemand_le [Nonempty G] {Z' : (G → ℝ) → G → ℝ} {η : ℝ}
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hW' : SatisfiesWalrasLaw Z')
    (hX_nn : ∀ ⦃q : G → ℝ⦄, (∀ g, 0 < q g) → ∀ g, -1 ≤ Z' q g)
    {p : G → ℝ} (hp : p ∈ tatonnementOuterBox G η) :
    ∑ g : G, (phantomExcessDemand Z' η p g) ^ 2 ≤
      (tatonnementBoundL (Fintype.card G) η) ^ 2 := by
  set n : ℝ := (Fintype.card G : ℝ)
  have hn_ge_1 : 1 ≤ n := Nat.one_le_cast.2 Fintype.card_pos
  have hn_pos : 0 < n := by linarith
  set Z := phantomExcessDemand Z' η
  have hWZ : SatisfiesWalrasLaw Z := satisfiesWalrasLaw_phantomExcessDemand hW' η
  have hp_pos : ∀ g, 0 < p g := fun g => (by positivity : 0 < η / (4 * n)).trans_le (hp g).1
  let X : G → ℝ := fun g => Z p g + (1 + η)
  have hX_pos : ∀ g, 0 ≤ X g := fun g => by
    have := neg_one_add_le_phantomExcessDemand hη0.le hX_nn hp_pos g
    dsimp only [X, Z]
    linarith
  obtain ⟨gMin, -, hgMin⟩ := exists_min_image univ p univ_nonempty
  obtain ⟨gMax, -, hgMax⟩ := exists_max_image univ p univ_nonempty
  -- Bound `∑ g, X g ≤ (p gMax / p gMin) * ∑ g, (1 + η)`.
  have hX_sum_le : ∑ g : G, X g ≤ (5 * n / η) * (2 * n) := by
    have h1 : p gMin * ∑ g : G, X g ≤ ∑ g : G, p g * X g := by
      rw [mul_sum]
      exact sum_le_sum fun g _ => mul_le_mul_of_nonneg_right (hgMin g (mem_univ g)) (hX_pos g)
    have hwal : ∑ g : G, p g * X g = ∑ g : G, p g * (1 + η) := by
      have hw0 : ∑ g : G, p g * Z p g = 0 := by
        rw [← expenditure_eq_sum]
        exact hWZ hp_pos
      calc ∑ g : G, p g * X g
          = (∑ g : G, p g * Z p g) + ∑ g : G, p g * (1 + η) := by
            simp only [X, mul_add, sum_add_distrib]
        _ = ∑ g : G, p g * (1 + η) := by rw [hw0, zero_add]
    have h2 : ∑ g : G, p g * (1 + η) ≤ p gMax * (2 * n) :=
      calc ∑ g : G, p g * (1 + η)
          ≤ ∑ _g : G, p gMax * 2 :=
            sum_le_sum fun g _ =>
              mul_le_mul (hgMax g (mem_univ g)) (by linarith) (by positivity) (hp_pos gMax).le
        _ = p gMax * (2 * n) := by
            simp only [sum_const, card_univ, nsmul_eq_mul, n]
            ring
    have hdiv : ∑ g : G, X g ≤ (p gMax / p gMin) * (2 * n) := by
      rw [div_mul_eq_mul_div]
      exact (le_div_iff₀' (hp_pos gMin)).2 (h1.trans (hwal ▸ h2))
    exact hdiv.trans (mul_le_mul_of_nonneg_right
      (priceRatio_le_of_mem_tatonnementOuterBox hη0 hη1 hp gMax gMin) (by positivity))
  -- Bound `∑ g, |Z p g| ≤ ∑ g, X g + ∑ g, (1 + η) ≤ 12 n^2 / η`.
  have hl1_le : ∑ g : G, |Z p g| ≤ tatonnementBoundL (Fintype.card G) η := by
    have hsum_abs : ∑ g : G, |Z p g| ≤ (∑ g : G, X g) + 2 * n := by
      have habs (g : G) : |Z p g| ≤ X g + (1 + η) := by
        have hZ_eq : Z p g = X g - (1 + η) := by dsimp only [X]; ring
        rw [hZ_eq]
        exact (abs_sub _ _).trans (by rw [abs_of_nonneg (hX_pos g), abs_of_nonneg (by positivity)])
      calc ∑ g : G, |Z p g|
          ≤ ∑ g : G, (X g + (1 + η)) := sum_le_sum fun g _ => habs g
        _ = (∑ g : G, X g) + n * (1 + η) := by
            simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, n]
            ring
        _ ≤ (∑ g : G, X g) + 2 * n := by nlinarith
    have h2n : 2 * n ≤ 2 * n ^ 2 / η := (le_div_iff₀ hη0).2 (by nlinarith)
    have hbound : (5 * n / η) * (2 * n) + 2 * n ≤ 12 * n ^ 2 / η :=
      calc (5 * n / η) * (2 * n) + 2 * n
          = 10 * n ^ 2 / η + 2 * n := by ring
        _ ≤ 10 * n ^ 2 / η + 2 * n ^ 2 / η := by linarith
        _ = 12 * n ^ 2 / η := by ring
    rw [tatonnementBoundL_eq]
    exact hsum_abs.trans (by linarith)
  -- Finally `∑ g, (Z p g)^2 ≤ (∑ g, |Z p g|)^2 ≤ L^2`.
  have hl2_le_l1 : ∑ g : G, (Z p g) ^ 2 ≤ (∑ g : G, |Z p g|) ^ 2 := by
    rw [sum_congr rfl fun g _ => (sq_abs (Z p g)).symm, sq, sum_mul]
    exact sum_le_sum fun g hg => by
      rw [sq]
      exact mul_le_mul_of_nonneg_left
        (single_le_sum (fun k _ => abs_nonneg (Z p k)) hg) (abs_nonneg (Z p g))
  exact hl2_le_l1.trans (pow_le_pow_left₀ (sum_nonneg fun g _ => abs_nonneg _) hl1_le 2)

/-- Componentwise projection `max (η / (2 |G|)) (min 1 (p g))` onto `tatonnementBox G η` (`Δ`)
([CodenottiVaradarajan2007], Section 6.3.1, p. 144). -/
noncomputable def projectTatonnementBox (η : ℝ) (p : G → ℝ) (g : G) : ℝ :=
  max (η / (2 * (Fintype.card G : ℝ))) (min 1 (p g))

@[simp] theorem projectTatonnementBox_apply (η : ℝ) (p : G → ℝ) (g : G) :
    projectTatonnementBox η p g = max (η / (2 * (Fintype.card G : ℝ))) (min 1 (p g)) := by rfl

/-- One step of the **projected discrete tâtonnement process** ([CodenottiVaradarajan2007],
Section 6.3.1, p. 144): if `p ∈ Δ⁺`, move in direction `Z p` with step size
`δ / (12 |G|^2 / η)^2`; otherwise project componentwise back onto `Δ`. -/
noncomputable def tatonnementStep (Z : (G → ℝ) → G → ℝ) (η δ : ℝ) (p : G → ℝ) : G → ℝ :=
  open Classical in
  if p ∈ tatonnementOuterBox G η then
    p + (δ / (tatonnementBoundL (Fintype.card G) η) ^ 2) • Z p
  else
    projectTatonnementBox η p

theorem tatonnementStep_of_mem (Z : (G → ℝ) → G → ℝ) (η δ : ℝ) {p : G → ℝ}
    (hp : p ∈ tatonnementOuterBox G η) :
    tatonnementStep Z η δ p = p + (δ / (tatonnementBoundL (Fintype.card G) η) ^ 2) • Z p := by
  unfold tatonnementStep
  classical
  exact ite_eq_left_iff.2 fun h => (h hp).elim

theorem tatonnementStep_of_not_mem (Z : (G → ℝ) → G → ℝ) (η δ : ℝ) {p : G → ℝ}
    (hp : p ∉ tatonnementOuterBox G η) :
    tatonnementStep Z η δ p = projectTatonnementBox η p := by
  unfold tatonnementStep
  classical
  exact ite_eq_right_iff.2 fun h => (hp h).elim

/-- `k`-th iterate of `tatonnementStep Z η δ` starting from `p₀`. -/
noncomputable def tatonnementIter (Z : (G → ℝ) → G → ℝ) (η δ : ℝ) (p₀ : G → ℝ) (k : ℕ) : G → ℝ :=
  (tatonnementStep Z η δ)^[k] p₀

@[simp] theorem tatonnementIter_zero (Z : (G → ℝ) → G → ℝ) (η δ : ℝ) (p₀ : G → ℝ) :
    tatonnementIter Z η δ p₀ 0 = p₀ := by rfl

theorem tatonnementIter_succ (Z : (G → ℝ) → G → ℝ) (η δ : ℝ) (p₀ : G → ℝ) (k : ℕ) :
    tatonnementIter Z η δ p₀ (k + 1) = tatonnementStep Z η δ (tatonnementIter Z η δ p₀ k) := by
  simp only [tatonnementIter, Function.iterate_succ_apply']

/-- **Theorem 6.9 (Lyapunov separating-hyperplane core)** ([CodenottiVaradarajan2007],
Section 6.3.1, pp. 147–148): let `Z` satisfy Walras's law on `ℝ_{++}^G` and `∑ g, (Z p g)^2 ≤ L^2`
on `Δ⁺`, and let `pStar ∈ Δ` be a reference vector (`0 < η ≤ 1`, `0 < δ`). Starting from any
`p₀ ∈ Δ`, within `k ≤ ⌊|G| / μ⌋` iterations (`μ = tatonnementMu |G| η δ`), `tatonnementIter`
visits a price vector `p_k ∈ Δ⁺` satisfying `expenditure pStar (Z p_k) < δ`.
(Note the minor intermediate exponent slip on p. 147 line 19 of [CodenottiVaradarajan2007] writing
`δ / L^2` before `‖Z‖_2^2` where `(δ / L^2)^2` is meant; the exact `2 (a · q) - ‖q‖_2^2` expansion
gives the exact printed decrease `δ^2 / L^2` on p. 148.) -/
theorem exists_le_tatonnementIter_sep_lt [Nonempty G] {Z : (G → ℝ) → G → ℝ}
    (hWZ : SatisfiesWalrasLaw Z)
    {η δ : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) (hδ : 0 < δ)
    (hnorm : ∀ p ∈ tatonnementOuterBox G η,
      ∑ g : G, (Z p g) ^ 2 ≤ (tatonnementBoundL (Fintype.card G) η) ^ 2)
    {pStar p₀ : G → ℝ} (hpStar : pStar ∈ tatonnementBox G η) (hp₀ : p₀ ∈ tatonnementBox G η) :
    ∃ k ≤ Nat.floor ((Fintype.card G : ℝ) / tatonnementMu (Fintype.card G) η δ),
      tatonnementIter Z η δ p₀ k ∈ tatonnementOuterBox G η ∧
        expenditure pStar (Z (tatonnementIter Z η δ p₀ k)) < δ := by
  set n := Fintype.card G
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.2 Fintype.card_pos
  set L := tatonnementBoundL n η
  have hL_pos : 0 < L := by dsimp only [L]; rw [tatonnementBoundL_eq]; positivity
  set μ := tatonnementMu n η δ
  have hμ_pos : 0 < μ := by
    dsimp only [μ]
    rw [tatonnementMu_eq]
    exact lt_min (by positivity) (by positivity)
  let pot : (G → ℝ) → ℝ := fun p => ∑ g : G, (pStar g - p g) ^ 2
  -- Step decrease lemma: if `p ∉ Δ⁺` or `δ ≤ expenditure pStar (Z p)`, `pot` drops by `≥ μ`.
  have hdrop : ∀ p : G → ℝ,
      ¬ (p ∈ tatonnementOuterBox G η ∧ expenditure pStar (Z p) < δ) →
      μ ≤ pot p - pot (tatonnementStep Z η δ p) := by
    intro p hfail
    by_cases hp_in : p ∈ tatonnementOuterBox G η
    · have hsep_ge : δ ≤ expenditure pStar (Z p) :=
        not_lt.1 fun hlt => hfail ⟨hp_in, hlt⟩
      rw [tatonnementStep_of_mem Z η δ hp_in]
      have hp_pos : ∀ g, 0 < p g := fun g =>
        (by positivity : 0 < η / (4 * (n : ℝ))).trans_le (hp_in g).1
      set s := δ / L ^ 2
      have hquad : pot p - pot (p + s • Z p) =
          2 * s * (expenditure pStar (Z p) - expenditure p (Z p)) -
            s ^ 2 * ∑ g : G, (Z p g) ^ 2 := by
        simp only [pot, expenditure_eq_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          ← sum_sub_distrib]
        have hpt : ∀ g : G, (pStar g - p g) ^ 2 - (pStar g - (p g + s * Z p g)) ^ 2 =
            2 * s * (pStar g * Z p g - p g * Z p g) - s ^ 2 * (Z p g) ^ 2 := fun _ => by ring
        simp_rw [hpt, sum_sub_distrib, ← mul_sum, sum_sub_distrib]
      rw [hquad, hWZ hp_pos, sub_zero]
      have h1 := mul_le_mul_of_nonneg_left hsep_ge (by positivity : 0 ≤ 2 * s)
      have h2 := mul_le_mul_of_nonneg_left (hnorm p hp_in) (sq_nonneg s)
      have h3 : 2 * s * δ - s ^ 2 * L ^ 2 = (δ / L) ^ 2 := by
        dsimp only [s]
        field_simp [hL_pos.ne']
        ring
      exact (min_le_left _ _).trans (by linarith)
    · -- Projection step `p ∉ Δ⁺`: clamping to `[η/(2n), 1]` drops `pot` by `≥ (η/(4n))^2`.
      rw [tatonnementStep_of_not_mem Z η δ hp_in]
      set low := η / (2 * (n : ℝ))
      have hlow_le_1 : low ≤ 1 := by
        have : (1 : ℝ) ≤ n := by exact_mod_cast Fintype.card_pos
        exact (div_le_one (by positivity)).2 (by linarith)
      -- Every coordinate projection is nonexpansive toward `pStar g ∈ [low, 1]`.
      have hcoord_ge : ∀ g : G,
          (max 0 (low - p g)) ^ 2 + (max 0 (p g - 1)) ^ 2 ≤
            (pStar g - p g) ^ 2 - (pStar g - projectTatonnementBox η p g) ^ 2 := by
        intro g
        rw [projectTatonnementBox_apply]
        change _ ≤ (pStar g - p g) ^ 2 - (pStar g - max low (min 1 (p g))) ^ 2
        have ⟨hps_low, hps_1⟩ := hpStar g
        rcases lt_or_ge (p g) low with hlt | hge
        · rw [max_eq_left ((min_le_right 1 _).trans hlt.le), max_eq_right (by linarith),
            max_eq_left (by linarith)]
          nlinarith
        · rcases le_or_gt (p g) 1 with hle1 | hgt1
          · rw [min_eq_right hle1, max_eq_right hge, max_eq_left (by linarith),
              max_eq_left (by linarith)]
            linarith
          · rw [min_eq_left hgt1.le, max_eq_right hlow_le_1, max_eq_left (by linarith),
              max_eq_right (by linarith)]
            nlinarith
      -- At least one coordinate violates `Δ⁺`, contributing `≥ (η / (4n))^2`.
      have hex_viol : ∃ g₀ : G,
          p g₀ < η / (4 * (n : ℝ)) ∨ 1 + η / (4 * (n : ℝ)) < p g₀ := by
        by_contra hall
        push Not at hall
        exact hp_in fun g => ⟨(hall g).1, (hall g).2⟩
      obtain ⟨g₀, hviol⟩ := hex_viol
      have hg₀_drop : (η / (4 * (n : ℝ))) ^ 2 ≤
          (pStar g₀ - p g₀) ^ 2 - (pStar g₀ - projectTatonnementBox η p g₀) ^ 2 := by
        have hr_pos : 0 < η / (4 * (n : ℝ)) := by positivity
        have hlow_eq : low = 2 * (η / (4 * (n : ℝ))) := by dsimp only [low]; ring
        refine le_trans ?_ (hcoord_ge g₀)
        rcases hviol with hsmall | hlarge
        · have : η / (4 * (n : ℝ)) ≤ max 0 (low - p g₀) :=
            le_trans (by linarith) (le_max_right _ _)
          nlinarith [sq_nonneg (max 0 (p g₀ - 1))]
        · have : η / (4 * (n : ℝ)) ≤ max 0 (p g₀ - 1) :=
            le_trans (by linarith) (le_max_right _ _)
          nlinarith [sq_nonneg (max 0 (low - p g₀))]
      refine (min_le_right _ _).trans ?_
      dsimp only [pot]
      rw [← sum_sub_distrib]
      exact hg₀_drop.trans (single_le_sum (fun g _ =>
        (by positivity : 0 ≤ (max 0 (low - p g)) ^ 2 + (max 0 (p g - 1)) ^ 2).trans (hcoord_ge g))
        (mem_univ g₀))
  -- Now telescope over `K + 1` steps where `K = ⌊n / μ⌋` if all `k ≤ K` failed.
  set K := Nat.floor ((n : ℝ) / μ)
  by_contra hnone
  push Not at hnone
  have htelescope : ∀ m : ℕ, m ≤ K + 1 →
      (m : ℝ) * μ ≤ pot p₀ - pot (tatonnementIter Z η δ p₀ m) := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm_succ
      have hstep_m := hdrop (tatonnementIter Z η δ p₀ m)
        fun h => not_lt_of_ge (hnone m (by omega) h.1) h.2
      calc ((m + 1 : ℕ) : ℝ) * μ
          = (m : ℝ) * μ + μ := by push_cast; ring
        _ ≤ (pot p₀ - pot (tatonnementIter Z η δ p₀ m)) +
              (pot (tatonnementIter Z η δ p₀ m) - pot (tatonnementIter Z η δ p₀ (m + 1))) := by
            rw [tatonnementIter_succ]
            linarith [ih (by omega)]
        _ = pot p₀ - pot (tatonnementIter Z η δ p₀ (m + 1)) := by ring
  have hpot0_le : pot p₀ ≤ n :=
    calc ∑ g : G, (pStar g - p₀ g) ^ 2
        ≤ ∑ _g : G, (1 : ℝ) := sum_le_sum fun g _ => by
          have := hpStar g
          have := hp₀ g
          have : 0 ≤ η / (2 * (n : ℝ)) := by positivity
          nlinarith
      _ = n := by simp [n]
  have hpot_nn : 0 ≤ pot (tatonnementIter Z η δ p₀ (K + 1)) := sum_nonneg fun _ _ => sq_nonneg _
  have hle_n : ((K + 1 : ℕ) : ℝ) * μ ≤ n := by linarith [htelescope (K + 1) le_rfl]
  push_cast at hle_n
  exact not_lt_of_ge ((le_div_iff₀ hμ_pos).2 hle_n) (Nat.lt_floor_add_one ((n : ℝ) / μ))

/-- **Theorem 6.9** ([CodenottiVaradarajan2007], Section 6.3.1, p. 147): for a unit-supply WGS
exchange economy `E` with continuous Marshallian demands `d i`, parameters `0 < η ≤ 1` and
`0 < ε ≤ 1`, separation constant `δ = tatonnementDelta |G| ε η`, and any starting price vector
`p₀ ∈ tatonnementBox G η`, projected discrete tâtonnement finds a weak `(1 + ε)`-approximate
equilibrium of `E.withPhantomTrader η hη0.le` inside `tatonnementOuterBox G η` within `⌊|G| / μ⌋`
iterations. -/
theorem exists_le_tatonnementIter_isWeakApproxEquilibrium [Nonempty G]
    {E : ExchangeMarket I G} (hray : ∀ i, IsRayConcave (E.utility i))
    (hu_nn : ∀ i b, (∀ g, 0 ≤ b g) → 0 ≤ E.utility i b)
    {d : I → (G → ℝ) → G → ℝ}
    (hd : ∀ ⦃q : G → ℝ⦄, (∀ g, 0 < q g) → ∀ i, d i q ∈ E.demandSet q i)
    {Z' : (G → ℝ) → G → ℝ}
    (hZ'_eq : ∀ ⦃q : G → ℝ⦄, (∀ g, 0 < q g) → ∀ g,
      Z' q g = (∑ i : I, d i q g) - E.totalSupply g)
    (hsup : ∀ g, E.totalSupply g = 1)
    (hH' : IsHomogeneousDegZero Z') (hW' : SatisfiesWalrasLaw Z')
    (hWGS' : IsWeakGrossSubstitutes Z')
    (hcont' : ContinuousOn Z' {q : G → ℝ | ∀ g, 0 < q g})
    {η ε : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {p₀ : G → ℝ} (hp₀ : p₀ ∈ tatonnementBox G η) :
    let δ := tatonnementDelta (Fintype.card G) ε η
    let μ := tatonnementMu (Fintype.card G) η δ
    ∃ k ≤ Nat.floor ((Fintype.card G : ℝ) / μ),
      tatonnementIter (phantomExcessDemand Z' η) η δ p₀ k ∈ tatonnementOuterBox G η ∧
        (E.withPhantomTrader η hη0.le).IsWeakApproxEquilibrium (1 + ε)
          (tatonnementIter (phantomExcessDemand Z' η) η δ p₀ k) := by
  intro δ μ
  have hX_nn : ∀ ⦃q : G → ℝ⦄, (∀ g, 0 < q g) → ∀ g, -1 ≤ Z' q g := fun q hq g => by
    rw [hZ'_eq hq g, hsup g]
    have : 0 ≤ ∑ i : I, d i q g := sum_nonneg fun i _ =>
      (((mem_demandSet).1 ((E.mem_demandSet).1 (hd hq i))).1.1 g)
    linarith
  obtain ⟨pStar, hpStar_box, hpStar_eq⟩ :=
    exists_mem_tatonnementBox_isWalrasianEquilibrium hη0 hη1 hH' hW' hX_nn hcont'
  have hδ_pos : 0 < δ := by
    dsimp only [δ]
    rw [tatonnementDelta_eq]
    have : (0 : ℝ) < Fintype.card G := Nat.cast_pos.2 Fintype.card_pos
    positivity
  obtain ⟨k, hk_le, hk_in, hk_lt⟩ := exists_le_tatonnementIter_sep_lt
    (satisfiesWalrasLaw_phantomExcessDemand hW' η) hη0 hη1 hδ_pos
    (fun p hp => sum_sq_phantomExcessDemand_le hη0 hη1 hW' hX_nn hp) hpStar_box hp₀
  refine ⟨k, hk_le, hk_in, ?_⟩
  by_contra hnot
  linarith [expenditure_phantomExcessDemand_ge_delta hray hu_nn hd hZ'_eq hH' hW' hWGS'
    hη0 hε0 hε1 hpStar_box hpStar_eq hk_in hnot]

/-- **End-to-end excess-demand oracle guarantee (Theorem 6.10 iteration bound)**
([CodenottiVaradarajan2007], Section 6.3.1, Theorem 6.10, p. 148): for **any** positively supplied
WGS exchange economy `E` (`∀ g, 0 < E.totalSupply g`) with continuous single-valued demands `d i`
and accuracy `0 < ε ≤ 1`, running projected discrete tâtonnement on the rescaled, regularized
excess-demand oracle with `η = ε / 3` from uniform prices `(fun _ => 1) ∈ Δ` visits within
`⌊|G| / μ⌋` oracle calls a price vector whose un-rescaled image `(fun g => p_k g / E.totalSupply g)`
is a weak `(1 + ε)`-approximate equilibrium of the original market `E`. -/
theorem exists_weakApproxEquilibrium_of_wgs_oracle [Nonempty G]
    {E : ExchangeMarket I G} (hW : ∀ g, 0 < E.totalSupply g)
    (hray : ∀ i, IsRayConcave (E.utility i))
    (hu_nn : ∀ i b, (∀ g, 0 ≤ b g) → 0 ≤ E.utility i b)
    {d : I → (G → ℝ) → G → ℝ}
    (hd : ∀ ⦃q : G → ℝ⦄, (∀ g, 0 < q g) → ∀ i, d i q ∈ E.demandSet q i)
    {Z : (G → ℝ) → G → ℝ}
    (hZ_eq : ∀ ⦃q : G → ℝ⦄, (∀ g, 0 < q g) → ∀ g, Z q g = (∑ i : I, d i q g) - E.totalSupply g)
    (hH : IsHomogeneousDegZero Z) (hWalras : SatisfiesWalrasLaw Z)
    (hWGS : IsWeakGrossSubstitutes Z)
    (hcont : ContinuousOn Z {q : G → ℝ | ∀ g, 0 < q g})
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    let Z' : (G → ℝ) → G → ℝ := fun p g => Z (fun l => p l / E.totalSupply l) g / E.totalSupply g
    let η : ℝ := ε / 3
    let δ : ℝ := tatonnementDelta (Fintype.card G) η η
    let μ : ℝ := tatonnementMu (Fintype.card G) η δ
    ∃ k ≤ Nat.floor ((Fintype.card G : ℝ) / μ),
      E.IsWeakApproxEquilibrium (1 + ε)
        (fun g =>
          tatonnementIter (phantomExcessDemand Z' η) η δ (fun _ => 1) k g / E.totalSupply g) := by
  intro Z' η δ μ
  have hη0 : 0 < η := by dsimp only [η]; positivity
  have hη1 : η ≤ 1 := by dsimp only [η]; linarith
  -- Verify `E.unitRescale` satisfies all hypotheses of `Theorem 6.9`.
  have hray' : ∀ i, IsRayConcave (E.unitRescale.utility i) := fun i b hb c hc0 hc1 => by
    have hmul : (fun g => E.totalSupply g * (c • b) g) = c • (fun g => E.totalSupply g * b g) :=
      funext fun g => by simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [E.unitRescale_utility, E.unitRescale_utility, hmul]
    exact hray i (fun g => mul_nonneg (hW g).le (hb g)) hc0 hc1
  have hu_nn' : ∀ i b, (∀ g, 0 ≤ b g) → 0 ≤ E.unitRescale.utility i b := fun i b hb =>
    hu_nn i _ fun g => mul_nonneg (hW g).le (hb g)
  let d' : I → (G → ℝ) → G → ℝ :=
    fun i q g => d i (fun l => q l / E.totalSupply l) g / E.totalSupply g
  have hd' : ∀ ⦃q : G → ℝ⦄, (∀ g, 0 < q g) → ∀ i, d' i q ∈ E.unitRescale.demandSet q i := by
    intro q hq i
    have hmem := (E.mem_demandSet).1 (hd (fun l => div_pos (hq l) (hW l)) i)
    rw [E.income_eq, mem_demandSet] at hmem
    rw [ExchangeMarket.mem_demandSet, ExchangeMarket.income_eq, mem_demandSet]
    have hendow_rec : (fun l => E.totalSupply l * E.unitRescale.endowment i l) = E.endowment i :=
      funext fun l => mul_div_cancel₀ _ (hW l).ne'
    have hd'_rec : (fun l => E.totalSupply l * d' i q l) = d i (fun l => q l / E.totalSupply l) :=
      funext fun l => mul_div_cancel₀ _ (hW l).ne'
    refine ⟨⟨fun g => div_nonneg (hmem.1.1 g) (hW g).le, by
        rw [← expenditure_div_mul_self (z := d' i q) hW,
          ← expenditure_div_mul_self (z := E.unitRescale.endowment i) hW, hd'_rec, hendow_rec]
        exact hmem.1.2⟩,
      fun b hb => by
        rw [E.unitRescale_utility, E.unitRescale_utility, hd'_rec]
        refine hmem.2 (fun l => E.totalSupply l * b l) ⟨fun l => mul_nonneg (hW l).le (hb.1 l), ?_⟩
        rw [expenditure_div_mul_self hW, ← hendow_rec, expenditure_div_mul_self hW]
        exact hb.2⟩
  have hsup' : ∀ g, E.unitRescale.totalSupply g = 1 := fun g => E.unitRescale_totalSupply (hW g)
  have hZ'_eq : ∀ ⦃q : G → ℝ⦄, (∀ g, 0 < q g) → ∀ g,
      Z' q g = (∑ i : I, d' i q g) - E.unitRescale.totalSupply g := fun q hq g => by
    dsimp only [Z', d']
    rw [hZ_eq (fun l => div_pos (hq l) (hW l)) g, sub_div, ← sum_div, div_self (hW g).ne', hsup' g]
  have hH' : IsHomogeneousDegZero Z' := fun c hc q hq => funext fun g => by
    dsimp only [Z']
    have hsmul : (fun l => (c • q) l / E.totalSupply l) = c • (fun l => q l / E.totalSupply l) :=
      funext fun l => by simp [Pi.smul_apply, smul_eq_mul, mul_div_assoc]
    rw [hsmul, hH hc fun l => div_pos (hq l) (hW l)]
  have hW' : SatisfiesWalrasLaw Z' := fun q hq => by
    have hw := hWalras fun l => div_pos (hq l) (hW l)
    rw [expenditure_eq_sum] at hw ⊢
    convert hw using 1
    exact sum_congr rfl fun g _ => by dsimp only [Z']; field_simp [(hW g).ne']
  have hcont' : ContinuousOn Z' {q : G → ℝ | ∀ g, 0 < q g} := by
    have hscale_maps : Set.MapsTo (fun q : G → ℝ => fun l => q l / E.totalSupply l)
        {q : G → ℝ | ∀ g, 0 < q g} {q : G → ℝ | ∀ g, 0 < q g} :=
      fun q hq l => div_pos (hq l) (hW l)
    have hcomp := hcont.comp
      (continuous_pi fun l => (continuous_apply l).div_const (E.totalSupply l)).continuousOn
      hscale_maps
    exact continuousOn_pi.2 fun g => ((continuous_apply g).comp_continuousOn hcomp).div_const _
  have hp0_box : (fun _ : G => (1 : ℝ)) ∈ tatonnementBox G η := fun g => by
    have : (1 : ℝ) ≤ Fintype.card G := by exact_mod_cast Fintype.card_pos
    exact ⟨(div_le_one (by positivity)).2 (by linarith), le_rfl⟩
  obtain ⟨k, hk_le, -, hk_approx⟩ :=
    exists_le_tatonnementIter_isWeakApproxEquilibrium hray' hu_nn' hd' hZ'_eq hsup'
      hH' hW' (isWeakGrossSubstitutes_unitRescale hW hWGS) hcont' hη0 hη1 hη0 hη1 hp0_box
  refine ⟨k, hk_le, ?_⟩
  -- Transfer `(1 + η)`-approx equilibrium on `M̂` → `(1 + η)^2`-approx on `M'` → `(1 + ε)` on `M`!
  have hM' :=
    E.unitRescale.isWeakApproxEquilibrium_of_withPhantomTrader hsup' hu_nn' hη0.le hk_approx
  exact ((E.isWeakApproxEquilibrium_unitRescale_iff hW ((1 + η) * (1 + η)) _).1 hM').mono
    (by dsimp only [η]; nlinarith) hu_nn

namespace CobbDouglasExchangeMarket

variable (E : CobbDouglasExchangeMarket I G)

omit [Fintype I] in
theorem isRayConcave_toExchangeMarket_utility (i : I) :
    IsRayConcave (E.toExchangeMarket.utility i) := by
  rw [E.toExchangeMarket_utility]
  exact isRayConcave_cobbDouglasUtility (E.sum_weight i)

omit [Fintype I] in
theorem toExchangeMarket_utility_nonneg (i : I) {b : G → ℝ} (hb : ∀ g, 0 ≤ b g) :
    0 ≤ E.toExchangeMarket.utility i b := by
  rw [E.toExchangeMarket_utility]
  exact cobbDouglasUtility_nonneg hb

theorem continuousOn_excessDemandFn :
    ContinuousOn E.excessDemandFn {q : G → ℝ | ∀ g, 0 < q g} := by
  rw [continuousOn_pi]
  intro g
  simp_rw [E.excessDemandFn_eq]
  refine (continuousOn_finsetSum univ fun i _ => ?_).sub continuousOn_const
  have hnum : Continuous fun q : G → ℝ => E.weight i g * expenditure q (E.endowment i) := by
    simp only [expenditure_eq_sum]
    exact continuous_const.mul
      (continuous_finsetSum univ fun k _ => (continuous_apply k).mul continuous_const)
  exact hnum.continuousOn.div₀ (continuous_apply g).continuousOn fun q hq => (hq g).ne'

/-- Direct instantiation of **Theorem 6.10** (`exists_weakApproxEquilibrium_of_wgs_oracle`) for any
positively supplied `CobbDouglasExchangeMarket`: discharges ray concavity, nonnegativity,
Marshallian demand optimality, Walras's law, WGS, and continuity automatically. -/
theorem exists_weakApproxEquilibrium_tatonnement [Nonempty G]
    (hW : ∀ g, 0 < E.toExchangeMarket.totalSupply g) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    let W := E.toExchangeMarket.totalSupply
    let Z' : (G → ℝ) → G → ℝ := fun p g => E.excessDemandFn (fun l => p l / W l) g / W g
    let η : ℝ := ε / 3
    let δ : ℝ := tatonnementDelta (Fintype.card G) η η
    let μ : ℝ := tatonnementMu (Fintype.card G) η δ
    ∃ k ≤ Nat.floor ((Fintype.card G : ℝ) / μ),
      E.toExchangeMarket.IsWeakApproxEquilibrium (1 + ε)
        (fun g => tatonnementIter (phantomExcessDemand Z' η) η δ (fun _ => 1) k g / W g) := by
  have hd : ∀ ⦃q : G → ℝ⦄, (∀ g, 0 < q g) → ∀ i : I,
      cobbDouglasDemand (E.weight i) q (expenditure q (E.endowment i)) ∈
        E.toExchangeMarket.demandSet q i := by
    intro q hq i
    rw [ExchangeMarket.mem_demandSet, E.toExchangeMarket_utility,
      ExchangeMarket.income_eq, E.toExchangeMarket_endowment]
    exact cobbDouglasDemand_mem_demandSet (E.weight_nonneg i) (E.sum_weight i) hq
      (expenditure_nonneg (fun g => (hq g).le) (E.endowment_nonneg i))
  have hZ_eq : ∀ ⦃q : G → ℝ⦄, (∀ g, 0 < q g) → ∀ g,
      E.excessDemandFn q g =
        (∑ i : I, cobbDouglasDemand (E.weight i) q (expenditure q (E.endowment i)) g) -
          E.toExchangeMarket.totalSupply g := by
    intro q _ g
    rw [E.excessDemandFn_eq]
    congr 1
    exact sum_congr rfl fun i _ => (cobbDouglasDemand_apply _ _ _ _).symm
  exact exists_weakApproxEquilibrium_of_wgs_oracle hW
    E.isRayConcave_toExchangeMarket_utility
    (fun i _ hb => E.toExchangeMarket_utility_nonneg i hb)
    hd hZ_eq E.isHomogeneousDegZero_excessDemandFn E.satisfiesWalrasLaw_excessDemandFn
    E.isWeakGrossSubstitutes_excessDemandFn E.continuousOn_excessDemandFn hε0 hε1

end CobbDouglasExchangeMarket

end DiscreteTatonnement

end Cslib.GameTheory.Market
