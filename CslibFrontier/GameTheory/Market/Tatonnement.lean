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
  · have hμ_pos : 0 < μ := lt_of_lt_of_le zero_lt_one hμ
    have hle := hopt xStar hxStar.1
    rw [one_div]
    exact (inv_mul_le_iff₀ hμ_pos).2 (by linarith)
  · have hμ_pos : 0 < μ := lt_of_lt_of_le zero_lt_one hμ
    have hy_le : u y ≤ u xStar := hxStar.2 y hy
    have hmul : u xStar ≤ μ * u x := by
      rw [one_div] at hge
      have := (inv_mul_le_iff₀ hμ_pos).1 hge
      linarith
    exact hy_le.trans hmul

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
  have hmem0 : (0 : G → ℝ) ∈ {y : G → ℝ | ∀ g, 0 ≤ y g} := fun _ => le_rfl
  have hmem_b : b ∈ {y : G → ℝ | ∀ g, 0 ≤ y g} := hb
  have hcomb := hconc.2 hmem_b hmem0 hc0.le (sub_nonneg.2 hc1) (by ring)
  simp only [smul_zero, add_zero, smul_eq_mul] at hcomb
  have hnonneg : 0 ≤ (1 - c) * u 0 := mul_nonneg (sub_nonneg.2 hc1) hu0
  linarith

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
  have h1 : IsApproxDemand (E.utility i) 1 p (E.endowment i) (x i) := by
    have hmem := (E.mem_demandSet (p := p) (i := i) (b := x i)).1 (hdem i)
    rw [E.income_eq] at hmem
    exact IsApproxDemand.of_mem_demandSet hmem
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
  · refine ⟨hμ, hp_nn, xHat, fun i => ?_, fun g => isEmptyElim g⟩
    have hx_nn : ∀ g, 0 ≤ xHat i g := fun g => isEmptyElim g
    refine ⟨hμ, hx_nn, ?_, fun y _ => ?_⟩
    · simp [expenditure_eq_sum]
    · have hy_eq : y = xHat i := funext fun g => isEmptyElim g
      rw [hy_eq]
      nlinarith [hu_nn i (xHat i) hx_nn]
  · obtain ⟨gMin, -, hgMin⟩ := exists_min_image univ (fun g => p g / pHat g) univ_nonempty
    obtain ⟨gMax, -, hgMax⟩ := exists_max_image univ (fun g => p g / pHat g) univ_nonempty
    set αMin := p gMin / pHat gMin
    set αMax := p gMax / pHat gMax
    have hαMin_pos : 0 < αMin := div_pos (hp gMin) (hpHat gMin)
    have hαMax_pos : 0 < αMax := div_pos (hp gMax) (hpHat gMax)
    have hMin_le_Max : αMin ≤ αMax := hgMin gMax (mem_univ gMax)
    set r := αMax / αMin
    have hr_ge_1 : 1 ≤ r := (one_le_div hαMin_pos).2 hMin_le_Max
    have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr_ge_1
    have hr_le : r ≤ 1 + ε / 3 := (div_le_iff₀ hαMin_pos).2 (hratio gMax gMin)
    have hp_le_max : ∀ g, p g ≤ αMax * pHat g := fun g =>
      (div_le_iff₀ (hpHat g)).1 (hgMax g (mem_univ g))
    have hp_ge_min : ∀ g, αMin * pHat g ≤ p g := fun g =>
      (le_div_iff₀ (hpHat g)).1 (hgMin g (mem_univ g))
    refine ⟨hμ, hp_nn, xHat, fun i => ?_, fun g => ?_⟩
    · have hdem_i := (E.mem_demandSet).1 (heq.2.1 i)
      rw [E.income_eq, Market.mem_demandSet] at hdem_i
      have hx_nn : ∀ g, 0 ≤ xHat i g := hdem_i.1.1
      have hexp_p : expenditure p (xHat i) ≤ (1 + ε / 3) * expenditure p (E.endowment i) := by
        have h1 : expenditure p (xHat i) ≤ αMax * expenditure pHat (xHat i) := by
          simp only [expenditure_eq_sum, mul_sum]
          refine sum_le_sum fun g _ => ?_
          have := mul_le_mul_of_nonneg_right (hp_le_max g) (hx_nn g)
          linarith
        have h2 : αMin * expenditure pHat (E.endowment i) ≤ expenditure p (E.endowment i) := by
          simp only [expenditure_eq_sum, mul_sum]
          refine sum_le_sum fun g _ => ?_
          have := mul_le_mul_of_nonneg_right (hp_ge_min g) (E.endowment_nonneg i g)
          linarith
        have hr_eq : αMax = r * αMin := (div_mul_cancel₀ αMax hαMin_pos.ne').symm
        have hexp_hat : expenditure pHat (xHat i) ≤ expenditure pHat (E.endowment i) := hdem_i.1.2
        have hexp_p_nn : 0 ≤ expenditure p (E.endowment i) :=
          expenditure_nonneg hp_nn (E.endowment_nonneg i)
        calc
          expenditure p (xHat i) ≤ (r * αMin) * expenditure pHat (xHat i) := by
            rwa [← hr_eq]
          _ ≤ (r * αMin) * expenditure pHat (E.endowment i) :=
            mul_le_mul_of_nonneg_left hexp_hat (mul_pos hr_pos hαMin_pos).le
          _ = r * (αMin * expenditure pHat (E.endowment i)) := by ring
          _ ≤ r * expenditure p (E.endowment i) := mul_le_mul_of_nonneg_left h2 hr_pos.le
          _ ≤ (1 + ε / 3) * expenditure p (E.endowment i) :=
            mul_le_mul_of_nonneg_right hr_le hexp_p_nn
      refine ⟨hμ, hx_nn, hexp_p, fun y hy => ?_⟩
      -- Scale `y` by `r⁻¹ ∈ (0, 1]` so it becomes affordable under `pHat`.
      have hrinv_pos : 0 < r⁻¹ := inv_pos.2 hr_pos
      have hrinv_le_1 : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr_ge_1
      have hy_scaled_feas :
          Market.IsBudgetFeasible pHat (expenditure pHat (E.endowment i)) (r⁻¹ • y) := by
        refine ⟨fun g => mul_nonneg hrinv_pos.le (hy.1 g), ?_⟩
        rw [expenditure_smul_right]
        have h_min_y : αMin * expenditure pHat y ≤ expenditure p y := by
          simp only [expenditure_eq_sum, mul_sum]
          refine sum_le_sum fun g _ => ?_
          have := mul_le_mul_of_nonneg_right (hp_ge_min g) (hy.1 g)
          linarith
        have h_max_w : expenditure p (E.endowment i) ≤ αMax * expenditure pHat (E.endowment i) := by
          simp only [expenditure_eq_sum, mul_sum]
          refine sum_le_sum fun g _ => ?_
          have := mul_le_mul_of_nonneg_right (hp_le_max g) (E.endowment_nonneg i g)
          linarith
        have h_chain : αMin * expenditure pHat y ≤ αMax * expenditure pHat (E.endowment i) :=
          h_min_y.trans (hy.2.trans h_max_w)
        have hdiv : expenditure pHat y ≤ r * expenditure pHat (E.endowment i) := by
          dsimp only [r]
          rw [div_mul_eq_mul_div]
          exact (le_div_iff₀' hαMin_pos).2 h_chain
        exact (inv_mul_le_iff₀ hr_pos).2 hdiv
      have hopt_scaled : E.utility i (r⁻¹ • y) ≤ E.utility i (xHat i) :=
        hdem_i.2 (r⁻¹ • y) hy_scaled_feas
      have hray_y : r⁻¹ * E.utility i y ≤ E.utility i (r⁻¹ • y) :=
        hray i hy.1 hrinv_pos hrinv_le_1
      have huy_le_r : E.utility i y ≤ r * E.utility i (xHat i) :=
        (inv_mul_le_iff₀ hr_pos).1 (hray_y.trans hopt_scaled)
      exact huy_le_r.trans
        (mul_le_mul_of_nonneg_right hr_le (hu_nn i (xHat i) hx_nn))
    · have hfeas := heq.isFeasibleAllocation.2 g
      have hsup_nn := E.totalSupply_nonneg g
      nlinarith

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
  have hexp_scale : ∀ z : G → ℝ,
      expenditure (fun g => p g / E.totalSupply g) (fun g => E.totalSupply g * z g) =
        expenditure p z := fun z => by
    simp only [expenditure_eq_sum]
    refine sum_congr rfl fun g _ => ?_
    have hWg := (hW g).ne'
    field_simp [hWg]
  have hexp_endow :
      expenditure (fun g => p g / E.totalSupply g) (E.endowment i) =
        expenditure p (E.unitRescale.endowment i) := by
    simp only [expenditure_eq_sum, unitRescale_endowment]
    refine sum_congr rfl fun g _ => ?_
    ring
  have hnn_iff : (∀ g, 0 ≤ b g) ↔ ∀ g, 0 ≤ E.totalSupply g * b g :=
    ⟨fun hb g => mul_nonneg (hW g).le (hb g),
      fun hb g => nonneg_of_mul_nonneg_right (hb g) (hW g)⟩
  constructor
  · rintro ⟨hμ, hb_nn, hexp, hopt⟩
    refine ⟨hμ, hnn_iff.1 hb_nn, ?_, fun y hy => ?_⟩
    · rw [hexp_scale, hexp_endow]
      exact hexp
    · let y' : G → ℝ := fun g => y g / E.totalSupply g
      have hy'_feas :
          Market.IsBudgetFeasible p (expenditure p (E.unitRescale.endowment i)) y' := by
        refine ⟨fun g => div_nonneg (hy.1 g) (hW g).le, ?_⟩
        have hy_eq : expenditure p y' =
            expenditure (fun g => p g / E.totalSupply g) y := by
          simp only [y', expenditure_eq_sum]
          refine sum_congr rfl fun g _ => ?_
          ring
        rw [hy_eq, ← hexp_endow]
        exact hy.2
      have h := hopt y' hy'_feas
      have hy_recover : (fun g => E.totalSupply g * y' g) = y := funext fun g =>
        mul_div_cancel₀ (y g) (hW g).ne'
      simpa only [unitRescale_utility, hy_recover] using h
  · rintro ⟨hμ, hb_nn, hexp, hopt⟩
    refine ⟨hμ, hnn_iff.2 hb_nn, ?_, fun y' hy' => ?_⟩
    · rw [← hexp_scale, ← hexp_endow]
      exact hexp
    · let y : G → ℝ := fun g => E.totalSupply g * y' g
      have hy_feas :
          Market.IsBudgetFeasible (fun g => p g / E.totalSupply g)
            (expenditure (fun g => p g / E.totalSupply g) (E.endowment i)) y := by
        refine ⟨fun g => mul_nonneg (hW g).le (hy'.1 g), ?_⟩
        rw [hexp_scale, hexp_endow]
        exact hy'.2
      simpa only [unitRescale_utility] using hopt y hy_feas

/-- **Lemma 6.5 (ii)** ([CodenottiVaradarajan2007], p. 143): `p` is a weak `μ`-approximate
equilibrium for `E.unitRescale` if and only if `(fun g => p g / E.totalSupply g)` is a weak
`μ`-approximate equilibrium for `E`. -/
theorem isWeakApproxEquilibrium_unitRescale_iff (E : ExchangeMarket I G)
    (hW : ∀ g, 0 < E.totalSupply g) (μ : ℝ) (p : G → ℝ) :
    E.unitRescale.IsWeakApproxEquilibrium μ p ↔
      E.IsWeakApproxEquilibrium μ (fun g => p g / E.totalSupply g) := by
  have hp_iff : (∀ g, 0 ≤ p g) ↔ ∀ g, 0 ≤ p g / E.totalSupply g :=
    ⟨fun hp g => div_nonneg (hp g) (hW g).le,
      fun hp g => by
        have := mul_nonneg (hp g) (hW g).le
        rwa [div_mul_cancel₀ _ (hW g).ne'] at this⟩
  constructor
  · rintro ⟨hμ, hp, x, hdem, hsup⟩
    refine ⟨hμ, hp_iff.1 hp, fun i g => E.totalSupply g * x i g, fun i => ?_, fun g => ?_⟩
    · exact (E.isApproxDemand_unitRescale_iff hW μ p i (x i)).1 (hdem i)
    · rw [← mul_sum]
      have h1 := hsup g
      rw [E.unitRescale_totalSupply (hW g), mul_one] at h1
      have := mul_le_mul_of_nonneg_left h1 (hW g).le
      linarith
  · rintro ⟨hμ, hp, y, hdem, hsup⟩
    refine ⟨hμ, hp_iff.2 hp, fun i g => y i g / E.totalSupply g, fun i => ?_, fun g => ?_⟩
    · refine (E.isApproxDemand_unitRescale_iff hW μ p i _).2 ?_
      have hrec : (fun g => E.totalSupply g * (y i g / E.totalSupply g)) = y i :=
        funext fun g => mul_div_cancel₀ (y i g) (hW g).ne'
      rw [hrec]
      exact hdem i
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
  intro p hp
  rw [mem_tatonnementBox] at hp
  rw [mem_tatonnementOuterBox]
  intro g
  have hcard_nn : (0 : ℝ) ≤ Fintype.card G := Nat.cast_nonneg _
  have hquarter_le_half :
      η / (4 * (Fintype.card G : ℝ)) ≤ η / (2 * (Fintype.card G : ℝ)) := by
    rcases eq_or_lt_of_le hcard_nn with h0 | hpos
    · simp [← h0]
    · exact div_le_div_of_nonneg_left hη (by positivity) (by linarith)
  have hquarter_nn : 0 ≤ η / (4 * (Fintype.card G : ℝ)) := by positivity
  exact ⟨hquarter_le_half.trans (hp g).1, (hp g).2.trans (by linarith)⟩

theorem priceRatio_le_of_mem_tatonnementOuterBox [Nonempty G] {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    {p : G → ℝ} (hp : p ∈ tatonnementOuterBox G η) (j k : G) :
    p j / p k ≤ 5 * (Fintype.card G : ℝ) / η := by
  rw [mem_tatonnementOuterBox] at hp
  set n : ℝ := (Fintype.card G : ℝ)
  have hn_ge_1 : 1 ≤ n := Nat.one_le_cast.2 Fintype.card_pos
  have hn_pos : 0 < n := lt_of_lt_of_le zero_lt_one hn_ge_1
  have hlow_pos : 0 < η / (4 * n) := by positivity
  have hpk_ge : η / (4 * n) ≤ p k := (hp k).1
  have hpj_le : p j ≤ 1 + η / (4 * n) := (hp j).2
  have hpk_pos : 0 < p k := lt_of_lt_of_le hlow_pos hpk_ge
  calc
    p j / p k ≤ (1 + η / (4 * n)) / (η / (4 * n)) :=
      div_le_div₀ (by positivity) hpj_le hlow_pos hpk_ge
    _ = (4 * n + η) / η := by
      field_simp [hη0.ne', hn_pos.ne']
    _ ≤ 5 * n / η := by
      refine div_le_div_of_nonneg_right ?_ hη0.le
      linarith

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

theorem isHomogeneousDegZero_phantomExcessDemand {Z' : (G → ℝ) → G → ℝ}
    (hH : IsHomogeneousDegZero Z') (η : ℝ) :
    IsHomogeneousDegZero (phantomExcessDemand Z' η) := by
  intro c hc p hp
  funext g
  simp only [phantomExcessDemand_apply, hH hc hp, phantomDemand_apply, expenditure_smul_left,
    Pi.smul_apply, smul_eq_mul]
  congr 1
  congr 1
  have hpg := (hp g).ne'
  field_simp [hc.ne', hpg]

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
  have hzk : Z' p k + (phantomDemand η p k - η) ≤ 0 := heq.2 k
  have hph_le : phantomDemand η p k ≤ 1 + η := by linarith [hX_nn heq.1 k]
  have hexp_ge : η * p j ≤ expenditure p (fun _ => η) := by
    rw [expenditure_eq_sum]
    have hsingle : p j * η ≤ ∑ l : G, p l * η :=
      single_le_sum (fun l _ => mul_nonneg (heq.1 l).le hη0.le) (mem_univ j)
    linarith
  have hph_ge : η * (p j / p k) / n ≤ phantomDemand η p k := by
    rw [phantomDemand_apply]
    have hpk := heq.1 k
    calc
      η * (p j / p k) / n = (1 / n) * (η * p j) / p k := by ring
      _ ≤ (1 / n) * expenditure p (fun _ => η) / p k :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hexp_ge (by positivity)) hpk.le
  have hmul : η * (p j / p k) ≤ (1 + η) * n := by
    have := (div_le_iff₀ hn_pos).1 (hph_ge.trans hph_le)
    linarith
  have h2n : (1 + η) * n ≤ 2 * n := by nlinarith
  exact (le_div_iff₀' hη0).2 (hmul.trans h2n)

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
  set pStar : G → ℝ := (p gMax)⁻¹ • p
  refine ⟨pStar, ?_, (isHomogeneousDegZero_phantomExcessDemand hH η).isWalrasianEquilibrium_smul
    heq (inv_pos.2 hpMax)⟩
  rw [mem_tatonnementBox]
  intro g
  simp only [pStar, Pi.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_⟩
  · have hrat := priceRatio_le_of_isWalrasianEquilibrium_phantomExcessDemand
      hη0 hη1 hX_nn heq gMax g
    have hn_pos : (0 : ℝ) < Fintype.card G := Nat.cast_pos.2 Fintype.card_pos
    have h2n_pos : (0 : ℝ) < 2 * Fintype.card G := by positivity
    have hpg : 0 < p g := heq.1 g
    have hmul : η * p gMax ≤ (2 * (Fintype.card G : ℝ)) * p g := by
      have h1 := (div_le_div_iff₀ hpg hη0).1 hrat
      linarith
    have hdiv : η / (2 * (Fintype.card G : ℝ)) ≤ p g / p gMax :=
      (div_le_div_iff₀ h2n_pos hpMax).2 (by linarith)
    simpa only [div_eq_inv_mul] using hdiv
  · simpa only [inv_mul_eq_div] using (div_le_one hpMax).2 (hgMax g (mem_univ g))

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
  have hn_pos : 0 < n := lt_of_lt_of_le zero_lt_one hn_ge_1
  set Z := phantomExcessDemand Z' η
  have hWZ : SatisfiesWalrasLaw Z := satisfiesWalrasLaw_phantomExcessDemand hW η
  set δ : ℝ := η / (8 * n ^ 2)
  have hδ_pos : 0 < δ := by positivity
  have hnδ_lt_1 : n * δ < 1 := by
    have : n * δ = η / (8 * n) := by
      dsimp only [δ]
      field_simp [hn_pos.ne']
    rw [this]
    have : 8 * n ≥ 8 := by linarith
    exact (div_lt_one (by positivity)).2 (by linarith)
  have h1_sub_pos : 0 < 1 - n * δ := sub_pos.2 hnδ_lt_1
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
    have hp_pos : ∀ g, 0 < p g := fun g => lt_of_lt_of_le hδ_pos (hp_low g)
    have hpos_nn : ∀ k, 0 ≤ posPart p k := fun k => le_max_left 0 _
    have hsum_pos_nn : 0 ≤ ∑ k : G, posPart p k := sum_nonneg fun k _ => hpos_nn k
    have hden_pos : 0 < 1 + τ * ∑ k : G, posPart p k := by positivity
    -- Upper bound `∑ k, posPart p k ≤ 2 / δ`:
    have hZ_lower : ∀ k, -(1 + η) ≤ Z p k := fun k => by
      simp only [Z, phantomExcessDemand_apply, phantomDemand_apply]
      have hph_nn : 0 ≤ (1 / n) * expenditure p (fun _ => η) / p k :=
        div_nonneg (mul_nonneg (by positivity)
          (expenditure_nonneg (fun l => (hp_pos l).le) (fun _ => hη0.le))) (hp_pos k).le
      linarith [hX_nn hp_pos k]
    have hX_sum_le : ∑ k : G, (Z p k + (1 + η)) ≤ 2 / δ := by
      have hmul_le : δ * ∑ k : G, (Z p k + (1 + η)) ≤
          ∑ k : G, p k * (Z p k + (1 + η)) := by
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
      exact (le_div_iff₀' hδ_pos).2 (hmul_le.trans (by linarith))
    have hpos_le_X : ∑ k : G, posPart p k ≤ 2 / δ := by
      refine (sum_le_sum fun k _ => ?_).trans hX_sum_le
      exact max_le (by linarith [hZ_lower k]) (by linarith)
    have hden_le_2 : 1 + τ * ∑ k : G, posPart p k ≤ 2 := by
      have : τ * ∑ k : G, posPart p k ≤ (δ / 2) * (2 / δ) :=
        mul_le_mul_of_nonneg_left hpos_le_X hτ_pos.le
      have h1 : (δ / 2) * (2 / δ) = 1 := by field_simp [hδ_pos.ne']
      linarith
    refine ⟨fun g => ?_, ?_⟩
    · dsimp only [gnMap]
      by_cases hpg2 : 2 * δ ≤ p g
      · have hnum : 2 * δ ≤ p g + τ * posPart p g := by
          have := mul_nonneg hτ_pos.le (hpos_nn g)
          linarith
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
            have hsub : Subsingleton G := Fintype.card_le_one_iff_subsingleton.1 hcard1.symm.le
            have hpg1 : p g = 1 := by
              rw [← hp_sum, sum_eq_single g (fun k _ hne => (hne (Subsingleton.elim k g)).elim)
                (fun h => (h (mem_univ g)).elim)]
            have hδ_le_nδ : δ ≤ n * δ := le_mul_of_one_le_left hδ_pos.le hn_ge_1
            have hnδ_le : n * δ ≤ 1 / 8 := by
              have : n * δ = η / (8 * n) := by
                dsimp only [δ]
                field_simp [hn_pos.ne']
              rw [this]
              exact div_le_div₀ zero_le_one hη1 (by positivity) (by linarith)
            linarith
          · exact Nat.ofNat_le_cast.2 (Nat.succ_le_of_lt hcard2)
        have hexp_η : expenditure p (fun _ => η) = η := by
          rw [expenditure_eq_sum, ← sum_mul, hp_sum, one_mul]
        have hph_gt : 4 * n < phantomDemand η p g := by
          rw [phantomDemand_apply, hexp_η]
          have h2δ_eq : 2 * δ = η / (4 * n ^ 2) := by
            dsimp only [δ]
            ring
          have hpg_lt : p g < η / (4 * n ^ 2) := h2δ_eq ▸ hpg2
          calc
            4 * n = ((1 / n) * η) / (η / (4 * n ^ 2)) := by
              field_simp [hη0.ne', hn_pos.ne']
            _ < (1 / n) * η / p g :=
              div_lt_div_of_pos_left (by positivity) (hp_pos g) hpg_lt
        have hZg_ge_2 : 2 ≤ posPart p g := by
          refine le_trans ?_ (le_max_right 0 (Z p g))
          simp only [Z, phantomExcessDemand_apply]
          linarith [hX_nn hp_pos g]
        have hnum : 2 * δ ≤ p g + τ * posPart p g := by
          have : δ ≤ τ * posPart p g := by
            dsimp only [τ]
            nlinarith
          linarith [hp_low g]
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
      (∀ g, δ ≤ toTrimmed y g) ∧ ∑ g : G, toTrimmed y g = 1 := by
    intro y hy0 hy1
    refine ⟨fun g => by dsimp only [toTrimmed]; nlinarith [hy0 g], ?_⟩
    simp only [toTrimmed, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ← mul_sum, hy1,
      mul_one]
    change n * δ + (1 - n * δ) = 1
    ring
  have hfromTrimmed : ∀ p : G → ℝ, (∀ g, δ ≤ p g) → ∑ g : G, p g = 1 →
      (∀ g, 0 ≤ fromTrimmed p g) ∧ ∑ g : G, fromTrimmed p g = 1 := by
    intro p hp0 hp1
    refine ⟨fun g => div_nonneg (sub_nonneg.2 (hp0 g)) h1_sub_pos.le, ?_⟩
    simp only [fromTrimmed, ← sum_div, sum_sub_distrib, hp1, sum_const, card_univ, nsmul_eq_mul]
    change (1 - n * δ) / (1 - n * δ) = 1
    exact div_self h1_sub_pos.ne'
  have hF_maps : Set.MapsTo F
      {y | ∀ i : Unit, (∀ g, 0 ≤ y i g) ∧ ∑ g, y i g = 1}
      {y | ∀ i : Unit, (∀ g, 0 ≤ y i g) ∧ ∑ g, y i g = 1} := by
    intro y hy i
    have ht := htoTrimmed (y ()) (hy ()).1 (hy ()).2
    have hg := hgn_maps (toTrimmed (y ())) ht.1 ht.2
    exact hfromTrimmed _ hg.1 hg.2
  have hcont_Z : ContinuousOn Z {p : G → ℝ | ∀ g, 0 < p g} := by
    let posSet : Set (G → ℝ) := {p : G → ℝ | ∀ g, 0 < p g}
    rw [continuousOn_pi]
    intro g
    dsimp only [Z]
    simp_rw [phantomExcessDemand_apply]
    have hZ'_g : ContinuousOn (fun p : G → ℝ => Z' p g) posSet :=
      (continuous_apply g).comp_continuousOn hcont
    have hph_g : ContinuousOn (fun p : G → ℝ => phantomDemand η p g) posSet := by
      simp_rw [phantomDemand_apply]
      have hnum_cont : Continuous fun p : G → ℝ =>
          (1 / (Fintype.card G : ℝ)) * expenditure p (fun _ => η) := by
        simp only [expenditure_eq_sum]
        exact continuous_const.mul
          (continuous_finsetSum univ fun k _ => (continuous_apply k).mul continuous_const)
      exact (hnum_cont.continuousOn (s := posSet)).div₀
        ((continuous_apply g).continuousOn (s := posSet))
        fun p hp => (hp g).ne'
    exact hZ'_g.add (hph_g.sub continuousOn_const)
  have hcont_gn : ContinuousOn gnMap {p : G → ℝ | ∀ g, 0 < p g} := by
    have hcont_pos : ∀ k : G, ContinuousOn (fun p : G → ℝ => posPart p k)
        {p : G → ℝ | ∀ g, 0 < p g} := fun k =>
      (continuous_const.max (continuous_apply k)).comp_continuousOn hcont_Z
    have hcont_den : ContinuousOn (fun p : G → ℝ => 1 + τ * ∑ k : G, posPart p k)
        {p : G → ℝ | ∀ g, 0 < p g} :=
      continuousOn_const.add (continuousOn_const.mul
        (continuousOn_finsetSum univ fun k _ => hcont_pos k))
    rw [continuousOn_pi]
    intro g
    refine ((continuous_apply g).continuousOn.add
      (continuousOn_const.mul (hcont_pos g))).div₀ hcont_den ?_
    intro p _
    have hnn : 0 ≤ ∑ k : G, posPart p k := sum_nonneg fun k _ => le_max_left 0 _
    positivity
  have hF_cont : ContinuousOn F {y | ∀ i : Unit, (∀ g, 0 ≤ y i g) ∧ ∑ g, y i g = 1} := by
    have hto_cont : Continuous (fun y : Unit → G → ℝ => toTrimmed (y ())) :=
      continuous_pi fun g => continuous_const.add
        (continuous_const.mul ((continuous_apply g).comp (continuous_apply ())))
    have hfrom_cont : Continuous fromTrimmed :=
      continuous_pi fun g => ((continuous_apply g).sub continuous_const).div_const _
    have hto_maps : Set.MapsTo (fun y : Unit → G → ℝ => toTrimmed (y ()))
        {y | ∀ i : Unit, (∀ g, 0 ≤ y i g) ∧ ∑ g, y i g = 1}
        {p : G → ℝ | ∀ g, 0 < p g} := by
      intro y hy g
      have ht := htoTrimmed (y ()) (hy ()).1 (hy ()).2
      exact lt_of_lt_of_le hδ_pos (ht.1 g)
    have hcomp := hfrom_cont.comp_continuousOn (hcont_gn.comp hto_cont.continuousOn hto_maps)
    exact continuous_pi (fun _ => continuous_id) |>.comp_continuousOn hcomp
  obtain ⟨yFix, hyFix_mem, hyFix_pt⟩ := Cslib.Brouwer.exists_isFixedPt_pi_simplex hF_maps hF_cont
  set pFix := toTrimmed (yFix ())
  have hpFix_trim := htoTrimmed (yFix ()) (hyFix_mem ()).1 (hyFix_mem ()).2
  have hpFix_pos : ∀ g, 0 < pFix g := fun g => lt_of_lt_of_le hδ_pos (hpFix_trim.1 g)
  have hgn_fix : gnMap pFix = pFix := by
    have h1 : fromTrimmed (gnMap pFix) = yFix () := congrFun hyFix_pt ()
    funext g
    have hfg := congrFun h1 g
    dsimp only [fromTrimmed, pFix, toTrimmed] at hfg ⊢
    have := (div_eq_iff h1_sub_pos.ne').1 hfg
    linarith
  -- Deduce `Z pFix g ≤ 0` for all `g` from `gnMap pFix = pFix` and Walras's law `hWZ`.
  have hpFix_eq : IsWalrasianEquilibrium Z pFix := by
    refine ⟨hpFix_pos, fun g => ?_⟩
    set S := ∑ k : G, posPart pFix k
    have hS_nn : 0 ≤ S := sum_nonneg fun k _ => le_max_left 0 _
    have hden_pos : 0 < 1 + τ * S := by positivity
    have hcoord : ∀ k : G, posPart pFix k = pFix k * S := by
      intro k
      have hk := congrFun hgn_fix k
      dsimp only [gnMap] at hk
      have hmul := (div_eq_iff hden_pos.ne').1 hk
      have hτ_eq : τ * posPart pFix k = τ * (pFix k * S) := by linarith
      exact mul_left_cancel₀ hτ_pos.ne' hτ_eq
    have hsq0 : ∑ k : G, (posPart pFix k) ^ 2 = 0 := by
      have hterm : ∀ k : G, (posPart pFix k) ^ 2 = Z pFix k * posPart pFix k := fun k => by
        dsimp only [posPart]
        rcases le_total (Z pFix k) 0 with hle | hge
        · rw [max_eq_left hle]
          ring
        · rw [max_eq_right hge]
          ring
      calc
        ∑ k : G, (posPart pFix k) ^ 2 = ∑ k : G, Z pFix k * (pFix k * S) := by
          refine sum_congr rfl fun k _ => ?_
          rw [hterm k, hcoord k]
        _ = (∑ k : G, pFix k * Z pFix k) * S := by
          rw [sum_mul]
          exact sum_congr rfl fun k _ => by ring
        _ = 0 := by
          have hw0 : ∑ k : G, pFix k * Z pFix k = 0 := by
            rw [← expenditure_eq_sum]
            exact hWZ hpFix_pos
          rw [hw0, zero_mul]
    have hpos0 : posPart pFix g = 0 := by
      have h0 := (sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (posPart pFix k))).1
        hsq0 g (mem_univ g)
      exact sq_eq_zero_iff.1 h0
    have hle : Z pFix g ≤ posPart pFix g := le_max_right 0 _
    linarith
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
      have hk_le : k ≤ n := by omega
      have hprev := ih hk_le
      have hbase_nn : 0 ≤ 1 + ε / (6 * (n : ℝ)) := by positivity
      calc
        (1 + ε / (6 * (n : ℝ))) ^ (k + 1)
          = (1 + ε / (6 * (n : ℝ))) ^ k * (1 + ε / (6 * (n : ℝ))) := pow_succ _ _
        _ ≤ (1 + (k : ℝ) * (ε / (3 * (n : ℝ)))) * (1 + ε / (6 * (n : ℝ))) :=
            mul_le_mul_of_nonneg_right hprev hbase_nn
        _ = 1 + (k : ℝ) * (ε / (3 * (n : ℝ))) + ε / (6 * (n : ℝ)) +
              ((k : ℝ) * ε ^ 2) / (18 * (n : ℝ) ^ 2) := by ring
        _ ≤ 1 + ((k + 1 : ℕ) : ℝ) * (ε / (3 * (n : ℝ))) := by
            have hk_cast : (k : ℝ) ≤ n := by exact_mod_cast hk_le
            have hsq : ε ^ 2 ≤ ε := by nlinarith
            have hk_eps : (k : ℝ) * ε ^ 2 ≤ (n : ℝ) * ε := by
              calc
                (k : ℝ) * ε ^ 2 ≤ (n : ℝ) * ε ^ 2 :=
                  mul_le_mul_of_nonneg_right hk_cast (sq_nonneg ε)
                _ ≤ (n : ℝ) * ε := mul_le_mul_of_nonneg_left hsq hn_pos.le
            have hquad : ((k : ℝ) * ε ^ 2) / (18 * (n : ℝ) ^ 2) ≤ ε / (6 * (n : ℝ)) := by
              rw [div_le_div_iff₀ (by positivity) (by positivity)]
              nlinarith [hk_eps]
            have hstep_ring : ((k : ℝ) + 1) * (ε / (3 * (n : ℝ))) =
                (k : ℝ) * (ε / (3 * (n : ℝ))) + 2 * (ε / (6 * (n : ℝ))) := by ring
            push_cast
            linarith
  have h1 := hind (n - 1) (by omega)
  have hlt : ((n - 1 : ℕ) : ℝ) * (ε / (3 * (n : ℝ))) < ε / 3 := by
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    rw [hcast]
    have : ((n : ℝ) - 1) * (ε / (3 * (n : ℝ))) = ε / 3 - ε / (3 * (n : ℝ)) := by
      field_simp [hn_pos.ne']
    rw [this]
    have : 0 < ε / (3 * (n : ℝ)) := by positivity
    linarith
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
  rw [mem_tatonnementBox] at hpHat_box
  rw [mem_tatonnementOuterBox] at hp_box
  have hpHat_pos : ∀ g, 0 < pHat g := heqHat.1
  have hp_pos : ∀ g, 0 < p g := fun g =>
    lt_of_lt_of_le (by positivity : 0 < η / (4 * (n : ℝ))) (hp_box g).1
  -- Construct the exact competitive equilibrium `(xHat, pHat)` of `M̂ = E.withPhantomTrader η`.
  let xHat : Option I → G → ℝ
    | some i => d i pHat
    | none => phantomDemand η pHat
  have hMhat_eq : (E.withPhantomTrader η hη0.le).IsCompetitiveEquilibrium xHat pHat := by
    have hz0 := hWZ.eq_zero_of_isWalrasianEquilibrium heqHat
    have hex_eq : ∀ g : G, (E.withPhantomTrader η hη0.le).excessDemand xHat g = Z pHat g := by
      intro g
      rw [ExchangeMarket.excessDemand_eq, Fintype.sum_option,
        E.withPhantomTrader_totalSupply η hη0.le g]
      simp only [xHat, Z, phantomExcessDemand_apply, hZ'_eq hpHat_pos g]
      ring
    refine ⟨fun g => (hpHat_pos g).le, ?_, fun g => ?_, fun g => ?_⟩
    · rintro (rfl | i)
      · rw [ExchangeMarket.mem_demandSet, ExchangeMarket.withPhantomTrader_utility_none,
          ExchangeMarket.income_eq]
        exact cobbDouglasDemand_mem_demandSet (fun _ => by positivity) sum_uniformWeight
          hpHat_pos (expenditure_nonneg (fun g => (hpHat_pos g).le) fun _ => hη0.le)
      · rw [ExchangeMarket.mem_demandSet, ExchangeMarket.withPhantomTrader_utility_some,
          ExchangeMarket.income_eq]
        have hmem := (E.mem_demandSet).1 (hd hpHat_pos i)
        rwa [E.income_eq] at hmem
    · rw [hex_eq, hz0]; exact le_rfl
    · rw [hex_eq, hz0, Pi.zero_apply, mul_zero]
  have hMhat_ray : ∀ t : Option I, IsRayConcave ((E.withPhantomTrader η hη0.le).utility t)
    | some i => hray i
    | none => isRayConcave_cobbDouglasUtility sum_uniformWeight
  have hMhat_nn : ∀ (t : Option I) (b : G → ℝ), (∀ g, 0 ≤ b g) →
      0 ≤ (E.withPhantomTrader η hη0.le).utility t b
    | some i, b, hb => hu_nn i b hb
    | none, b, hb => cobbDouglasUtility_nonneg hb
  -- Contrapositive of Exercise 6.5 gives a pair of goods violating `(1 + ε / 3)`.
  have hspread : ∃ j l : G, (1 + ε / 3) * (p l / pHat l) < p j / pHat j := by
    by_contra hall
    push Not at hall
    exact hnot ((E.withPhantomTrader η hη0.le).isWeakApproxEquilibrium_of_priceRatio_le
      hMhat_ray hMhat_nn hMhat_eq hpHat_pos hp_pos hε0.le hall)
  set σ := sortedPriceRatioEquiv pHat p
  set α := fun t : Fin n => p (σ t) / pHat (σ t)
  set q := fun t : Fin n => hybridPrice pHat p (α t)
  set sFirst : Fin n := ⟨0, hn_pos⟩
  set sLast : Fin n := ⟨n - 1, Nat.sub_lt hn_pos Nat.zero_lt_one⟩
  have hα_spread : (1 + ε / 3) * α sFirst < α sLast := by
    obtain ⟨j, l, hjl⟩ := hspread
    obtain ⟨tj, rfl⟩ := σ.surjective j
    obtain ⟨tl, rfl⟩ := σ.surjective l
    have h1 : α sFirst ≤ α tl := monotone_sortedPriceRatio pHat p (Nat.zero_le tl.val)
    have h2 : α tj ≤ α sLast :=
      monotone_sortedPriceRatio pHat p (Nat.le_sub_one_of_lt tj.isLt)
    have : (1 + ε / 3) * α sFirst ≤ (1 + ε / 3) * α tl :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  have hn_ge_2 : 2 ≤ n := by
    by_contra hlt2
    have hn1 : n = 1 := by omega
    have heq_idx : sFirst = sLast := Fin.ext (by simp [sFirst, sLast, hn1])
    rw [heq_idx] at hα_spread
    have hα_pos : 0 < α sLast := div_pos (hp_pos _) (hpHat_pos _)
    nlinarith
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
        have hstep := hall ⟨k, by omega⟩
        have hprev := ih (by omega)
        calc
          α ⟨k + 1, hk⟩ ≤ (1 + ε / (6 * (n : ℝ))) * α ⟨k, by omega⟩ := hstep.le
          _ ≤ (1 + ε / (6 * (n : ℝ))) * ((1 + ε / (6 * (n : ℝ))) ^ k * α sFirst) :=
            mul_le_mul_of_nonneg_left hprev (by positivity)
          _ = (1 + ε / (6 * (n : ℝ))) ^ (k + 1) * α sFirst := by rw [pow_succ']; ring
    have hlast_le := hind (n - 1) (Nat.sub_lt hn_pos Nat.zero_lt_one)
    have hpow_lt := pow_one_add_div_six_lt hn_ge_2 hε0 hε1
    have hα0_pos : 0 < α sFirst := div_pos (hp_pos _) (hpHat_pos _)
    have : α sLast < (1 + ε / 3) * α sFirst :=
      lt_of_le_of_lt hlast_le (mul_lt_mul_of_pos_right hpow_lt hα0_pos)
    linarith
  obtain ⟨kGap, hkGap⟩ := hex_gap
  set s : Fin n := ⟨kGap.val, by omega⟩
  set s' : Fin n := ⟨kGap.val + 1, by omega⟩
  have hαs_pos : 0 < α s := div_pos (hp_pos _) (hpHat_pos _)
  have hαs'_pos : 0 < α s' := div_pos (hp_pos _) (hpHat_pos _)
  have hα0_pos : 0 < α sFirst := div_pos (hp_pos _) (hpHat_pos _)
  -- Bound `1 - α s / α s' ≥ ε / (12 n)`.
  have h1_sub_ge : ε / (12 * (n : ℝ)) ≤ 1 - α s / α s' := by
    have hdiv_le : α s / α s' ≤ 1 / (1 + ε / (6 * (n : ℝ))) := by
      rw [div_le_div_iff₀ hαs'_pos (by positivity), one_mul]
      linarith
    have h6n_le_2 : 1 + ε / (6 * (n : ℝ)) ≤ 2 := by
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn_pos
      have : ε / (6 * (n : ℝ)) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
      linarith
    calc
      ε / (12 * (n : ℝ)) = (ε / (6 * (n : ℝ))) / 2 := by ring
      _ ≤ (ε / (6 * (n : ℝ))) / (1 + ε / (6 * (n : ℝ))) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) h6n_le_2
      _ = 1 - 1 / (1 + ε / (6 * (n : ℝ))) := by
        have hden : 1 + ε / (6 * (n : ℝ)) ≠ 0 := by positivity
        field_simp [hden]
        ring
      _ ≤ 1 - α s / α s' := by linarith
  -- Bound the phantom trader's income jump and demand jump on `g₀ = σ sFirst`.
  have hinc_jump : (ε / (6 * (n : ℝ))) * α s * pHat (σ sLast) * η ≤
      expenditure (q s') (fun _ => η) - expenditure (q s) (fun _ => η) := by
    have hqs_le : ∀ g, q s g ≤ q s' g :=
      hybridPrice_mono pHat p (monotone_sortedPriceRatio pHat p (show s ≤ s' by
        change kGap.val ≤ kGap.val + 1; omega)) fun g => (hpHat_pos g).le
    have hdiff_sum : expenditure (q s') (fun _ => η) - expenditure (q s) (fun _ => η) =
        ∑ g : G, (q s' g - q s g) * η := by
      simp only [expenditure_eq_sum, ← sum_sub_distrib, sub_mul]
    rw [hdiff_sum]
    have hsingle : (q s' (σ sLast) - q s (σ sLast)) * η ≤ ∑ g : G, (q s' g - q s g) * η :=
      single_le_sum (fun g _ => mul_nonneg (sub_nonneg.2 (hqs_le g)) hη0.le)
        (mem_univ (σ sLast))
    have hs_last : s ≤ sLast := by change kGap.val ≤ n - 1; omega
    have hs'_last : s' ≤ sLast := by change kGap.val + 1 ≤ n - 1; omega
    have hq_s'_last : q s' (σ sLast) = α s' * pHat (σ sLast) :=
      hybridPrice_sorted_of_ge hpHat_pos hs'_last
    have hq_s_last : q s (σ sLast) = α s * pHat (σ sLast) :=
      hybridPrice_sorted_of_ge hpHat_pos hs_last
    have hgap_diff : ε / (6 * (n : ℝ)) * α s ≤ α s' - α s := by linarith
    have hpHat_last_nn := (hpHat_pos (σ sLast)).le
    have hprod_le : (ε / (6 * (n : ℝ)) * α s) * (pHat (σ sLast) * η) ≤
        (α s' - α s) * (pHat (σ sLast) * η) :=
      mul_le_mul_of_nonneg_right hgap_diff (mul_nonneg hpHat_last_nn hη0.le)
    rw [hq_s'_last, hq_s_last] at hsingle
    linarith
  have hZ_jump_g0 :
      (ε * α s * pHat (σ sLast) * η) / (6 * (n : ℝ) ^ 2 * p (σ sFirst)) ≤
        Z (q s') (σ sFirst) - Z (q s) (σ sFirst) := by
    have h0_le_s : sFirst ≤ s := Nat.zero_le _
    have hss' : s ≤ s' := by change kGap.val ≤ kGap.val + 1; omega
    have hZ'_nn : 0 ≤ Z' (q s') (σ sFirst) - Z' (q s) (σ sFirst) :=
      sub_nonneg.2 (excessDemand_hybridPrice_le_succ_of_le hWGS' hpHat_pos hp_pos hss' h0_le_s)
    have hqs'_0 : q s' (σ sFirst) = p (σ sFirst) :=
      hybridPrice_sorted_of_le hpHat_pos (h0_le_s.trans hss')
    have hqs_0 : q s (σ sFirst) = p (σ sFirst) :=
      hybridPrice_sorted_of_le hpHat_pos h0_le_s
    have hph_diff : phantomDemand η (q s') (σ sFirst) - phantomDemand η (q s) (σ sFirst) =
        (1 / (n : ℝ)) * (expenditure (q s') (fun _ => η) - expenditure (q s) (fun _ => η)) /
          p (σ sFirst) := by
      simp only [phantomDemand_apply, hqs'_0, hqs_0]
      ring
    have hph_ge : (ε * α s * pHat (σ sLast) * η) / (6 * (n : ℝ) ^ 2 * p (σ sFirst)) ≤
        phantomDemand η (q s') (σ sFirst) - phantomDemand η (q s) (σ sFirst) := by
      rw [hph_diff]
      have hp0_pos : 0 < p (σ sFirst) := hp_pos (σ sFirst)
      calc
        (ε * α s * pHat (σ sLast) * η) / (6 * (n : ℝ) ^ 2 * p (σ sFirst))
          = (1 / (n : ℝ)) * ((ε / (6 * (n : ℝ))) * α s * pHat (σ sLast) * η) / p (σ sFirst) := by
              field_simp [hn_rpos.ne', hp0_pos.ne']
        _ ≤ (1 / (n : ℝ)) *
              (expenditure (q s') (fun _ => η) - expenditure (q s) (fun _ => η)) /
              p (σ sFirst) :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hinc_jump (by positivity)) hp0_pos.le
    simp only [Z, phantomExcessDemand_apply]
    linarith
  -- Plug `t = sFirst` into Equation `(6.5)` (`expenditure_hybridPrice_step_ge`) at `kGap`.
  have hstep_k : tatonnementDelta n ε η ≤
      expenditure pHat (Z (q s')) - expenditure pHat (Z (q s)) := by
    have hge65 := expenditure_hybridPrice_step_ge hHZ hWZ hWGSZ heqHat hp_pos
      (s := s) (s' := s') rfl
    have hss' : s ≤ s' := by change kGap.val ≤ kGap.val + 1; omega
    have hmem0 : sFirst ∈ univ.filter (· ≤ s) := mem_filter.2 ⟨mem_univ sFirst, Nat.zero_le _⟩
    have hsum_ge : pHat (σ sFirst) * (Z (q s') (σ sFirst) - Z (q s) (σ sFirst)) ≤
        ∑ t ∈ univ.filter (· ≤ s), pHat (σ t) * (Z (q s') (σ t) - Z (q s) (σ t)) :=
      single_le_sum (fun t ht => mul_nonneg (hpHat_pos (σ t)).le
        (sub_nonneg.2 (excessDemand_hybridPrice_le_succ_of_le hWGSZ hpHat_pos hp_pos hss'
          (mem_filter.1 ht).2))) hmem0
    have hα0_le_αs : α sFirst ≤ α s := monotone_sortedPriceRatio pHat p (Nat.zero_le _)
    have hratio_ge_1 : 1 ≤ pHat (σ sFirst) * α s / p (σ sFirst) := by
      have hp0_eq : p (σ sFirst) = α sFirst * pHat (σ sFirst) :=
        (div_mul_cancel₀ (p (σ sFirst)) (hpHat_pos (σ sFirst)).ne').symm
      rw [hp0_eq, mul_comm (pHat _), mul_div_mul_right _ _ (hpHat_pos (σ sFirst)).ne']
      exact (one_le_div hα0_pos).2 hα0_le_αs
    have hpHat_last_ge : η / (2 * (n : ℝ)) ≤ pHat (σ sLast) := (hpHat_box (σ sLast)).1
    have hterm_ge : ε ^ 2 * η ^ 2 / (144 * (n : ℝ) ^ 4) ≤
        (ε / (12 * (n : ℝ))) *
          (pHat (σ sFirst) *
            ((ε * α s * pHat (σ sLast) * η) / (6 * (n : ℝ) ^ 2 * p (σ sFirst)))) := by
      have hp0_pos := hp_pos (σ sFirst)
      calc
        ε ^ 2 * η ^ 2 / (144 * (n : ℝ) ^ 4)
          = (ε / (12 * (n : ℝ))) *
              (1 * ((ε * (η / (2 * (n : ℝ))) * η) / (6 * (n : ℝ) ^ 2))) := by
              field_simp [hn_rpos.ne']
              ring
        _ ≤ (ε / (12 * (n : ℝ))) *
              ((pHat (σ sFirst) * α s / p (σ sFirst)) *
                ((ε * pHat (σ sLast) * η) / (6 * (n : ℝ) ^ 2))) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              refine mul_le_mul hratio_ge_1 ?_ (by positivity) (by positivity)
              refine div_le_div_of_nonneg_right ?_ (by positivity)
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hpHat_last_ge hε0.le) hη0.le
        _ = (ε / (12 * (n : ℝ))) *
              (pHat (σ sFirst) *
                ((ε * α s * pHat (σ sLast) * η) / (6 * (n : ℝ) ^ 2 * p (σ sFirst)))) := by
              field_simp [hn_rpos.ne', hp0_pos.ne']
    have hprod_ge :
        (ε / (12 * (n : ℝ))) *
          (pHat (σ sFirst) *
            ((ε * α s * pHat (σ sLast) * η) / (6 * (n : ℝ) ^ 2 * p (σ sFirst)))) ≤
        (1 - α s / α s') *
          (∑ t ∈ univ.filter (· ≤ s), pHat (σ t) * (Z (q s') (σ t) - Z (q s) (σ t))) := by
      have hp0_pos := hp_pos (σ sFirst)
      have hpHat0_pos := hpHat_pos (σ sFirst)
      have hpHatL_pos := hpHat_pos (σ sLast)
      refine mul_le_mul h1_sub_ge ?_ (by positivity)
        (by linarith [h1_sub_ge, show 0 < ε / (12 * (n : ℝ)) by positivity])
      exact (mul_le_mul_of_nonneg_left hZ_jump_g0 hpHat0_pos.le).trans hsum_ge
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
  have hn_pos : 0 < n := lt_of_lt_of_le zero_lt_one hn_ge_1
  set Z := phantomExcessDemand Z' η
  have hWZ : SatisfiesWalrasLaw Z := satisfiesWalrasLaw_phantomExcessDemand hW' η
  have hp_pos : ∀ g, 0 < p g := fun g => by
    have := ((mem_tatonnementOuterBox).1 hp g).1
    exact lt_of_lt_of_le (by positivity) this
  let X : G → ℝ := fun g => Z p g + (1 + η)
  have hX_pos : ∀ g, 0 ≤ X g := fun g => by
    dsimp only [X, Z]
    rw [phantomExcessDemand_apply, phantomDemand_apply]
    have hph_nn : 0 ≤ (1 / n) * expenditure p (fun _ => η) / p g :=
      div_nonneg (mul_nonneg (by positivity)
        (expenditure_nonneg (fun l => (hp_pos l).le) (fun _ => hη0.le))) (hp_pos g).le
    linarith [hX_nn hp_pos g]
  obtain ⟨gMin, -, hgMin⟩ := exists_min_image univ p univ_nonempty
  obtain ⟨gMax, -, hgMax⟩ := exists_max_image univ p univ_nonempty
  have hpMin_pos : 0 < p gMin := hp_pos gMin
  -- Bound `∑ g, X g ≤ (p gMax / p gMin) * ∑ g, (1 + η)`.
  have hX_sum_le : ∑ g : G, X g ≤ (5 * n / η) * (2 * n) := by
    have h1 : p gMin * ∑ g : G, X g ≤ ∑ g : G, p g * X g := by
      rw [mul_sum]
      exact sum_le_sum fun g _ => mul_le_mul_of_nonneg_right (hgMin g (mem_univ g)) (hX_pos g)
    have hwal : ∑ g : G, p g * X g = ∑ g : G, p g * (1 + η) := by
      have hw0 : ∑ g : G, p g * Z p g = 0 := by
        rw [← expenditure_eq_sum]
        exact hWZ hp_pos
      calc
        ∑ g : G, p g * (Z p g + (1 + η)) =
            (∑ g : G, p g * Z p g) + ∑ g : G, p g * (1 + η) := by
          simp only [mul_add, sum_add_distrib]
        _ = ∑ g : G, p g * (1 + η) := by rw [hw0, zero_add]
    have h2 : ∑ g : G, p g * (1 + η) ≤ p gMax * (2 * n) := by
      calc
        ∑ g : G, p g * (1 + η) ≤ ∑ _g : G, p gMax * 2 :=
          sum_le_sum fun g _ => mul_le_mul (hgMax g (mem_univ g)) (by linarith) (by positivity)
            (hp_pos gMax).le
        _ = p gMax * (2 * n) := by
          simp only [sum_const, card_univ, nsmul_eq_mul, n]
          ring
    have hdiv : ∑ g : G, X g ≤ (p gMax / p gMin) * (2 * n) := by
      rw [div_mul_eq_mul_div]
      exact (le_div_iff₀' hpMin_pos).2 (h1.trans (hwal ▸ h2))
    have hrat := priceRatio_le_of_mem_tatonnementOuterBox hη0 hη1 hp gMax gMin
    exact hdiv.trans (mul_le_mul_of_nonneg_right hrat (by positivity))
  -- Bound `∑ g, |Z p g| ≤ ∑ g, X g + ∑ g, (1 + η) ≤ 12 n^2 / η`.
  have hl1_le : ∑ g : G, |Z p g| ≤ tatonnementBoundL (Fintype.card G) η := by
    have habs : ∀ g : G, |Z p g| ≤ X g + (1 + η) := fun g => by
      have : Z p g = X g - (1 + η) := by dsimp only [X]; ring
      rw [this]
      exact (abs_sub _ _).trans (by rw [abs_of_nonneg (hX_pos g), abs_of_nonneg (by positivity)])
    have hsum_abs : ∑ g : G, |Z p g| ≤ (∑ g : G, X g) + 2 * n := by
      calc
        ∑ g : G, |Z p g| ≤ ∑ g : G, (X g + (1 + η)) := sum_le_sum fun g _ => habs g
        _ = (∑ g : G, X g) + n * (1 + η) := by
          simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, n]
          ring
        _ ≤ (∑ g : G, X g) + 2 * n := by nlinarith
    have hbound : (5 * n / η) * (2 * n) + 2 * n ≤ 12 * n ^ 2 / η := by
      have h2n : 2 * n ≤ 2 * n ^ 2 / η := by
        rw [le_div_iff₀ hη0]
        have : n * η ≤ n ^ 2 := by nlinarith
        linarith
      calc
        (5 * n / η) * (2 * n) + 2 * n = 10 * n ^ 2 / η + 2 * n := by ring
        _ ≤ 10 * n ^ 2 / η + 2 * n ^ 2 / η := by linarith
        _ = 12 * n ^ 2 / η := by ring
    rw [tatonnementBoundL_eq]
    exact hsum_abs.trans (by linarith)
  -- Finally `∑ g, (Z p g)^2 ≤ (∑ g, |Z p g|)^2 ≤ L^2`.
  have hl2_le_l1 : ∑ g : G, (Z p g) ^ 2 ≤ (∑ g : G, |Z p g|) ^ 2 := by
    have hrew : ∑ g : G, (Z p g) ^ 2 = ∑ g : G, |Z p g| ^ 2 :=
      sum_congr rfl fun g _ => (sq_abs (Z p g)).symm
    rw [hrew, sq, sum_mul]
    refine sum_le_sum fun g hg => ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_left
      (single_le_sum (fun k _ => abs_nonneg (Z p k)) hg) (abs_nonneg (Z p g))
  have hl1_nn : 0 ≤ ∑ g : G, |Z p g| := sum_nonneg fun g _ => abs_nonneg _
  exact hl2_le_l1.trans (pow_le_pow_left₀ hl1_nn hl1_le 2)

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
  rw [mem_tatonnementBox] at hpStar hp₀
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
        lt_of_lt_of_le (by positivity) (((mem_tatonnementOuterBox).1 hp_in g).1)
      have hw_p : expenditure p (Z p) = 0 := hWZ hp_pos
      set s := δ / L ^ 2
      have hs_pos : 0 < s := by positivity
      have hquad : pot p - pot (p + s • Z p) =
          2 * s * (expenditure pStar (Z p) - expenditure p (Z p)) -
            s ^ 2 * ∑ g : G, (Z p g) ^ 2 := by
        simp only [pot, expenditure_eq_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have hpt : ∀ g : G,
            (pStar g - p g) ^ 2 - (pStar g - (p g + s * Z p g)) ^ 2 =
              2 * s * (pStar g * Z p g - p g * Z p g) - s ^ 2 * (Z p g) ^ 2 :=
          fun g => by ring
        simp_rw [← sum_sub_distrib, hpt, sum_sub_distrib, ← mul_sum, sum_sub_distrib]
      rw [hquad, hw_p, sub_zero]
      have hnorm_p := hnorm p hp_in
      have hge1 : (δ / L) ^ 2 ≤ 2 * s * expenditure pStar (Z p) - s ^ 2 * ∑ g : G, (Z p g) ^ 2 := by
        have h1 : 2 * s * δ ≤ 2 * s * expenditure pStar (Z p) :=
          mul_le_mul_of_nonneg_left hsep_ge (by positivity)
        have h2 : s ^ 2 * ∑ g : G, (Z p g) ^ 2 ≤ s ^ 2 * L ^ 2 :=
          mul_le_mul_of_nonneg_left hnorm_p (sq_nonneg s)
        have h3 : 2 * (δ / L ^ 2) * δ - (δ / L ^ 2) ^ 2 * L ^ 2 = (δ / L) ^ 2 := by
          field_simp [hL_pos.ne']
          ring
        dsimp only [s] at h1 h2 ⊢
        linarith
      exact (min_le_left _ _).trans hge1
    · -- Projection step `p ∉ Δ⁺`: clamping to `[η/(2n), 1]` drops `pot` by `≥ (η/(4n))^2`.
      rw [tatonnementStep_of_not_mem Z η δ hp_in]
      set low := η / (2 * (n : ℝ))
      have hlow_nn : 0 ≤ low := by positivity
      have hlow_le_1 : low ≤ 1 := by
        have : 2 * (n : ℝ) ≥ 2 := by
          have : (1 : ℝ) ≤ n := by exact_mod_cast Fintype.card_pos
          linarith
        exact (div_le_one (by positivity)).2 (by linarith)
      -- Every coordinate projection is nonexpansive toward `pStar g ∈ [low, 1]`.
      have hcoord_nn : ∀ g : G,
          0 ≤ (pStar g - p g) ^ 2 - (pStar g - projectTatonnementBox η p g) ^ 2 := by
        intro g
        rw [projectTatonnementBox_apply]
        change 0 ≤ (pStar g - p g) ^ 2 - (pStar g - max low (min 1 (p g))) ^ 2
        have hps_low : low ≤ pStar g := (hpStar g).1
        have hps_1 : pStar g ≤ 1 := (hpStar g).2
        rcases lt_trichotomy (p g) low with hlt | heq | hgt
        · have hcl : max low (min 1 (p g)) = low :=
            max_eq_left ((min_le_right 1 (p g)).trans hlt.le)
          rw [hcl]
          nlinarith
        · rw [heq, min_eq_right hlow_le_1, max_self, sub_self]
        · rcases le_or_gt (p g) 1 with hle1 | hgt1
          · have hcl : max low (min 1 (p g)) = p g := by
              rw [min_eq_right hle1, max_eq_right hgt.le]
            rw [hcl, sub_self]
          · have hcl : max low (min 1 (p g)) = 1 := by
              rw [min_eq_left hgt1.le, max_eq_right hlow_le_1]
            rw [hcl]
            nlinarith
      -- At least one coordinate violates `Δ⁺`, contributing `≥ (η / (4n))^2`.
      have hex_viol : ∃ g₀ : G,
          p g₀ < η / (4 * (n : ℝ)) ∨ 1 + η / (4 * (n : ℝ)) < p g₀ := by
        by_contra hall
        push Not at hall
        exact hp_in ((mem_tatonnementOuterBox).2 fun g => ⟨(hall g).1, (hall g).2⟩)
      obtain ⟨g₀, hviol⟩ := hex_viol
      have hg₀_drop : (η / (4 * (n : ℝ))) ^ 2 ≤
          (pStar g₀ - p g₀) ^ 2 - (pStar g₀ - projectTatonnementBox η p g₀) ^ 2 := by
        rw [projectTatonnementBox_apply]
        change (η / (4 * (n : ℝ))) ^ 2 ≤
          (pStar g₀ - p g₀) ^ 2 - (pStar g₀ - max low (min 1 (p g₀))) ^ 2
        have hps_low : low ≤ pStar g₀ := (hpStar g₀).1
        have hps_1 : pStar g₀ ≤ 1 := (hpStar g₀).2
        have hlow_eq : low = 2 * (η / (4 * (n : ℝ))) := by
          dsimp only [low]
          ring
        rcases hviol with hsmall | hlarge
        · have hlt_low : p g₀ < low := by linarith [show 0 < η / (4 * (n : ℝ)) by positivity]
          have hcl : max low (min 1 (p g₀)) = low :=
            max_eq_left ((min_le_right 1 (p g₀)).trans hlt_low.le)
          rw [hcl]
          have hgap : η / (4 * (n : ℝ)) ≤ low - p g₀ := by linarith
          nlinarith [show 0 ≤ pStar g₀ - low by linarith, show 0 < η / (4 * (n : ℝ)) by positivity]
        · have hgt1 : 1 < p g₀ := by linarith [show 0 < η / (4 * (n : ℝ)) by positivity]
          have hcl : max low (min 1 (p g₀)) = 1 := by
            rw [min_eq_left hgt1.le, max_eq_right hlow_le_1]
          rw [hcl]
          have hgap : η / (4 * (n : ℝ)) ≤ p g₀ - 1 := by linarith
          nlinarith [show 0 ≤ 1 - pStar g₀ by linarith, show 0 < η / (4 * (n : ℝ)) by positivity]
      have htot_drop : (η / (4 * (n : ℝ))) ^ 2 ≤ pot p - pot (projectTatonnementBox η p) := by
        dsimp only [pot]
        rw [← sum_sub_distrib]
        exact hg₀_drop.trans (single_le_sum (fun g _ => hcoord_nn g) (mem_univ g₀))
      exact (min_le_right _ _).trans htot_drop
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
      have hprev := ih (by omega)
      have hfail_m : ¬ (tatonnementIter Z η δ p₀ m ∈ tatonnementOuterBox G η ∧
          expenditure pStar (Z (tatonnementIter Z η δ p₀ m)) < δ) :=
        fun h => not_lt_of_ge (hnone m (by omega) h.1) h.2
      have hstep_m := hdrop (tatonnementIter Z η δ p₀ m) hfail_m
      rw [tatonnementIter_succ]
      push_cast
      linarith
  have hK1 := htelescope (K + 1) le_rfl
  have hpot0_le : pot p₀ ≤ n := by
    dsimp only [pot]
    calc
      ∑ g : G, (pStar g - p₀ g) ^ 2 ≤ ∑ _g : G, (1 : ℝ) := by
        refine sum_le_sum fun g _ => ?_
        have h1 := hpStar g
        have h2 := hp₀ g
        have hlow_nn : 0 ≤ η / (2 * (n : ℝ)) := by positivity
        nlinarith
      _ = n := by simp [n]
  have hpot_nn : 0 ≤ pot (tatonnementIter Z η δ p₀ (K + 1)) :=
    sum_nonneg fun g _ => sq_nonneg _
  have hle_n : ((K + 1 : ℕ) : ℝ) * μ ≤ n := by linarith
  have hdiv_le : (K : ℝ) + 1 ≤ (n : ℝ) / μ := by
    push_cast at hle_n
    exact (le_div_iff₀ hμ_pos).2 hle_n
  exact not_lt_of_ge hdiv_le (Nat.lt_floor_add_one ((n : ℝ) / μ))

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
  have hX_nn : ∀ ⦃q : G → ℝ⦄, (∀ g, 0 < q g) → ∀ g, -1 ≤ Z' q g := by
    intro q hq g
    rw [hZ'_eq hq g, hsup g]
    have hd_nn : 0 ≤ ∑ i : I, d i q g := sum_nonneg fun i _ =>
      (((mem_demandSet).1 ((E.mem_demandSet).1 (hd hq i))).1.1 g)
    linarith
  obtain ⟨pStar, hpStar_box, hpStar_eq⟩ :=
    exists_mem_tatonnementBox_isWalrasianEquilibrium hη0 hη1 hH' hW' hX_nn hcont'
  have hδ_pos : 0 < δ := by
    dsimp only [δ]
    rw [tatonnementDelta_eq]
    have : (0 : ℝ) < Fintype.card G := Nat.cast_pos.2 Fintype.card_pos
    positivity
  have hWZ : SatisfiesWalrasLaw (phantomExcessDemand Z' η) :=
    satisfiesWalrasLaw_phantomExcessDemand hW' η
  have hnorm : ∀ p ∈ tatonnementOuterBox G η,
      ∑ g : G, (phantomExcessDemand Z' η p g) ^ 2 ≤
        (tatonnementBoundL (Fintype.card G) η) ^ 2 :=
    fun p hp => sum_sq_phantomExcessDemand_le hη0 hη1 hW' hX_nn hp
  obtain ⟨k, hk_le, hk_in, hk_lt⟩ :=
    exists_le_tatonnementIter_sep_lt hWZ hη0 hη1 hδ_pos hnorm hpStar_box hp₀
  refine ⟨k, hk_le, hk_in, ?_⟩
  by_contra hnot
  have hge := expenditure_phantomExcessDemand_ge_delta hray hu_nn hd hZ'_eq hH' hW' hWGS'
    hη0 hε0 hε1 hpStar_box hpStar_eq hk_in hnot
  linarith

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
  have hray' : ∀ i, IsRayConcave (E.unitRescale.utility i) := by
    intro i b hb c hc0 hc1
    rw [E.unitRescale_utility, E.unitRescale_utility]
    have hmul : (fun g => E.totalSupply g * (c • b) g) =
        c • (fun g => E.totalSupply g * b g) := funext fun g => by
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hmul]
    exact hray i (fun g => mul_nonneg (hW g).le (hb g)) hc0 hc1
  have hu_nn' : ∀ i b, (∀ g, 0 ≤ b g) → 0 ≤ E.unitRescale.utility i b := fun i b hb => by
    rw [E.unitRescale_utility]
    exact hu_nn i _ fun g => mul_nonneg (hW g).le (hb g)
  let d' : I → (G → ℝ) → G → ℝ :=
    fun i q g => d i (fun l => q l / E.totalSupply l) g / E.totalSupply g
  have hd' : ∀ ⦃q : G → ℝ⦄, (∀ g, 0 < q g) → ∀ i, d' i q ∈ E.unitRescale.demandSet q i := by
    intro q hq i
    have hq_div : ∀ l, 0 < q l / E.totalSupply l := fun l => div_pos (hq l) (hW l)
    have hmem := (E.mem_demandSet).1 (hd hq_div i)
    rw [E.income_eq, mem_demandSet] at hmem
    rw [ExchangeMarket.mem_demandSet, ExchangeMarket.income_eq, mem_demandSet]
    have hexp_eq : ∀ b : G → ℝ,
        expenditure q b =
          expenditure (fun l => q l / E.totalSupply l) (fun l => E.totalSupply l * b l) :=
      fun b => by
        simp only [expenditure_eq_sum]
        refine sum_congr rfl fun l _ => ?_
        have hWl := (hW l).ne'
        field_simp [hWl]
    have hendow_recover :
        (fun l => E.totalSupply l * E.unitRescale.endowment i l) = E.endowment i :=
      funext fun l => by
        rw [E.unitRescale_endowment]
        exact mul_div_cancel₀ _ (hW l).ne'
    have hd'_recover : (fun l => E.totalSupply l * d' i q l) =
        d i (fun l => q l / E.totalSupply l) :=
      funext fun l => mul_div_cancel₀ _ (hW l).ne'
    refine ⟨⟨fun g => div_nonneg (hmem.1.1 g) (hW g).le, ?_⟩, fun b hb => ?_⟩
    · rw [hexp_eq (d' i q), hexp_eq (E.unitRescale.endowment i), hd'_recover, hendow_recover]
      exact hmem.1.2
    · rw [E.unitRescale_utility, E.unitRescale_utility, hd'_recover]
      refine hmem.2 (fun l => E.totalSupply l * b l) ⟨fun l => mul_nonneg (hW l).le (hb.1 l), ?_⟩
      rw [← hexp_eq b, ← hendow_recover, ← hexp_eq (E.unitRescale.endowment i)]
      exact hb.2
  have hsup' : ∀ g, E.unitRescale.totalSupply g = 1 := fun g => E.unitRescale_totalSupply (hW g)
  have hZ'_eq : ∀ ⦃q : G → ℝ⦄, (∀ g, 0 < q g) → ∀ g,
      Z' q g = (∑ i : I, d' i q g) - E.unitRescale.totalSupply g := by
    intro q hq g
    have hq_div : ∀ l, 0 < q l / E.totalSupply l := fun l => div_pos (hq l) (hW l)
    dsimp only [Z', d']
    rw [hZ_eq hq_div g, sub_div, ← sum_div, div_self (hW g).ne', hsup' g]
  have hH' : IsHomogeneousDegZero Z' := by
    intro c hc q hq
    funext g
    dsimp only [Z']
    have hsmul : (fun l => (c • q) l / E.totalSupply l) = c • (fun l => q l / E.totalSupply l) :=
      funext fun l => by simp [Pi.smul_apply, smul_eq_mul, mul_div_assoc]
    rw [hsmul, hH hc fun l => div_pos (hq l) (hW l)]
  have hW' : SatisfiesWalrasLaw Z' := by
    intro q hq
    have hq_div : ∀ l, 0 < q l / E.totalSupply l := fun l => div_pos (hq l) (hW l)
    have hw := hWalras hq_div
    rw [expenditure_eq_sum] at hw ⊢
    convert hw using 1
    refine sum_congr rfl fun g _ => ?_
    dsimp only [Z']
    have hWg := (hW g).ne'
    field_simp [hWg]
  have hWGS' : IsWeakGrossSubstitutes Z' := isWeakGrossSubstitutes_unitRescale hW hWGS
  have hcont' : ContinuousOn Z' {q : G → ℝ | ∀ g, 0 < q g} := by
    have hscale_cont : Continuous (fun q : G → ℝ => fun l => q l / E.totalSupply l) :=
      continuous_pi fun l => (continuous_apply l).div_const _
    have hscale_maps : Set.MapsTo (fun q : G → ℝ => fun l => q l / E.totalSupply l)
        {q : G → ℝ | ∀ g, 0 < q g} {q : G → ℝ | ∀ g, 0 < q g} :=
      fun q hq l => div_pos (hq l) (hW l)
    have hcomp := hcont.comp hscale_cont.continuousOn hscale_maps
    rw [continuousOn_pi]
    intro g
    exact ((continuous_apply g).comp_continuousOn hcomp).div_const (E.totalSupply g)
  have hp0_box : (fun _ : G => (1 : ℝ)) ∈ tatonnementBox G η := by
    rw [mem_tatonnementBox]
    intro g
    have : 2 * (Fintype.card G : ℝ) ≥ 2 := by
      have : (1 : ℝ) ≤ Fintype.card G := by exact_mod_cast Fintype.card_pos
      linarith
    exact ⟨(div_le_one (by positivity)).2 (by linarith), le_rfl⟩
  obtain ⟨k, hk_le, -, hk_approx⟩ :=
    exists_le_tatonnementIter_isWeakApproxEquilibrium hray' hu_nn' hd' hZ'_eq hsup'
      hH' hW' hWGS' hcont' hη0 hη1 hη0 hη1 hp0_box
  refine ⟨k, hk_le, ?_⟩
  -- Transfer `(1 + η)`-approx equilibrium on `M̂` → `(1 + η)^2`-approx on `M'` → `(1 + ε)` on `M`!
  have hM' := E.unitRescale.isWeakApproxEquilibrium_of_withPhantomTrader hsup' hu_nn' hη0.le
    hk_approx
  have hM := (E.isWeakApproxEquilibrium_unitRescale_iff hW ((1 + η) * (1 + η)) _).1 hM'
  refine hM.mono ?_ hu_nn
  dsimp only [η]
  nlinarith

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
  let posSet : Set (G → ℝ) := {q : G → ℝ | ∀ g, 0 < q g}
  rw [continuousOn_pi]
  intro g
  simp_rw [E.excessDemandFn_eq]
  refine ContinuousOn.sub ?_ continuousOn_const
  refine continuousOn_finsetSum univ fun i _ => ?_
  have hnum : Continuous fun q : G → ℝ =>
      E.weight i g * expenditure q (E.endowment i) := by
    simp only [expenditure_eq_sum]
    exact continuous_const.mul
      (continuous_finsetSum univ fun k _ => (continuous_apply k).mul continuous_const)
  exact (hnum.continuousOn (s := posSet)).div₀
    ((continuous_apply g).continuousOn (s := posSet))
    fun q hq => (hq g).ne'

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
