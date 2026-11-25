/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Market.EisenbergGale
public import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Second Welfare Theorem and fairness of Fisher market equilibria

While the First Welfare Theorem (`ExchangeMarket.IsCompetitiveEquilibrium.isParetoOptimal` in
`CslibFrontier.GameTheory.Market.Basic`) requires only local nonsatiation, its converse—the
**Second Fundamental Theorem of Welfare Economics** ([Arrow1951Welfare]; [ArrowDebreu1954])—uses
convexity of preferences and hyperplane separation to decentralize any Pareto-optimal allocation `x`
via a nonzero nonnegative price vector `p`:

1. **Negative-orthant separating hyperplane (`exists_price_of_convex_disjoint_negOrthant`):**
   derived from `geometric_hahn_banach_open`, any nonempty convex subset `K ⊆ (G → ℝ)` disjoint from
   the open negative orthant `negOrthant G = {z | ∀ g, z g < 0}` in which `0` is approximable admits
   a nonzero nonnegative price vector `p ≥ 0` (`∃ g, 0 < p g`) with `∀ z ∈ K, 0 ≤ expenditure p z`.
   This serves as the shared separation engine for both the Second Welfare Theorem and the
   Debreu–Scarf core equivalence theorem in `CslibFrontier.GameTheory.Market.Core`.
2. **Consumer quasi-demand and cheaper-point upgrade (`IsQuasiDemand`,
   `IsQuasiDemand.mem_demandSet_of_budget_pos`):** a bundle `x` is a quasi-demand at `(p, m)` if it
   is budget-feasible and every strictly preferred nonnegative bundle costs at least `m`. When `u`
   is continuous on `ℝ_+^G` and `0 < m` (so `0 ∈ ℝ_+^G` provides a strictly cheaper bundle), ray
   scaling upgrades `IsQuasiDemand` to full Marshallian demand `x ∈ demandSet u p m`.
3. **Second Welfare Theorem
   (`ExchangeMarket.exists_priceQuasiEquilibrium_reendow_of_isParetoOptimal` and
   `ExchangeMarket.exists_isCompetitiveEquilibrium_reendow_of_isParetoOptimal`):** under local
   nonsatiation and convex strictly-preferred upper contour sets (`HasConvexPreferences`, implied by
   `QuasiconcaveOn` or `ConcaveOn`), every Pareto-optimal allocation `x` admits a price vector `p`
   supporting `(x, p)` as a price quasi-equilibrium after lump-sum redistribution `E.reendow x`
   (with complementary slackness `p g * E.excessDemand x g = 0` against original supply). When
   utilities are continuous on `ℝ_+^G` and `x` is strictly positive (`∀ i g, 0 < x i g`, or more
   generally every trader receives positive value at `p`), `(x, p)` is a full competitive
   equilibrium of `E.reendow x`.
4. **Budget-weighted envy-freeness and proportionality of Fisher equilibria ([Varian1974]):**
   in any `FisherMarket` with ray-concave utilities (and unconditionally in any
   `LinearFisherMarket`), market equilibria are budget-weighted envy-free
   (`budget i * u_i(x_j) ≤ budget j * u_i(x_i)` in the linear model, specializing to exact
   envy-freeness when budgets are equal) and guarantee every buyer at least their budget-share
   fraction of total supply utility (`proportional_share`).

## Main definitions

* `Cslib.GameTheory.Market.negOrthant`: open negative orthant `{z : G → ℝ | ∀ g, z g < 0}`.
* `Cslib.GameTheory.Market.HasConvexPreferences`: convexity of strictly preferred upper contour sets
  `{b | (∀ g, 0 ≤ b g) ∧ u x < u b}` on `ℝ_+^G`.
* `Cslib.GameTheory.Market.IsQuasiDemand`: budget feasibility paired with expenditure lower bound
  `u x < u b → m ≤ expenditure p b` on `ℝ_+^G`.
* `Cslib.GameTheory.Market.ExchangeMarket.reendow`,
  `Cslib.GameTheory.Market.ExchangeMarket.IsPriceQuasiEquilibrium`: lump-sum endowment
  redistribution and price quasi-equilibrium of an exchange market.

## Main results

* `Cslib.GameTheory.Market.exists_price_of_convex_disjoint_negOrthant`: nonzero nonnegative
  separating price vector for convex sets disjoint from `negOrthant G` containing `0` in their
  closure.
* `Cslib.GameTheory.Market.IsQuasiDemand.mem_demandSet_of_budget_pos`,
  `ExchangeMarket.IsPriceQuasiEquilibrium.isCompetitiveEquilibrium_of_income_pos`:
  cheaper-point upgrade from quasi-demand and price quasi-equilibrium to Marshallian demand and
  competitive equilibrium.
* `ExchangeMarket.exists_priceQuasiEquilibrium_reendow_of_isParetoOptimal`,
  `ExchangeMarket.exists_isCompetitiveEquilibrium_reendow_of_isParetoOptimal`:
  **Second Fundamental Theorem of Welfare Economics** (quasi-equilibrium and full competitive
  equilibrium with lump-sum transfers).
* `Cslib.GameTheory.Market.LinearFisherMarket.IsEquilibrium.budget_mul_utility_le`,
  `Cslib.GameTheory.Market.LinearFisherMarket.IsEquilibrium.envyFree_of_budget_eq`,
  `Cslib.GameTheory.Market.LinearFisherMarket.IsEquilibrium.proportional_share`:
  budget-weighted envy-freeness, equal-budget envy-freeness, and proportional-share guarantees for
  linear Fisher equilibria.

## References

* [Arrow1951Welfare] (primary PDF unverified)
* [ArrowDebreu1954]
* [Varian1974] (primary PDF unverified)
* [Vazirani2007], Section 5.1–5.2, pp. 103–107
-/

public section

namespace Cslib.GameTheory.Market

open Finset
open scoped BigOperators

/-! ### Negative-orthant hyperplane separation -/

section Separation

variable {G : Type*}

/-- The open negative orthant `{z : G → ℝ | ∀ g, z g < 0}`. -/
def negOrthant (G : Type*) : Set (G → ℝ) :=
  {z | ∀ g : G, z g < 0}

@[simp] theorem mem_negOrthant {z : G → ℝ} :
    z ∈ negOrthant G ↔ ∀ g : G, z g < 0 := by rfl

theorem convex_negOrthant : Convex ℝ (negOrthant G) := by
  intro x hx y hy a b ha hb hab g
  rw [mem_negOrthant] at hx hy
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · have hb1 : b = 1 := by linarith
    simp [hb1, hy g]
  · have hax : a * x g < 0 := mul_neg_of_pos_of_neg ha_pos (hx g)
    have hby : b * y g ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb (hy g).le
    linarith

theorem isOpen_negOrthant [Finite G] : IsOpen (negOrthant G) := by
  have hrep : negOrthant G = ⋂ g : G, (fun z : G → ℝ => z g) ⁻¹' Set.Iio (0 : ℝ) := by
    ext z
    simp [mem_negOrthant]
  rw [hrep]
  exact isOpen_iInter_of_finite fun g => isOpen_Iio.preimage (continuous_apply g)

/-- Finite-dimensional separating price lemma: if `K ⊆ (G → ℝ)` is convex, nonempty, disjoint from
`negOrthant G`, and contains arbitrarily small vectors in `ℓ_∞` norm (`0 ∈ closure K`), then there
exists a nonzero nonnegative price vector `p : G → ℝ` such that `0 ≤ expenditure p z` for all
`z ∈ K`. -/
theorem exists_price_of_convex_disjoint_negOrthant [Fintype G]
    {K : Set (G → ℝ)} (hK_conv : Convex ℝ K) (hK_ne : K.Nonempty)
    (hdisj : Disjoint (negOrthant G) K)
    (hzero : ∀ ε : ℝ, 0 < ε → ∃ z ∈ K, ∀ g : G, |z g| < ε) :
    ∃ p : G → ℝ, (∀ g, 0 ≤ p g) ∧ (∃ g, 0 < p g) ∧ ∀ z ∈ K, 0 ≤ expenditure p z := by
  classical
  obtain ⟨f, u, hlt, hge⟩ :=
    geometric_hahn_banach_open convex_negOrthant isOpen_negOrthant hK_conv hdisj
  let p : G → ℝ := fun g => f (Pi.single g 1)
  have hf_eq : ∀ z : G → ℝ, f z = expenditure p z := by
    intro z
    have hz_sum : z = ∑ g : G, z g • Pi.single g (1 : ℝ) := by
      funext k
      simp [Pi.single_apply]
    conv_lhs => rw [hz_sum]
    rw [map_sum, expenditure_eq_sum]
    refine sum_congr rfl fun g _ => ?_
    rw [f.map_smul, smul_eq_mul, mul_comm]
  -- Step 1: `0 ≤ u` via small uniform negative vectors `fun _ => -ε ∈ negOrthant G`.
  have hu_nn : 0 ≤ u := by
    by_contra hu_neg; push Not at hu_neg
    set S : ℝ := ∑ g : G, |p g|
    have hS_nn : 0 ≤ S := sum_nonneg fun g _ => abs_nonneg _
    set ε : ℝ := (-u) / (2 * (1 + S))
    have hε_pos : 0 < ε := div_pos (neg_pos.2 hu_neg) (by positivity)
    have ha_lt : expenditure p (fun _ => -ε) < u := by
      simpa only [hf_eq] using hlt (fun _ => -ε) (fun _ => by simp [hε_pos])
    have ha_ge : -ε * S ≤ expenditure p (fun _ => -ε) := by
      simp only [expenditure_eq_sum, S, mul_sum]
      exact sum_le_sum fun g _ => by nlinarith [le_abs_self (p g)]
    have hεS_le : ε * S ≤ (-u) / 2 := by
      dsimp only [ε]; rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  -- Step 2: `∀ g, 0 ≤ p g` by scaling `-Pi.single g₀ 1` inside `negOrthant G`.
  have hp_nn : ∀ g : G, 0 ≤ p g := by
    intro g₀
    by_contra hpg_neg
    push Not at hpg_neg
    set S : ℝ := ∑ g : G, |p g|
    have hS_nn : 0 ≤ S := sum_nonneg fun g _ => abs_nonneg _
    set M : ℝ := (|u| + S + 1) / (-p g₀)
    have hM_pos : 0 < M := div_pos (by positivity) (neg_pos.2 hpg_neg)
    let a : G → ℝ := (fun _ => (-1 : ℝ)) - M • Pi.single g₀ 1
    have ha_mem : a ∈ negOrthant G := fun g => by
      simp only [a, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
        mul_zero]
      split_ifs <;> linarith
    have ha_lt : expenditure p a < u := by simpa only [hf_eq a] using hlt a ha_mem
    have ha_val : expenditure p a = -(∑ g : G, p g) - M * p g₀ := by
      rw [expenditure_sub, expenditure_smul_right]
      simp [expenditure_eq_sum, Pi.single_apply]
    have hM_mul : -M * p g₀ = |u| + S + 1 := by dsimp only [M]; field_simp [hpg_neg.ne]
    linarith [sum_le_sum fun g (_ : g ∈ univ) => le_abs_self (p g), le_abs_self u]
  -- Step 3: `∃ g, 0 < p g` since `p = 0` collapses `f` to `0`.
  have hp_pos : ∃ g : G, 0 < p g := by
    by_contra hall; push Not at hall
    have hp0 : ∀ g : G, p g = 0 := fun g => le_antisymm (hall g) (hp_nn g)
    obtain ⟨z₀, hz₀⟩ := hK_ne
    have h1 := hlt (fun _ => (-1 : ℝ)) (fun _ => by norm_num)
    have h2 := hge z₀ hz₀
    simp only [hf_eq, expenditure_eq_sum, hp0, zero_mul, sum_const_zero] at h1 h2
    linarith
  -- Step 4: `u ≤ 0` from `hzero`, hence `0 ≤ expenditure p z` on `K`.
  have hu_le : u ≤ 0 := by
    by_contra hu_pos; push Not at hu_pos
    obtain ⟨g₀, hpg₀⟩ := hp_pos
    set P : ℝ := ∑ g : G, p g
    have hP_pos : 0 < P := lt_of_lt_of_le hpg₀ (single_le_sum (fun g _ => hp_nn g) (mem_univ g₀))
    obtain ⟨z, hzK, hz_norm⟩ := hzero (u / (2 * P)) (by positivity)
    have hz_ge : u ≤ expenditure p z := by simpa only [hf_eq] using hge z hzK
    have hz_le : expenditure p z ≤ u / 2 := calc
      expenditure p z ≤ ∑ g : G, p g * (u / (2 * P)) := by
        rw [expenditure_eq_sum]
        exact sum_le_sum fun g _ => mul_le_mul_of_nonneg_left
          ((le_abs_self (z g)).trans (hz_norm g).le) (hp_nn g)
      _ = u / 2 := by rw [← sum_mul, show ∑ g, p g = P from rfl]; field_simp [hP_pos.ne']
    linarith
  refine ⟨p, hp_nn, hp_pos, fun z hz => ?_⟩
  simpa only [le_antisymm hu_le hu_nn, hf_eq z] using hge z hz

end Separation

/-! ### Convex preferences, strict finite Jensen, and consumer quasi-demand -/

section ConsumerWelfare

variable {G : Type*}

/-- A utility function `u : (G → ℝ) → ℝ` has **convex preferences** on `ℝ_+^G` if for every
nonnegative bundle `x`, the strictly preferred upper contour set
`{b : G → ℝ | (∀ g, 0 ≤ b g) ∧ u x < u b}` is convex. -/
@[expose] def HasConvexPreferences (u : (G → ℝ) → ℝ) : Prop :=
  ∀ ⦃x : G → ℝ⦄, (∀ g, 0 ≤ x g) → Convex ℝ {b : G → ℝ | (∀ g, 0 ≤ b g) ∧ u x < u b}

theorem HasConvexPreferences.of_quasiconcaveOn {u : (G → ℝ) → ℝ}
    (hq : QuasiconcaveOn ℝ {b : G → ℝ | ∀ g, 0 ≤ b g} u) :
    HasConvexPreferences u := by
  intro x _ b₁ hb₁ b₂ hb₂ a c ha hc hac
  have hnn : ∀ g, 0 ≤ (a • b₁ + c • b₂) g := fun g =>
    add_nonneg (mul_nonneg ha (hb₁.1 g)) (mul_nonneg hc (hb₂.1 g))
  refine ⟨hnn, ?_⟩
  set r := min (u b₁) (u b₂)
  have hr_gt : u x < r := lt_min hb₁.2 hb₂.2
  have hcomb := hq r ⟨hb₁.1, min_le_left _ _⟩ ⟨hb₂.1, min_le_right _ _⟩ ha hc hac
  exact lt_of_lt_of_le hr_gt hcomb.2

theorem HasConvexPreferences.of_concaveOn {u : (G → ℝ) → ℝ}
    (hc : ConcaveOn ℝ {b : G → ℝ | ∀ g, 0 ≤ b g} u) :
    HasConvexPreferences u := by
  intro x _ b₁ hb₁ b₂ hb₂ a c ha hcc hac
  have hcomb := hc.2 hb₁.1 hb₂.1 ha hcc hac
  refine ⟨hc.1 hb₁.1 hb₂.1 ha hcc hac, ?_⟩
  simp only [smul_eq_mul] at hcomb
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · have hc1 : c = 1 := by linarith
    subst hc1
    linarith [hb₂.2, hcomb]
  · have : u x = a * u x + c * u x := by
      calc
        u x = (a + c) * u x := by rw [hac, one_mul]
        _ = a * u x + c * u x := add_mul a c (u x)
    have h1 : a * u x < a * u b₁ := mul_lt_mul_of_pos_left hb₁.2 ha_pos
    have h2 : c * u x ≤ c * u b₂ := mul_le_mul_of_nonneg_left hb₂.2.le hcc
    linarith

theorem hasConvexPreferences_linearUtility [Fintype G] (v : G → ℝ) :
    HasConvexPreferences (linearUtility v) := by
  refine HasConvexPreferences.of_concaveOn ⟨?_, fun x _ y _ a b _ _ _ => ?_⟩
  · intro x hx y hy a b ha hb _ g
    exact add_nonneg (mul_nonneg ha (hx g)) (mul_nonneg hb (hy g))
  · simp only [linearUtility_eq_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
      sum_add_distrib, mul_sum]
    refine le_of_eq (congrArg₂ (· + ·)
      (sum_congr rfl fun g _ => by ring)
      (sum_congr rfl fun g _ => by ring))

/-- **Strict finite Jensen inequality** on `ℝ_+^G` for `StrictConcaveOn`: if `u` is strictly
concave on `ℝ_+^G`, `w` assigns strictly positive weights on `S` summing to `1`, and `f` takes at
least two distinct values on `S`, then `∑ c ∈ S, w c * u (f c) < u (∑ c ∈ S, w c • f c)`. -/
theorem StrictConcaveOn.sum_mul_lt_of_ne {ι : Type*} {u : (G → ℝ) → ℝ}
    (hsc : StrictConcaveOn ℝ {b : G → ℝ | ∀ g, 0 ≤ b g} u)
    {S : Finset ι} {w : ι → ℝ} {f : ι → G → ℝ}
    (hw_pos : ∀ c ∈ S, 0 < w c) (hw_sum : ∑ c ∈ S, w c = 1)
    (hf_nn : ∀ c ∈ S, ∀ g, 0 ≤ f c g)
    (hne : ∃ c₁ ∈ S, ∃ c₂ ∈ S, f c₁ ≠ f c₂) :
    ∑ c ∈ S, w c * u (f c) < u (∑ c ∈ S, w c • f c) := by
  classical
  have hconc : ConcaveOn ℝ {b : G → ℝ | ∀ g, 0 ≤ b g} u := hsc.concaveOn
  induction S using Finset.strongInduction generalizing w with
  | H S ih =>
    obtain ⟨c₁, hc₁, c₂, hc₂, hne₁₂⟩ := hne
    have hc₁_ne_c₂ : c₂ ≠ c₁ := fun h => hne₁₂ (congrArg f h.symm)
    set T := S.erase c₁
    have hc₂_T : c₂ ∈ T := mem_erase.2 ⟨hc₁_ne_c₂, hc₂⟩
    have hW_split : w c₁ + ∑ c ∈ T, w c = 1 := by
      rw [← hw_sum]
      exact add_sum_erase S w hc₁
    set WT := ∑ c ∈ T, w c
    have hWT_pos : 0 < WT :=
      lt_of_lt_of_le (hw_pos c₂ hc₂)
        (single_le_sum (fun c hc => (hw_pos c (mem_of_mem_erase hc)).le) hc₂_T)
    let wT : ι → ℝ := fun c => w c / WT
    have hwT_pos : ∀ c ∈ T, 0 < wT c := fun c hc =>
      div_pos (hw_pos c (mem_of_mem_erase hc)) hWT_pos
    have hwT_sum : ∑ c ∈ T, wT c = 1 := by
      dsimp only [wT]
      rw [← sum_div]
      exact div_self hWT_pos.ne'
    let rest : G → ℝ := ∑ c ∈ T, wT c • f c
    have hrest_nn : ∀ g, 0 ≤ rest g := fun g => by
      simp only [rest, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact sum_nonneg fun c hc => mul_nonneg (hwT_pos c hc).le (hf_nn c (mem_of_mem_erase hc) g)
    have havg_eq : ∑ c ∈ S, w c • f c = w c₁ • f c₁ + WT • rest := by
      rw [← add_sum_erase S (fun c => w c • f c) hc₁]
      congr 1
      simp only [rest, Finset.smul_sum, smul_smul, wT]
      refine sum_congr rfl fun c _ => ?_
      rw [mul_div_cancel₀ _ hWT_pos.ne']
    have hval_split : ∑ c ∈ S, w c * u (f c) =
        w c₁ * u (f c₁) + WT * ∑ c ∈ T, wT c * u (f c) := by
      rw [← add_sum_erase S (fun c => w c * u (f c)) hc₁, mul_sum]
      congr 1
      refine sum_congr rfl fun c _ => ?_
      dsimp only [wT]
      field_simp [hWT_pos.ne']
    have hrest_jensen : ∑ c ∈ T, wT c * u (f c) ≤ u rest := by
      simpa only [smul_eq_mul] using
        hconc.le_map_sum (fun c hc => (hwT_pos c hc).le) hwT_sum
          (fun c hc => hf_nn c (mem_of_mem_erase hc))
    rw [havg_eq, hval_split]
    by_cases heq_rest : f c₁ = rest
    · -- Since `f c₂ ≠ f c₁ = rest`, `f` cannot be constant on `T`.
      have hT_nonconst : ∃ d₁ ∈ T, ∃ d₂ ∈ T, f d₁ ≠ f d₂ := by
        by_contra hall_eq
        push Not at hall_eq
        have hrest_eq_c2 : rest = f c₂ := by
          have hcongr : ∑ c ∈ T, wT c • f c = ∑ c ∈ T, wT c • f c₂ :=
            sum_congr rfl fun c hc => by rw [hall_eq c hc c₂ hc₂_T]
          dsimp only [rest]
          rw [hcongr, ← sum_smul, hwT_sum, one_smul]
        exact hne₁₂ (heq_rest.trans hrest_eq_c2)
      have hT_strict : ∑ c ∈ T, wT c * u (f c) < u rest :=
        ih T (erase_ssubset hc₁) hwT_pos hwT_sum
          (fun c hc => hf_nn c (mem_of_mem_erase hc)) hT_nonconst
      have hcomb := hconc.2 (hf_nn c₁ hc₁) hrest_nn (hw_pos c₁ hc₁).le hWT_pos.le hW_split
      simp only [smul_eq_mul] at hcomb
      have : WT * ∑ c ∈ T, wT c * u (f c) < WT * u rest :=
        mul_lt_mul_of_pos_left hT_strict hWT_pos
      linarith
    · have hstrict2 := hsc.2 (hf_nn c₁ hc₁) hrest_nn heq_rest (hw_pos c₁ hc₁) hWT_pos hW_split
      simp only [smul_eq_mul] at hstrict2
      have : WT * ∑ c ∈ T, wT c * u (f c) ≤ WT * u rest :=
        mul_le_mul_of_nonneg_left hrest_jensen hWT_pos.le
      linarith

variable [Fintype G]

/-- Bundle `x` is a **quasi-demand** of a consumer with utility `u` and budget `m` at prices `p` if
`x` is budget-feasible and every strictly preferred nonnegative bundle costs at least `m`. -/
@[expose] def IsQuasiDemand (u : (G → ℝ) → ℝ) (p : G → ℝ) (m : ℝ) (x : G → ℝ) : Prop :=
  IsBudgetFeasible p m x ∧ ∀ b : G → ℝ, (∀ g, 0 ≤ b g) → u x < u b → m ≤ expenditure p b

theorem IsQuasiDemand.of_mem_demandSet {u : (G → ℝ) → ℝ} {p : G → ℝ} {m : ℝ} {x : G → ℝ}
    (hx : x ∈ demandSet u p m) : IsQuasiDemand u p m x := by
  rw [mem_demandSet] at hx
  exact ⟨hx.1, fun b hb hub => (lt_expenditure_of_mem_demandSet
    ((mem_demandSet).2 hx) hb hub).le⟩

/-- Under local nonsatiation and nonnegative prices `p`, every nonnegative bundle `x` admits a
strictly preferred nonnegative bundle whose expenditure is strictly less than `expenditure p x + δ`
for any `δ > 0`. -/
theorem IsLocallyNonsatiated.exists_lt_expenditure_lt {u : (G → ℝ) → ℝ}
    (hlns : IsLocallyNonsatiated u) {p x : G → ℝ} (hp : ∀ g, 0 ≤ p g) (hx : ∀ g, 0 ≤ x g)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ b : G → ℝ, (∀ g, 0 ≤ b g) ∧ u x < u b ∧ expenditure p b < expenditure p x + δ := by
  set S : ℝ := ∑ g : G, p g
  have hS_nn : 0 ≤ S := sum_nonneg fun g _ => hp g
  obtain ⟨b, hb_nn, hb_dist, hub⟩ := hlns x hx (δ / (2 * (1 + S))) (by positivity)
  refine ⟨b, hb_nn, hub, ?_⟩
  have hdiff : expenditure p b - expenditure p x ≤ δ / 2 := by
    calc
      expenditure p b - expenditure p x = ∑ g : G, p g * (b g - x g) := by
        rw [← expenditure_sub, expenditure_eq_sum]
        rfl
      _ ≤ ∑ g : G, p g * (δ / (2 * (1 + S))) :=
        sum_le_sum fun g _ => mul_le_mul_of_nonneg_left
          ((le_abs_self _).trans (hb_dist g).le) (hp g)
      _ = S * (δ / (2 * (1 + S))) := by rw [← sum_mul]
      _ ≤ δ / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
  linarith

/-- Under local nonsatiation, a quasi-demand bundle exhausts the consumer's budget
(`expenditure p x = m`). -/
theorem IsLocallyNonsatiated.expenditure_eq_of_isQuasiDemand {u : (G → ℝ) → ℝ}
    (hlns : IsLocallyNonsatiated u) {p : G → ℝ} (hp : ∀ g, 0 ≤ p g) {m : ℝ} {x : G → ℝ}
    (hq : IsQuasiDemand u p m x) : expenditure p x = m := by
  refine le_antisymm hq.1.2 ?_
  by_contra hlt
  obtain ⟨b, hb_nn, hub, hb_exp⟩ :=
    hlns.exists_lt_expenditure_lt hp hq.1.1 (sub_pos.2 (not_le.1 hlt))
  linarith [hq.2 b hb_nn hub]

/-- **Cheaper-point upgrade (`IsQuasiDemand` → `demandSet`):** if `u` is continuous on `ℝ_+^G`,
prices are nonnegative, and budget `m` is strictly positive (`0 < m`, so `0 ∈ ℝ_+^G` is strictly
cheaper than `m`), then any quasi-demand bundle `x` is an exact Marshallian demand bundle
`x ∈ demandSet u p m`. -/
theorem IsQuasiDemand.mem_demandSet_of_budget_pos {u : (G → ℝ) → ℝ} {p : G → ℝ} {m : ℝ}
    {x : G → ℝ} (hq : IsQuasiDemand u p m x) (hp : ∀ g, 0 ≤ p g) (hm : 0 < m)
    (hcont : ContinuousOn u {b : G → ℝ | ∀ g, 0 ≤ b g}) :
    x ∈ demandSet u p m := by
  rw [mem_demandSet]
  refine ⟨hq.1, fun b hb => ?_⟩
  by_contra hlt; push Not at hlt
  have hcw : ContinuousWithinAt (fun c : ℝ => u (c • b)) (Set.Ici 0) 1 :=
    (hcont.comp (continuous_id.smul continuous_const).continuousOn
      fun c hc g => mul_nonneg hc (hb.1 g)).continuousWithinAt (by norm_num)
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    Metric.continuousWithinAt_iff.1 hcw ((u b - u x) / 2) (by linarith)
  set c : ℝ := max (1 / 2) (1 - δ / 2)
  have hc_pos : 0 < c := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hc_lt_1 : c < 1 := max_lt (by norm_num) (by linarith)
  have hclose := hδ hc_pos.le (by
    rw [Real.dist_eq, abs_of_neg (sub_neg.2 hc_lt_1)]; linarith [le_max_right (1 / 2) (1 - δ / 2)])
  rw [one_smul, Real.dist_eq] at hclose
  have hm_le : m ≤ c * expenditure p b := by
    rw [← expenditure_smul_right]
    exact hq.2 (c • b) (fun g => mul_nonneg hc_pos.le (hb.1 g)) (by linarith [(abs_lt.1 hclose).1])
  have _ := expenditure_nonneg hp hb.1
  linarith [mul_le_mul_of_nonneg_left hb.2 hc_pos.le, mul_lt_mul_of_pos_right hc_lt_1 hm]

end ConsumerWelfare

/-! ### Price quasi-equilibria and the Second Fundamental Theorem of Welfare Economics -/

namespace ExchangeMarket

section SecondWelfare

variable {I G : Type*} [Fintype I] [Fintype G]

/-- Lump-sum endowment redistribution supporting allocation `x`: replaces initial endowments with
`x` while preserving traders' utility functions. -/
def reendow (E : ExchangeMarket I G) (x : I → G → ℝ)
    (hx : ∀ (i : I) (g : G), 0 ≤ x i g) : ExchangeMarket I G where
  endowment := x
  utility := E.utility
  endowment_nonneg := hx

omit [Fintype G] in
theorem IsParetoOptimal.nonneg {E : ExchangeMarket I G} {x : I → G → ℝ}
    (hpo : E.IsParetoOptimal x) (i : I) (g : G) : 0 ≤ x i g :=
  hpo.1.1 i g

/-- At any nonnegative price vector `p`, aggregate expenditure under a feasible allocation `x` is
at most the market value of total supply. -/
theorem IsFeasibleAllocation.sum_expenditure_le_totalSupply
    {E : ExchangeMarket I G} {x : I → G → ℝ} {p : G → ℝ}
    (hx : E.IsFeasibleAllocation x) (hp : ∀ g, 0 ≤ p g) :
    ∑ i : I, expenditure p (x i) ≤ expenditure p E.totalSupply := by
  calc
    ∑ i : I, expenditure p (x i) = ∑ g : G, p g * ∑ i : I, x i g := by
      simp only [expenditure_eq_sum, mul_sum]
      exact sum_comm
    _ ≤ ∑ g : G, p g * E.totalSupply g :=
      sum_le_sum fun g _ => mul_le_mul_of_nonneg_left (hx.2 g) (hp g)
    _ = expenditure p E.totalSupply := (expenditure_eq_sum p E.totalSupply).symm

/-- For any feasible allocation `x` and nonnegative price vector `p`, zero aggregate excess-demand
value `expenditure p (E.excessDemand x) = 0` forces pointwise complementary slackness
`p g * E.excessDemand x g = 0` for every good `g`. -/
theorem IsFeasibleAllocation.price_mul_excessDemand_eq_zero
    {E : ExchangeMarket I G} {x : I → G → ℝ} {p : G → ℝ}
    (hx : E.IsFeasibleAllocation x) (hp : ∀ g, 0 ≤ p g)
    (hex0 : expenditure p (E.excessDemand x) = 0) (g : G) :
    p g * E.excessDemand x g = 0 := by
  classical
  rw [expenditure_eq_sum] at hex0
  have hnonpos : ∀ k ∈ (univ : Finset G), p k * E.excessDemand x k ≤ 0 := fun k _ => by
    rw [E.excessDemand_eq]
    exact mul_nonpos_of_nonneg_of_nonpos (hp k) (sub_nonpos.2 (hx.2 k))
  have hrest : ∑ k ∈ univ.erase g, p k * E.excessDemand x k ≤ 0 :=
    sum_nonpos fun k hk => hnonpos k (mem_of_mem_erase hk)
  have hsplit := add_sum_erase univ (fun k => p k * E.excessDemand x k) (mem_univ g)
  linarith [hnonpos g (mem_univ g)]

omit [Fintype G] in
/-- Under local nonsatiation, every feasible allocation `x` of a nonempty market can be perturbed
to a nonnegative profile `y` strictly preferred by every trader whose aggregate excess over
`E.totalSupply g` is at most any prescribed `δ > 0`. -/
theorem IsFeasibleAllocation.exists_forall_utility_lt_sum_sub_totalSupply_le [Nonempty I]
    {E : ExchangeMarket I G} {x : I → G → ℝ} (hx : E.IsFeasibleAllocation x)
    (hlns : ∀ i, IsLocallyNonsatiated (E.utility i)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ y : I → G → ℝ, (∀ i g, 0 ≤ y i g) ∧ (∀ i, E.utility i (x i) < E.utility i (y i)) ∧
      ∀ g : G, (∑ i : I, y i g) - E.totalSupply g ≤ δ := by
  set m : ℝ := (Fintype.card I : ℝ)
  have hm_pos : 0 < m := Nat.cast_pos.2 Fintype.card_pos
  choose y hy_nn hy_dist hy_gt using fun i =>
    hlns i (x i) (hx.1 i) (δ / m) (div_pos hδ hm_pos)
  refine ⟨y, hy_nn, hy_gt, fun g => ?_⟩
  have hsum_diff : (∑ i : I, y i g) - ∑ i : I, x i g ≤ δ := by
    rw [← sum_sub_distrib]
    calc
      ∑ i : I, (y i g - x i g) ≤ ∑ _i : I, (δ / m) :=
        sum_le_sum fun i _ => (le_abs_self _).trans (hy_dist i g).le
      _ = m * (δ / m) := by simp [m]
      _ = δ := mul_div_cancel₀ δ hm_pos.ne'
  linarith [hx.2 g]

omit [Fintype I] [Fintype G] in
@[simp] theorem reendow_endowment (E : ExchangeMarket I G) (x : I → G → ℝ)
    (hx : ∀ i g, 0 ≤ x i g) : (E.reendow x hx).endowment = x := by rfl

omit [Fintype I] [Fintype G] in
@[simp] theorem reendow_utility (E : ExchangeMarket I G) (x : I → G → ℝ)
    (hx : ∀ i g, 0 ≤ x i g) : (E.reendow x hx).utility = E.utility := by rfl

omit [Fintype I] in
@[simp] theorem reendow_income (E : ExchangeMarket I G) (x : I → G → ℝ)
    (hx : ∀ i g, 0 ≤ x i g) (p : G → ℝ) (i : I) :
    (E.reendow x hx).income p i = expenditure p (x i) := by
  rw [income_eq, reendow_endowment]

omit [Fintype G] in
@[simp] theorem reendow_excessDemand (E : ExchangeMarket I G) (x : I → G → ℝ)
    (hx : ∀ i g, 0 ≤ x i g) : (E.reendow x hx).excessDemand x = 0 := by
  funext g
  simp [excessDemand_eq, totalSupply_eq_sum]

/-- A **price quasi-equilibrium** `(x, p)` of exchange market `E` ([Arrow1951Welfare];
[ArrowDebreu1954]): a nonzero nonnegative price vector `p` and allocation `x` such that every
trader `i`'s bundle is a quasi-demand within `E.income p i`, no good is over-demanded, and any good
in strict excess supply has price zero. -/
@[expose] def IsPriceQuasiEquilibrium (E : ExchangeMarket I G) (x : I → G → ℝ) (p : G → ℝ) :
    Prop :=
  (∀ g, 0 ≤ p g) ∧ (∃ g, 0 < p g) ∧
    (∀ i, IsQuasiDemand (E.utility i) p (E.income p i) (x i)) ∧
    (∀ g, E.excessDemand x g ≤ 0) ∧ ∀ g, p g * E.excessDemand x g = 0

theorem IsPriceQuasiEquilibrium.of_isCompetitiveEquilibrium {E : ExchangeMarket I G}
    {x : I → G → ℝ} {p : G → ℝ} (heq : E.IsCompetitiveEquilibrium x p)
    (hp_nz : ∃ g, 0 < p g) : E.IsPriceQuasiEquilibrium x p :=
  ⟨heq.1, hp_nz, fun i => IsQuasiDemand.of_mem_demandSet ((E.mem_demandSet).1 (heq.2.1 i)),
    heq.2.2.1, heq.2.2.2⟩

/-- When utilities are continuous on `ℝ_+^G` and every trader has strictly positive income
`0 < E.income p i`, any price quasi-equilibrium `(x, p)` is a full competitive equilibrium. -/
theorem IsPriceQuasiEquilibrium.isCompetitiveEquilibrium_of_income_pos {E : ExchangeMarket I G}
    {x : I → G → ℝ} {p : G → ℝ} (hq : E.IsPriceQuasiEquilibrium x p)
    (hcont : ∀ i, ContinuousOn (E.utility i) {b : G → ℝ | ∀ g, 0 ≤ b g})
    (hinc : ∀ i, 0 < E.income p i) :
    E.IsCompetitiveEquilibrium x p := by
  refine ⟨hq.1, fun i => ?_, hq.2.2.2.1, hq.2.2.2.2⟩
  rw [E.mem_demandSet]
  exact (hq.2.2.1 i).mem_demandSet_of_budget_pos hq.1 (hinc i) (hcont i)

omit [Fintype I] in
private theorem exists_forall_lt_sum_expenditure_sub_le [Finite I] [Nonempty I]
    {u : I → (G → ℝ) → ℝ} (hlns : ∀ i, IsLocallyNonsatiated (u i))
    {p : G → ℝ} (hp : ∀ g, 0 ≤ p g) {x : I → G → ℝ} (hx : ∀ i g, 0 ≤ x i g)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ y : I → G → ℝ, (∀ i g, 0 ≤ y i g) ∧ (∀ i, u i (x i) < u i (y i)) ∧
      ∀ S : Finset I, ∑ i ∈ S, (expenditure p (y i) - expenditure p (x i)) ≤ δ := by
  have := Fintype.ofFinite I
  set m : ℝ := (Fintype.card I : ℝ)
  have hm_pos : 0 < m := Nat.cast_pos.2 Fintype.card_pos
  choose y hy_nn hy_gt hy_exp using fun i =>
    (hlns i).exists_lt_expenditure_lt hp (hx i) (div_pos hδ hm_pos)
  refine ⟨y, hy_nn, hy_gt, fun S => ?_⟩
  calc
    ∑ i ∈ S, (expenditure p (y i) - expenditure p (x i))
      ≤ ∑ _i ∈ S, (δ / m) := sum_le_sum fun i _ => by linarith [hy_exp i]
    _ ≤ ∑ _i : I, (δ / m) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ S) fun _ _ _ => (div_pos hδ hm_pos).le
    _ = m * (δ / m) := by simp [m]
    _ = δ := mul_div_cancel₀ δ hm_pos.ne'

/-- **Second Fundamental Theorem of Welfare Economics (price quasi-equilibrium form)**
([Arrow1951Welfare]; [ArrowDebreu1954]): in a locally nonsatiated exchange economy with a nonempty
finite trader set and convex preferences (`HasConvexPreferences`), every Pareto-optimal
allocation `x` admits a nonzero nonnegative price vector `p` supporting `(x, p)` as a price
quasi-equilibrium of `E.reendow x` and satisfying complementary slackness `p g * E.excessDemand x g
= 0` against `E.totalSupply`. -/
theorem exists_priceQuasiEquilibrium_reendow_of_isParetoOptimal [Nonempty I]
    (E : ExchangeMarket I G)
    (hlns : ∀ i, IsLocallyNonsatiated (E.utility i))
    (hconv : ∀ i, HasConvexPreferences (E.utility i))
    {x : I → G → ℝ} (hpo : E.IsParetoOptimal x) :
    ∃ p : G → ℝ,
      (E.reendow x hpo.nonneg).IsPriceQuasiEquilibrium x p ∧
        ∀ g : G, p g * E.excessDemand x g = 0 := by
  classical
  -- Aggregate strictly-preferred net-excess set with free disposal relative to `E.totalSupply`.
  let K : Set (G → ℝ) :=
    {z | ∃ y : I → G → ℝ, (∀ i g, 0 ≤ y i g) ∧ (∀ i, E.utility i (x i) < E.utility i (y i)) ∧
      ∀ g, (∑ i : I, y i g) - E.totalSupply g ≤ z g}
  have hK_conv : Convex ℝ K := by
    rintro z₁ ⟨y₁, hy₁_nn, hy₁_gt, hz₁⟩ z₂ ⟨y₂, hy₂_nn, hy₂_gt, hz₂⟩ a b ha hb hab
    refine ⟨fun i => a • y₁ i + b • y₂ i, ?_, ?_, fun g => ?_⟩
    · intro i g
      exact add_nonneg (mul_nonneg ha (hy₁_nn i g)) (mul_nonneg hb (hy₂_nn i g))
    · intro i
      exact (hconv i (hpo.1.1 i) ⟨hy₁_nn i, hy₁_gt i⟩ ⟨hy₂_nn i, hy₂_gt i⟩ ha hb hab).2
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum]
      have h1 := hz₁ g
      have h2 := hz₂ g
      have hW : E.totalSupply g = (a + b) * E.totalSupply g := by rw [hab, one_mul]
      nlinarith
  have hK_ne : K.Nonempty := by
    obtain ⟨y, hy_nn, hy_gt, -⟩ :=
      hpo.1.exists_forall_utility_lt_sum_sub_totalSupply_le hlns zero_lt_one
    exact ⟨fun g => (∑ i : I, y i g) - E.totalSupply g, y, hy_nn, hy_gt, fun _ => le_rfl⟩
  have hdisj : Disjoint (negOrthant G) K := by
    rw [Set.disjoint_left]
    rintro z hz_neg ⟨y, hy_nn, hy_gt, hz_le⟩
    rw [mem_negOrthant] at hz_neg
    obtain ⟨i₀⟩ := ‹Nonempty I›
    exact hpo.2 ⟨y, ⟨hy_nn, fun g => by linarith [hz_le g, hz_neg g]⟩,
      fun i => (hy_gt i).le, ⟨i₀, hy_gt i₀⟩⟩
  have hzero : ∀ ε : ℝ, 0 < ε → ∃ z ∈ K, ∀ g : G, |z g| < ε := fun ε hε => by
    obtain ⟨y, hy_nn, hy_gt, hy_le⟩ :=
      hpo.1.exists_forall_utility_lt_sum_sub_totalSupply_le hlns (half_pos hε)
    refine ⟨fun g => max ((∑ i : I, y i g) - E.totalSupply g) 0,
      ⟨y, hy_nn, hy_gt, fun g => le_max_left _ _⟩, fun g => ?_⟩
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_lt ((hy_le g).trans_lt (half_lt_self hε)) hε
  obtain ⟨p, hp_nn, hp_pos, hsep⟩ :=
    exists_price_of_convex_disjoint_negOrthant hK_conv hK_ne hdisj hzero
  have hexp_excess : ∀ y : I → G → ℝ,
      expenditure p (fun g => (∑ i : I, y i g) - E.totalSupply g) =
        (∑ i : I, expenditure p (y i)) - expenditure p E.totalSupply := fun y => by
    simp only [expenditure_eq_sum, mul_sub, sum_sub_distrib, mul_sum]
    rw [sum_comm]
  -- Approximate `x` via `exists_forall_lt_sum_expenditure_sub_le` to extract supply-value
  -- exhaustion and individual quasi-demands.
  have hsum_ge : expenditure p E.totalSupply ≤ ∑ i : I, expenditure p (x i) := by
    by_contra hlt
    obtain ⟨y, hy_nn, hy_gt, hy_sum⟩ :=
      exists_forall_lt_sum_expenditure_sub_le hlns hp_nn hpo.1.1
        (half_pos (sub_pos.2 (not_le.1 hlt)))
    have hge0 := hsep _ ⟨y, hy_nn, hy_gt, fun _ => le_rfl⟩
    have hsub := hy_sum univ
    rw [hexp_excess] at hge0
    rw [sum_sub_distrib] at hsub
    linarith
  have hsum_eq : ∑ i : I, expenditure p (x i) = expenditure p E.totalSupply :=
    le_antisymm (hpo.1.sum_expenditure_le_totalSupply hp_nn) hsum_ge
  have hex0 : expenditure p (E.excessDemand x) = 0 := by
    rw [show E.excessDemand x = fun g => (∑ i : I, x i g) - E.totalSupply g from
      funext (E.excessDemand_eq x), hexp_excess, hsum_eq, sub_self]
  have hcs : ∀ g : G, p g * E.excessDemand x g = 0 :=
    hpo.1.price_mul_excessDemand_eq_zero hp_nn hex0
  have hquasi : ∀ i : I, IsQuasiDemand (E.utility i) p (expenditure p (x i)) (x i) := by
    intro i
    refine ⟨⟨hpo.1.1 i, le_rfl⟩, fun b hb_nn hub => ?_⟩
    by_contra hlt
    obtain ⟨yNear, hyNear_nn, hyNear_gt, hyNear_sum⟩ :=
      exists_forall_lt_sum_expenditure_sub_le hlns hp_nn hpo.1.1
        (half_pos (sub_pos.2 (not_le.1 hlt)))
    let y : I → G → ℝ := Function.update yNear i b
    have hy_nn : ∀ j g, 0 ≤ y j g := fun j g => by
      by_cases hj : j = i
      · subst hj; simp [y, hb_nn g]
      · simp [y, hj, hyNear_nn j g]
    have hy_gt : ∀ j, E.utility j (x j) < E.utility j (y j) := fun j => by
      by_cases hj : j = i
      · subst hj; simpa [y] using hub
      · simpa [y, hj] using hyNear_gt j
    have hge0 := hsep _ ⟨y, hy_nn, hy_gt, fun _ => le_rfl⟩
    rw [hexp_excess, ← hsum_eq] at hge0
    have htot_diff : (∑ j : I, expenditure p (y j)) - ∑ j : I, expenditure p (x j) =
        (expenditure p b - expenditure p (x i)) +
          ∑ j ∈ univ.erase i, (expenditure p (yNear j) - expenditure p (x j)) := by
      rw [← sum_sub_distrib, ← add_sum_erase univ _ (mem_univ i)]
      simp only [y, Function.update_self]
      congr 1
      refine sum_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (mem_erase.1 hj).1]
    linarith [hyNear_sum (univ.erase i)]
  refine ⟨p, ⟨hp_nn, hp_pos, fun i => ?_, fun g => ?_, fun g => ?_⟩, hcs⟩
  · simpa only [reendow_utility, reendow_income] using hquasi i
  · simp [reendow_excessDemand]
  · simp [reendow_excessDemand]

/-- **Second Fundamental Theorem of Welfare Economics (full competitive equilibrium with lump-sum
transfers)** ([Arrow1951Welfare]; [ArrowDebreu1954]): if utilities are locally nonsatiated,
continuous on `ℝ_+^G`, and have convex preferences, then every strictly positive Pareto-optimal
allocation `x` (`∀ i g, 0 < x i g`) is supported by a nonzero nonnegative price vector `p` as a
full competitive equilibrium of `E.reendow x`. -/
theorem exists_isCompetitiveEquilibrium_reendow_of_isParetoOptimal [Nonempty I]
    (E : ExchangeMarket I G)
    (hlns : ∀ i, IsLocallyNonsatiated (E.utility i))
    (hconv : ∀ i, HasConvexPreferences (E.utility i))
    (hcont : ∀ i, ContinuousOn (E.utility i) {b : G → ℝ | ∀ g, 0 ≤ b g})
    {x : I → G → ℝ} (hpo : E.IsParetoOptimal x)
    (hx_pos : ∀ (i : I) (g : G), 0 < x i g) :
    ∃ p : G → ℝ, (∃ g, 0 < p g) ∧
      (E.reendow x hpo.nonneg).IsCompetitiveEquilibrium x p ∧
      ∀ g : G, p g * E.excessDemand x g = 0 := by
  obtain ⟨p, hquasi, hcs⟩ :=
    E.exists_priceQuasiEquilibrium_reendow_of_isParetoOptimal hlns hconv hpo
  obtain ⟨g₀, hpg₀⟩ := hquasi.2.1
  refine ⟨p, ⟨g₀, hpg₀⟩, hquasi.isCompetitiveEquilibrium_of_income_pos
    (fun i => by simpa only [reendow_utility] using hcont i) fun i => ?_, hcs⟩
  rw [reendow_income, expenditure_eq_sum]
  exact lt_of_lt_of_le (mul_pos hpg₀ (hx_pos i g₀))
    (single_le_sum (fun g _ => mul_nonneg (hquasi.1 g) (hpo.1.1 i g)) (mem_univ g₀))

end SecondWelfare

end ExchangeMarket

/-! ### Budget-weighted envy-freeness and proportionality of Fisher market equilibria -/

section FisherFairness

variable {I G : Type*} [Fintype I] [Fintype G]

namespace FisherMarket

/-- **Proportional-share guarantee for general Fisher markets** ([Varian1974]): in any Fisher
market equilibrium `(x, p)` under local nonsatiation with `0 < M.totalBudget`, every buyer `i`
can afford their budget-share fraction `(M.budget i / M.totalBudget) • M.supply` of total market
supply, so `M.utility i ((M.budget i / M.totalBudget) • M.supply) ≤ M.utility i (x i)`. -/
theorem IsEquilibrium.utility_budgetShare_supply_le {M : FisherMarket I G}
    {x : I → G → ℝ} {p : G → ℝ} (heq : M.IsEquilibrium x p)
    (hlns : ∀ i, IsLocallyNonsatiated (M.utility i)) (hB : 0 < M.totalBudget) (i : I) :
    M.utility i ((M.budget i / M.totalBudget) • M.supply) ≤ M.utility i (x i) := by
  have hdem := (Market.mem_demandSet).1 ((M.mem_demandSet).1 (heq.2.1 i))
  refine hdem.2 _ ⟨fun g => mul_nonneg (div_nonneg (M.budget_nonneg i) hB.le) (M.supply_nonneg g),
    ?_⟩
  rw [expenditure_smul_right, heq.expenditure_supply_eq_totalBudget hlns,
    div_mul_cancel₀ _ hB.ne']

/-- **Equal-budget envy-freeness for general Fisher markets** ([Varian1974]): if buyers `i` and
`j` have `M.budget j ≤ M.budget i` and every buyer is locally nonsatiated, then at any Fisher
equilibrium `(x, p)`, buyer `i` weakly prefers their own bundle `x i` to `x j`
(`M.utility i (x j) ≤ M.utility i (x i)`). -/
theorem IsEquilibrium.utility_le_of_budget_le {M : FisherMarket I G}
    {x : I → G → ℝ} {p : G → ℝ} (heq : M.IsEquilibrium x p) {i j : I}
    (hbud : M.budget j ≤ M.budget i) :
    M.utility i (x j) ≤ M.utility i (x i) := by
  have hdem_i := (Market.mem_demandSet).1 ((M.mem_demandSet).1 (heq.2.1 i))
  have hdem_j := (Market.mem_demandSet).1 ((M.mem_demandSet).1 (heq.2.1 j))
  exact hdem_i.2 (x j) ⟨hdem_j.1.1, hdem_j.1.2.trans hbud⟩

end FisherMarket

namespace LinearFisherMarket

private theorem linearUtility_smul (v : G → ℝ) (c : ℝ) (z : G → ℝ) :
    linearUtility v (c • z) = c * linearUtility v z := by
  simp only [linearUtility_eq_sum, Pi.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun g _ => by ring

/-- **Budget-weighted envy-freeness of linear Fisher equilibria** ([Varian1974]; [Vazirani2007],
Section 5.2): at any equilibrium `(x, p)` of a linear Fisher market `M` where buyer `j` has
positive budget (or unconditionally via cross-multiplication `M.budget i * u_i(x_j) ≤ M.budget j *
u_i(x_i)`), no buyer envies another buyer on a per-dollar-of-budget basis. -/
theorem IsEquilibrium.budget_mul_utility_le {M : LinearFisherMarket I G}
    {x : I → G → ℝ} {p : G → ℝ} (heq : M.IsEquilibrium x p) (i j : I) :
    M.budget i * linearUtility (M.utility i) (x j) ≤ M.budget j * M.buyerUtility x i := by
  have hdem_i := (Market.mem_demandSet).1 ((M.toFisherMarket.mem_demandSet).1 (heq.2.1 i))
  have hdem_j := (Market.mem_demandSet).1 ((M.toFisherMarket.mem_demandSet).1 (heq.2.1 j))
  rw [M.toFisherMarket_utility, M.toFisherMarket_budget] at hdem_i hdem_j
  rw [M.buyerUtility_eq]
  rcases eq_or_lt_of_le (M.budget_nonneg j) with hbj0 | hbj_pos
  · rw [← hbj0, zero_mul]
    rcases eq_or_lt_of_le (M.budget_nonneg i) with hbi0 | _
    · rw [← hbi0, zero_mul]
    · -- Since `expenditure p (x j) = 0`, `x i + x j` is budget-feasible for buyer `i`.
      have hexp0 : expenditure p (x j) = 0 :=
        le_antisymm (by simpa [← hbj0] using hdem_j.1.2) (expenditure_nonneg heq.1 hdem_j.1.1)
      have hle := hdem_i.2 (x i + x j) ⟨fun g => add_nonneg (hdem_i.1.1 g) (hdem_j.1.1 g),
        by rw [expenditure_add, hexp0, add_zero]; exact hdem_i.1.2⟩
      simp only [linearUtility_eq_sum, Pi.add_apply, mul_add, sum_add_distrib] at hle ⊢
      have hnn : 0 ≤ ∑ g, M.utility i g * x j g :=
        sum_nonneg fun g _ => mul_nonneg (M.utility_nonneg i g) (hdem_j.1.1 g)
      nlinarith [M.budget_nonneg i]
  · have hopt := hdem_i.2 ((M.budget i / M.budget j) • x j)
      ⟨fun g => mul_nonneg (div_nonneg (M.budget_nonneg i) hbj_pos.le) (hdem_j.1.1 g), by
        rw [expenditure_smul_right]
        exact (mul_le_mul_of_nonneg_left hdem_j.1.2
          (div_nonneg (M.budget_nonneg i) hbj_pos.le)).trans_eq (div_mul_cancel₀ _ hbj_pos.ne')⟩
    rw [linearUtility_smul] at hopt
    have hmul := mul_le_mul_of_nonneg_left hopt hbj_pos.le
    have hcancel : M.budget j * ((M.budget i / M.budget j) * linearUtility (M.utility i) (x j)) =
        M.budget i * linearUtility (M.utility i) (x j) := by field_simp [hbj_pos.ne']
    linarith

/-- **Equal-budget envy-freeness of linear Fisher equilibria:** when `M.budget i = M.budget j`,
every linear Fisher equilibrium allocation is envy-free between `i` and `j`. -/
theorem IsEquilibrium.envyFree_of_budget_eq {M : LinearFisherMarket I G}
    {x : I → G → ℝ} {p : G → ℝ} (heq : M.IsEquilibrium x p) {i j : I}
    (hbud : M.budget i = M.budget j) :
    linearUtility (M.utility i) (x j) ≤ M.buyerUtility x i := by
  simpa only [M.toFisherMarket_utility, M.buyerUtility_eq] using
    FisherMarket.IsEquilibrium.utility_le_of_budget_le heq
      (show M.toFisherMarket.budget j ≤ M.toFisherMarket.budget i by simp [hbud])

/-- **Proportional-share guarantee for linear Fisher equilibria:** when every buyer desires at least
one good (`buyer_nonsatiated`) and `0 < ∑ k, M.budget k`, every buyer `i` achieves at least fraction
`M.budget i / ∑ k, M.budget k` of their utility for the entire market supply `M.supply`. -/
theorem IsEquilibrium.proportional_share {M : LinearFisherMarket I G}
    {x : I → G → ℝ} {p : G → ℝ} (heq : M.IsEquilibrium x p)
    (hns : ∀ i, ∃ g, 0 < M.utility i g)
    (hB : 0 < ∑ k : I, M.budget k) (i : I) :
    (M.budget i / ∑ k : I, M.budget k) * linearUtility (M.utility i) M.supply ≤
      M.buyerUtility x i := by
  have hB_eq : M.toFisherMarket.totalBudget = ∑ k : I, M.budget k := by
    simp [FisherMarket.totalBudget_eq_sum]
  have hlns : ∀ k, IsLocallyNonsatiated (M.toFisherMarket.utility k) := fun k => by
    rw [M.toFisherMarket_utility]; exact (isLocallyNonsatiated_linearUtility_iff _).2 (hns k)
  have h := FisherMarket.IsEquilibrium.utility_budgetShare_supply_le heq hlns (hB_eq.symm ▸ hB) i
  rwa [M.toFisherMarket_utility, M.toFisherMarket_budget, M.toFisherMarket_supply, hB_eq,
    ← M.buyerUtility_eq, linearUtility_smul] at h

end LinearFisherMarket

end FisherFairness

end Cslib.GameTheory.Market
