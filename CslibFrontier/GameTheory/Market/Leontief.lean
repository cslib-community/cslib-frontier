/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Bimatrix.Basic
public import CslibFrontier.GameTheory.Market.Basic
public import Mathlib.Analysis.Convex.Function
import CslibFrontier.Foundations.Analysis.Brouwer.Simplex
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Monoid

/-!
# Leontief exchange economies and correspondence with bimatrix Nash equilibria

In a **Leontief (fixed-proportions) utility function** ([CodenottiVaradarajan2007], Section 6.1.5,
p. 139 and Section 6.5.2, p. 152), a consumer desires goods in fixed nonnegative proportions
`f : G → ℝ`, obtaining utility `leontiefUtility f b = min_{g : f g > 0} (b g / f g)` (or `0` when
no good has positive proportion). At nonnegative prices `π` with positive unit-utility cost
`expenditure π f > 0` and budget `m ≥ 0`, every optimal bundle attains utility
`U* = m / expenditure π f`, allocates at least `U* * f g` to each desired good, and equals
`U* * f g` on every positively priced good (`mem_demandSet_leontiefUtility_iff`).

Following Codenotti, Saberi, Varadarajan, and Ye (2006) as presented in
[CodenottiVaradarajan2007], Section 6.5.2, p. 152, any bimatrix game `(A, B)` with strictly
positive `M × N` payoff matrices induces a bipartite Leontief exchange economy
`bimatrixLeontiefMarket` with traders and goods indexed by `M ⊕ N`:

* every trader `t : M ⊕ N` holds an initial endowment of one unit of good `t`;
* each trader `inl i` (`i : M`) desires goods `inr j` (`j : N`) in proportions given by row `i` of
  `B`;
* each trader `inr j` (`j : N`) desires goods `inl i` (`i : M`) in proportions given by column `j`
  of `A`.

Allowing nonnegative (not strictly positive) equilibrium prices—as required on p. 152—this module
establishes the exact **one-to-one correspondence**
(`bimatrixLeontiefNashEquivEquilibriumPrice`) between mixed Nash equilibria `(x, y)` of
`(A, B)` and normalized equilibrium price vectors `π : M ⊕ N → ℝ` (`∑ g, π g = 1`) of
`bimatrixLeontiefMarket`: equilibrium utilities `(U, V)` correspond via payoff scaling
`(U, V) = (v₂⁻¹ • x, v₁⁻¹ • y)` to Nash strategies, and each Nash support induces a strictly
positive column-stochastic bipartite price transfer whose unique stationary distribution (proved
via Brouwer's fixed-point theorem and strict `ℓ₁` contraction) determines `π` uniquely.

## Main definitions

* `Cslib.GameTheory.Market.leontiefUtility`: fixed-proportions Leontief utility
  `min_{g : 0 < f g} (b g / f g)`.
* `Cslib.GameTheory.Market.LeontiefExchangeMarket`: Arrow–Debreu exchange economy with Leontief
  utilities, bridged to `ExchangeMarket` via `toExchangeMarket`.
* `Cslib.GameTheory.Market.bimatrixLeontiefMarket`: the `(M ⊕ N)`-trader, `(M ⊕ N)`-good bipartite
  Leontief exchange economy encoding a strictly positive bimatrix game `G : BimatrixGame M N`
  ([CodenottiVaradarajan2007], Section 6.5.2, p. 152).

## Main results

* `Cslib.GameTheory.Market.leontiefUtility_smul`,
  `Cslib.GameTheory.Market.concaveOn_leontiefUtility`,
  `Cslib.GameTheory.Market.isLocallyNonsatiated_leontiefUtility`: degree-`1` homogeneity,
  concavity, and local nonsatiation of Leontief utilities.
* `Cslib.GameTheory.Market.mem_demandSet_leontiefUtility_iff`,
  `Cslib.GameTheory.Market.demandSet_leontiefUtility_eq_empty_of_cost_zero`: exact Marshallian
  demand characterization of Leontief consumers at nonnegative prices (including zero-priced goods).
* `Cslib.GameTheory.Market.bimatrixLeontiefMarket_isNash_of_equilibriumPrice`,
  `Cslib.GameTheory.Market.bimatrixLeontiefMarket_existsUnique_equilibriumPrice_of_isNash`,
  `Cslib.GameTheory.Market.bimatrixLeontiefNashEquivEquilibriumPrice`: exact one-to-one
  correspondence between mixed Nash equilibria of a strictly positive bimatrix game `(A, B)` and
  normalized nonnegative-price competitive equilibria of `bimatrixLeontiefMarket`
  ([CodenottiVaradarajan2007], Section 6.5.2, p. 152).

## References

* [CodenottiVaradarajan2007], Sections 6.1.5, 6.5.2, and 6.7, pp. 139, 152, 156
-/

public section

namespace Cslib.GameTheory.Market

open Finset Matrix
open scoped BigOperators

/-! ### Leontief (fixed-proportions) utility and Marshallian demand -/

section LeontiefUtility

variable {G : Type*} [Fintype G]

/-- **Leontief (fixed-proportions) utility function** ([CodenottiVaradarajan2007], Section 6.1.5,
p. 139 and Section 6.5.2, p. 152): given nonnegative desired proportions `f : G → ℝ`, the utility
of bundle `b` is `min_{g : 0 < f g} (b g / f g)` (or `0` when no good has `0 < f g`). -/
noncomputable def leontiefUtility (f b : G → ℝ) : ℝ :=
  open Classical in
  if h : (univ.filter fun g : G => 0 < f g).Nonempty then
    (univ.filter fun g : G => 0 < f g).inf' h fun g => b g / f g
  else 0

theorem leontiefUtility_eq_inf' {f b : G → ℝ} [DecidablePred fun g : G => 0 < f g]
    (h : (univ.filter fun g : G => 0 < f g).Nonempty) :
    leontiefUtility f b = (univ.filter fun g : G => 0 < f g).inf' h fun g => b g / f g := by
  have hfilt : @Finset.filter G (fun g => 0 < f g) (Classical.decPred _) univ =
      univ.filter fun g : G => 0 < f g := by
    ext g; simp only [mem_filter, mem_univ, true_and]
  unfold leontiefUtility
  simp only [hfilt, h, ↓reduceDIte]

theorem le_leontiefUtility_iff {f b : G → ℝ} {u : ℝ} (hpos : ∃ g : G, 0 < f g) :
    u ≤ leontiefUtility f b ↔ ∀ g : G, 0 < f g → u * f g ≤ b g := by
  classical
  have hne : (univ.filter fun g : G => 0 < f g).Nonempty := by
    obtain ⟨g, hg⟩ := hpos
    exact ⟨g, mem_filter.2 ⟨mem_univ g, hg⟩⟩
  rw [leontiefUtility_eq_inf' hne, le_inf'_iff]
  constructor
  · intro h g hg
    exact (le_div_iff₀ hg).1 (h g (mem_filter.2 ⟨mem_univ g, hg⟩))
  · intro h g hg
    have hfg := (mem_filter.1 hg).2
    exact (le_div_iff₀ hfg).2 (h g hfg)

theorem leontiefUtility_mul_le {f b : G → ℝ} (hf : ∀ g, 0 ≤ f g) (hb : ∀ g, 0 ≤ b g) (g : G) :
    leontiefUtility f b * f g ≤ b g := by
  rcases (hf g).eq_or_lt with hfg0 | hfg
  · rw [← hfg0, mul_zero]; exact hb g
  · exact (le_leontiefUtility_iff ⟨g, hfg⟩).1 le_rfl g hfg

theorem leontiefUtility_nonneg {f b : G → ℝ} (hb : ∀ g, 0 ≤ b g) : 0 ≤ leontiefUtility f b := by
  classical
  by_cases h : ∃ g : G, 0 < f g
  · exact (le_leontiefUtility_iff h).2 fun g _ => by simpa only [zero_mul] using hb g
  · unfold leontiefUtility
    have hempty : ¬ (univ.filter fun g : G => 0 < f g).Nonempty := fun ⟨g, hg⟩ =>
      h ⟨g, (mem_filter.1 hg).2⟩
    rw [dite_eq_right hempty]

/-- Scaling bundle `b` by `c ≥ 0` scales `leontiefUtility f b` by `c`
([CodenottiVaradarajan2007], Section 6.1.5, p. 139). -/
theorem leontiefUtility_smul {f b : G → ℝ} {c : ℝ} (hc : 0 ≤ c) :
    leontiefUtility f (c • b) = c * leontiefUtility f b := by
  classical
  by_cases h : ∃ g : G, 0 < f g
  · have hne : (univ.filter fun g : G => 0 < f g).Nonempty := by
      obtain ⟨g, hg⟩ := h; exact ⟨g, mem_filter.2 ⟨mem_univ g, hg⟩⟩
    refine le_antisymm ?_ ?_
    · obtain ⟨g₀, hg₀_mem, hg₀_eq⟩ :=
        exists_mem_eq_inf' hne fun g => b g / f g
      rw [leontiefUtility_eq_inf' hne, leontiefUtility_eq_inf' hne, hg₀_eq]
      calc (univ.filter fun g : G => 0 < f g).inf' hne (fun g => (c • b) g / f g)
          ≤ (c • b) g₀ / f g₀ := inf'_le _ hg₀_mem
        _ = c * (b g₀ / f g₀) := by simp only [Pi.smul_apply, smul_eq_mul]; ring
    · exact (le_leontiefUtility_iff h).2 fun g hfg => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_left
          ((le_leontiefUtility_iff h).1 le_rfl g hfg) hc
  · unfold leontiefUtility
    have hempty : ¬ (univ.filter fun g : G => 0 < f g).Nonempty := fun ⟨g, hg⟩ =>
      h ⟨g, (mem_filter.1 hg).2⟩
    simp [dite_eq_right hempty]

/-- `leontiefUtility f` is concave on `{b : G → ℝ | ∀ g, 0 ≤ b g}` (as a finite pointwise minimum
of linear functions). -/
theorem concaveOn_leontiefUtility (f : G → ℝ) :
    ConcaveOn ℝ {b : G → ℝ | ∀ g, 0 ≤ b g} (leontiefUtility f) := by
  have hconv : Convex ℝ {b : G → ℝ | ∀ g, 0 ≤ b g} := fun x hx y hy a b ha hb _ g =>
    add_nonneg (mul_nonneg ha (hx g)) (mul_nonneg hb (hy g))
  refine ⟨hconv, fun x hx y hy a b ha hb _ => ?_⟩
  by_cases h : ∃ g : G, 0 < f g
  · rw [le_leontiefUtility_iff h]
    intro g hfg
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc]
    exact add_le_add
      (mul_le_mul_of_nonneg_left ((le_leontiefUtility_iff h).1 le_rfl g hfg) ha)
      (mul_le_mul_of_nonneg_left ((le_leontiefUtility_iff h).1 le_rfl g hfg) hb)
  · classical
    unfold leontiefUtility
    have hempty : ¬ (univ.filter fun g : G => 0 < f g).Nonempty := fun ⟨g, hg⟩ =>
      h ⟨g, (mem_filter.1 hg).2⟩
    simp [dite_eq_right hempty]

/-- A Leontief consumer with `f ≥ 0` and at least one desired good (`∃ g, 0 < f g`) is locally
nonsatiated on nonnegative bundles. -/
theorem isLocallyNonsatiated_leontiefUtility {f : G → ℝ}
    (hf : ∀ g, 0 ≤ f g) (hpos : ∃ g : G, 0 < f g) :
    IsLocallyNonsatiated (leontiefUtility f) := by
  intro b hb ε hε
  set M : ℝ := 1 + ∑ g : G, f g
  have hM : 0 < M := add_pos_of_pos_of_nonneg zero_lt_one (sum_nonneg fun g _ => hf g)
  set δ : ℝ := ε / (2 * M)
  have hδ : 0 < δ := div_pos hε (by positivity)
  refine ⟨fun g => b g + δ * f g, fun g => add_nonneg (hb g) (mul_nonneg hδ.le (hf g)),
    fun g => ?_, ?_⟩
  · have hfg_le : f g ≤ M := by
      have h1 : f g ≤ ∑ k : G, f k := single_le_sum (fun k _ => hf k) (mem_univ g)
      linarith
    rw [add_sub_cancel_left, abs_of_nonneg (mul_nonneg hδ.le (hf g))]
    calc δ * f g ≤ δ * M := mul_le_mul_of_nonneg_left hfg_le hδ.le
      _ = ε / 2 := by dsimp only [δ]; field_simp [hM.ne']
      _ < ε := half_lt_self hε
  · have hle : leontiefUtility f b + δ ≤ leontiefUtility f (fun g => b g + δ * f g) := by
      rw [le_leontiefUtility_iff hpos]
      intro g hfg
      rw [add_mul]
      linarith [(le_leontiefUtility_iff (b := b) hpos).1 le_rfl g hfg]
    linarith

/-- Utility of a scalar multiple `c • f` (`c ≥ 0`) of the desired proportion vector equals `c`. -/
theorem leontiefUtility_smul_self {f : G → ℝ} {c : ℝ}
    (hpos : ∃ g : G, 0 < f g) (hc : 0 ≤ c) :
    leontiefUtility f (c • f) = c := by
  have h1 : leontiefUtility f f = 1 := by
    classical
    obtain ⟨g₀, hg₀⟩ := hpos
    have hne : (univ.filter fun g : G => 0 < f g).Nonempty :=
      ⟨g₀, mem_filter.2 ⟨mem_univ g₀, hg₀⟩⟩
    rw [leontiefUtility_eq_inf' hne]
    refine le_antisymm ?_ (le_inf' _ _ fun g hg => by rw [div_self (mem_filter.1 hg).2.ne'])
    exact (inf'_le _ (mem_filter.2 ⟨mem_univ g₀, hg₀⟩)).trans_eq (div_self hg₀.ne')
  rw [leontiefUtility_smul hc, h1, mul_one]

/-- If a Leontief consumer's desired bundle costs `0` at nonnegative prices `p` (`expenditure p f =
0`) while `∃ g, 0 < f g` and `0 ≤ m`, then utility is unbounded on the budget set, so `demandSet` is
empty. -/
theorem demandSet_leontiefUtility_eq_empty_of_cost_zero {f p : G → ℝ} {m : ℝ}
    (hf : ∀ g, 0 ≤ f g) (hpos : ∃ g : G, 0 < f g) (hm : 0 ≤ m) (hcost : expenditure p f = 0) :
    demandSet (leontiefUtility f) p m = ∅ := by
  ext b
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hb
  rw [mem_demandSet] at hb
  set K : ℝ := max 0 (leontiefUtility f b) + 1
  have hK : 0 ≤ K := by positivity
  have hfeas : IsBudgetFeasible p m (K • f) :=
    ⟨fun g => mul_nonneg hK (hf g), by rw [expenditure_smul_right, hcost, mul_zero]; exact hm⟩
  have hle := hb.2 (K • f) hfeas
  rw [leontiefUtility_smul_self hpos hK] at hle
  linarith [le_max_right (0 : ℝ) (leontiefUtility f b)]

/-- **Exact Marshallian demand characterization of a Leontief consumer** at nonnegative prices `p`
with positive unit-utility cost `0 < expenditure p f` and budget `m ≥ 0`: `b` is optimal if and only
if `b` is budget-feasible and `∀ g, 0 < f g → (m / expenditure p f) * f g ≤ b g`. -/
theorem mem_demandSet_leontiefUtility_iff {f p : G → ℝ} {m : ℝ} {b : G → ℝ}
    (hf : ∀ g, 0 ≤ f g) (hpos : ∃ g : G, 0 < f g) (hp : ∀ g, 0 ≤ p g)
    (hm : 0 ≤ m) (hcost : 0 < expenditure p f) :
    b ∈ demandSet (leontiefUtility f) p m ↔
      IsBudgetFeasible p m b ∧ ∀ g : G, 0 < f g → (m / expenditure p f) * f g ≤ b g := by
  set U : ℝ := m / expenditure p f
  have hU_nn : 0 ≤ U := div_nonneg hm hcost.le
  have hUf_feas : IsBudgetFeasible p m (U • f) :=
    ⟨fun g => mul_nonneg hU_nn (hf g), by
      rw [expenditure_smul_right, div_mul_cancel₀ m hcost.ne']⟩
  have hbound : ∀ b' : G → ℝ, IsBudgetFeasible p m b' → leontiefUtility f b' ≤ U := fun b' hb' => by
    have hmul : leontiefUtility f b' * expenditure p f ≤ expenditure p b' := by
      rw [expenditure_eq_sum, expenditure_eq_sum, mul_sum]
      refine sum_le_sum fun g _ => ?_
      have h1 := mul_le_mul_of_nonneg_left (leontiefUtility_mul_le hf hb'.1 g) (hp g)
      linarith
    exact (le_div_iff₀ hcost).2 (hmul.trans hb'.2)
  rw [mem_demandSet]
  constructor
  · intro hb
    refine ⟨hb.1, ?_⟩
    rw [← le_leontiefUtility_iff hpos]
    have hge := hb.2 (U • f) hUf_feas
    rwa [leontiefUtility_smul_self hpos hU_nn] at hge
  · rintro ⟨hb_feas, hge⟩
    have hUb : U ≤ leontiefUtility f b := (le_leontiefUtility_iff hpos).2 hge
    exact ⟨hb_feas, fun b' hb' => (hbound b' hb').trans hUb⟩

/-- At any optimal Leontief bundle `b ∈ demandSet (leontiefUtility f) p m`, every positively priced
good `0 < p g` is purchased in exact proportion `b g = (m / expenditure p f) * f g` (in particular,
undesired positively priced goods with `f g = 0` have `b g = 0`). -/
theorem eq_proportion_of_mem_demandSet_leontiefUtility {f p : G → ℝ} {m : ℝ} {b : G → ℝ}
    (hf : ∀ g, 0 ≤ f g) (hpos : ∃ g : G, 0 < f g) (hp : ∀ g, 0 ≤ p g)
    (hm : 0 ≤ m) (hcost : 0 < expenditure p f)
    (hb : b ∈ demandSet (leontiefUtility f) p m) {g : G} (hpg : 0 < p g) :
    b g = (m / expenditure p f) * f g := by
  obtain ⟨hb_feas, hge⟩ := (mem_demandSet_leontiefUtility_iff hf hpos hp hm hcost).1 hb
  set U : ℝ := m / expenditure p f
  have hU_nn : 0 ≤ U := div_nonneg hm hcost.le
  have hge_all : ∀ k : G, U * f k ≤ b k := fun k => by
    rcases (hf k).eq_or_lt with hfk0 | hfk
    · rw [← hfk0, mul_zero]; exact hb_feas.1 k
    · exact hge k hfk
  have hdiff_nn : ∀ k ∈ (univ : Finset G), 0 ≤ p k * (b k - U * f k) := fun k _ =>
    mul_nonneg (hp k) (sub_nonneg.2 (hge_all k))
  have hsum_le0 : ∑ k : G, p k * (b k - U * f k) ≤ 0 := by
    have hexp_eq : ∑ k : G, p k * (b k - U * f k) = expenditure p b - m := by
      simp only [mul_sub, sum_sub_distrib]
      have h1 : ∑ k : G, p k * b k = expenditure p b := (expenditure_eq_sum p b).symm
      have h2 : ∑ k : G, p k * (U * f k) = m := by
        calc ∑ k : G, p k * (U * f k)
            = U * expenditure p f := by
                rw [expenditure_eq_sum, mul_sum]; exact sum_congr rfl fun k _ => by ring
          _ = m := div_mul_cancel₀ m hcost.ne'
      rw [h1, h2]
    rw [hexp_eq]
    linarith [hb_feas.2]
  have hsum0 : ∑ k : G, p k * (b k - U * f k) = 0 :=
    le_antisymm hsum_le0 (sum_nonneg hdiff_nn)
  have hg0 := (sum_eq_zero_iff_of_nonneg hdiff_nn).1 hsum0 g (mem_univ g)
  exact sub_eq_zero.1 ((mul_eq_zero.1 hg0).resolve_left hpg.ne')

end LeontiefUtility

/-! ### Leontief exchange economies and strictly positive column-stochastic stationary vectors -/

/-- A **Leontief Arrow–Debreu exchange economy** ([CodenottiVaradarajan2007], Section 6.5.2,
p. 152): each trader `i : I` has nonnegative endowment `endowment i` and nonnegative Leontief
desired-proportion vector `proportion i`. -/
structure LeontiefExchangeMarket (I G : Type*) where
  /-- Initial endowment `endowment i g` of good `g` held by trader `i`. -/
  endowment : I → G → ℝ
  /-- Desired fixed proportions `proportion i g` of trader `i`. -/
  proportion : I → G → ℝ
  /-- Initial endowments are nonnegative. -/
  endowment_nonneg : ∀ (i : I) (g : G), 0 ≤ endowment i g
  /-- Desired proportions are nonnegative. -/
  proportion_nonneg : ∀ (i : I) (g : G), 0 ≤ proportion i g

namespace LeontiefExchangeMarket

variable {I G : Type*} [Fintype G] (E : LeontiefExchangeMarket I G)

/-- View `E` as a general `ExchangeMarket I G` with `leontiefUtility (E.proportion i)`. -/
noncomputable def toExchangeMarket : ExchangeMarket I G where
  endowment := E.endowment
  utility i := leontiefUtility (E.proportion i)
  endowment_nonneg := E.endowment_nonneg

@[simp] theorem toExchangeMarket_endowment : E.toExchangeMarket.endowment = E.endowment := by rfl

@[simp] theorem toExchangeMarket_utility (i : I) :
    E.toExchangeMarket.utility i = leontiefUtility (E.proportion i) := by rfl

end LeontiefExchangeMarket

/-- Existence and uniqueness of the stationary probability vector of a strictly positive
column-stochastic matrix (`∀ i j, 0 < K i j` and `∀ j, ∑ i, K i j = 1`), via Brouwer's fixed-point
theorem on the simplex and strict `ℓ₁` triangle inequality. -/
private theorem existsUnique_stationary_of_pos_colStochastic {T : Type*} [Fintype T] [Nonempty T]
    {K : Matrix T T ℝ} (hpos : ∀ i j : T, 0 < K i j) (hcol : ∀ j : T, ∑ i : T, K i j = 1) :
    ∃! v : T → ℝ, (∀ i, 0 ≤ v i) ∧ (∑ i : T, v i = 1) ∧ K *ᵥ v = v := by
  -- Existence via `Cslib.Brouwer.exists_isFixedPt_pi_simplex`.
  let F : (Unit → T → ℝ) → Unit → T → ℝ := fun y _ => K *ᵥ (y ())
  have hmaps : Set.MapsTo F
      {y | ∀ _ : Unit, (∀ i, 0 ≤ y () i) ∧ ∑ i, y () i = 1}
      {y | ∀ _ : Unit, (∀ i, 0 ≤ y () i) ∧ ∑ i, y () i = 1} := by
    intro y hy _
    obtain ⟨hy0, hy1⟩ := hy ()
    refine ⟨fun i => sum_nonneg fun j _ => mul_nonneg (hpos i j).le (hy0 j), ?_⟩
    simp only [F, mulVec, dotProduct]
    rw [sum_comm]
    calc ∑ j : T, ∑ i : T, K i j * y () j
        = ∑ j : T, (∑ i : T, K i j) * y () j := sum_congr rfl fun j _ => (sum_mul _ _ _).symm
      _ = ∑ j : T, y () j := sum_congr rfl fun j _ => by rw [hcol j, one_mul]
      _ = 1 := hy1
  have hcont : ContinuousOn F {y | ∀ _ : Unit, (∀ i, 0 ≤ y () i) ∧ ∑ i, y () i = 1} :=
    (continuous_pi fun _ => continuous_pi fun i =>
      continuous_finsetSum univ fun j _ =>
        continuous_const.mul ((continuous_apply j).comp (continuous_apply ()))).continuousOn
  obtain ⟨yFix, hyFix_mem, hyFix_pt⟩ := Cslib.Brouwer.exists_isFixedPt_pi_simplex hmaps hcont
  refine ⟨yFix (), ⟨(hyFix_mem ()).1, (hyFix_mem ()).2, congrFun hyFix_pt ()⟩, ?_⟩
  -- Uniqueness via strict `ℓ₁` triangle inequality on `w = v - yFix ()`.
  rintro v ⟨hv0, hv1, hv_fix⟩
  set v₀ := yFix ()
  have hv₀_sum : ∑ i : T, v₀ i = 1 := (hyFix_mem ()).2
  have hv₀_fix : K *ᵥ v₀ = v₀ := congrFun hyFix_pt ()
  by_contra hne
  let w : T → ℝ := fun i => v i - v₀ i
  have hw_fix : K *ᵥ w = w := by
    have : w = v - v₀ := rfl
    rw [this, mulVec_sub, hv_fix, hv₀_fix]
  have hw_sum0 : ∑ i : T, w i = 0 := by
    simp only [w, sum_sub_distrib, hv1, hv₀_sum, sub_self]
  have hw_ne0 : ∃ j, w j ≠ 0 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
    exact ⟨j, sub_ne_zero.2 hj⟩
  have hex_pos : ∃ j₁ : T, 0 < w j₁ := by
    by_contra hno
    push Not at hno
    obtain ⟨j, hj⟩ := hw_ne0
    have hlt : ∑ i : T, w i < 0 := by
      have := sum_lt_sum (s := univ) (f := w) (g := fun _ => (0 : ℝ))
        (fun i _ => hno i) ⟨j, mem_univ j, lt_of_le_of_ne (hno j) hj⟩
      simpa only [sum_const_zero] using this
    linarith
  have hex_neg : ∃ j₂ : T, w j₂ < 0 := by
    by_contra hno
    push Not at hno
    obtain ⟨j, hj⟩ := hw_ne0
    have hgt : 0 < ∑ i : T, w i := by
      have := sum_lt_sum (s := univ) (f := fun _ => (0 : ℝ)) (g := w)
        (fun i _ => hno i) ⟨j, mem_univ j, lt_of_le_of_ne (hno j) (Ne.symm hj)⟩
      simpa only [sum_const_zero] using this
    linarith
  obtain ⟨j₁, hj₁⟩ := hex_pos
  obtain ⟨j₂, hj₂⟩ := hex_neg
  have hstrict_i : ∀ i : T, |w i| < ∑ j : T, K i j * |w j| := fun i => by
    have hwi : w i = ∑ j : T, K i j * w j := (congrFun hw_fix i).symm
    rw [hwi]
    have hpos_term : 0 < K i j₁ * w j₁ := mul_pos (hpos i j₁) hj₁
    have hneg_term : K i j₂ * w j₂ < 0 := mul_neg_of_pos_of_neg (hpos i j₂) hj₂
    have hlt_abs : |∑ j : T, K i j * w j| < ∑ j : T, |K i j * w j| := by
      rw [abs_lt]
      refine ⟨?_, ?_⟩
      · have hle : ∑ j : T, -(K i j * w j) < ∑ j : T, |K i j * w j| :=
          sum_lt_sum (fun j _ => neg_le_abs _)
            ⟨j₁, mem_univ j₁, by rw [abs_of_pos hpos_term]; linarith⟩
        rw [sum_neg_distrib] at hle
        linarith
      · exact sum_lt_sum (fun j _ => le_abs_self _)
          ⟨j₂, mem_univ j₂, by rw [abs_of_neg hneg_term]; linarith⟩
    refine hlt_abs.trans_eq (sum_congr rfl fun j _ => ?_)
    rw [abs_mul, abs_of_pos (hpos i j)]
  have hsum_lt : ∑ i : T, |w i| < ∑ i : T, ∑ j : T, K i j * |w j| :=
    sum_lt_sum (fun i _ => (hstrict_i i).le) ⟨Classical.arbitrary T, mem_univ _, hstrict_i _⟩
  have hsum_eq : ∑ i : T, ∑ j : T, K i j * |w j| = ∑ j : T, |w j| := by
    rw [sum_comm]
    calc ∑ j : T, ∑ i : T, K i j * |w j|
        = ∑ j : T, (∑ i : T, K i j) * |w j| := sum_congr rfl fun j _ => (sum_mul _ _ _).symm
      _ = ∑ j : T, |w j| := sum_congr rfl fun j _ => by rw [hcol j, one_mul]
  linarith

/-! ### §6.5.2 Bimatrix-to-Leontief exchange economy correspondence -/

section BimatrixCorrespondence

variable {M N : Type*} [Fintype M] [Fintype N]

/-- **Bimatrix-to-Leontief exchange economy** ([CodenottiVaradarajan2007], Section 6.5.2, p. 152;
Codenotti–Saberi–Varadarajan–Ye 2006): given a bimatrix game `G : BimatrixGame M N` with strictly
positive payoff matrices `A, B > 0`, construct the bipartite Leontief exchange economy on `M ⊕ N`
where each trader `t` is endowed with one unit of good `t`, trader `inl i` desires goods `inr j` in
proportions given by row `i` of `B`, and trader `inr j` desires goods `inl i` in proportions given
by column `j` of `A`. -/
noncomputable def bimatrixLeontiefMarket (G : BimatrixGame M N)
    (hA : ∀ i j, 0 < G.A i j) (hB : ∀ i j, 0 < G.B i j) :
    LeontiefExchangeMarket (M ⊕ N) (M ⊕ N) where
  endowment t g := open Classical in if g = t then 1 else 0
  proportion t g :=
    match t, g with
    | Sum.inl i, Sum.inr j => G.B i j
    | Sum.inr j, Sum.inl i => G.A i j
    | _, _ => 0
  endowment_nonneg t g := by
    classical
    split_ifs <;> norm_num
  proportion_nonneg t g := by
    cases t <;> cases g
    · exact le_rfl
    · exact (hB _ _).le
    · exact (hA _ _).le
    · exact le_rfl

omit [Fintype M] [Fintype N] in
@[simp] theorem bimatrixLeontiefMarket_proportion_inl_inl (G : BimatrixGame M N)
    (hA : ∀ i j, 0 < G.A i j) (hB : ∀ i j, 0 < G.B i j) (i i' : M) :
    (bimatrixLeontiefMarket G hA hB).proportion (Sum.inl i) (Sum.inl i') = 0 := by rfl

omit [Fintype M] [Fintype N] in
@[simp] theorem bimatrixLeontiefMarket_proportion_inl_inr (G : BimatrixGame M N)
    (hA : ∀ i j, 0 < G.A i j) (hB : ∀ i j, 0 < G.B i j) (i : M) (j : N) :
    (bimatrixLeontiefMarket G hA hB).proportion (Sum.inl i) (Sum.inr j) = G.B i j := by rfl

omit [Fintype M] [Fintype N] in
@[simp] theorem bimatrixLeontiefMarket_proportion_inr_inl (G : BimatrixGame M N)
    (hA : ∀ i j, 0 < G.A i j) (hB : ∀ i j, 0 < G.B i j) (j : N) (i : M) :
    (bimatrixLeontiefMarket G hA hB).proportion (Sum.inr j) (Sum.inl i) = G.A i j := by rfl

omit [Fintype M] [Fintype N] in
@[simp] theorem bimatrixLeontiefMarket_proportion_inr_inr (G : BimatrixGame M N)
    (hA : ∀ i j, 0 < G.A i j) (hB : ∀ i j, 0 < G.B i j) (j j' : N) :
    (bimatrixLeontiefMarket G hA hB).proportion (Sum.inr j) (Sum.inr j') = 0 := by rfl

@[simp] theorem bimatrixLeontiefMarket_totalSupply (G : BimatrixGame M N)
    (hA : ∀ i j, 0 < G.A i j) (hB : ∀ i j, 0 < G.B i j) (g : M ⊕ N) :
    (bimatrixLeontiefMarket G hA hB).toExchangeMarket.totalSupply g = 1 := by
  classical
  rw [ExchangeMarket.totalSupply_eq_sum]
  simp only [LeontiefExchangeMarket.toExchangeMarket_endowment, bimatrixLeontiefMarket]
  rw [sum_eq_single g (fun t _ hne => ite_eq_right fun h => hne h.symm)
    (fun h => (h (mem_univ g)).elim)]
  simp

@[simp] theorem bimatrixLeontiefMarket_income (G : BimatrixGame M N)
    (hA : ∀ i j, 0 < G.A i j) (hB : ∀ i j, 0 < G.B i j) (π : M ⊕ N → ℝ) (t : M ⊕ N) :
    (bimatrixLeontiefMarket G hA hB).toExchangeMarket.income π t = π t := by
  classical
  rw [ExchangeMarket.income_eq, expenditure_eq_sum]
  simp only [LeontiefExchangeMarket.toExchangeMarket_endowment, bimatrixLeontiefMarket]
  rw [sum_eq_single t (fun g _ hne => by simp [hne]) (fun h => (h (mem_univ t)).elim)]
  simp

@[simp] theorem bimatrixLeontiefMarket_cost_inl (G : BimatrixGame M N)
    (hA : ∀ i j, 0 < G.A i j) (hB : ∀ i j, 0 < G.B i j) (π : M ⊕ N → ℝ) (i : M) :
    expenditure π ((bimatrixLeontiefMarket G hA hB).proportion (Sum.inl i)) =
      (G.B *ᵥ (π ∘ Sum.inr)) i := by
  rw [expenditure_eq_sum, Fintype.sum_sum_type]
  simp only [bimatrixLeontiefMarket, mul_zero, sum_const_zero, zero_add, mulVec, dotProduct,
    Function.comp_apply]
  exact sum_congr rfl fun j _ => mul_comm _ _

@[simp] theorem bimatrixLeontiefMarket_cost_inr (G : BimatrixGame M N)
    (hA : ∀ i j, 0 < G.A i j) (hB : ∀ i j, 0 < G.B i j) (π : M ⊕ N → ℝ) (j : N) :
    expenditure π ((bimatrixLeontiefMarket G hA hB).proportion (Sum.inr j)) =
      ((π ∘ Sum.inl) ᵥ* G.A) j := by
  rw [expenditure_eq_sum, Fintype.sum_sum_type]
  simp only [bimatrixLeontiefMarket, mul_zero, sum_const_zero, add_zero, vecMul, dotProduct,
    Function.comp_apply]

/-- Normalized competitive equilibrium price predicate for `bimatrixLeontiefMarket`: `π` sums to
`1` and supports some competitive equilibrium allocation `X`. -/
@[expose] def IsBimatrixLeontiefEquilibriumPrice (G : BimatrixGame M N)
    (hA : ∀ i j, 0 < G.A i j) (hB : ∀ i j, 0 < G.B i j) (π : M ⊕ N → ℝ) : Prop :=
  (∑ g : M ⊕ N, π g = 1) ∧
    ∃ X : (M ⊕ N) → (M ⊕ N) → ℝ,
      (bimatrixLeontiefMarket G hA hB).toExchangeMarket.IsCompetitiveEquilibrium X π

/-- Structural characterization of equilibrium price vectors `π` of `bimatrixLeontiefMarket`:
defining `U i = π (inl i) / (B *ᵥ q) i` and `V j = π (inr j) / (p ᵥ* A) j` where `p = π ∘ inl` and
`q = π ∘ inr`, both sides have strictly positive total price (`∑ p = ∑ q`), `(A *ᵥ V) i ≤ 1` with
equality when `p i > 0`, and `(U ᵥ* B) j ≤ 1` with equality when `q j > 0`. -/
private theorem bimatrixLeontiefMarket_equilibrium_equations [Nonempty M] [Nonempty N]
    {G : BimatrixGame M N} {hA : ∀ i j, 0 < G.A i j} {hB : ∀ i j, 0 < G.B i j}
    {X : (M ⊕ N) → (M ⊕ N) → ℝ} {π : M ⊕ N → ℝ}
    (heq : (bimatrixLeontiefMarket G hA hB).toExchangeMarket.IsCompetitiveEquilibrium X π) :
    let p : M → ℝ := π ∘ Sum.inl
    let q : N → ℝ := π ∘ Sum.inr
    let U : M → ℝ := fun i => p i / (G.B *ᵥ q) i
    let V : N → ℝ := fun j => q j / (p ᵥ* G.A) j
    (∀ i, 0 ≤ p i) ∧ (∀ j, 0 ≤ q j) ∧
    (0 < ∑ i : M, p i) ∧ (0 < ∑ j : N, q j) ∧
    (∀ i, 0 < (G.B *ᵥ q) i) ∧ (∀ j, 0 < (p ᵥ* G.A) j) ∧
    (∀ i, (G.A *ᵥ V) i ≤ 1) ∧ (∀ i, 0 < p i → (G.A *ᵥ V) i = 1) ∧
    (∀ j, (U ᵥ* G.B) j ≤ 1) ∧ (∀ j, 0 < q j → (U ᵥ* G.B) j = 1) ∧
    (∑ i : M, p i = ∑ j : N, q j) := by
  intro p q U V
  set E := bimatrixLeontiefMarket G hA hB
  have hp_nn : ∀ i, 0 ≤ p i := fun i => heq.1 (Sum.inl i)
  have hq_nn : ∀ j, 0 ≤ q j := fun j => heq.1 (Sum.inr j)
  have hpos_inl : ∀ i : M, ∃ g : M ⊕ N, 0 < E.proportion (Sum.inl i) g := fun i =>
    ⟨Sum.inr (Classical.arbitrary N), hB i _⟩
  have hpos_inr : ∀ j : N, ∃ g : M ⊕ N, 0 < E.proportion (Sum.inr j) g := fun j =>
    ⟨Sum.inl (Classical.arbitrary M), hA _ j⟩
  have hcost_pos : ∀ t : M ⊕ N, (∃ g : M ⊕ N, 0 < E.proportion t g) →
      0 < expenditure π (E.proportion t) := fun t hpos_t => by
    have hnn : 0 ≤ expenditure π (E.proportion t) :=
      expenditure_nonneg heq.1 (E.proportion_nonneg t)
    have hne : expenditure π (E.proportion t) ≠ 0 := fun h0 => by
      have hdem := heq.2.1 t
      rw [ExchangeMarket.mem_demandSet, E.toExchangeMarket_utility,
        bimatrixLeontiefMarket_income] at hdem
      rw [demandSet_leontiefUtility_eq_empty_of_cost_zero (E.proportion_nonneg t)
        hpos_t (heq.1 t) h0] at hdem
      exact hdem
    exact lt_of_le_of_ne hnn (Ne.symm hne)
  have hcost_inl_pos : ∀ i : M, 0 < (G.B *ᵥ q) i := fun i => by
    have hlt := hcost_pos (Sum.inl i) (hpos_inl i)
    rwa [bimatrixLeontiefMarket_cost_inl] at hlt
  have hcost_inr_pos : ∀ j : N, 0 < (p ᵥ* G.A) j := fun j => by
    have hlt := hcost_pos (Sum.inr j) (hpos_inr j)
    rwa [bimatrixLeontiefMarket_cost_inr] at hlt
  have hp_sum_pos : 0 < ∑ i : M, p i := by
    by_contra hnot
    have hp0 : ∀ i, p i = 0 := fun i =>
      (sum_eq_zero_iff_of_nonneg fun k _ => hp_nn k).1
        (le_antisymm (not_lt.1 hnot) (sum_nonneg fun k _ => hp_nn k)) i (mem_univ i)
    have h0 : (p ᵥ* G.A) (Classical.arbitrary N) = 0 := by
      simp [vecMul, dotProduct, hp0]
    linarith [hcost_inr_pos (Classical.arbitrary N)]
  have hq_sum_pos : 0 < ∑ j : N, q j := by
    by_contra hnot
    have hq0 : ∀ j, q j = 0 := fun j =>
      (sum_eq_zero_iff_of_nonneg fun k _ => hq_nn k).1
        (le_antisymm (not_lt.1 hnot) (sum_nonneg fun k _ => hq_nn k)) j (mem_univ j)
    have h0 : (G.B *ᵥ q) (Classical.arbitrary M) = 0 := by
      simp [mulVec, dotProduct, hq0]
    linarith [hcost_inl_pos (Classical.arbitrary M)]
  have hdem_inl : ∀ i : M, X (Sum.inl i) ∈
      demandSet (leontiefUtility (E.proportion (Sum.inl i))) π (p i) := fun i => by
    have h := heq.2.1 (Sum.inl i)
    rwa [ExchangeMarket.mem_demandSet, E.toExchangeMarket_utility,
      bimatrixLeontiefMarket_income] at h
  have hdem_inr : ∀ j : N, X (Sum.inr j) ∈
      demandSet (leontiefUtility (E.proportion (Sum.inr j))) π (q j) := fun j => by
    have h := heq.2.1 (Sum.inr j)
    rwa [ExchangeMarket.mem_demandSet, E.toExchangeMarket_utility,
      bimatrixLeontiefMarket_income] at h
  have hX_nn : ∀ t g, 0 ≤ X t g := fun t g =>
    (Market.mem_demandSet.1 ((ExchangeMarket.mem_demandSet _).1 (heq.2.1 t))).1.1 g
  have hAV_le : ∀ i : M, (G.A *ᵥ V) i ≤ 1 := fun i => by
    calc (G.A *ᵥ V) i
        = ∑ j : N, V j * G.A i j := by
            simp only [mulVec, dotProduct]; exact sum_congr rfl fun j _ => mul_comm _ _
      _ ≤ ∑ j : N, X (Sum.inr j) (Sum.inl i) := sum_le_sum fun j _ => by
            have h := ((mem_demandSet_leontiefUtility_iff (E.proportion_nonneg (Sum.inr j))
              (hpos_inr j) heq.1 (hq_nn j)
              (by rw [bimatrixLeontiefMarket_cost_inr]; exact hcost_inr_pos j)).1
              (hdem_inr j)).2 (Sum.inl i) (hA i j)
            dsimp only [E, V] at h ⊢
            rw [bimatrixLeontiefMarket_cost_inr] at h
            exact h
      _ ≤ ∑ t : M ⊕ N, X t (Sum.inl i) := by
            rw [Fintype.sum_sum_type]
            exact le_add_of_nonneg_left (sum_nonneg fun k _ => hX_nn (Sum.inl k) (Sum.inl i))
      _ ≤ 1 := by
            have hclr := heq.2.2.1 (Sum.inl i)
            rw [ExchangeMarket.excessDemand_eq, bimatrixLeontiefMarket_totalSupply,
              sub_nonpos] at hclr
            exact hclr
  have hAV_eq : ∀ i : M, 0 < p i → (G.A *ᵥ V) i = 1 := fun i hpi => by
    have hclr := heq.sum_eq_totalSupply_of_price_pos (g := Sum.inl i) hpi
    rw [bimatrixLeontiefMarket_totalSupply, Fintype.sum_sum_type] at hclr
    have h1 : ∀ k : M, X (Sum.inl k) (Sum.inl i) = 0 := fun k => by
      have h := eq_proportion_of_mem_demandSet_leontiefUtility (E.proportion_nonneg (Sum.inl k))
        (hpos_inl k) heq.1 (hp_nn k)
        (by rw [bimatrixLeontiefMarket_cost_inl]; exact hcost_inl_pos k) (hdem_inl k) hpi
      simpa only [E, bimatrixLeontiefMarket, mul_zero] using h
    have h2 : ∀ j : N, X (Sum.inr j) (Sum.inl i) = V j * G.A i j := fun j => by
      have h := eq_proportion_of_mem_demandSet_leontiefUtility (E.proportion_nonneg (Sum.inr j))
        (hpos_inr j) heq.1 (hq_nn j)
        (by rw [bimatrixLeontiefMarket_cost_inr]; exact hcost_inr_pos j) (hdem_inr j) hpi
      dsimp only [E, V] at h ⊢
      rw [bimatrixLeontiefMarket_cost_inr] at h
      exact h
    rw [sum_eq_zero fun k _ => h1 k, zero_add, sum_congr rfl fun j _ => h2 j] at hclr
    simpa only [mulVec, dotProduct, mul_comm (G.A i _)] using hclr
  have hUB_le : ∀ j : N, (U ᵥ* G.B) j ≤ 1 := fun j => by
    calc (U ᵥ* G.B) j
        = ∑ i : M, U i * G.B i j := rfl
      _ ≤ ∑ i : M, X (Sum.inl i) (Sum.inr j) := sum_le_sum fun i _ => by
            have h := ((mem_demandSet_leontiefUtility_iff (E.proportion_nonneg (Sum.inl i))
              (hpos_inl i) heq.1 (hp_nn i)
              (by rw [bimatrixLeontiefMarket_cost_inl]; exact hcost_inl_pos i)).1
              (hdem_inl i)).2 (Sum.inr j) (hB i j)
            dsimp only [E, U] at h ⊢
            rw [bimatrixLeontiefMarket_cost_inl] at h
            exact h
      _ ≤ ∑ t : M ⊕ N, X t (Sum.inr j) := by
            rw [Fintype.sum_sum_type]
            exact le_add_of_nonneg_right (sum_nonneg fun k _ => hX_nn (Sum.inr k) (Sum.inr j))
      _ ≤ 1 := by
            have hclr := heq.2.2.1 (Sum.inr j)
            rw [ExchangeMarket.excessDemand_eq, bimatrixLeontiefMarket_totalSupply,
              sub_nonpos] at hclr
            exact hclr
  have hUB_eq : ∀ j : N, 0 < q j → (U ᵥ* G.B) j = 1 := fun j hqj => by
    have hclr := heq.sum_eq_totalSupply_of_price_pos (g := Sum.inr j) hqj
    rw [bimatrixLeontiefMarket_totalSupply, Fintype.sum_sum_type] at hclr
    have h1 : ∀ i : M, X (Sum.inl i) (Sum.inr j) = U i * G.B i j := fun i => by
      have h := eq_proportion_of_mem_demandSet_leontiefUtility (E.proportion_nonneg (Sum.inl i))
        (hpos_inl i) heq.1 (hp_nn i)
        (by rw [bimatrixLeontiefMarket_cost_inl]; exact hcost_inl_pos i) (hdem_inl i) hqj
      dsimp only [E, U] at h ⊢
      rw [bimatrixLeontiefMarket_cost_inl] at h
      exact h
    have h2 : ∀ k : N, X (Sum.inr k) (Sum.inr j) = 0 := fun k => by
      have h := eq_proportion_of_mem_demandSet_leontiefUtility (E.proportion_nonneg (Sum.inr k))
        (hpos_inr k) heq.1 (hq_nn k)
        (by rw [bimatrixLeontiefMarket_cost_inr]; exact hcost_inr_pos k) (hdem_inr k) hqj
      simpa only [E, bimatrixLeontiefMarket, mul_zero] using h
    rw [sum_eq_zero fun k _ => h2 k, add_zero, sum_congr rfl fun i _ => h1 i] at hclr
    exact hclr
  have hsum_pq : ∑ i : M, p i = ∑ j : N, q j := by
    have hp_eq : ∀ i : M, p i = U i * (G.B *ᵥ q) i := fun i =>
      (div_mul_cancel₀ (p i) (hcost_inl_pos i).ne').symm
    calc ∑ i : M, p i
        = ∑ i : M, U i * (G.B *ᵥ q) i := sum_congr rfl fun i _ => hp_eq i
      _ = ∑ j : N, (U ᵥ* G.B) j * q j := by
            simp only [mulVec, vecMul, dotProduct, mul_sum, sum_mul]
            rw [sum_comm]
            exact sum_congr rfl fun j _ => sum_congr rfl fun i _ => by ring
      _ = ∑ j : N, q j := sum_congr rfl fun j _ => by
            rcases (hq_nn j).eq_or_lt with hq0 | hqpos
            · simp [← hq0]
            · rw [hUB_eq j hqpos, one_mul]
  exact ⟨hp_nn, hq_nn, hp_sum_pos, hq_sum_pos, hcost_inl_pos, hcost_inr_pos,
    hAV_le, hAV_eq, hUB_le, hUB_eq, hsum_pq⟩

/-- Explicit mixed-strategy profile extracted from an equilibrium price vector `π` of
`bimatrixLeontiefMarket`: normalize the Leontief equilibrium utility profiles
`U i = π (inl i) / (B *ᵥ q) i` and `V j = π (inr j) / (p ᵥ* A) j`. -/
@[expose] noncomputable def bimatrixLeontiefToStrategy (G : BimatrixGame M N) (π : M ⊕ N → ℝ) :
    (M → ℝ) × (N → ℝ) :=
  let U : M → ℝ := fun i => π (Sum.inl i) / (G.B *ᵥ (π ∘ Sum.inr)) i
  let V : N → ℝ := fun j => π (Sum.inr j) / ((π ∘ Sum.inl) ᵥ* G.A) j
  ((∑ i : M, U i)⁻¹ • U, (∑ j : N, V j)⁻¹ • V)

/-- **Market equilibrium → Bimatrix Nash equilibrium** ([CodenottiVaradarajan2007], Section 6.5.2,
p. 152): any competitive equilibrium `(X, π)` of `bimatrixLeontiefMarket G hA hB` projects via
`bimatrixLeontiefToStrategy G π` to a mixed Nash equilibrium `(x, y)` of `G`. -/
theorem bimatrixLeontiefMarket_isNash_of_equilibriumPrice [Nonempty M] [Nonempty N]
    {G : BimatrixGame M N} {hA : ∀ i j, 0 < G.A i j} {hB : ∀ i j, 0 < G.B i j}
    {X : (M ⊕ N) → (M ⊕ N) → ℝ} {π : M ⊕ N → ℝ}
    (heq : (bimatrixLeontiefMarket G hA hB).toExchangeMarket.IsCompetitiveEquilibrium X π) :
    G.IsNash (bimatrixLeontiefToStrategy G π).1 (bimatrixLeontiefToStrategy G π).2 := by
  obtain ⟨hp_nn, hq_nn, hp_sum_pos, hq_sum_pos, hcost_inl, hcost_inr,
    hAV_le, hAV_eq, hUB_le, hUB_eq, _⟩ := bimatrixLeontiefMarket_equilibrium_equations heq
  set p : M → ℝ := π ∘ Sum.inl
  set q : N → ℝ := π ∘ Sum.inr
  set U : M → ℝ := fun i => p i / (G.B *ᵥ q) i
  set V : N → ℝ := fun j => q j / (p ᵥ* G.A) j
  have hU_nn : ∀ i, 0 ≤ U i := fun i => div_nonneg (hp_nn i) (hcost_inl i).le
  have hV_nn : ∀ j, 0 ≤ V j := fun j => div_nonneg (hq_nn j) (hcost_inr j).le
  have hU_pos : 0 < ∑ i : M, U i := by
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_lt_of_sum_lt (s := univ) (f := fun _ => (0 : ℝ)) (g := p)
      (by simpa only [sum_const_zero] using hp_sum_pos)
    exact (sum_pos_iff_of_nonneg fun i _ => hU_nn i).2 ⟨i₀, mem_univ i₀, div_pos hi₀ (hcost_inl i₀)⟩
  have hV_pos : 0 < ∑ j : N, V j := by
    obtain ⟨j₀, -, hj₀⟩ := Finset.exists_lt_of_sum_lt (s := univ) (f := fun _ => (0 : ℝ)) (g := q)
      (by simpa only [sum_const_zero] using hq_sum_pos)
    exact (sum_pos_iff_of_nonneg fun j _ => hV_nn j).2 ⟨j₀, mem_univ j₀, div_pos hj₀ (hcost_inr j₀)⟩
  have hU_ne : U ≠ 0 := fun h0 => by simp [h0] at hU_pos
  have hV_ne : V ≠ 0 := fun h0 => by simp [h0] at hV_pos
  have hx_ms : IsMixedStrategy ((∑ i : M, U i)⁻¹ • U) := isMixedStrategy_inv_sum_smul hU_nn hU_ne
  have hy_ms : IsMixedStrategy ((∑ j : N, V j)⁻¹ • V) := isMixedStrategy_inv_sum_smul hV_nn hV_ne
  rw [BimatrixGame.isNash_iff, BimatrixGame.isBestResponse₁_iff, BimatrixGame.isBestResponse₂_iff]
  refine ⟨⟨hx_ms, fun i hi => BimatrixGame.isPureBestResponse₁_iff.2 fun i' => ?_⟩,
    ⟨hy_ms, fun j hj => BimatrixGame.isPureBestResponse₂_iff.2 fun j' => ?_⟩⟩
  · have hUi : 0 < U i := pos_of_mul_pos_right hi (inv_pos.2 hU_pos).le
    have hpi : 0 < p i := (div_pos_iff_of_pos_right (hcost_inl i)).1 hUi
    change (G.A *ᵥ ((∑ j : N, V j)⁻¹ • V)) i' ≤ (G.A *ᵥ ((∑ j : N, V j)⁻¹ • V)) i
    simp only [mulVec_smul, Pi.smul_apply, smul_eq_mul]
    rw [hAV_eq i hpi]
    exact mul_le_mul_of_nonneg_left (hAV_le i') (inv_pos.2 hV_pos).le
  · have hVj : 0 < V j := pos_of_mul_pos_right hj (inv_pos.2 hV_pos).le
    have hqj : 0 < q j := (div_pos_iff_of_pos_right (hcost_inr j)).1 hVj
    change (((∑ i : M, U i)⁻¹ • U) ᵥ* G.B) j' ≤ (((∑ i : M, U i)⁻¹ • U) ᵥ* G.B) j
    simp only [smul_vecMul, Pi.smul_apply, smul_eq_mul]
    rw [hUB_eq j hqj]
    exact mul_le_mul_of_nonneg_left (hUB_le j') (inv_pos.2 hU_pos).le

/-- **Bimatrix Nash equilibrium → Unique normalized market equilibrium price**
([CodenottiVaradarajan2007], Section 6.5.2, p. 152): every mixed Nash equilibrium `(x, y)` of a
strictly positive bimatrix game `G` induces a **unique** normalized competitive equilibrium price
vector `π` (`∑ g, π g = 1`) of `bimatrixLeontiefMarket G hA hB` satisfying
`bimatrixLeontiefToStrategy G π = (x, y)`. -/
theorem bimatrixLeontiefMarket_existsUnique_equilibriumPrice_of_isNash [Nonempty M] [Nonempty N]
    {G : BimatrixGame M N} {hA : ∀ i j, 0 < G.A i j} {hB : ∀ i j, 0 < G.B i j}
    {x : M → ℝ} {y : N → ℝ} (hnash : G.IsNash x y) :
    ∃! π : M ⊕ N → ℝ,
      IsBimatrixLeontiefEquilibriumPrice G hA hB π ∧
        bimatrixLeontiefToStrategy G π = (x, y) := by
  classical
  obtain ⟨hbr1, hbr2⟩ := BimatrixGame.isNash_iff.1 hnash
  have hx_ms : IsMixedStrategy x := hbr1.isMixedStrategy
  have hy_ms : IsMixedStrategy y := hbr2.isMixedStrategy
  set v₁ : ℝ := G.payoff₁ x y
  set v₂ : ℝ := G.payoff₂ x y
  have hv₁ : 0 < v₁ := G.payoff₁_pos hA hx_ms hy_ms
  have hv₂ : 0 < v₂ := G.payoff₂_pos hB hx_ms hy_ms
  let U : M → ℝ := v₂⁻¹ • x
  let V : N → ℝ := v₁⁻¹ • y
  have hU_nn : ∀ i, 0 ≤ U i := fun i => mul_nonneg (inv_pos.2 hv₂).le (hx_ms.nonneg i)
  have hV_nn : ∀ j, 0 ≤ V j := fun j => mul_nonneg (inv_pos.2 hv₁).le (hy_ms.nonneg j)
  have hAV_le : ∀ i, (G.A *ᵥ V) i ≤ 1 := fun i => by
    simp only [V, mulVec_smul, Pi.smul_apply, smul_eq_mul]
    exact (inv_mul_le_iff₀ hv₁).2 (by simpa only [mul_one] using hbr1.le_payoff₁ i)
  have hAV_eq : ∀ i, 0 < x i → (G.A *ᵥ V) i = 1 := fun i hi => by
    simp only [V, mulVec_smul, Pi.smul_apply, smul_eq_mul]
    rw [← hbr1.payoff₁_eq_of_pos hi]
    exact inv_mul_cancel₀ hv₁.ne'
  have hUB_le : ∀ j, (U ᵥ* G.B) j ≤ 1 := fun j => by
    simp only [U, smul_vecMul, Pi.smul_apply, smul_eq_mul]
    exact (inv_mul_le_iff₀ hv₂).2 (by simpa only [mul_one] using hbr2.le_payoff₂ j)
  have hUB_eq : ∀ j, 0 < y j → (U ᵥ* G.B) j = 1 := fun j hj => by
    simp only [U, smul_vecMul, Pi.smul_apply, smul_eq_mul]
    rw [← hbr2.payoff₂_eq_of_pos hj]
    exact inv_mul_cancel₀ hv₂.ne'
  -- Restrict to the nonempty supports `S = {i | 0 < x i}` and `T = {j | 0 < y j}`.
  let S : Finset M := univ.filter fun i => 0 < x i
  let T : Finset N := univ.filter fun j => 0 < y j
  have hS_ne : S.Nonempty := by
    obtain ⟨i, hi⟩ := hx_ms.exists_pos
    exact ⟨i, mem_filter.2 ⟨mem_univ i, hi⟩⟩
  have hT_ne : T.Nonempty := by
    obtain ⟨j, hj⟩ := hy_ms.exists_pos
    exact ⟨j, mem_filter.2 ⟨mem_univ j, hj⟩⟩
  have : Nonempty S := hS_ne.coe_sort
  have : Nonempty T := hT_ne.coe_sort
  -- Define strictly positive column-stochastic matrices `P : Matrix S T ℝ`, `Q : Matrix T S ℝ`.
  let P : Matrix S T ℝ := Matrix.of fun i j => U i.1 * G.B i.1 j.1
  let Q : Matrix T S ℝ := Matrix.of fun j i => V j.1 * G.A i.1 j.1
  have hP_pos : ∀ i j, 0 < P i j := fun i j =>
    mul_pos (mul_pos (inv_pos.2 hv₂) (mem_filter.1 i.2).2) (hB i.1 j.1)
  have hQ_pos : ∀ j i, 0 < Q j i := fun j i =>
    mul_pos (mul_pos (inv_pos.2 hv₁) (mem_filter.1 j.2).2) (hA i.1 j.1)
  have hP_col : ∀ j : T, ∑ i : S, P i j = 1 := fun j => by
    calc ∑ i : S, U i.1 * G.B i.1 j.1
        = ∑ i ∈ S, U i * G.B i j.1 := sum_coe_sort S fun i => U i * G.B i j.1
      _ = ∑ i : M, U i * G.B i j.1 := sum_subset (subset_univ S) fun i _ hi => by
            have hx0 : x i = 0 := le_antisymm (not_lt.1 fun h => hi (mem_filter.2 ⟨mem_univ i, h⟩))
              (hx_ms.nonneg i)
            simp [U, hx0]
      _ = (U ᵥ* G.B) j.1 := rfl
      _ = 1 := hUB_eq j.1 (mem_filter.1 j.2).2
  have hQ_col : ∀ i : S, ∑ j : T, Q j i = 1 := fun i => by
    calc ∑ j : T, V j.1 * G.A i.1 j.1
        = ∑ j ∈ T, V j * G.A i.1 j := sum_coe_sort T fun j => V j * G.A i.1 j
      _ = ∑ j : N, V j * G.A i.1 j := sum_subset (subset_univ T) fun j _ hj => by
            have hy0 : y j = 0 := le_antisymm (not_lt.1 fun h => hj (mem_filter.2 ⟨mem_univ j, h⟩))
              (hy_ms.nonneg j)
            simp [V, hy0]
      _ = (G.A *ᵥ V) i.1 := by
            simp only [mulVec, dotProduct]; exact sum_congr rfl fun j _ => mul_comm _ _
      _ = 1 := hAV_eq i.1 (mem_filter.1 i.2).2
  let K : Matrix T T ℝ := Q * P
  have hK_pos : ∀ j₁ j₂ : T, 0 < K j₁ j₂ := fun j₁ j₂ =>
    sum_pos (fun i _ => mul_pos (hQ_pos j₁ i) (hP_pos i j₂)) univ_nonempty
  have hK_col : ∀ j₂ : T, ∑ j₁ : T, K j₁ j₂ = 1 := fun j₂ => by
    have hent : ∀ j₁ : T, K j₁ j₂ = ∑ i : S, Q j₁ i * P i j₂ := fun j₁ => Matrix.mul_apply
    simp_rw [hent]
    rw [sum_comm]
    calc ∑ i : S, ∑ j₁ : T, Q j₁ i * P i j₂
        = ∑ i : S, (∑ j₁ : T, Q j₁ i) * P i j₂ := sum_congr rfl fun i _ => (sum_mul _ _ _).symm
      _ = ∑ i : S, P i j₂ := sum_congr rfl fun i _ => by rw [hQ_col i, one_mul]
      _ = 1 := hP_col j₂
  obtain ⟨qT, ⟨hqT_nn, hqT_sum, hqT_fix⟩, hqT_uniq⟩ :=
    existsUnique_stationary_of_pos_colStochastic hK_pos hK_col
  -- Construct normalized prices `p, q` with `∑ p = ∑ q = 1/2`.
  let pS : S → ℝ := P *ᵥ qT
  have hpS_nn : ∀ i : S, 0 ≤ pS i := fun i =>
    sum_nonneg fun j _ => mul_nonneg (hP_pos i j).le (hqT_nn j)
  have hpS_sum : ∑ i : S, pS i = 1 := by
    simp only [pS, mulVec, dotProduct]
    rw [sum_comm]
    calc ∑ j : T, ∑ i : S, P i j * qT j
        = ∑ j : T, (∑ i : S, P i j) * qT j := sum_congr rfl fun j _ => (sum_mul _ _ _).symm
      _ = ∑ j : T, qT j := sum_congr rfl fun j _ => by rw [hP_col j, one_mul]
      _ = 1 := hqT_sum
  have hQpS : Q *ᵥ pS = qT := by
    dsimp only [pS]
    rw [mulVec_mulVec]
    exact hqT_fix
  let p : M → ℝ := fun i => if h : i ∈ S then (1 / 2) * pS ⟨i, h⟩ else 0
  let q : N → ℝ := fun j => if h : j ∈ T then (1 / 2) * qT ⟨j, h⟩ else 0
  let π : M ⊕ N → ℝ := Sum.elim p q
  have hp_nn : ∀ i, 0 ≤ p i := fun i => by
    dsimp only [p]; split_ifs with h
    · exact mul_nonneg (by norm_num) (hpS_nn ⟨i, h⟩)
    · exact le_rfl
  have hq_nn : ∀ j, 0 ≤ q j := fun j => by
    dsimp only [q]; split_ifs with h
    · exact mul_nonneg (by norm_num) (hqT_nn ⟨j, h⟩)
    · exact le_rfl
  have hsum_p : ∑ i : M, p i = 1 / 2 := by
    calc ∑ i : M, p i = ∑ i ∈ S, p i :=
            (sum_subset (subset_univ S) fun i _ hi => by simp [p, hi]).symm
      _ = ∑ i : S, (1 / 2) * pS i := by
            rw [← sum_coe_sort S p]; exact sum_congr rfl fun i _ => by simp [p, i.2]
      _ = 1 / 2 := by rw [← mul_sum, hpS_sum, mul_one]
  have hsum_q : ∑ j : N, q j = 1 / 2 := by
    calc ∑ j : N, q j = ∑ j ∈ T, q j :=
            (sum_subset (subset_univ T) fun j _ hj => by simp [q, hj]).symm
      _ = ∑ j : T, (1 / 2) * qT j := by
            rw [← sum_coe_sort T q]; exact sum_congr rfl fun j _ => by simp [q, j.2]
      _ = 1 / 2 := by rw [← mul_sum, hqT_sum, mul_one]
  have hπ_sum : ∑ g : M ⊕ N, π g = 1 := by
    rw [Fintype.sum_sum_type]
    simp only [π, Sum.elim_inl, Sum.elim_inr, hsum_p, hsum_q]
    norm_num
  have hcost_inl_pos : ∀ i : M, 0 < (G.B *ᵥ q) i := fun i => by
    have hq_pos : ∃ j : N, 0 < q j := by
      obtain ⟨j, -, hj⟩ := Finset.exists_lt_of_sum_lt (s := univ) (f := fun _ => (0 : ℝ)) (g := q)
        (by rw [sum_const_zero, hsum_q]; norm_num)
      exact ⟨j, hj⟩
    obtain ⟨j₀, hj₀⟩ := hq_pos
    exact (sum_pos_iff_of_nonneg fun j _ => mul_nonneg (hB i j).le (hq_nn j)).2
      ⟨j₀, mem_univ j₀, mul_pos (hB i j₀) hj₀⟩
  have hcost_inr_pos : ∀ j : N, 0 < (p ᵥ* G.A) j := fun j => by
    have hp_pos : ∃ i : M, 0 < p i := by
      obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt (s := univ) (f := fun _ => (0 : ℝ)) (g := p)
        (by rw [sum_const_zero, hsum_p]; norm_num)
      exact ⟨i, hi⟩
    obtain ⟨i₀, hi₀⟩ := hp_pos
    exact (sum_pos_iff_of_nonneg fun i _ => mul_nonneg (hp_nn i) (hA i j).le).2
      ⟨i₀, mem_univ i₀, mul_pos hi₀ (hA i₀ j)⟩
  have hp_eq_U : ∀ i : M, p i = U i * (G.B *ᵥ q) i := fun i => by
    by_cases hi : i ∈ S
    · simp only [p, hi, ↓reduceDIte, pS, mulVec, dotProduct]
      calc (1 / 2 : ℝ) * ∑ j : T, P ⟨i, hi⟩ j * qT j
          = ∑ j : T, U i * G.B i j.1 * ((1 / 2 : ℝ) * qT j) := by
              rw [mul_sum]
              exact sum_congr rfl fun j _ => by dsimp only [P, Matrix.of_apply]; ring
        _ = ∑ j ∈ T, U i * G.B i j * q j := by
              rw [← sum_coe_sort T fun j => U i * G.B i j * q j]
              exact sum_congr rfl fun j _ => by simp [q, j.2]
        _ = ∑ j : N, U i * G.B i j * q j := sum_subset (subset_univ T) fun j _ hj => by
              simp [q, hj]
        _ = U i * ∑ j : N, G.B i j * q j := by
              rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
    · have hx0 : x i = 0 := le_antisymm (not_lt.1 fun h => hi (mem_filter.2 ⟨mem_univ i, h⟩))
        (hx_ms.nonneg i)
      simp [p, hi, U, hx0]
  have hq_eq_V : ∀ j : N, q j = V j * (p ᵥ* G.A) j := fun j => by
    by_cases hj : j ∈ T
    · have hqj_eq := congrFun hQpS ⟨j, hj⟩
      simp only [q, hj, ↓reduceDIte, ← hqj_eq, mulVec, dotProduct]
      calc (1 / 2 : ℝ) * ∑ i : S, Q ⟨j, hj⟩ i * pS i
          = ∑ i : S, V j * ((1 / 2 : ℝ) * pS i * G.A i.1 j) := by
              rw [mul_sum]
              exact sum_congr rfl fun i _ => by dsimp only [Q, Matrix.of_apply]; ring
        _ = ∑ i ∈ S, V j * (p i * G.A i j) := by
              rw [← sum_coe_sort S fun i => V j * (p i * G.A i j)]
              exact sum_congr rfl fun i _ => by simp [p, i.2]
        _ = ∑ i : M, V j * (p i * G.A i j) := sum_subset (subset_univ S) fun i _ hi => by
              simp [p, hi]
        _ = V j * ∑ i : M, p i * G.A i j := (mul_sum _ _ _).symm
    · have hy0 : y j = 0 := le_antisymm (not_lt.1 fun h => hj (mem_filter.2 ⟨mem_univ j, h⟩))
        (hy_ms.nonneg j)
      simp [q, hj, V, hy0]
  -- Explicit competitive equilibrium allocation `X`.
  set E := bimatrixLeontiefMarket G hA hB
  let X : (M ⊕ N) → (M ⊕ N) → ℝ := fun t g => Sum.elim U V t * E.proportion t g
  have hEq : E.toExchangeMarket.IsCompetitiveEquilibrium X π := by
    have hπ_nn : ∀ g, 0 ≤ π g := fun g => by
      cases g with | inl i => exact hp_nn i | inr j => exact hq_nn j
    refine ⟨hπ_nn, fun t => ?_, fun g => ?_, fun g => ?_⟩
    · cases t with
      | inl i =>
        rw [ExchangeMarket.mem_demandSet, E.toExchangeMarket_utility, bimatrixLeontiefMarket_income]
        dsimp only [π, Sum.elim_inl]
        have hcost : 0 < expenditure π (E.proportion (Sum.inl i)) := by
          rw [bimatrixLeontiefMarket_cost_inl]; exact hcost_inl_pos i
        rw [mem_demandSet_leontiefUtility_iff (E.proportion_nonneg (Sum.inl i))
          ⟨Sum.inr (Classical.arbitrary N), hB i _⟩ hπ_nn (hp_nn i) hcost]
        have hUi_eq : p i / expenditure π (E.proportion (Sum.inl i)) = U i := by
          rw [bimatrixLeontiefMarket_cost_inl]
          exact (div_eq_iff (hcost_inl_pos i).ne').2 (hp_eq_U i)
        refine ⟨⟨fun g => mul_nonneg (hU_nn i) (E.proportion_nonneg (Sum.inl i) g), ?_⟩,
          fun g _ => by simp only [X, Sum.elim_inl, hUi_eq]; exact le_rfl⟩
        have hX_eq : X (Sum.inl i) = U i • E.proportion (Sum.inl i) := rfl
        rw [hX_eq, expenditure_smul_right, bimatrixLeontiefMarket_cost_inl]
        exact (hp_eq_U i).ge
      | inr j =>
        rw [ExchangeMarket.mem_demandSet, E.toExchangeMarket_utility, bimatrixLeontiefMarket_income]
        dsimp only [π, Sum.elim_inr]
        have hcost : 0 < expenditure π (E.proportion (Sum.inr j)) := by
          rw [bimatrixLeontiefMarket_cost_inr]; exact hcost_inr_pos j
        rw [mem_demandSet_leontiefUtility_iff (E.proportion_nonneg (Sum.inr j))
          ⟨Sum.inl (Classical.arbitrary M), hA _ j⟩ hπ_nn (hq_nn j) hcost]
        have hVj_eq : q j / expenditure π (E.proportion (Sum.inr j)) = V j := by
          rw [bimatrixLeontiefMarket_cost_inr]
          exact (div_eq_iff (hcost_inr_pos j).ne').2 (hq_eq_V j)
        refine ⟨⟨fun g => mul_nonneg (hV_nn j) (E.proportion_nonneg (Sum.inr j) g), ?_⟩,
          fun g _ => by simp only [X, Sum.elim_inr, hVj_eq]; exact le_rfl⟩
        have hX_eq : X (Sum.inr j) = V j • E.proportion (Sum.inr j) := rfl
        rw [hX_eq, expenditure_smul_right, bimatrixLeontiefMarket_cost_inr]
        exact (hq_eq_V j).ge
    · rw [ExchangeMarket.excessDemand_eq, bimatrixLeontiefMarket_totalSupply, sub_nonpos,
        Fintype.sum_sum_type]
      cases g with
      | inl i =>
        simp only [X, Sum.elim_inr, E, bimatrixLeontiefMarket, mul_zero,
          sum_const_zero, zero_add]
        simpa only [mulVec, dotProduct, mul_comm (G.A i _)] using hAV_le i
      | inr j =>
        simp only [X, Sum.elim_inl, E, bimatrixLeontiefMarket, mul_zero,
          sum_const_zero, add_zero]
        exact hUB_le j
    · rw [ExchangeMarket.excessDemand_eq, bimatrixLeontiefMarket_totalSupply, Fintype.sum_sum_type]
      cases g with
      | inl i =>
        simp only [π, Sum.elim_inl, X, Sum.elim_inr, E, bimatrixLeontiefMarket, mul_zero,
          sum_const_zero, zero_add]
        rcases (hp_nn i).eq_or_lt with hp0 | hp_pos
        · rw [← hp0, zero_mul]
        · have hiS : i ∈ S := by
            by_contra hi
            simp [p, hi] at hp_pos
          have hsum_eq : ∑ j : N, V j * G.A i j = 1 := by
            simpa only [mulVec, dotProduct, mul_comm (G.A i _)] using
              hAV_eq i (mem_filter.1 hiS).2
          rw [hsum_eq, sub_self, mul_zero]
      | inr j =>
        simp only [π, Sum.elim_inr, X, Sum.elim_inl, E, bimatrixLeontiefMarket, mul_zero,
          sum_const_zero, add_zero]
        rcases (hq_nn j).eq_or_lt with hq0 | hq_pos
        · rw [← hq0, zero_mul]
        · have hjT : j ∈ T := by
            by_contra hj
            simp [q, hj] at hq_pos
          have hsum_eq : ∑ i : M, U i * G.B i j = 1 := hUB_eq j (mem_filter.1 hjT).2
          rw [hsum_eq, sub_self, mul_zero]
  have hproj : bimatrixLeontiefToStrategy G π = (x, y) := by
    dsimp only [bimatrixLeontiefToStrategy]
    have hU_eq : (fun i : M => π (Sum.inl i) / (G.B *ᵥ (π ∘ Sum.inr)) i) = U := funext fun i =>
      (div_eq_iff (hcost_inl_pos i).ne').2 (hp_eq_U i)
    have hV_eq : (fun j : N => π (Sum.inr j) / ((π ∘ Sum.inl) ᵥ* G.A) j) = V := funext fun j =>
      (div_eq_iff (hcost_inr_pos j).ne').2 (hq_eq_V j)
    rw [hU_eq, hV_eq]
    have hsumU : ∑ i : M, U i = v₂⁻¹ := by
      simp only [U, Pi.smul_apply, smul_eq_mul, ← mul_sum, hx_ms.sum_eq_one, mul_one]
    have hsumV : ∑ j : N, V j = v₁⁻¹ := by
      simp only [V, Pi.smul_apply, smul_eq_mul, ← mul_sum, hy_ms.sum_eq_one, mul_one]
    rw [hsumU, hsumV, inv_inv, inv_inv]
    exact Prod.ext
      (funext fun i => by simp only [U, Pi.smul_apply, smul_eq_mul, mul_inv_cancel_left₀ hv₂.ne'])
      (funext fun j => by simp only [V, Pi.smul_apply, smul_eq_mul, mul_inv_cancel_left₀ hv₁.ne'])
  refine ⟨π, ⟨⟨hπ_sum, ⟨X, hEq⟩⟩, hproj⟩, ?_⟩
  -- Uniqueness: any other normalized equilibrium price `π'` projecting to `(x, y)` must equal `π`.
  rintro π' ⟨⟨hπ'_sum, ⟨X', hEq'⟩⟩, hproj'⟩
  obtain ⟨hp'_nn, hq'_nn, _, _, hcost'_inl, hcost'_inr, _, hAV'_eq, _, hUB'_eq, hsum'_pq⟩ :=
    bimatrixLeontiefMarket_equilibrium_equations hEq'
  set p' : M → ℝ := π' ∘ Sum.inl
  set q' : N → ℝ := π' ∘ Sum.inr
  set U' : M → ℝ := fun i => p' i / (G.B *ᵥ q') i
  set V' : N → ℝ := fun j => q' j / (p' ᵥ* G.A) j
  have hsum_p'_half : ∑ i : M, p' i = 1 / 2 := by
    rw [Fintype.sum_sum_type] at hπ'_sum
    change (∑ i : M, p' i) + (∑ j : N, q' j) = 1 at hπ'_sum
    linarith
  have hsum_q'_half : ∑ j : N, q' j = 1 / 2 := by linarith
  have hx_eq : (∑ i : M, U' i)⁻¹ • U' = x := congrArg Prod.fst hproj'
  have hy_eq : (∑ j : N, V' j)⁻¹ • V' = y := congrArg Prod.snd hproj'
  -- Verify `U' = U` and `V' = V`.
  have hU'_nn : ∀ i, 0 ≤ U' i := fun i => div_nonneg (hp'_nn i) (hcost'_inl i).le
  have hV'_nn : ∀ j, 0 ≤ V' j := fun j => div_nonneg (hq'_nn j) (hcost'_inr j).le
  have hU'_sum_pos : 0 < ∑ i : M, U' i := by
    by_contra h0
    have hU'0 : ∀ i, U' i = 0 := fun i =>
      (sum_eq_zero_iff_of_nonneg fun k _ => hU'_nn k).1
        (le_antisymm (not_lt.1 h0) (sum_nonneg fun k _ => hU'_nn k)) i (mem_univ i)
    have : x = 0 := by rw [← hx_eq]; ext i; simp [hU'0 i]
    exact hx_ms.ne_zero this
  have hV'_sum_pos : 0 < ∑ j : N, V' j := by
    by_contra h0
    have hV'0 : ∀ j, V' j = 0 := fun j =>
      (sum_eq_zero_iff_of_nonneg fun k _ => hV'_nn k).1
        (le_antisymm (not_lt.1 h0) (sum_nonneg fun k _ => hV'_nn k)) j (mem_univ j)
    have : y = 0 := by rw [← hy_eq]; ext j; simp [hV'0 j]
    exact hy_ms.ne_zero this
  have hU'_eq_U : U' = U := by
    have hv₂_eq : v₂ = (∑ i : M, U' i)⁻¹ := by
      have hdot : y ⬝ᵥ (U' ᵥ* G.B) = 1 := by
        calc y ⬝ᵥ (U' ᵥ* G.B)
            = ∑ j : N, y j * (U' ᵥ* G.B) j := rfl
          _ = ∑ j : N, y j := sum_congr rfl fun j _ => by
                rcases (hy_ms.nonneg j).eq_or_lt with hy0 | hy_pos
                · simp [← hy0]
                · have hV'j : 0 < V' j := by
                    have := congrFun hy_eq j
                    simp only [Pi.smul_apply, smul_eq_mul] at this
                    rw [← this] at hy_pos
                    exact pos_of_mul_pos_right hy_pos (inv_pos.2 hV'_sum_pos).le
                  have hq'j : 0 < q' j := (div_pos_iff_of_pos_right (hcost'_inr j)).1 hV'j
                  rw [hUB'_eq j hq'j, mul_one]
          _ = 1 := hy_ms.sum_eq_one
      dsimp only [v₂]
      rw [G.payoff₂_eq_dotProduct, ← hx_eq, smul_vecMul, dotProduct_smul, smul_eq_mul, hdot,
        mul_one]
    ext i
    have h1 := congrFun hx_eq i
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    dsimp only [U]
    simp only [Pi.smul_apply, smul_eq_mul, hv₂_eq, inv_inv, ← h1]
    field_simp [hU'_sum_pos.ne']
  have hV'_eq_V : V' = V := by
    have hv₁_eq : v₁ = (∑ j : N, V' j)⁻¹ := by
      have hdot : x ⬝ᵥ (G.A *ᵥ V') = 1 := by
        calc x ⬝ᵥ (G.A *ᵥ V')
            = ∑ i : M, x i * (G.A *ᵥ V') i := rfl
          _ = ∑ i : M, x i := sum_congr rfl fun i _ => by
                rcases (hx_ms.nonneg i).eq_or_lt with hx0 | hx_pos
                · simp [← hx0]
                · have hU'i : 0 < U' i := by
                    have := congrFun hx_eq i
                    simp only [Pi.smul_apply, smul_eq_mul] at this
                    rw [← this] at hx_pos
                    exact pos_of_mul_pos_right hx_pos (inv_pos.2 hU'_sum_pos).le
                  have hp'i : 0 < p' i := (div_pos_iff_of_pos_right (hcost'_inl i)).1 hU'i
                  rw [hAV'_eq i hp'i, mul_one]
          _ = 1 := hx_ms.sum_eq_one
      dsimp only [v₁]
      rw [G.payoff₁_eq_dotProduct, ← hy_eq, mulVec_smul, dotProduct_smul, smul_eq_mul, hdot,
        mul_one]
    ext j
    have h1 := congrFun hy_eq j
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    dsimp only [V]
    simp only [Pi.smul_apply, smul_eq_mul, hv₁_eq, inv_inv, ← h1]
    field_simp [hV'_sum_pos.ne']
  -- Deduce `p' i = 0` off `S`, `q' j = 0` off `T`, and `2 • q'|_T` is stationary for `K = Q * P`.
  have hp'_eq : ∀ i, p' i = U i * (G.B *ᵥ q') i := fun i => by
    rw [← hU'_eq_U]
    exact (div_mul_cancel₀ (p' i) (hcost'_inl i).ne').symm
  have hq'_eq : ∀ j, q' j = V j * (p' ᵥ* G.A) j := fun j => by
    rw [← hV'_eq_V]
    exact (div_mul_cancel₀ (q' j) (hcost'_inr j).ne').symm
  have hp'_zero_off : ∀ i, i ∉ S → p' i = 0 := fun i hi => by
    have hx0 : x i = 0 := le_antisymm (not_lt.1 fun h => hi (mem_filter.2 ⟨mem_univ i, h⟩))
      (hx_ms.nonneg i)
    simp [hp'_eq i, U, hx0]
  have hq'_zero_off : ∀ j, j ∉ T → q' j = 0 := fun j hj => by
    have hy0 : y j = 0 := le_antisymm (not_lt.1 fun h => hj (mem_filter.2 ⟨mem_univ j, h⟩))
      (hy_ms.nonneg j)
    simp [hq'_eq j, V, hy0]
  let qT' : T → ℝ := fun j => 2 * q' j.1
  have hqT'_nn : ∀ j : T, 0 ≤ qT' j := fun j => mul_nonneg (by norm_num) (hq'_nn j.1)
  have hqT'_sum : ∑ j : T, qT' j = 1 := by
    calc ∑ j : T, 2 * q' j.1 = 2 * ∑ j ∈ T, q' j := by
            rw [← mul_sum, sum_coe_sort T q']
      _ = 2 * ∑ j : N, q' j := by
            rw [sum_subset (subset_univ T) fun j _ hj => hq'_zero_off j hj]
      _ = 1 := by rw [hsum_q'_half]; norm_num
  have hpS'_eq : ∀ i : S, (P *ᵥ qT') i = 2 * p' i.1 := fun i => by
    rw [hp'_eq i.1]
    simp only [mulVec, dotProduct, P, Matrix.of_apply, qT']
    calc ∑ j : T, U i.1 * G.B i.1 j.1 * (2 * q' j.1)
        = 2 * (U i.1 * ∑ j ∈ T, G.B i.1 j * q' j) := by
            rw [mul_sum, mul_sum, ← sum_coe_sort T fun j => 2 * (U i.1 * (G.B i.1 j * q' j))]
            exact sum_congr rfl fun j _ => by ring
      _ = 2 * (U i.1 * ∑ j : N, G.B i.1 j * q' j) := by
            congr 2
            exact sum_subset (subset_univ T) fun j _ hj => by simp [hq'_zero_off j hj]
  have hqT'_fix : K *ᵥ qT' = qT' := by
    have hK_mul : K *ᵥ qT' = Q *ᵥ (P *ᵥ qT') := (mulVec_mulVec qT' Q P).symm
    rw [hK_mul]
    ext j
    change ∑ i : S, Q j i * (P *ᵥ qT') i = qT' j
    rw [sum_congr rfl fun i _ => by rw [hpS'_eq i]]
    dsimp only [Q, Matrix.of_apply, qT']
    rw [hq'_eq j.1]
    calc ∑ i : S, V j.1 * G.A i.1 j.1 * (2 * p' i.1)
        = 2 * (V j.1 * ∑ i ∈ S, p' i * G.A i j.1) := by
            rw [mul_sum, mul_sum, ← sum_coe_sort S fun i => 2 * (V j.1 * (p' i * G.A i j.1))]
            exact sum_congr rfl fun i _ => by ring
      _ = 2 * (V j.1 * ∑ i : M, p' i * G.A i j.1) := by
            congr 2
            exact sum_subset (subset_univ S) fun i _ hi => by simp [hp'_zero_off i hi]
  have hqT'_eq_qT : qT' = qT := hqT_uniq qT' ⟨hqT'_nn, hqT'_sum, hqT'_fix⟩
  funext g
  cases g with
  | inl i =>
    change p' i = p i
    by_cases hi : i ∈ S
    · simp only [p, hi, ↓reduceDIte, pS]
      have h1 := hpS'_eq ⟨i, hi⟩
      rw [hqT'_eq_qT] at h1
      linarith
    · simp [p, hi, hp'_zero_off i hi]
  | inr j =>
    change q' j = q j
    by_cases hj : j ∈ T
    · simp only [q, hj, ↓reduceDIte]
      have h1 := congrFun hqT'_eq_qT ⟨j, hj⟩
      dsimp only [qT'] at h1
      linarith
    · simp [q, hj, hq'_zero_off j hj]

/-- **One-to-one correspondence between bimatrix Nash equilibria and normalized Leontief market
equilibrium prices** ([CodenottiVaradarajan2007], Section 6.5.2, p. 152;
Codenotti–Saberi–Varadarajan–Ye 2006). -/
noncomputable def bimatrixLeontiefNashEquivEquilibriumPrice [Nonempty M] [Nonempty N]
    (G : BimatrixGame M N) (hA : ∀ i j, 0 < G.A i j) (hB : ∀ i j, 0 < G.B i j) :
    {xy : (M → ℝ) × (N → ℝ) // G.IsNash xy.1 xy.2} ≃
      {π : M ⊕ N → ℝ // IsBimatrixLeontiefEquilibriumPrice G hA hB π} where
  toFun xy :=
    let hEx := bimatrixLeontiefMarket_existsUnique_equilibriumPrice_of_isNash
      (hA := hA) (hB := hB) xy.property
    ⟨hEx.choose, hEx.choose_spec.left.left⟩
  invFun π :=
    ⟨bimatrixLeontiefToStrategy G π.val,
      bimatrixLeontiefMarket_isNash_of_equilibriumPrice π.property.right.choose_spec⟩
  left_inv xy := by
    let hEx := bimatrixLeontiefMarket_existsUnique_equilibriumPrice_of_isNash
      (hA := hA) (hB := hB) xy.property
    exact Subtype.ext hEx.choose_spec.left.right
  right_inv π := by
    apply Subtype.ext
    have hnash : G.IsNash (bimatrixLeontiefToStrategy G π.val).1
        (bimatrixLeontiefToStrategy G π.val).2 :=
      bimatrixLeontiefMarket_isNash_of_equilibriumPrice π.property.right.choose_spec
    exact ((bimatrixLeontiefMarket_existsUnique_equilibriumPrice_of_isNash
      (hA := hA) (hB := hB) hnash).choose_spec.right π.val ⟨π.property, rfl⟩).symm

@[simp] theorem bimatrixLeontiefNashEquivEquilibriumPrice_symm_apply
    [Nonempty M] [Nonempty N] (G : BimatrixGame M N)
    (hA : ∀ i j, 0 < G.A i j) (hB : ∀ i j, 0 < G.B i j)
    (π : {π : M ⊕ N → ℝ // IsBimatrixLeontiefEquilibriumPrice G hA hB π}) :
    ((bimatrixLeontiefNashEquivEquilibriumPrice G hA hB).symm π).1 =
      bimatrixLeontiefToStrategy G π.1 := by rfl

end BimatrixCorrespondence

end Cslib.GameTheory.Market
