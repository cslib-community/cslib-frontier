/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.GameTheory.Strategic.Correlated
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Interdependent security games, tipping cascades, correlated equilibria, and Price of Anarchy

Kunreuther and Heal [KunreutherHeal2003] and Heal and Kunreuther [HealKunreuther2007] (surveyed in
[AndersonMooreNagarajaOzment2007], §25.2.1, p. 635) formalize **interdependent security (IDS)**:
each agent `i : ι` chooses whether to invest in security (`true`) at cost `investCost i` or remain
unprotected (`false`). Investment eliminates an agent's own direct disaster probability
`directProb i`, but an investing agent still remains exposed to stochastic **contagion**
(`contagion j i`) originating at each unprotected peer `j ≠ i`. Disasters are non-additive ("a house
only burns once"), so an unprotected agent incurs contagion loss `loss i` only on the event
`1 - directProb i` that no domestic disaster occurred.

## Main definitions

* `Cslib.GameTheory.InterdependentSecuritySpec`: general heterogeneous `ι`-agent Class 1 IDS
  specification (`directProb`, `loss`, `investCost`, `contagion`).
* `Cslib.GameTheory.InterdependentSecuritySpec.noContagionProb`, `contagionProb`, `criticalCost`,
  `toCostGame`: survival probability against peer contagion, contagion risk, critical investment
  threshold `p_i L_i ∏_{j ≠ i, ¬ s_j} (1 - r_{j, i})`, and induced `CostGame ι (fun _ => Bool)`.
* `Cslib.GameTheory.symmetricIDSSpec`: the identical-agent model of [KunreutherHeal2003], §2, with
  `contagion j i = p * q`.
* `Cslib.GameTheory.InterdependentSecuritySpec.bestResponse`, `IsCriticalCoalition`, `cascadeStep`,
  `TipsAll`: monotone best-response operator, one-step critical coalitions ([HealKunreuther2007],
  Definition 2), and multi-round domino tipping cascades ([HealKunreuther2007], §5.2).

## Main results

* `Cslib.GameTheory.InterdependentSecuritySpec.cost_update_false_sub_cost_update_true`,
  `Cslib.GameTheory.InterdependentSecuritySpec.isPureNash_toCostGame_iff`: unilateral switching gain
  equals `criticalCost i s - investCost i`, characterizing all pure Nash equilibria.
* `Cslib.GameTheory.symmetricIDSSpec_cost_allFalse_eq_geom_sum`,
  `Cslib.GameTheory.symmetricIDSSpec_criticalCost_eq_geom_sum`,
  `Cslib.GameTheory.tendsto_symmetricIDSSpec_cost_allFalse_atTop`,
  `Cslib.GameTheory.eventually_not_dominant_invest_symmetricIDSSpec` ([KunreutherHeal2003], §2,
  Proposition 1 and Corollary 1, pp. 7–8): geometric-series contagion formulas, convergence of
  unprotected expected loss to `L` as `n → ∞`, and eventual failure of dominant-strategy investment
  for every `c > 0`.
* `Cslib.GameTheory.eq_const_of_isPureNash_symmetricIDSSpec`,
  `Cslib.GameTheory.isCoarseCorrelatedEquilibrium_symmetricIDSSpec_taxed_unique`
  ([KunreutherHeal2003], §2–§3, pp. 9–13): every pure Nash equilibrium of the `n`-agent
  identical-agent IDS game with `c, p, q, L > 0` is symmetric (`all true` or `all false`), and any
  Pigouvian non-investment tax above `c - p L (1 - p q)^{n-1}` makes full investment the unique
  coarse correlated (and pure Nash) equilibrium.
* `Cslib.GameTheory.InterdependentSecuritySpec.criticalCost_mono`,
  `Cslib.GameTheory.InterdependentSecuritySpec.isPureNash_iterate_bestResponse_bot`,
  `Cslib.GameTheory.InterdependentSecuritySpec.exists_isPureNash`,
  `Cslib.GameTheory.InterdependentSecuritySpec.coexistence_pureNash_iff_and_pareto`
  ([HealKunreuther2007], §3, Theorems 1 and 2, pp. 8–9): strategic complementarity (`criticalCost`
  monotone in `s`), constructive pure-Nash existence in `|ι|` best-response rounds from `⊥`, and
  coexistence plus Pareto dominance of full investment over zero investment.
* `Cslib.GameTheory.InterdependentSecuritySpec.IsCriticalCoalition.tipsAll`,
  `Cslib.GameTheory.InterdependentSecuritySpec.isPureNash_allTrue_of_tipsAll`,
  `Cslib.GameTheory.InterdependentSecuritySpec.isCriticalCoalition_of_higher_contagion`
  ([HealKunreuther2007], §3.1, Theorem 3, and §5.2): domino tipping cascades, self-enforcing Nash
  persistence once the seed mandate is lifted, and greedy top-`k` externality optimality when
  higher-contagion agents have at least as high normalized reluctance `c_i / (p_i L_i)` (noting in
  the docstring and test suite why [HealKunreuther2007] Theorem 3's literal unaligned-cost
  statement omits checking `i ∈ M' \ M` in Appendix eq. (17)).
* `Cslib.GameTheory.InterdependentSecuritySpec.isCorrelatedEquilibrium_publicSignal`,
  `Cslib.GameTheory.symmetricIDSSpec_isMixedNash_and_correlated_strict_improvement` (original): in
  the multi-equilibrium regime, every public-signal mixture of `all true` and `all false` is a
  correlated equilibrium, and at the `2`-agent mixed-Nash marginal investment rate `θ`, public
  correlation strictly lowers every player's expected cost by `θ * (1 - θ) * p^2 * q * L > 0`.
* `Cslib.GameTheory.InterdependentSecuritySpec.isSmooth_toCostGame`,
  `Cslib.GameTheory.InterdependentSecuritySpec.expected_socialCost_le_of_isCCE`,
  `Cslib.GameTheory.symmetricIDSSpec_poa_eq_inv_one_sub`,
  `Cslib.GameTheory.symmetricIDSSpec_prisonersDilemma_socialCost_le` (original):
  `(1, μ)`-smoothness giving a robust `1 / (1 - μ)` Price-of-Anarchy bound over all coarse
  correlated equilibria (tight with equality `1 / (1 - q)` at `n = 2, p = 1`), alongside the
  `1 + (n - 1) * q` bound in the Prisoner's Dilemma regime `p * L < c`.

## References

* [R. Anderson, T. Moore, S. Nagaraja, and A. Ozment, *Incentives and Information
  Security*][AndersonMooreNagarajaOzment2007]
* [G. Heal and H. Kunreuther, *Modeling Interdependent Risks*][HealKunreuther2007]
* [H. Kunreuther and G. Heal, *Interdependent Security*][KunreutherHeal2003]
-/

public section

open Finset Function
open scoped Topology

namespace Cslib.GameTheory

/-- Parameters of a Class 1 **interdependent security (IDS) game** ([HealKunreuther2007], §3 & §5,
pp. 6–16; [KunreutherHeal2003], §2, pp. 3–8): each agent `i : ι` chooses `Bool` (`true` = invest in
protection at cost `investCost i`, `false` = remain unprotected with direct disaster probability
`directProb i` and loss `loss i`), while each unprotected peer `j ≠ i` independently contaminates
`i` with probability `contagion j i`. -/
structure InterdependentSecuritySpec (ι : Type*) where
  /-- Probability `p_i` of a direct domestic disaster at `i` when `i` does not invest. -/
  directProb : ι → ℝ
  /-- Loss magnitude `L_i` suffered by `i` if at least one disaster strikes `i`. -/
  loss : ι → ℝ
  /-- Upfront security expenditure `c_i` paid by `i` when `s i = true`. -/
  investCost : ι → ℝ
  /-- Probability `r_{j, i}` that an unprotected peer `j` originates and transmits damage to `i`. -/
  contagion : ι → ι → ℝ

/-- The identical-agent Kunreuther–Heal interdependent security model ([KunreutherHeal2003], §2,
pp. 3–8): every agent has direct disaster probability `p`, loss `L`, investment cost `c`, and
pairwise contagion probability `p * q` from each unprotected peer. -/
@[expose] def symmetricIDSSpec (ι : Type*) (p q L c : ℝ) : InterdependentSecuritySpec ι where
  directProb := fun _ => p
  loss := fun _ => L
  investCost := fun _ => c
  contagion := fun _ _ => p * q

namespace InterdependentSecuritySpec

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (G : InterdependentSecuritySpec ι)

/-- Probability `∏_{j ≠ i, s j = false} (1 - r_{j, i})` that no unprotected peer contaminates
agent `i`. -/
@[expose] def noContagionProb (i : ι) (s : ι → Bool) : ℝ :=
  ∏ j ∈ (univ.erase i).filter (fun j => !s j), (1 - G.contagion j i)

/-- Probability `1 - noContagionProb i s` that at least one unprotected peer contaminates `i`. -/
def contagionProb (i : ι) (s : ι → Bool) : ℝ :=
  1 - G.noContagionProb i s

/-- Critical protection cost `c_i(s_{-i}) = p_i L_i · noContagionProb i s` ([HealKunreuther2007],
eq. (3), p. 8; [KunreutherHeal2003], `c*(n - 1)`, p. 9): the expected loss reduction that agent `i`
obtains by switching from `false` to `true` against opponents' profile `s`. -/
@[expose] def criticalCost (i : ι) (s : ι → Bool) : ℝ :=
  G.directProb i * G.loss i * G.noContagionProb i s

/-- The strategic `CostGame` induced by `G`: investing pays `investCost i` plus expected contagion
loss `loss i * contagionProb i s`, whereas not investing incurs expected loss
`loss i * (directProb i + (1 - directProb i) * contagionProb i s)`. -/
@[expose] def toCostGame : CostGame ι (fun _ => Bool) where
  cost i s :=
    if s i then
      G.investCost i + G.loss i * G.contagionProb i s
    else
      G.loss i * (G.directProb i + (1 - G.directProb i) * G.contagionProb i s)

@[simp] theorem noContagionProb_update_self (i : ι) (s : ι → Bool) (b : Bool) :
    G.noContagionProb i (update s i b) = G.noContagionProb i s := by
  simp only [noContagionProb]
  congr 1
  refine filter_congr fun j hj => ?_
  rw [update_of_ne (ne_of_mem_erase hj)]

@[simp] theorem contagionProb_update_self (i : ι) (s : ι → Bool) (b : Bool) :
    G.contagionProb i (update s i b) = G.contagionProb i s := by
  simp only [contagionProb, noContagionProb_update_self]

@[simp] theorem noContagionProb_allTrue (i : ι) :
    G.noContagionProb i (fun _ => true) = 1 := by
  rw [noContagionProb, filter_false_of_mem (fun _ _ => by simp), prod_empty]

@[simp] theorem contagionProb_allTrue (i : ι) :
    G.contagionProb i (fun _ => true) = 0 := by
  simp only [contagionProb, noContagionProb_allTrue, sub_self]

@[simp] theorem criticalCost_allTrue (i : ι) :
    G.criticalCost i (fun _ => true) = G.directProb i * G.loss i := by
  simp only [criticalCost, noContagionProb_allTrue, mul_one]

/-- **Marginal benefit of security investment** ([HealKunreuther2007], eqs. (1)–(3), pp. 7–8):
unilaterally switching player `i` from `false` to `true` lowers `i`'s expected cost by
`criticalCost i s - investCost i`. -/
theorem cost_update_false_sub_cost_update_true (i : ι) (s : ι → Bool) :
    G.toCostGame.cost i (update s i false) - G.toCostGame.cost i (update s i true) =
      G.criticalCost i s - G.investCost i := by
  dsimp only [toCostGame]
  simp only [update_self, Bool.false_eq_true, ↓reduceIte, contagionProb,
    noContagionProb_update_self, criticalCost]
  ring

/-- **Pure-Nash characterization of IDS games** ([HealKunreuther2007], Definition 1, p. 8): a
profile `s` is a pure Nash equilibrium of `G.toCostGame` if and only if investing agents have
`investCost i ≤ criticalCost i s` and non-investing agents have
`criticalCost i s ≤ investCost i`. -/
theorem isPureNash_toCostGame_iff (s : ι → Bool) :
    G.toCostGame.IsPureNash s ↔
      ∀ i, (s i = true → G.investCost i ≤ G.criticalCost i s) ∧
        (s i = false → G.criticalCost i s ≤ G.investCost i) := by
  refine ⟨fun hN i => ⟨fun hT => ?_, fun hF => ?_⟩, fun h i b => ?_⟩
  · have hle := hN i false
    conv_lhs at hle => rw [← update_eq_self i s, hT]
    linarith [G.cost_update_false_sub_cost_update_true i s]
  · have hle := hN i true
    conv_lhs at hle => rw [← update_eq_self i s, hF]
    linarith [G.cost_update_false_sub_cost_update_true i s]
  · obtain ⟨hT, hF⟩ := h i
    cases hs : s i <;> cases b
    · rw [← hs, update_eq_self]
    · conv_lhs => rw [← update_eq_self i s, hs]
      linarith [hF hs, G.cost_update_false_sub_cost_update_true i s]
    · conv_lhs => rw [← update_eq_self i s, hs]
      linarith [hT hs, G.cost_update_false_sub_cost_update_true i s]
    · rw [← hs, update_eq_self]

theorem isPureNash_allTrue_iff :
    G.toCostGame.IsPureNash (fun _ => true) ↔ ∀ i, G.investCost i ≤ G.directProb i * G.loss i := by
  rw [G.isPureNash_toCostGame_iff]
  simp only [Bool.true_eq_false, IsEmpty.forall_iff, and_true, forall_const, criticalCost_allTrue]

theorem isPureNash_allFalse_iff :
    G.toCostGame.IsPureNash (fun _ => false) ↔
      ∀ i, G.criticalCost i (fun _ => false) ≤ G.investCost i := by
  rw [G.isPureNash_toCostGame_iff]
  simp only [Bool.false_eq_true, IsEmpty.forall_iff, true_and, forall_const]

/-! ### Supermodularity, constructive Nash existence, coexistence, and tipping cascades -/

theorem noContagionProb_le_one (h0 : ∀ j i, 0 ≤ G.contagion j i)
    (h1 : ∀ j i, G.contagion j i ≤ 1) (i : ι) (s : ι → Bool) :
    G.noContagionProb i s ≤ 1 :=
  prod_le_one₀ (fun j _ => sub_nonneg.mpr (h1 j i)) fun j _ => sub_le_self 1 (h0 j i)

/-- **Strategic complementarity / supermodularity** ([HealKunreuther2007], §3, p. 8): as more peers
invest (`s ≤ s'` pointwise in `Bool`), the probability of escaping contagion and the critical
protection cost `criticalCost i s` increase monotonically. -/
theorem noContagionProb_mono (h0 : ∀ j i, 0 ≤ G.contagion j i)
    (h1 : ∀ j i, G.contagion j i ≤ 1) (i : ι) :
    Monotone (G.noContagionProb i) := by
  intro s s' hss'
  simp only [noContagionProb]
  have hsub : (univ.erase i).filter (fun j => !s' j) ⊆ (univ.erase i).filter (fun j => !s j) := by
    intro j hj
    simp only [mem_filter] at hj ⊢
    refine ⟨hj.1, ?_⟩
    cases hsj : s j
    · rfl
    · have : true ≤ s' j := hsj ▸ hss' j
      have hs'j : s' j = true := le_antisymm (Bool.le_true _) this
      simp only [hs'j, Bool.not_true, Bool.false_eq_true, and_false] at hj
  exact prod_le_prod_of_subset_of_le_one₀ hsub
    (fun j _ => sub_nonneg.mpr (h1 j i))
    (fun j _ _ => sub_le_self 1 (h0 j i))

theorem criticalCost_mono (hp : ∀ i, 0 ≤ G.directProb i) (hL : ∀ i, 0 ≤ G.loss i)
    (h0 : ∀ j i, 0 ≤ G.contagion j i) (h1 : ∀ j i, G.contagion j i ≤ 1) (i : ι) :
    Monotone (G.criticalCost i) := fun _ _ hss' =>
  mul_le_mul_of_nonneg_left (G.noContagionProb_mono h0 h1 i hss') (mul_nonneg (hp i) (hL i))

/-- Synchronous deterministic best-response map: player `i` invests iff
`investCost i ≤ criticalCost i s`. -/
noncomputable def bestResponse (s : ι → Bool) : ι → Bool :=
  fun i => decide (G.investCost i ≤ G.criticalCost i s)

theorem bestResponse_mono (hp : ∀ i, 0 ≤ G.directProb i) (hL : ∀ i, 0 ≤ G.loss i)
    (h0 : ∀ j i, 0 ≤ G.contagion j i) (h1 : ∀ j i, G.contagion j i ≤ 1) :
    Monotone G.bestResponse := by
  intro s s' hss' i
  simp only [bestResponse]
  by_cases h : G.investCost i ≤ G.criticalCost i s
  · have h' : G.investCost i ≤ G.criticalCost i s' :=
      h.trans (G.criticalCost_mono hp hL h0 h1 i hss')
    simp only [h, h', decide_true, le_rfl]
  · simp only [h, decide_false, Bool.false_le]

theorem isPureNash_of_bestResponse_eq {s : ι → Bool} (hfp : G.bestResponse s = s) :
    G.toCostGame.IsPureNash s := by
  rw [G.isPureNash_toCostGame_iff]
  intro i
  have hi := congrFun hfp i
  simp only [bestResponse] at hi
  refine ⟨fun hT => ?_, fun hF => ?_⟩
  · rw [hT, decide_eq_true_eq] at hi
    exact hi
  · rw [hF, decide_eq_false_iff_not] at hi
    exact le_of_lt (lt_of_not_ge hi)

omit [DecidableEq ι] in
/-- Iterating any monotone map `f : (ι → Bool) → (ι → Bool)` from a profile `s₀` with `s₀ ≤ f s₀`
stabilizes at a fixed point after `Fintype.card ι` rounds. -/
private theorem iterate_fixed_of_monotone_extensive {f : (ι → Bool) → (ι → Bool)}
    (hf : Monotone f) {s₀ : ι → Bool} (h0 : s₀ ≤ f s₀) :
    f (f^[Fintype.card ι] s₀) = f^[Fintype.card ι] s₀ := by
  classical
  have hchain : ∀ k, f^[k] s₀ ≤ f^[k + 1] s₀ := fun k => by
    induction k with
    | zero => exact h0
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply' f (k + 1)]
      exact hf ih
  by_contra hne
  -- Strict growth at step `Fintype.card ι` implies strict growth at every earlier step `k < |ι|`.
  have hstrict : ∀ k ≤ Fintype.card ι + 1, k ≤ (univ.filter fun i => f^[k] s₀ i = true).card := by
    intro k hk
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have hne_k : f^[k] s₀ ≠ f^[k + 1] s₀ := fun heq => hne <| by
        have hfix : ∀ m, f^[k + m] s₀ = f^[k] s₀ := fun m => by
          induction m with
          | zero => rfl
          | succ m ihm =>
            rw [← Nat.add_assoc, Function.iterate_succ_apply', ihm,
              ← Function.iterate_succ_apply' f k s₀, heq]
        have h1 := hfix (Fintype.card ι - k)
        rw [Nat.add_sub_of_le (Nat.le_of_succ_le_succ hk)] at h1
        rw [h1]
        exact (Function.iterate_succ_apply' f k s₀).symm.trans heq.symm
      have hsub : (univ.filter fun i => f^[k] s₀ i = true) ⊆
          (univ.filter fun i => f^[k + 1] s₀ i = true) := fun i hi => by
        simp only [mem_filter, mem_univ, true_and] at hi ⊢
        exact le_antisymm (Bool.le_true _) (hi ▸ hchain k i)
      have hne_set : (univ.filter fun i => f^[k] s₀ i = true) ≠
          (univ.filter fun i => f^[k + 1] s₀ i = true) := fun hset => hne_k <| funext fun i =>
        Bool.eq_iff_iff.mpr
          (by simpa only [mem_filter, mem_univ, true_and] using Finset.ext_iff.mp hset i)
      exact Nat.succ_le_of_lt (lt_of_le_of_lt (ih (Nat.le_of_succ_le hk))
        (card_lt_card (ssubset_of_subset_of_ne hsub hne_set)))
  -- At step `|ι|`, all coordinates are already `true`, so step `|ι| + 1` cannot strictly grow.
  have hle := (hstrict (Fintype.card ι + 1) le_rfl).trans (card_filter_le _ _)
  rw [card_univ] at hle
  omega

/-- **Heal–Kunreuther Theorem 1, constructive least pure Nash equilibrium**
([HealKunreuther2007], §3, Theorem 1, p. 9): iterating synchronous best response `|ι|` times from
`fun _ => false` produces a pure Nash equilibrium of `G.toCostGame`. -/
theorem isPureNash_iterate_bestResponse_bot (hp : ∀ i, 0 ≤ G.directProb i)
    (hL : ∀ i, 0 ≤ G.loss i) (h0 : ∀ j i, 0 ≤ G.contagion j i)
    (h1 : ∀ j i, G.contagion j i ≤ 1) :
    G.toCostGame.IsPureNash (G.bestResponse^[Fintype.card ι] (fun _ => false)) :=
  G.isPureNash_of_bestResponse_eq <|
    iterate_fixed_of_monotone_extensive (G.bestResponse_mono hp hL h0 h1) fun _ => Bool.false_le _

/-- **Heal–Kunreuther Theorem 1, existence** ([HealKunreuther2007], §3, Theorem 1, p. 9): every
finite Class 1 interdependent security game has a pure Nash equilibrium. -/
theorem exists_isPureNash (hp : ∀ i, 0 ≤ G.directProb i) (hL : ∀ i, 0 ≤ G.loss i)
    (h0 : ∀ j i, 0 ≤ G.contagion j i) (h1 : ∀ j i, G.contagion j i ≤ 1) :
    ∃ s, G.toCostGame.IsPureNash s :=
  ⟨_, G.isPureNash_iterate_bestResponse_bot hp hL h0 h1⟩

/-- **Heal–Kunreuther Theorem 2, coexistence and Pareto dominance** ([HealKunreuther2007], §3,
Theorem 2, p. 9, and Appendix, p. 20): both `fun _ => true` and `fun _ => false` are pure Nash
equilibria if and only if `criticalCost i (fun _ => false) ≤ investCost i ≤ directProb i * loss i`
for all `i`; whenever `fun _ => true` is a pure Nash equilibrium, it Pareto-dominates
`fun _ => false`. -/
theorem coexistence_pureNash_iff_and_pareto (hp1 : ∀ i, G.directProb i ≤ 1)
    (hL : ∀ i, 0 ≤ G.loss i) (h0 : ∀ j i, 0 ≤ G.contagion j i)
    (h1 : ∀ j i, G.contagion j i ≤ 1) :
    ((G.toCostGame.IsPureNash (fun _ => true) ∧ G.toCostGame.IsPureNash (fun _ => false)) ↔
      ∀ i, G.criticalCost i (fun _ => false) ≤ G.investCost i ∧
        G.investCost i ≤ G.directProb i * G.loss i) ∧
    (G.toCostGame.IsPureNash (fun _ => true) →
      ∀ i, G.toCostGame.cost i (fun _ => true) ≤ G.toCostGame.cost i (fun _ => false)) := by
  refine ⟨?_, fun hTrue i => ?_⟩
  · rw [G.isPureNash_allTrue_iff, G.isPureNash_allFalse_iff]
    exact ⟨fun ⟨h1, h2⟩ i => ⟨h2 i, h1 i⟩, fun h => ⟨fun i => (h i).2, fun i => (h i).1⟩⟩
  · have hc := G.isPureNash_allTrue_iff.mp hTrue i
    have hcont_nonneg : 0 ≤ G.contagionProb i (fun _ => false) :=
      sub_nonneg.mpr (G.noContagionProb_le_one h0 h1 i _)
    have hextra : 0 ≤ G.loss i * ((1 - G.directProb i) * G.contagionProb i (fun _ => false)) :=
      mul_nonneg (hL i) (mul_nonneg (sub_nonneg.mpr (hp1 i)) hcont_nonneg)
    simp only [toCostGame, ↓reduceIte, Bool.false_eq_true, contagionProb_allTrue, mul_zero,
      add_zero]
    linarith

/-- A **critical coalition** ([HealKunreuther2007], §3.1, Definition 2, p. 9): when every member of
`M` invests (`true`), investing becomes an immediate best response for every non-member `j ∉ M`. -/
@[expose] def IsCriticalCoalition (M : Finset ι) : Prop :=
  ∀ j, j ∉ M → G.investCost j ≤ G.criticalCost j (fun i => decide (i ∈ M))

/-- One synchronous wave of a **tipping cascade** seeded by `M` ([HealKunreuther2007], §5.2,
pp. 15–16): members of `M` stay committed to `true`, while every other agent best-responds. -/
@[expose] noncomputable def cascadeStep (M : Finset ι) (s : ι → Bool) : ι → Bool :=
  fun i => decide (i ∈ M) || decide (G.investCost i ≤ G.criticalCost i s)

/-- Coalition `M` **tips the entire population** if iterating `cascadeStep M` from the seed profile
`fun i => decide (i ∈ M)` reaches universal investment `fun _ => true` within `|ι|` waves. -/
@[expose] def TipsAll (M : Finset ι) : Prop :=
  (G.cascadeStep M)^[Fintype.card ι] (fun i => decide (i ∈ M)) = fun _ => true

theorem cascadeStep_mono (hp : ∀ i, 0 ≤ G.directProb i) (hL : ∀ i, 0 ≤ G.loss i)
    (h0 : ∀ j i, 0 ≤ G.contagion j i) (h1 : ∀ j i, G.contagion j i ≤ 1) (M : Finset ι) :
    Monotone (G.cascadeStep M) := by
  intro s s' hss' i
  simp only [cascadeStep]
  cases decide (i ∈ M)
  · simp only [Bool.false_or]
    exact G.bestResponse_mono hp hL h0 h1 hss' i
  · simp only [Bool.true_or, le_rfl]

/-- Every one-step critical coalition tips the entire population in a cascade. -/
theorem IsCriticalCoalition.tipsAll (hp : ∀ i, 0 ≤ G.directProb i) (hL : ∀ i, 0 ≤ G.loss i)
    (h0 : ∀ j i, 0 ≤ G.contagion j i) (h1 : ∀ j i, G.contagion j i ≤ 1)
    {M : Finset ι} (hM : G.IsCriticalCoalition M) : G.TipsAll M := by
  have h1step : G.cascadeStep M (fun i => decide (i ∈ M)) = fun _ => true := by
    ext j
    by_cases hj : j ∈ M <;> simp [cascadeStep, hj, hM j]
  have htop : G.cascadeStep M (fun _ => true) = fun _ => true := by
    have hle := G.cascadeStep_mono hp hL h0 h1 M
      (a := fun i => decide (i ∈ M)) (b := fun _ => true) fun _ => Bool.le_true _
    rw [h1step] at hle
    exact le_antisymm (fun _ => Bool.le_true _) hle
  rcases hcard : Fintype.card ι with _ | k
  · ext i
    exact (Fintype.card_eq_zero_iff.mp hcard).elim i
  · unfold TipsAll
    rw [hcard, Function.iterate_succ_apply, h1step]
    clear hcard
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, htop]

/-- **Self-enforcing persistence after tipping**: if a coalition `M` whose own members satisfy
`investCost m ≤ directProb m * loss m` triggers a full cascade (`TipsAll M`), then `fun _ => true`
is a pure Nash equilibrium of the unmodified game `G.toCostGame` even after the mandate on `M` is
removed. -/
theorem isPureNash_allTrue_of_tipsAll (hp : ∀ i, 0 ≤ G.directProb i) (hL : ∀ i, 0 ≤ G.loss i)
    (h0 : ∀ j i, 0 ≤ G.contagion j i) (h1 : ∀ j i, G.contagion j i ≤ 1)
    {M : Finset ι} (hTips : G.TipsAll M)
    (hSeed : ∀ m ∈ M, G.investCost m ≤ G.directProb m * G.loss m) :
    G.toCostGame.IsPureNash (fun _ => true) := by
  rw [G.isPureNash_allTrue_iff]
  intro i
  by_cases hi : i ∈ M
  · exact hSeed i hi
  · have hfix := iterate_fixed_of_monotone_extensive (G.cascadeStep_mono hp hL h0 h1 M)
      (s₀ := fun k => decide (k ∈ M)) fun j => by
        simp only [cascadeStep]
        cases decide (j ∈ M) <;> simp
    rw [hTips] at hfix
    have hi_eq := congrFun hfix i
    simp only [cascadeStep, hi, decide_false, Bool.false_or, criticalCost_allTrue,
      decide_eq_true_eq] at hi_eq
    exact hi_eq

/-- **Heal–Kunreuther Theorem 3, corrected greedy top-`k` critical coalition theorem**
([HealKunreuther2007], §3.1, Theorem 3, p. 10, and Appendix, p. 20): under agent-uniform contagion
rates `contagion j i = qExt j` (`qExt j ≤ 1`), if `M` and `M'` have equal size
`M.card = M'.card` such that every `j ∈ M \ M'` generates at least as much contagion as every
`k ∈ M' \ M` (`qExt k ≤ qExt j`), and higher-contagion agents replaced by `M` also have at least as
high normalized reluctance `investCost / (directProb * loss)` (`c_k / (p_k L_k) ≤ c_j / (p_j L_j)`
for `k ∈ M' \ M`, `j ∈ M \ M'`, which holds automatically under identical `(p, L, c)`), then
`G.IsCriticalCoalition M'` implies `G.IsCriticalCoalition M`.

Note on [HealKunreuther2007], Appendix eq. (17), p. 20: the published proof checks only agents
`i > k` outside `M ∪ M'`, overlooking replaced members `k ∈ M' \ M` whose arbitrary `investCost k`
was bypassed while inside `M'`. Without the normalized-reluctance alignment on `M' \ M` vs.
`M \ M'`, both 1-step `IsCriticalCoalition` and multi-step `TipsAll` can fail on `3`- and `4`-agent
instances even when both `(all false)` and `(all true)` are strict pure Nash equilibria (checked in
`CslibFrontierTests.GameTheory.SecurityEconomics`). -/
theorem isCriticalCoalition_of_higher_contagion {qExt : ι → ℝ}
    (hp : ∀ i, 0 < G.directProb i) (hL : ∀ i, 0 < G.loss i)
    (hContagion : ∀ j i, j ≠ i → G.contagion j i = qExt j) (hq1 : ∀ j, qExt j ≤ 1)
    {M M' : Finset ι} (hcard : M.card = M'.card)
    (hDom : ∀ j ∈ M \ M', ∀ k ∈ M' \ M, qExt k ≤ qExt j)
    (hReluct : ∀ j ∈ M \ M', ∀ k ∈ M' \ M,
      G.investCost k / (G.directProb k * G.loss k) ≤
        G.investCost j / (G.directProb j * G.loss j))
    (hCrit : G.IsCriticalCoalition M') : G.IsCriticalCoalition M := by
  -- Helper rewriting `noContagionProb i (seed S)` as `∏ u ∈ univ \ (insert i S), (1 - qExt u)`.
  have hprod_eq : ∀ (S : Finset ι) (i : ι),
      G.noContagionProb i (fun u => decide (u ∈ S)) = ∏ u ∈ univ \ insert i S, (1 - qExt u) :=
    fun S i => by
      simp only [noContagionProb]
      have hset : (univ.erase i).filter (fun j => !decide (j ∈ S)) = univ \ insert i S := by
        ext u
        simp only [mem_filter, mem_erase, mem_sdiff, mem_insert, mem_univ, Bool.not_eq_true',
          decide_eq_false_iff_not, not_or, and_true, true_and]
      rw [hset]
      exact prod_congr rfl fun u hu => by
        rw [hContagion u i fun h => (mem_sdiff.mp hu).2 (mem_insert.mpr (Or.inl h))]
  -- Equal-cardinality domination implies `∏ u ∈ A, (1 - qExt u) ≤ ∏ u ∈ B, (1 - qExt u)` whenever
  -- `B \ A` has smaller `1 - qExt` (larger `qExt`) than `A \ B`, so removing `M` leaves larger
  -- `(1 - qExt)` factors outside `M` than outside `M'`.
  have hbij_prod : ∀ (X Y : Finset ι), X.card = Y.card →
      (∀ x ∈ X, ∀ y ∈ Y, qExt y ≤ qExt x) →
      ∏ x ∈ X, (1 - qExt x) ≤ ∏ y ∈ Y, (1 - qExt y) := by
    intro X Y hXY hOrd
    have hbij := Finset.equivOfCardEq hXY
    rw [← prod_coe_sort Y,
      ← Fintype.prod_equiv hbij (fun x => 1 - qExt (hbij x).1) (fun y => 1 - qExt y.1)
        (fun _ => rfl),
      ← prod_coe_sort X]
    exact prod_le_prod₀ (fun x _ => sub_nonneg.mpr (hq1 x.1))
      fun x _ => sub_le_sub_left (hOrd x.1 x.2 (hbij x).1 (hbij x).2) 1
  -- Multiply both sides by the common complement `univ \ (insert i M ∪ insert j M')`.
  have hcompl : ∀ A B : Finset ι, A.card = B.card → A \ B ⊆ M \ M' → B \ A ⊆ M' \ M →
      ∏ u ∈ univ \ B, (1 - qExt u) ≤ ∏ u ∈ univ \ A, (1 - qExt u) := by
    have hsplit : ∀ S T : Finset ι, ∏ u ∈ univ \ S, (1 - qExt u) =
        (∏ u ∈ T \ S, (1 - qExt u)) * ∏ u ∈ univ \ (T ∪ S), (1 - qExt u) := fun S T => by
      have hset : (univ \ S) \ (univ \ (T ∪ S)) = T \ S := by
        ext
        simp only [mem_sdiff, mem_univ, true_and, mem_union, not_or]
        tauto
      rw [← prod_sdiff (sdiff_subset_sdiff (subset_refl univ) subset_union_right), hset]
    intro A B hAB hA hB
    rw [hsplit B A, hsplit A B, union_comm B A]
    exact mul_le_mul_of_nonneg_right (hbij_prod _ _ (card_sdiff_comm hAB)
      fun x hx y hy => hDom x (hA hx) y (hB hy)) (prod_nonneg fun u _ => sub_nonneg.mpr (hq1 u))
  intro i hiM
  -- Compare `noContagionProb i (seed M)` with `noContagionProb j (seed M')`.
  -- `(univ.erase j) \ M'` vs `(univ.erase i) \ M`:
  -- Note `(univ \ insert j M')` vs `(univ \ insert i M)`!
  -- Specifically, `insert i M = insert i ((M ∩ M') ∪ (M \ M'))` and
  -- `insert j M' = insert j ((M ∩ M') ∪ (M' \ M))`.
  obtain ⟨j, hjM', hcardAB, hA, hB, hrel⟩ : ∃ j, j ∉ M' ∧
      (insert i M).card = (insert j M').card ∧ insert i M \ insert j M' ⊆ M \ M' ∧
      insert j M' \ insert i M ⊆ M' \ M ∧ G.investCost i / (G.directProb i * G.loss i) ≤
        G.investCost j / (G.directProb j * G.loss j) := by
    by_cases hiM' : i ∈ M'
    · -- `i ∈ M' \ M`: choose `j ∈ M \ M'` (nonempty since `i ∈ M' \ M` and `|M \ M'| = |M' \ M|`).
      obtain ⟨j, hj⟩ := card_pos.mp ((card_sdiff_comm hcard).symm ▸
        card_pos.mpr ⟨i, mem_sdiff.mpr ⟨hiM', hiM⟩⟩ : 0 < (M \ M').card)
      obtain ⟨hjM, hjM'⟩ := mem_sdiff.mp hj
      refine ⟨j, hjM', by rw [card_insert_of_notMem hiM, card_insert_of_notMem hjM', hcard],
        fun u hu => ?_, fun u hu => ?_, hReluct j hj i (mem_sdiff.mpr ⟨hiM', hiM⟩)⟩
      · simp only [mem_sdiff, mem_insert, not_or] at hu ⊢
        obtain ⟨rfl | huM, -, hu'⟩ := hu
        exacts [absurd hiM' hu', ⟨huM, hu'⟩]
      · simp only [mem_sdiff, mem_insert, not_or] at hu ⊢
        obtain ⟨rfl | huM', -, hu'⟩ := hu
        exacts [absurd hjM hu', ⟨huM', hu'⟩]
    · -- `i ∉ M ∪ M'`: `M'` already tipped `i`, and `M` removes larger `qExt` than `M'`.
      refine ⟨i, hiM', by rw [card_insert_of_notMem hiM, card_insert_of_notMem hiM', hcard],
        fun u hu => ?_, fun u hu => ?_, le_rfl⟩ <;>
        simp only [mem_sdiff, mem_insert, not_or] at hu ⊢ <;>
        exact ⟨hu.1.resolve_left hu.2.1, hu.2.2⟩
  have hi_div : G.investCost i / (G.directProb i * G.loss i) ≤
      G.noContagionProb i (fun u => decide (u ∈ M)) :=
    calc G.investCost i / (G.directProb i * G.loss i)
        ≤ G.investCost j / (G.directProb j * G.loss j) := hrel
      _ ≤ G.noContagionProb j (fun u => decide (u ∈ M')) := by
          rw [div_le_iff₀ (mul_pos (hp j) (hL j)), mul_comm]
          simpa only [criticalCost] using hCrit j hjM'
      _ ≤ G.noContagionProb i (fun u => decide (u ∈ M)) := by
          rw [hprod_eq, hprod_eq]
          exact hcompl _ _ hcardAB hA hB
  rw [criticalCost, mul_comm, ← div_le_iff₀ (mul_pos (hp i) (hL i))]
  exact hi_div

/-! ### Correlated equilibria and Roughgarden `(1, μ)`-smoothness / Price of Anarchy -/

/-- **Public-signal correlated equilibrium** in the multi-equilibrium IDS regime (original):
whenever both `fun _ => true` and `fun _ => false` are pure Nash equilibria, every convex mixture
`α • δ_{all true} + (1 - α) • δ_{all false}` (`0 ≤ α ≤ 1`) is a correlated equilibrium of
`G.toCostGame`. -/
theorem isCorrelatedEquilibrium_publicSignal
    (hTrue : G.toCostGame.IsPureNash (fun _ => true))
    (hFalse : G.toCostGame.IsPureNash (fun _ => false))
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    G.toCostGame.IsCorrelatedEquilibrium
      (.duple (fun _ => true) (fun _ => false)
        (s := α) (t := 1 - α) hα0 (by linarith) (by ring)) :=
  hTrue.isCorrelatedEquilibrium_duple hFalse hα0 (by linarith) (by ring)

/-- Union bound on peer contagion: `contagionProb i s` is at most the sum of contagion rates from
unprotected peers `j ≠ i`. -/
theorem contagionProb_le_sum (h0 : ∀ j i, 0 ≤ G.contagion j i)
    (h1 : ∀ j i, G.contagion j i ≤ 1) (i : ι) (s : ι → Bool) :
    G.contagionProb i s ≤ ∑ j ∈ (univ.erase i).filter (fun j => !s j), G.contagion j i := by
  simp only [contagionProb, noContagionProb]
  set S := (univ.erase i).filter (fun j => !s j)
  induction S using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [prod_insert ha, sum_insert ha]
    have hT_nonneg : 0 ≤ ∏ j ∈ T, (1 - G.contagion j i) :=
      prod_nonneg fun j _ => sub_nonneg.mpr (h1 j i)
    have ha0 : 0 ≤ G.contagion a i := h0 a i
    have ha1 : G.contagion a i ≤ 1 := h1 a i
    -- `1 - (1 - r_a) P_T = r_a P_T + (1 - P_T) ≤ r_a + (1 - P_T)` since `P_T ≤ 1`.
    have hT_le_one : ∏ j ∈ T, (1 - G.contagion j i) ≤ 1 :=
      prod_le_one₀ (fun j _ => sub_nonneg.mpr (h1 j i)) fun j _ => sub_le_self 1 (h0 j i)
    nlinarith

/-- **`(1, μ)`-smoothness of heterogeneous interdependent security games** (original): if the
expected contagion damages `∑ i ≠ j, contagion j i * loss i` generated by each unprotected agent `j`
are at most `μ` times `j`'s own expected direct loss `directProb j * loss j`, then `G.toCostGame` is
`(1, μ)`-smooth in Roughgarden's framework (`CostGame.IsSmooth 1 μ`). -/
theorem isSmooth_toCostGame {μ : ℝ}
    (hp0 : ∀ i, 0 ≤ G.directProb i) (hp1 : ∀ i, G.directProb i ≤ 1)
    (hL : ∀ i, 0 ≤ G.loss i) (hc : ∀ i, 0 ≤ G.investCost i)
    (h0 : ∀ j i, 0 ≤ G.contagion j i) (h1 : ∀ j i, G.contagion j i ≤ 1)
    (hμ0 : 0 ≤ μ)
    (hExt : ∀ j, ∑ i ∈ univ.erase j, G.contagion j i * G.loss i ≤
      μ * (G.directProb j * G.loss j)) :
    G.toCostGame.IsSmooth 1 μ := by
  intro s s'
  -- Step 1: Bound each unilateral deviation `cost i (update s i (s' i))` by `cost i s'` plus
  -- additive contagion losses from unprotected peers under `s`.
  have hpt : ∀ i : ι,
      G.toCostGame.cost i (update s i (s' i)) ≤
        G.toCostGame.cost i s' +
          ∑ j ∈ (univ.erase i).filter (fun j => !s j), G.contagion j i * G.loss i := fun i => by
    have hub := mul_le_mul_of_nonneg_left (G.contagionProb_le_sum h0 h1 i s) (hL i)
    rw [mul_sum] at hub
    have hub' : G.loss i * G.contagionProb i s ≤
        ∑ j ∈ (univ.erase i).filter (fun j => !s j), G.contagion j i * G.loss i := by
      simpa only [mul_comm (G.loss i)] using hub
    have hcont_s'_nonneg : 0 ≤ G.loss i * G.contagionProb i s' :=
      mul_nonneg (hL i) (sub_nonneg.mpr (G.noContagionProb_le_one h0 h1 i s'))
    cases hs' : s' i
    · -- `s' i = false`
      simp only [toCostGame, update_self, hs', Bool.false_eq_true, ↓reduceIte,
        contagionProb_update_self]
      have h1_sub : 1 - G.directProb i ≤ 1 := sub_le_self 1 (hp0 i)
      have hcont_s_nonneg : 0 ≤ G.contagionProb i s :=
        sub_nonneg.mpr (G.noContagionProb_le_one h0 h1 i s)
      have hscale : G.loss i * ((1 - G.directProb i) * G.contagionProb i s) ≤
          G.loss i * G.contagionProb i s :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hcont_s_nonneg h1_sub) (hL i)
      have hextra_s' : 0 ≤ G.loss i * ((1 - G.directProb i) * G.contagionProb i s') :=
        mul_nonneg (hL i) (mul_nonneg (sub_nonneg.mpr (hp1 i))
          (sub_nonneg.mpr (G.noContagionProb_le_one h0 h1 i s')))
      linarith [hscale, hextra_s']
    · -- `s' i = true`
      simp only [toCostGame, update_self, hs', ↓reduceIte, contagionProb_update_self]
      linarith
  -- Step 2: Sum over `i` and swap double sum to group by unprotected source `j`.
  have hsum1 : ∑ i, G.toCostGame.cost i (update s i (s' i)) ≤
      G.toCostGame.socialCost s' +
        ∑ i, ∑ j ∈ (univ.erase i).filter (fun j => !s j), G.contagion j i * G.loss i := by
    simpa only [CostGame.socialCost, sum_add_distrib] using sum_le_sum fun i _ => hpt i
  have hswap : (∑ i, ∑ j ∈ (univ.erase i).filter (fun j => !s j), G.contagion j i * G.loss i) =
      ∑ j ∈ univ.filter (fun j => !s j), ∑ i ∈ univ.erase j, G.contagion j i * G.loss i := by
    have he : ∀ a : ι, univ.erase a = univ.filter (· ≠ a) := fun a => by
      ext
      simp [and_comm]
    simp only [he, filter_filter, sum_filter]
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    by_cases hsj : (!s j) = true <;> simp [hsj, ne_comm]
  -- Step 3: For each `j` with `!s j`, `directProb j * loss j ≤ cost j s`, while investing `j` have
  -- `0 ≤ μ * cost j s`.
  have hbound_j : ∑ j ∈ univ.filter (fun j => !s j),
      (∑ i ∈ univ.erase j, G.contagion j i * G.loss i) ≤ μ * G.toCostGame.socialCost s := by
    calc ∑ j ∈ univ.filter (fun j => !s j), ∑ i ∈ univ.erase j, G.contagion j i * G.loss i
        ≤ ∑ j ∈ univ.filter (fun j => !s j), μ * G.toCostGame.cost j s := by
          refine sum_le_sum fun j hj => ?_
          have hsj : s j = false := by
            have := (mem_filter.mp hj).2
            simpa only [Bool.not_eq_true'] using this
          have hcj : G.directProb j * G.loss j ≤ G.toCostGame.cost j s := by
            simp only [toCostGame, hsj, Bool.false_eq_true, ↓reduceIte]
            have hextra : 0 ≤ G.loss j * ((1 - G.directProb j) * G.contagionProb j s) :=
              mul_nonneg (hL j) (mul_nonneg (sub_nonneg.mpr (hp1 j))
                (sub_nonneg.mpr (G.noContagionProb_le_one h0 h1 j s)))
            linarith
          exact (hExt j).trans (mul_le_mul_of_nonneg_left hcj hμ0)
      _ ≤ ∑ j, μ * G.toCostGame.cost j s := by
          refine sum_le_univ_sum_of_nonneg fun j => mul_nonneg hμ0 ?_
          simp only [toCostGame]
          split_ifs
          · exact add_nonneg (hc j)
              (mul_nonneg (hL j) (sub_nonneg.mpr (G.noContagionProb_le_one h0 h1 j s)))
          · exact mul_nonneg (hL j) (add_nonneg (hp0 j) (mul_nonneg (sub_nonneg.mpr (hp1 j))
              (sub_nonneg.mpr (G.noContagionProb_le_one h0 h1 j s))))
      _ = μ * G.toCostGame.socialCost s := by rw [← mul_sum]; rfl
  rw [one_mul]
  linarith [hsum1, hswap, hbound_j]

/-- **Robust `1 / (1 - μ)` Price of Anarchy for coarse correlated equilibria** (original) of
interdependent security games: when `μ < 1` bounds each agent's outgoing contagion-to-direct-loss
ratio, every coarse correlated equilibrium `σ` has expected social cost at most
`1 / (1 - μ) * socialCost s'`. -/
theorem expected_socialCost_le_of_isCCE {μ : ℝ}
    (hp0 : ∀ i, 0 ≤ G.directProb i) (hp1 : ∀ i, G.directProb i ≤ 1)
    (hL : ∀ i, 0 ≤ G.loss i) (hc : ∀ i, 0 ≤ G.investCost i)
    (h0 : ∀ j i, 0 ≤ G.contagion j i) (h1 : ∀ j i, G.contagion j i ≤ 1)
    (hμ0 : 0 ≤ μ) (hμ1 : μ < 1)
    (hExt : ∀ j, ∑ i ∈ univ.erase j, G.contagion j i * G.loss i ≤
      μ * (G.directProb j * G.loss j))
    {σ : Convexity.StdSimplex ℝ (ι → Bool)}
    (hσ : G.toCostGame.IsCoarseCorrelatedEquilibrium σ) (s' : ι → Bool) :
    σ.weights.sum (fun s w => w * G.toCostGame.socialCost s) ≤
      1 / (1 - μ) * G.toCostGame.socialCost s' :=
  (G.isSmooth_toCostGame hp0 hp1 hL hc h0 h1 hμ0 hExt).expected_socialCost_le hμ1 hσ s'

end InterdependentSecuritySpec

/-! ### Kunreuther–Heal (2003) identical-agent theorems, mixed vs. correlated gap, and tight PoA -/

section SymmetricIDS

theorem symmetricIDSSpec_noContagionProb {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q L c : ℝ) (i : ι) (s : ι → Bool) :
    (symmetricIDSSpec ι p q L c).noContagionProb i s =
      (1 - p * q) ^ ((univ.erase i).filter (fun j => !s j)).card := by
  simp only [InterdependentSecuritySpec.noContagionProb, symmetricIDSSpec, prod_const]

/-- **Kunreuther–Heal geometric-sum critical cost identity** ([KunreutherHeal2003], §2, p. 8 &
`c*(n - 1)`, p. 9): with `u` unprotected peers, `p L - p² q L ∑_{k < u} (1 - p q)^k` simplifies to
`p L (1 - p q)^u`. -/
theorem symmetricIDSSpec_criticalCost_eq_geom_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q L c : ℝ) (i : ι) (s : ι → Bool) :
    (symmetricIDSSpec ι p q L c).criticalCost i s =
      p * L - p ^ 2 * q * L *
        ∑ k ∈ range ((univ.erase i).filter (fun j => !s j)).card, (1 - p * q) ^ k ∧
    (symmetricIDSSpec ι p q L c).criticalCost i s =
      p * L * (1 - p * q) ^ ((univ.erase i).filter (fun j => !s j)).card := by
  set u := ((univ.erase i).filter (fun j => !s j)).card
  have hclosed : (symmetricIDSSpec ι p q L c).criticalCost i s = p * L * (1 - p * q) ^ u := by
    rw [InterdependentSecuritySpec.criticalCost, symmetricIDSSpec_noContagionProb]
    rfl
  refine ⟨?_, hclosed⟩
  rw [hclosed]
  have hgeom : p * q * ∑ k ∈ range u, (1 - p * q) ^ k = 1 - (1 - p * q) ^ u := by
    have := geom_sum_mul_neg (1 - p * q) u
    linarith
  calc p * L * (1 - p * q) ^ u
      = p * L - p * L * (1 - (1 - p * q) ^ u) := by ring
    _ = p * L - p * L * (p * q * ∑ k ∈ range u, (1 - p * q) ^ k) := by rw [hgeom]
    _ = p * L - p ^ 2 * q * L * ∑ k ∈ range u, (1 - p * q) ^ k := by ring

/-- **Kunreuther–Heal unprotected expected-loss formula** ([KunreutherHeal2003], §2, p. 7): when
none of `n + 1` identical agents invests, each agent's expected loss is
`p L + p q L (1 - p) ∑_{k < n} (1 - p q)^k = L (1 - (1 - p)(1 - p q)^n)`. -/
theorem symmetricIDSSpec_cost_allFalse_eq_geom_sum (n : ℕ) (p q L c : ℝ) (i : Fin (n + 1)) :
    (symmetricIDSSpec (Fin (n + 1)) p q L c).toCostGame.cost i (fun _ => false) =
      p * L + p * q * L * (1 - p) * ∑ k ∈ range n, (1 - p * q) ^ k ∧
    (symmetricIDSSpec (Fin (n + 1)) p q L c).toCostGame.cost i (fun _ => false) =
      L * (1 - (1 - p) * (1 - p * q) ^ n) := by
  have hcard : ((univ.erase i).filter (fun _ : Fin (n + 1) => !false)).card = n := by
    rw [filter_true_of_mem (fun _ _ => by simp), card_erase_of_mem (mem_univ i), card_univ,
      Fintype.card_fin, Nat.add_sub_cancel]
  have hclosed : (symmetricIDSSpec (Fin (n + 1)) p q L c).toCostGame.cost i (fun _ => false) =
      L * (1 - (1 - p) * (1 - p * q) ^ n) := by
    simp only [InterdependentSecuritySpec.toCostGame, Bool.false_eq_true, ↓reduceIte,
      InterdependentSecuritySpec.contagionProb, symmetricIDSSpec_noContagionProb, hcard]
    simp only [symmetricIDSSpec]
    ring
  refine ⟨?_, hclosed⟩
  rw [hclosed]
  have hgeom : p * q * ∑ k ∈ range n, (1 - p * q) ^ k = 1 - (1 - p * q) ^ n := by
    have := geom_sum_mul_neg (1 - p * q) n
    linarith
  calc L * (1 - (1 - p) * (1 - p * q) ^ n)
      = p * L + L * (1 - p) * (1 - (1 - p * q) ^ n) := by ring
    _ = p * L + L * (1 - p) * (p * q * ∑ k ∈ range n, (1 - p * q) ^ k) := by rw [hgeom]
    _ = p * L + p * q * L * (1 - p) * ∑ k ∈ range n, (1 - p * q) ^ k := by ring

/-- **Kunreuther–Heal Proposition 1** ([KunreutherHeal2003], §2, Proposition 1, pp. 7–8): for
`0 < p ≤ 1` and `0 < q ≤ 1`, as the number of identical agents grows (`n → ∞`), each agent's
expected loss when none invests converges to the certain loss `L`. -/
theorem tendsto_symmetricIDSSpec_cost_allFalse_atTop {p q L c : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    Filter.Tendsto
      (fun n : ℕ => (symmetricIDSSpec (Fin (n + 1)) p q L c).toCostGame.cost 0 (fun _ => false))
      Filter.atTop (nhds L) := by
  have hfn (n : ℕ) := (symmetricIDSSpec_cost_allFalse_eq_geom_sum n p q L c 0).2
  simp only [hfn]
  have hpq_pos : 0 < p * q := mul_pos hp0 hq0
  have hpq_le1 : p * q ≤ 1 := by nlinarith
  have hlim : Filter.Tendsto (fun n : ℕ => L * (1 - (1 - p) * (1 - p * q) ^ n)) Filter.atTop
      (nhds (L * (1 - (1 - p) * 0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith))))
  simpa only [mul_zero, sub_zero, mul_one] using hlim

/-- **Kunreuther–Heal Corollary 1** ([KunreutherHeal2003], §2, Corollary 1, p. 8): for any positive
security cost `c > 0` (`0 < p ≤ 1`, `0 < q ≤ 1`, `0 ≤ L`), eventually for all sufficiently large
agent populations `n + 1`, investing against unprotected peers strictly increases an agent's cost
(so `fun _ => false` is a strict pure Nash equilibrium and investing is never a dominant
strategy). -/
theorem eventually_not_dominant_invest_symmetricIDSSpec {p q L c : ℝ}
    (hc : 0 < c) (hp0 : 0 < p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q ≤ 1) (hL : 0 ≤ L) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (symmetricIDSSpec (Fin (n + 1)) p q L c).toCostGame.cost 0 (fun _ => false) <
        (symmetricIDSSpec (Fin (n + 1)) p q L c).toCostGame.cost 0
          (update (fun _ => false) 0 true) ∧
      (symmetricIDSSpec (Fin (n + 1)) p q L c).toCostGame.IsPureNash (fun _ => false) := by
  have hpq_pos : 0 < p * q := mul_pos hp0 hq0
  have hpq_le1 : p * q ≤ 1 := by nlinarith
  have hpow : Filter.Tendsto (fun n : ℕ => p * L * (1 - p * q) ^ n) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r := 1 - p * q) (by linarith) (by linarith))
  filter_upwards [hpow.eventually (gt_mem_nhds hc)] with n hn
  have hcrit : ∀ i : Fin (n + 1),
      (symmetricIDSSpec (Fin (n + 1)) p q L c).criticalCost i (fun _ => false) =
        p * L * (1 - p * q) ^ n := fun i => by
    have hcard : ((univ.erase i).filter (fun _ : Fin (n + 1) => !false)).card = n := by
      rw [filter_true_of_mem (fun _ _ => by simp), card_erase_of_mem (mem_univ i), card_univ,
        Fintype.card_fin, Nat.add_sub_cancel]
    rw [(symmetricIDSSpec_criticalCost_eq_geom_sum p q L c i (fun _ => false)).2, hcard]
  have hdiff := (symmetricIDSSpec (Fin (n + 1)) p q L c).cost_update_false_sub_cost_update_true
    0 (fun _ => false)
  have hinv : (symmetricIDSSpec (Fin (n + 1)) p q L c).investCost 0 = c := rfl
  rw [update_eq_self, hcrit 0, hinv] at hdiff
  have _ := hL
  exact ⟨by linarith,
    (symmetricIDSSpec (Fin (n + 1)) p q L c).isPureNash_allFalse_iff.mpr fun i => hcrit i ▸ hn.le⟩

/-- **Symmetry of all pure Nash equilibria in identical-agent IDS games** (resolving the `n`-agent
question of [KunreutherHeal2003], §2, p. 9): for any `c > 0`, `0 < p ≤ 1`, `0 < q ≤ 1`, and
`0 < L`, every pure Nash equilibrium of `(symmetricIDSSpec ι p q L c).toCostGame` is constant
(`(∀ i, s i = true) ∨ (∀ i, s i = false)`). -/
theorem eq_const_of_isPureNash_symmetricIDSSpec {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p q L c : ℝ} (hc : 0 < c) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hL : 0 < L)
    {s : ι → Bool} (hs : (symmetricIDSSpec ι p q L c).toCostGame.IsPureNash s) :
    (∀ i, s i = true) ∨ (∀ i, s i = false) := by
  by_contra hmix
  push Not at hmix
  obtain ⟨⟨iN, hiN_ne⟩, ⟨iS, hiS_ne⟩⟩ := hmix
  have hiN : s iN = false := Bool.eq_false_iff.mpr hiN_ne
  have hiS : s iS = true := Bool.eq_true_of_not_eq_false hiS_ne
  have hNash := ((symmetricIDSSpec ι p q L c).isPureNash_toCostGame_iff s).mp hs
  set U := univ.filter (fun j => !s j)
  have hiN_mem : iN ∈ U := by simp only [U, mem_filter, mem_univ, hiN, Bool.not_false, and_self]
  have hiS_not_mem : iS ∉ U := by
    simp only [U, mem_filter, mem_univ, hiS, Bool.not_true, Bool.false_eq_true, and_false,
      not_false_eq_true]
  -- Investor `iS` faces `U.card` unprotected peers; non-investor `iN` faces `U.card - 1`.
  have hcard_iS : ((univ.erase iS).filter (fun j => !s j)).card = U.card := by
    congr 1
    ext j
    simp only [U, mem_filter, mem_erase, mem_univ, true_and, and_true]
    exact ⟨fun h => h.2, fun hj => ⟨fun heq => by rw [heq] at hj; simp [hiS] at hj, hj⟩⟩
  have hcard_iN : ((univ.erase iN).filter (fun j => !s j)).card = U.card - 1 := by
    have heq : (univ.erase iN).filter (fun j => !s j) = U.erase iN := by
      ext j
      simp only [U, mem_filter, mem_erase, mem_univ, true_and, and_true]
    rw [heq, card_erase_of_mem hiN_mem]
  have hS_le : c ≤ p * L * (1 - p * q) ^ U.card := by
    have h := (hNash iS).1 hiS
    rwa [(symmetricIDSSpec_criticalCost_eq_geom_sum p q L c iS s).2, hcard_iS] at h
  have hN_ge : p * L * (1 - p * q) ^ (U.card - 1) ≤ c := by
    have h := (hNash iN).2 hiN
    rwa [(symmetricIDSSpec_criticalCost_eq_geom_sum p q L c iN s).2, hcard_iN] at h
  have hpL_pos : 0 < p * L := mul_pos hp0 hL
  have hU_pos : 1 ≤ U.card := card_pos.mpr ⟨iN, hiN_mem⟩
  -- Since `0 < c ≤ p L (1 - pq)^{|U|}` and `p L > 0`, we must have `0 < 1 - pq < 1`.
  have hbase_nn : 0 ≤ 1 - p * q := by nlinarith
  have hbase_pos : 0 < 1 - p * q := lt_of_le_of_ne hbase_nn fun h => by
    rw [← h, zero_pow (by omega), mul_zero] at hS_le
    linarith
  have hpow_lt : (1 - p * q) ^ U.card < (1 - p * q) ^ (U.card - 1) :=
    pow_lt_pow_right_of_lt_one₀ hbase_pos (by nlinarith) (by omega)
  linarith [mul_lt_mul_of_pos_left hpow_lt hpL_pos]

/-- **Pigouvian non-investment tax uniqueness** ([KunreutherHeal2003], §3, p. 13): levying a tax
`t` on unprotected agents is strategically equivalent to lowering investment cost from `c` to
`c - t` (up to an additive constant `t`), and whenever `c - p L (1 - p q)^{|ι|-1} < t`, universal
investment `fun _ => true` is the **unique coarse correlated equilibrium** (and hence unique
correlated, mixed Nash, and pure Nash equilibrium). -/
theorem isCoarseCorrelatedEquilibrium_symmetricIDSSpec_taxed_unique
    {ι : Type*} [Fintype ι] [DecidableEq ι] {p q L c t : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hL : 0 ≤ L)
    (ht : c - p * L * (1 - p * q) ^ (Fintype.card ι - 1) < t)
    {σ : Convexity.StdSimplex ℝ (ι → Bool)}
    (hσ : (symmetricIDSSpec ι p q L (c - t)).toCostGame.IsCoarseCorrelatedEquilibrium σ) :
    σ = Convexity.StdSimplex.single (fun _ => true) := by
  set G := symmetricIDSSpec ι p q L (c - t)
  have hpq0 : 0 ≤ p * q := mul_nonneg hp0 hq0
  have hpq1 : p * q ≤ 1 := by nlinarith
  -- For EVERY profile `s` and player `i`, `criticalCost i s ≥ p L (1 - pq)^{|ι|-1} > c - t`.
  have hdom : ∀ (i : ι) (s : ι → Bool),
      s i = false → G.toCostGame.cost i (update s i true) < G.toCostGame.cost i s := by
    intro i s hsi
    have hcard_le : ((univ.erase i).filter (fun j => !s j)).card ≤ Fintype.card ι - 1 := by
      calc ((univ.erase i).filter (fun j => !s j)).card
          ≤ (univ.erase i).card := card_filter_le _ _
        _ = Fintype.card ι - 1 := by rw [card_erase_of_mem (mem_univ i), card_univ]
    have hpow_ge : (1 - p * q) ^ (Fintype.card ι - 1) ≤
        (1 - p * q) ^ ((univ.erase i).filter (fun j => !s j)).card :=
      pow_le_pow_of_le_one (by linarith) (by linarith) hcard_le
    have hcrit_ge : p * L * (1 - p * q) ^ (Fintype.card ι - 1) ≤ G.criticalCost i s := by
      rw [(symmetricIDSSpec_criticalCost_eq_geom_sum p q L (c - t) i s).2]
      exact mul_le_mul_of_nonneg_left hpow_ge (mul_nonneg hp0 hL)
    have hdiff := G.cost_update_false_sub_cost_update_true i s
    conv at hdiff =>
      enter [1, 1]
      rw [← hsi, update_eq_self]
    have hinv : G.investCost i = c - t := rfl
    linarith
  -- Every `s ∈ σ.weights.support` must therefore be `fun _ => true`.
  have hsupp : ∀ s ∈ σ.weights.support, s = fun _ => true := by
    intro s hs
    by_contra hne
    obtain ⟨i, hi⟩ : ∃ i, s i = false := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      exact ⟨i, Bool.eq_false_iff.mpr hi⟩
    have hws_pos : 0 < σ.weights s :=
      lt_of_le_of_ne (Convexity.StdSimplex.weights_nonneg s)
        (Ne.symm (Finsupp.mem_support_iff.mp hs))
    have hpt_le : ∀ s' ∈ σ.weights.support,
        σ.weights s' * G.toCostGame.cost i (update s' i true) ≤
          σ.weights s' * G.toCostGame.cost i s' := fun s' _ => by
      cases hs'i : s' i
      · exact mul_le_mul_of_nonneg_left (hdom i s' hs'i).le
          (Convexity.StdSimplex.weights_nonneg s')
      · rw [← hs'i, update_eq_self]
    have hstrict : ∑ s' ∈ σ.weights.support,
        σ.weights s' * G.toCostGame.cost i (update s' i true) <
        ∑ s' ∈ σ.weights.support, σ.weights s' * G.toCostGame.cost i s' :=
      sum_lt_sum hpt_le ⟨s, hs, mul_lt_mul_of_pos_left (hdom i s hi) hws_pos⟩
    have hCCE := hσ i true
    simp only [Finsupp.sum] at hCCE
    linarith
  ext s
  by_cases hs : s = fun _ => true
  · subst hs
    simp only [Convexity.StdSimplex.weights_single, Finsupp.single_eq_same]
    simpa only [sum_singleton] using (sum_subset (fun x hx => mem_singleton.mpr (hsupp x hx))
      fun x _ hx => Finsupp.notMem_support_iff.mp hx).symm.trans σ.total
  · simp only [Convexity.StdSimplex.weights_single, Finsupp.single_apply, Ne.symm hs, ↓reduceIte]
    exact not_ne_iff.mp fun hne0 => hs (hsupp s (Finsupp.mem_support_iff.mpr hne0))

/-- **Mixed Nash vs. public-signal correlated equilibrium in 2-agent Kunreuther–Heal IDS**
(original): in the interior coordination regime `p L (1 - p q) < c < p L`, let
`θ = 1 - (p L - c) / (p² q L) ∈ (0, 1)`.
1. Independent mixing at rate `θ` is an exact `CostGame.IsMixedNash` equilibrium of the `2`-agent
   IDS game with expected cost `c + (1 - θ) p q L` per player.
2. Publicly correlating `(true, true)` with probability `θ` and `(false, false)` with probability
   `1 - θ` preserves each player's marginal investment probability `θ`, forms a
   `CostGame.IsCorrelatedEquilibrium`, and strictly reduces each player's expected cost by
   `θ * (1 - θ) * p ^ 2 * q * L > 0`. -/
theorem symmetricIDSSpec_isMixedNash_and_correlated_strict_improvement
    {p q L c : ℝ} (hp : 0 < p) (hq : 0 < q) (hL : 0 < L)
    (hLow : p * L * (1 - p * q) < c) (hHigh : c < p * L) :
    let G := (symmetricIDSSpec (Fin 2) p q L c).toCostGame
    let θ : ℝ := 1 - (p * L - c) / (p ^ 2 * q * L)
    let mix : Fin 2 → Bool → ℝ := fun _ b => if b then θ else 1 - θ
    0 < θ ∧ θ < 1 ∧
    G.IsMixedNash mix ∧
    (∃ σ : Convexity.StdSimplex ℝ (Fin 2 → Bool),
      G.IsCorrelatedEquilibrium σ ∧
      (∀ i, σ.weights.sum (fun s w => w * if s i then 1 else 0) = θ) ∧
      (∀ i, G.expectedCost mix i - σ.weights.sum (fun s w => w * G.cost i s) =
        θ * (1 - θ) * p ^ 2 * q * L)) ∧
    0 < θ * (1 - θ) * p ^ 2 * q * L := by
  intro G θ mix
  have hden : 0 < p ^ 2 * q * L := by positivity
  have hu_pos : 0 < (p * L - c) / (p ^ 2 * q * L) := div_pos (by linarith) hden
  have hu_lt1 : (p * L - c) / (p ^ 2 * q * L) < 1 := (div_lt_one hden).mpr (by linarith)
  have hθ0 : 0 < θ := by dsimp only [θ]; linarith
  have hθ1 : θ < 1 := by dsimp only [θ]; linarith
  -- Compute pure profile costs on `Fin 2` explicitly.
  have h10_ne : (1 : Fin 2) ≠ 0 := by decide
  have h01_ne : (0 : Fin 2) ≠ 1 := by decide
  have hsub0 : (1 : Fin 2) - 0 = 1 := by decide
  have hsub1 : (1 : Fin 2) - 1 = 0 := by decide
  have hcost_TT : ∀ i : Fin 2, G.cost i (fun _ => true) = c := fun i => by
    simp only [G, InterdependentSecuritySpec.toCostGame, ↓reduceIte,
      InterdependentSecuritySpec.contagionProb_allTrue, mul_zero, add_zero, symmetricIDSSpec]
  have hcard_other : ∀ (i : Fin 2) (s : Fin 2 → Bool),
      ((univ.erase i).filter (fun j => !s j)).card = if s (1 - i) then 0 else 1 := fun i s => by
    have her0 : univ.erase (0 : Fin 2) = {1} := by decide
    have her1 : univ.erase (1 : Fin 2) = {0} := by decide
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, her0, her1, hsub0, hsub1, filter_singleton]
    · cases s 1 <;> simp
    · cases s 0 <;> simp
  have hcost_eval : ∀ (i : Fin 2) (s : Fin 2 → Bool),
      G.cost i s =
        if s i then c + (if s (1 - i) then 0 else p * q * L)
        else if s (1 - i) then p * L else p * L + (1 - p) * p * q * L := fun i s => by
    dsimp only [G, InterdependentSecuritySpec.toCostGame]
    rw [InterdependentSecuritySpec.contagionProb, symmetricIDSSpec_noContagionProb, hcard_other i s]
    dsimp only [symmetricIDSSpec]
    cases s i <;> cases s (1 - i) <;> simp <;> ring
  have hexp_fin2 : ∀ F : (Fin 2 → Bool) → ℝ,
      (∑ s : Fin 2 → Bool, F s) = ∑ b0 : Bool, ∑ b1 : Bool, F ![b0, b1] := fun F =>
    (Fintype.sum_equiv (finTwoArrowEquiv Bool).symm (fun u : Bool × Bool => F ![u.1, u.2]) F
      fun _ => rfl).symm.trans (Fintype.sum_prod_type fun u : Bool × Bool => F ![u.1, u.2])
  have h1_sub_θ : (1 - θ) * (p ^ 2 * q * L) = p * L - c := by
    dsimp only [θ]
    field_simp [hden.ne']
    ring
  -- Evaluate `deviationCost mix i b` for `b = true` and `b = false`.
  have hdev_true : ∀ i : Fin 2, G.deviationCost mix i true = c + (1 - θ) * p * q * L := fun i => by
    rw [CostGame.deviationCost_def, hexp_fin2]
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fintype.sum_bool, productWeight_def,
      Fin.prod_univ_two, hcost_eval, mix, Fin.isValue, update_self, hsub0, hsub1,
      update_of_ne h10_ne, update_of_ne h01_ne,
      Matrix.cons_val_zero, Matrix.cons_val_one, ↓reduceIte, Bool.false_eq_true] <;> ring
  have hdev_false : ∀ i : Fin 2,
      G.deviationCost mix i false = c + (1 - θ) * p * q * L := fun i => by
    rw [CostGame.deviationCost_def, hexp_fin2]
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fintype.sum_bool, productWeight_def,
      Fin.prod_univ_two, hcost_eval, mix, Fin.isValue, update_self, hsub0, hsub1,
      update_of_ne h10_ne, update_of_ne h01_ne,
      Matrix.cons_val_zero, Matrix.cons_val_one, ↓reduceIte, Bool.false_eq_true] <;>
      nlinarith [h1_sub_θ]
  have hMixed_wf : ∀ i, IsMixedStrategy (mix i) := fun _ =>
    isMixedStrategy_iff.2
      ⟨fun b => by cases b <;> simp only [mix, ↓reduceIte, Bool.false_eq_true] <;> linarith,
        by simp only [Fintype.sum_bool, mix, ↓reduceIte, Bool.false_eq_true]; ring⟩
  have hMixed : G.IsMixedNash mix := by
    refine ⟨hMixed_wf, fun i a => ?_⟩
    rw [← G.sum_mul_deviationCost_eq_expectedCost mix (hMixed_wf i).sum_eq_one]
    cases a <;>
      simp only [Fintype.sum_bool, mix, ↓reduceIte, Bool.false_eq_true, hdev_true i,
        hdev_false i] <;>
      linarith
  -- Construct the public-signal correlated equilibrium `σ`.
  have hTrue_N : G.IsPureNash (fun _ => true) :=
    (symmetricIDSSpec (Fin 2) p q L c).isPureNash_allTrue_iff.mpr fun _ => hHigh.le
  have hFalse_N : G.IsPureNash (fun _ => false) :=
    (symmetricIDSSpec (Fin 2) p q L c).isPureNash_allFalse_iff.mpr fun i => by
      rw [(symmetricIDSSpec_criticalCost_eq_geom_sum p q L c i (fun _ => false)).2,
        hcard_other i (fun _ => false)]
      simp only [Bool.false_eq_true, ↓reduceIte, pow_one]
      exact hLow.le
  let σ : Convexity.StdSimplex ℝ (Fin 2 → Bool) :=
    .duple (fun _ => true) (fun _ => false) (s := θ) (t := 1 - θ) hθ0.le (by linarith) (by ring)
  have hCE : G.IsCorrelatedEquilibrium σ :=
    (symmetricIDSSpec (Fin 2) p q L c).isCorrelatedEquilibrium_publicSignal hTrue_N hFalse_N
      hθ0.le hθ1.le
  have hσ_sum : ∀ f : (Fin 2 → Bool) → ℝ,
      σ.weights.sum (fun s w => w * f s) = θ * f (fun _ => true) + (1 - θ) * f (fun _ => false) :=
    fun f => by
      dsimp only [σ]
      rw [Convexity.StdSimplex.weights_duple,
        Finsupp.sum_add_index' (fun s => zero_mul (f s)) (fun s _ _ => add_mul _ _ (f s)),
        Finsupp.sum_single_index (zero_mul _), Finsupp.sum_single_index (zero_mul _)]
  refine ⟨hθ0, hθ1, hMixed, ⟨σ, hCE, fun i => ?_, fun i => ?_⟩, by positivity⟩
  · rw [hσ_sum]
    simp only [↓reduceIte, Bool.false_eq_true, mul_one, mul_zero, add_zero]
  · have hexp_i : G.expectedCost mix i = c + (1 - θ) * p * q * L := by
      rw [← G.sum_mul_deviationCost_eq_expectedCost mix (hMixed_wf i).sum_eq_one]
      simp only [Fintype.sum_bool, mix, ↓reduceIte, Bool.false_eq_true, hdev_true i, hdev_false i]
      ring
    have hFF : G.cost i (fun _ => false) = p * L + (1 - p) * p * q * L := by
      rw [hcost_eval]
      simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hexp_i, hσ_sum, hcost_TT i, hFF]
    nlinarith [h1_sub_θ]

/-- **Exact tightness of the `1 / (1 - (n - 1) q)` smoothness Price-of-Anarchy bound** (original):
at `n = 2`, `p = 1`, `0 < q < 1`, `0 < L`, and `c = L * (1 - q)`, both `(true, true)` and
`(false, false)` are pure Nash equilibria, `(true, true)` is globally socially optimal, and
`socialCost (false, false)` equals `1 / (1 - q) * socialCost (true, true)` with exact equality. -/
theorem symmetricIDSSpec_poa_eq_inv_one_sub {q L : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hL : 0 < L) :
    let G := symmetricIDSSpec (Fin 2) 1 q L (L * (1 - q))
    G.toCostGame.IsSmooth 1 q ∧
    G.toCostGame.IsPureNash (fun _ => false) ∧
    G.toCostGame.IsPureNash (fun _ => true) ∧
    (∀ s, G.toCostGame.socialCost (fun _ => true) ≤ G.toCostGame.socialCost s) ∧
    G.toCostGame.socialCost (fun _ => false) =
      1 / (1 - q) * G.toCostGame.socialCost (fun _ => true) := by
  intro G
  have hSmooth : G.toCostGame.IsSmooth 1 q := by
    refine G.isSmooth_toCostGame (fun _ => zero_le_one) (fun _ => le_rfl) (fun _ => hL.le)
      (fun _ => mul_nonneg hL.le (by linarith))
      (fun _ _ => by simp only [G, symmetricIDSSpec, one_mul]; exact hq0.le)
      (fun _ _ => by simp only [G, symmetricIDSSpec, one_mul]; exact hq1.le) hq0.le fun j => ?_
    have hcard : (univ.erase j).card = 1 := by
      rw [card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin]
    simp only [G, symmetricIDSSpec, one_mul, sum_const, hcard, one_smul, le_rfl]
  have hFalse : G.toCostGame.IsPureNash (fun _ => false) := by
    rw [G.isPureNash_allFalse_iff]
    intro i
    have hcard : ((univ.erase i).filter (fun _ : Fin 2 => !false)).card = 1 := by
      rw [filter_true_of_mem (fun _ _ => by simp), card_erase_of_mem (mem_univ i), card_univ,
        Fintype.card_fin]
    rw [(symmetricIDSSpec_criticalCost_eq_geom_sum 1 q L (L * (1 - q)) i (fun _ => false)).2, hcard]
    change _ ≤ L * (1 - q)
    linarith
  have hTrue : G.toCostGame.IsPureNash (fun _ => true) := by
    rw [G.isPureNash_allTrue_iff]
    intro _
    simp only [G, symmetricIDSSpec, one_mul]
    nlinarith
  have hsoc_T : G.toCostGame.socialCost (fun _ => true) = 2 * (L * (1 - q)) := by
    simp only [CostGame.socialCost, Fin.sum_univ_two, G, InterdependentSecuritySpec.toCostGame,
      ↓reduceIte, InterdependentSecuritySpec.contagionProb_allTrue, mul_zero, add_zero,
      symmetricIDSSpec]
    ring
  have hsoc_F : G.toCostGame.socialCost (fun _ => false) = 2 * L := by
    have h0 := (symmetricIDSSpec_cost_allFalse_eq_geom_sum 1 1 q L (L * (1 - q)) 0).2
    have h1 := (symmetricIDSSpec_cost_allFalse_eq_geom_sum 1 1 q L (L * (1 - q)) 1).2
    simp only [CostGame.socialCost, Fin.sum_univ_two, G, h0, h1]
    ring
  refine ⟨hSmooth, hFalse, hTrue, fun s => sum_le_sum fun i _ => ?_, ?_⟩
  · -- At `p = 1`, `c = L * (1 - q)`, every player's cost is at least `L * (1 - q)` pointwise.
    have hcont_nn : 0 ≤ G.contagionProb i s := sub_nonneg.mpr <|
      G.noContagionProb_le_one (fun _ _ => by simp [G, symmetricIDSSpec, hq0.le])
        (fun _ _ => by simp [G, symmetricIDSSpec, hq1.le]) i s
    dsimp only [InterdependentSecuritySpec.toCostGame]
    simp only [show ∀ j, G.investCost j = L * (1 - q) from fun _ => rfl,
      show ∀ j, G.loss j = L from fun _ => rfl, show ∀ j, G.directProb j = 1 from fun _ => rfl]
    cases s i <;> simp only [↓reduceIte, Bool.false_eq_true,
      InterdependentSecuritySpec.contagionProb_allTrue, mul_zero, add_zero, sub_self, zero_mul] <;>
      nlinarith
  · rw [hsoc_F, hsoc_T]
    field_simp [(by linarith : 1 - q ≠ 0)]

/-- **Pure-Nash Price of Anarchy in the Prisoner's Dilemma IDS regime** (original, motivated by the
Prisoner's Dilemma regime `p * L < c` in [KunreutherHeal2003], §2, Table 3, p. 9): when
`p * L < c` (with `0 < p ≤ 1`, `0 ≤ q ≤ 1`, `0 < L`), `(fun _ => false)` is the unique pure Nash
equilibrium of the `(n + 1)`-agent symmetric IDS game and its social cost is at most `(1 + n * q)`
times the social cost of every profile `s'` (at most `(n + 1)` times optimal since `q ≤ 1`). -/
theorem symmetricIDSSpec_prisonersDilemma_socialCost_le (n : ℕ) {p q L c : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hL : 0 < L)
    (hPD : p * L < c) (s' : Fin (n + 1) → Bool) :
    (symmetricIDSSpec (Fin (n + 1)) p q L c).toCostGame.socialCost (fun _ => false) ≤
      (1 + (n : ℝ) * q) * (symmetricIDSSpec (Fin (n + 1)) p q L c).toCostGame.socialCost s' := by
  set G := symmetricIDSSpec (Fin (n + 1)) p q L c
  -- Every player in `s'` pays at least `min c (p * L) = p * L`.
  have hlb_pt : ∀ i : Fin (n + 1), p * L ≤ G.toCostGame.cost i s' := fun i => by
    have h0_c : ∀ j k : Fin (n + 1), 0 ≤ G.contagion j k := fun _ _ => mul_nonneg hp0.le hq0
    have h1_c : ∀ j k : Fin (n + 1), G.contagion j k ≤ 1 := fun _ _ => by
      change p * q ≤ 1
      nlinarith
    have hcont_nn : 0 ≤ G.contagionProb i s' :=
      sub_nonneg.mpr (G.noContagionProb_le_one h0_c h1_c i s')
    change p * L ≤
      if s' i = true then c + L * G.contagionProb i s'
      else L * (p + (1 - p) * G.contagionProb i s')
    split_ifs
    · linarith [mul_nonneg hL.le hcont_nn]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hp1) hcont_nn]
  have hlb_soc : ((n + 1 : ℕ) : ℝ) * (p * L) ≤ G.toCostGame.socialCost s' := by
    simpa only [CostGame.socialCost, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] using
      sum_le_sum fun i (_ : i ∈ univ) => hlb_pt i
  -- Bound `cost i (fun _ => false) ≤ p L + n p q L = (1 + n q) p L`.
  have hub_pt : ∀ i : Fin (n + 1),
      G.toCostGame.cost i (fun _ => false) ≤ (1 + (n : ℝ) * q) * (p * L) := fun i => by
    rw [(symmetricIDSSpec_cost_allFalse_eq_geom_sum n p q L c i).1]
    have hpq0 : 0 ≤ p * q := mul_nonneg hp0.le hq0
    have hpq1 : p * q ≤ 1 := by nlinarith
    have hsum_le : ∑ k ∈ range n, (1 - p * q) ^ k ≤ (n : ℝ) := by
      calc ∑ k ∈ range n, (1 - p * q) ^ k
          ≤ ∑ _ ∈ range n, (1 : ℝ) :=
            sum_le_sum fun k _ => pow_le_one₀ (by linarith) (by linarith)
        _ = (n : ℝ) := by simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
    have h1_sub_p : 1 - p ≤ 1 := sub_le_self 1 hp0.le
    have hterm : p * q * L * (1 - p) * ∑ k ∈ range n, (1 - p * q) ^ k ≤
        p * q * L * (n : ℝ) := by
      have hA : 0 ≤ p * q * L := by positivity
      have hB : 0 ≤ ∑ k ∈ range n, (1 - p * q) ^ k :=
        sum_nonneg fun k _ => pow_nonneg (by linarith) _
      calc p * q * L * (1 - p) * ∑ k ∈ range n, (1 - p * q) ^ k
          ≤ p * q * L * 1 * ∑ k ∈ range n, (1 - p * q) ^ k :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1_sub_p hA) hB
        _ ≤ p * q * L * (n : ℝ) := by
            rw [mul_one]
            exact mul_le_mul_of_nonneg_left hsum_le hA
    linarith [show (1 + (n : ℝ) * q) * (p * L) = p * L + p * q * L * (n : ℝ) by ring]
  have hub_soc : G.toCostGame.socialCost (fun _ => false) ≤
      ((n + 1 : ℕ) : ℝ) * ((1 + (n : ℝ) * q) * (p * L)) := by
    simpa only [CostGame.socialCost, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] using
      sum_le_sum fun i (_ : i ∈ univ) => hub_pt i
  have h1nq_nonneg : 0 ≤ 1 + (n : ℝ) * q := by positivity
  calc G.toCostGame.socialCost (fun _ => false)
      ≤ (1 + (n : ℝ) * q) * (((n + 1 : ℕ) : ℝ) * (p * L)) := by linarith
    _ ≤ (1 + (n : ℝ) * q) * G.toCostGame.socialCost s' :=
        mul_le_mul_of_nonneg_left hlb_soc h1nq_nonneg

end SymmetricIDS

end Cslib.GameTheory
