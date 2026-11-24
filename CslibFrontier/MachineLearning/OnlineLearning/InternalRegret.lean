/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.OnlineLearning.Greedy
public import CslibFrontier.MachineLearning.OnlineLearning.SwapRegret
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Modification rules, internal regret, and swap-regret separations

This module formalizes the general memoryless modification-rule framework `R_F` of
[BlumMansour2007AGT, §4.2, pp. 81–82], specializing to external regret (`F^ex`), pairwise internal
regret (`F^in`), and swap regret (`F^sw`), together with Exercises 4.1, 4.2, and 4.6
([BlumMansour2007AGT, p. 101]).

## Overview and source mapping

* **Pushforward modification rules** (`pushforwardProb`, `sum_pushforwardProb_mul`, `ruleRegret`,
  `modRegret` — [BlumMansour2007AGT, §4.2, p. 82]):
  A memoryless modification rule `f : ι → ι` shifts the learner's round-`t` mass `p t j` to `f j`,
  inducing the distribution `pushforwardProb f (p t) i = ∑_{j : f j = i} p t j` whose expected loss
  equals `∑ j, p t j * ℓ t (f j)` (`sum_pushforwardProb_mul`). For a set `F : Set (ι → ι)` of
  modification rules, `modRegret F p ℓ T = sSup (ruleRegret p ℓ T '' F)`.
* **External, internal, and swap regret** (`externalRules`, `externalRegret`, `switchRule`,
  `internalRules`, `internalRegret`, `swapRules`, `swapRegret` — [BlumMansour2007AGT, §4.2, p. 82,
  and §4.4.3, p. 90]):
  `externalRules` are the constant maps `Function.const ι k`, `internalRules` are the pairwise
  single-action switches `switchRule a b` (including `a = b`, matching the displayed definition
  `max_{i, j ∈ X} ∑_t p_i^t (ℓ_i^t - ℓ_j^t)` on p. 82 so that `0 ≤ internalRegret`), and
  `swapRules = Set.univ` consists of all maps `ι → ι`. Both external and internal regret are at most
  swap regret (`externalRegret_le_swapRegret`, `internalRegret_le_swapRegret`), and swap regret
  decomposes as `∑ i, max_j ∑_t p_i^t (ℓ_i^t - ℓ_j^t)` (`swapRegret_eq_sum_sup`).
* **Exercise 4.1 and tightness** (`swapRegret_le_card_mul_internalRegret`,
  `exists_swapRegret_eq_pred_card_mul_internalRegret` — [BlumMansour2007AGT, Exercise 4.1, p. 101]):
  Swap regret is at most `N` times internal regret (`swapRegret ≤ N * internalRegret`), and on
  `Fin N` (`N ≥ 2`) there is a `{0, 1}` loss sequence with uniform play achieving
  `internalRegret = 1` and `swapRegret = N - 1`.
* **Exercise 4.2** (`exists_externalRegret_zero_and_swapRegret_eq`,
  `exists_unbounded_swapRegret_div_externalRegret` — [BlumMansour2007AGT, Exercise 4.2, p. 101]):
  Even for `N = 3`, `{0, 1}` losses, and deterministic play, external regret can be `0` while swap
  regret is `3 m` (`internalRegret = m`) for arbitrary `m`, and appending one round makes
  `externalRegret = 1 > 0` while `swapRegret / externalRegret = 3 m + 1` is arbitrarily large.
* **Exercise 4.6 and open-problem note on Exercise 4.7** (`swapRegret_blumMansourProb_le_sqrt`,
  `blumMansourPW_swap_regret_le_sqrt` — [BlumMansour2007AGT, Exercise 4.6, p. 101]):
  `blumMansourProb` achieves `swapRegret ≤ 2 √(T N ln N)` with Hedge copies, and the analogous
  Polynomial Weights (`mwFactor`) reduction (`blumMansourPWProb`) achieves the same `2 √(T N ln N)`
  bound on `[0, 1]` losses using the hint that the copies' perceived losses sum to at most `T`.
  *(Historical note on Exercise 4.7, p. 101: Blum and Mansour posed as an open problem whether swap
  regret requires `Ω(√(T N log N))`; this was subsequently resolved in the negative for
  information-theoretic/exponential-horizon regimes by Peng and Rubinstein (STOC 2024) and Dagan,
  Daskalakis, Fishelson, and Golowich (STOC 2024).)*

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.Experts.pushforwardProb`: distribution induced by a
  modification rule `f : ι → ι`.
* `Cslib.MachineLearning.OnlineLearning.Experts.ruleRegret`,
  `Cslib.MachineLearning.OnlineLearning.Experts.modRegret`: regret against one modification rule and
  against a family `F : Set (ι → ι)`.
* `Cslib.MachineLearning.OnlineLearning.Experts.externalRules`,
  `Cslib.MachineLearning.OnlineLearning.Experts.externalRegret`: constant-action rules and external
  regret.
* `Cslib.MachineLearning.OnlineLearning.Experts.switchRule`,
  `Cslib.MachineLearning.OnlineLearning.Experts.internalRules`,
  `Cslib.MachineLearning.OnlineLearning.Experts.internalRegret`: single-action switch rules and
  internal regret.
* `Cslib.MachineLearning.OnlineLearning.Experts.swapRules`,
  `Cslib.MachineLearning.OnlineLearning.Experts.swapRegret`: arbitrary memoryless rules and swap
  regret.
* `Cslib.MachineLearning.OnlineLearning.Experts.blumMansourPWProb`: Blum–Mansour learner
  instantiated with Polynomial Weights (`mwFactor`) copies.

## Main results

* `Cslib.MachineLearning.OnlineLearning.Experts.sum_pushforwardProb_mul`: pushforward loss identity.
* `Cslib.MachineLearning.OnlineLearning.Experts.externalRegret_eq_sub_minCumLoss`,
  `Cslib.MachineLearning.OnlineLearning.Experts.swapRegret_eq_sum_sup`: closed forms for external
  and swap regret.
* `Cslib.MachineLearning.OnlineLearning.Experts.externalRegret_le_swapRegret`,
  `Cslib.MachineLearning.OnlineLearning.Experts.internalRegret_le_swapRegret`: monotonicity across
  `F^ex, F^in ⊆ F^sw`.
* `Cslib.MachineLearning.OnlineLearning.Experts.swapRegret_le_card_mul_internalRegret`,
  `Cslib.MachineLearning.OnlineLearning.Experts.exists_swapRegret_eq_pred_card_mul_internalRegret`:
  [BlumMansour2007AGT, Exercise 4.1] and `N - 1` tightness.
* `Cslib.MachineLearning.OnlineLearning.Experts.exists_externalRegret_zero_and_swapRegret_eq`,
  `Cslib.MachineLearning.OnlineLearning.Experts.exists_unbounded_swapRegret_div_externalRegret`:
  [BlumMansour2007AGT, Exercise 4.2].
* `Cslib.MachineLearning.OnlineLearning.Experts.swapRegret_blumMansourProb_le_sqrt`,
  `Cslib.MachineLearning.OnlineLearning.Experts.blumMansourPW_swap_regret_le_sqrt`:
  [BlumMansour2007AGT, Exercise 4.6].

## References

* [A. Blum and Y. Mansour, *Learning, Regret Minimization, and Equilibria*][BlumMansour2007AGT]
* [A. Blum and Y. Mansour, *From External to Internal Regret*][BlumMansour2007]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.Experts

open Finset Matrix Real

variable {ι : Type*} [Fintype ι]

/-! ### Memoryless modification rules and `F`-regret -/

/-- Distribution `f_*(p)` induced by shifting the mass `p j` to `f j`
[BlumMansour2007AGT, §4.2, p. 82]. -/
def pushforwardProb [DecidableEq ι] (f : ι → ι) (p : ι → ℝ) (i : ι) : ℝ :=
  ∑ j with f j = i, p j

theorem pushforwardProb_apply [DecidableEq ι] (f : ι → ι) (p : ι → ℝ) (i : ι) :
    pushforwardProb f p i = ∑ j with f j = i, p j := by rw [pushforwardProb]

/-- Expected loss under `pushforwardProb f p` equals `∑ j, p j * ℓ (f j)`
[BlumMansour2007AGT, §4.2, p. 82]. -/
theorem sum_pushforwardProb_mul [DecidableEq ι] (f : ι → ι) (p ℓ : ι → ℝ) :
    ∑ i, pushforwardProb f p i * ℓ i = ∑ j, p j * ℓ (f j) := by
  unfold pushforwardProb
  calc ∑ i, (∑ j with f j = i, p j) * ℓ i
      = ∑ i, ∑ j, if f j = i then p j * ℓ i else 0 :=
        sum_congr rfl fun i _ => by rw [sum_mul, sum_filter]
    _ = ∑ j, ∑ i, if f j = i then p j * ℓ i else 0 := sum_comm
    _ = ∑ j, p j * ℓ (f j) :=
        sum_congr rfl fun j _ => by simp only [sum_ite_eq, mem_univ, ↓reduceIte]

/-- Cumulative regret `L_H^T - L_{H, f}^T = ∑ t < T, ∑ i, p t i * (ℓ t i - ℓ t (f i))` against a
single modification rule `f : ι → ι`. -/
def ruleRegret (p ℓ : ℕ → ι → ℝ) (T : ℕ) (f : ι → ι) : ℝ :=
  ∑ t ∈ range T, ∑ i, p t i * (ℓ t i - ℓ t (f i))

theorem ruleRegret_eq_sub (p ℓ : ℕ → ι → ℝ) (T : ℕ) (f : ι → ι) :
    ruleRegret p ℓ T f =
      (∑ t ∈ range T, ∑ i, p t i * ℓ t i) - ∑ t ∈ range T, ∑ i, p t i * ℓ t (f i) := by
  simp only [ruleRegret, mul_sub, sum_sub_distrib]

@[simp] theorem ruleRegret_id (p ℓ : ℕ → ι → ℝ) (T : ℕ) :
    ruleRegret p ℓ T id = 0 := by
  simp only [ruleRegret, id_eq, sub_self, mul_zero, sum_const_zero]

/-- General `F`-modification regret `R_F = sup_{f ∈ F} (L_H^T - L_{H, f}^T)`
[BlumMansour2007AGT, §4.2, p. 82]. -/
noncomputable def modRegret (F : Set (ι → ι)) (p ℓ : ℕ → ι → ℝ) (T : ℕ) : ℝ :=
  sSup (ruleRegret p ℓ T '' F)

private theorem bddAbove_image_ruleRegret (F : Set (ι → ι)) (p ℓ : ℕ → ι → ℝ) (T : ℕ) :
    BddAbove (ruleRegret p ℓ T '' F) :=
  (Set.toFinite _).bddAbove

theorem ruleRegret_le_modRegret {F : Set (ι → ι)} (p ℓ : ℕ → ι → ℝ) (T : ℕ)
    {f : ι → ι} (hf : f ∈ F) :
    ruleRegret p ℓ T f ≤ modRegret F p ℓ T :=
  le_csSup (bddAbove_image_ruleRegret F p ℓ T) ⟨f, hf, rfl⟩

theorem modRegret_le_iff {F : Set (ι → ι)} (hF : F.Nonempty) {p ℓ : ℕ → ι → ℝ} {T : ℕ} {R : ℝ} :
    modRegret F p ℓ T ≤ R ↔ ∀ f ∈ F, ruleRegret p ℓ T f ≤ R := by
  unfold modRegret
  rw [csSup_le_iff (bddAbove_image_ruleRegret F p ℓ T) (hF.image _)]
  simp only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

theorem modRegret_mono {F₁ F₂ : Set (ι → ι)} (hF₁ : F₁.Nonempty) (hsub : F₁ ⊆ F₂)
    (p ℓ : ℕ → ι → ℝ) (T : ℕ) :
    modRegret F₁ p ℓ T ≤ modRegret F₂ p ℓ T :=
  csSup_le_csSup (bddAbove_image_ruleRegret F₂ p ℓ T) (hF₁.image _) (Set.image_mono hsub)

/-! ### External, internal, and swap regret -/

/-- Constant modification rules `F^ex = {x ↦ k | k ∈ ι}` [BlumMansour2007AGT, §4.2, p. 82]. -/
def externalRules (ι : Type*) : Set (ι → ι) :=
  Set.range (Function.const ι)

/-- External regret `R = modRegret (externalRules ι) p ℓ T`. -/
noncomputable def externalRegret (p ℓ : ℕ → ι → ℝ) (T : ℕ) : ℝ :=
  modRegret (externalRules ι) p ℓ T

/-- Single-action switch rule `switch(x, a, b)`: replaces `a` by `b` and leaves all other actions
unchanged [BlumMansour2007AGT, §4.2, p. 82, and §4.4.3, p. 90]. -/
def switchRule [DecidableEq ι] (a b : ι) (x : ι) : ι :=
  if x = a then b else x

omit [Fintype ι] in
theorem switchRule_apply [DecidableEq ι] (a b x : ι) :
    switchRule a b x = if x = a then b else x := by rw [switchRule]

omit [Fintype ι] in
@[simp] theorem switchRule_self [DecidableEq ι] (a : ι) : switchRule a a = id := by
  funext x
  simp only [switchRule, id_eq, ite_eq_right_iff]
  exact fun h => h.symm

theorem ruleRegret_switchRule [DecidableEq ι] (p ℓ : ℕ → ι → ℝ) (T : ℕ) (a b : ι) :
    ruleRegret p ℓ T (switchRule a b) = ∑ t ∈ range T, p t a * (ℓ t a - ℓ t b) := by
  unfold ruleRegret
  refine sum_congr rfl fun t _ => ?_
  have hsingle : ∀ i, p t i * (ℓ t i - ℓ t (switchRule a b i)) =
      if i = a then p t a * (ℓ t a - ℓ t b) else 0 := fun i => by
    unfold switchRule
    by_cases hia : i = a
    · subst hia
      simp
    · simp [hia]
  simp only [hsingle, sum_ite_eq', mem_univ, ↓reduceIte]

/-- Pairwise single-action switch rules `F^in = {switchRule a b | a, b ∈ ι}`
[BlumMansour2007AGT, §4.2, p. 82]. -/
def internalRules (ι : Type*) [DecidableEq ι] : Set (ι → ι) :=
  {f | ∃ a b : ι, f = switchRule a b}

/-- Internal regret `modRegret (internalRules ι) p ℓ T`. -/
noncomputable def internalRegret [DecidableEq ι] (p ℓ : ℕ → ι → ℝ) (T : ℕ) : ℝ :=
  modRegret (internalRules ι) p ℓ T

/-- All memoryless modification rules `F^sw = Set.univ` [BlumMansour2007AGT, §4.2, p. 82]. -/
def swapRules (ι : Type*) : Set (ι → ι) :=
  Set.univ

/-- Swap regret `modRegret (swapRules ι) p ℓ T`. -/
noncomputable def swapRegret (p ℓ : ℕ → ι → ℝ) (T : ℕ) : ℝ :=
  modRegret (swapRules ι) p ℓ T

theorem swapRegret_le_iff {p ℓ : ℕ → ι → ℝ} {T : ℕ} {R : ℝ} :
    swapRegret p ℓ T ≤ R ↔ ∀ δ : ι → ι, ruleRegret p ℓ T δ ≤ R := by
  unfold swapRegret swapRules
  rw [modRegret_le_iff ⟨id, Set.mem_univ _⟩]
  simp only [Set.mem_univ, forall_true_left]

theorem nonneg_swapRegret (p ℓ : ℕ → ι → ℝ) (T : ℕ) : 0 ≤ swapRegret p ℓ T := by
  have := ruleRegret_le_modRegret (F := swapRules ι) p ℓ T (Set.mem_univ id)
  rwa [ruleRegret_id] at this

theorem nonneg_internalRegret [DecidableEq ι] [Nonempty ι] (p ℓ : ℕ → ι → ℝ) (T : ℕ) :
    0 ≤ internalRegret p ℓ T := by
  obtain ⟨a₀⟩ := ‹Nonempty ι›
  have hm : (id : ι → ι) ∈ internalRules ι := ⟨a₀, a₀, (switchRule_self a₀).symm⟩
  have h := ruleRegret_le_modRegret p ℓ T hm
  rwa [ruleRegret_id] at h

/-- External regret is at most swap regret (`F^ex ⊆ F^sw`, [BlumMansour2007AGT, §4.2, p. 82]). -/
theorem externalRegret_le_swapRegret [Nonempty ι] (p ℓ : ℕ → ι → ℝ) (T : ℕ) :
    externalRegret p ℓ T ≤ swapRegret p ℓ T := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hne : (externalRules ι).Nonempty := ⟨Function.const ι i₀, i₀, rfl⟩
  exact modRegret_mono hne (Set.subset_univ _) p ℓ T

/-- Internal regret is at most swap regret (`F^in ⊆ F^sw`, [BlumMansour2007AGT, §4.2, p. 82]). -/
theorem internalRegret_le_swapRegret [DecidableEq ι] [Nonempty ι] (p ℓ : ℕ → ι → ℝ) (T : ℕ) :
    internalRegret p ℓ T ≤ swapRegret p ℓ T := by
  obtain ⟨a₀⟩ := ‹Nonempty ι›
  have hne : (internalRules ι).Nonempty := ⟨switchRule a₀ a₀, a₀, a₀, rfl⟩
  exact modRegret_mono hne (Set.subset_univ _) p ℓ T

/-- When `p t` sums to `1` in every round `t < T`, `externalRegret` equals
`L_H^T - minCumLoss ℓ T` [BlumMansour2007AGT, §4.2, p. 81]. -/
theorem externalRegret_eq_sub_minCumLoss [Nonempty ι] {p ℓ : ℕ → ι → ℝ} {T : ℕ}
    (hp : ∀ t < T, ∑ i, p t i = 1) :
    externalRegret p ℓ T = (∑ t ∈ range T, ∑ i, p t i * ℓ t i) - minCumLoss ℓ T := by
  have hconst : ∀ k : ι, ruleRegret p ℓ T (Function.const ι k) =
      (∑ t ∈ range T, ∑ i, p t i * ℓ t i) - cumLoss ℓ T k := fun k => by
    rw [ruleRegret_eq_sub]
    congr 1
    rw [cumLoss]
    refine sum_congr rfl fun t ht => ?_
    simp only [Function.const_apply, ← sum_mul, hp t (mem_range.mp ht), one_mul]
  have hne : (externalRules ι).Nonempty := by
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    exact ⟨Function.const ι i₀, i₀, rfl⟩
  apply le_antisymm
  · rw [externalRegret, modRegret_le_iff hne]
    rintro _ ⟨k, rfl⟩
    rw [hconst k]
    linarith [minCumLoss_le ℓ T k]
  · obtain ⟨k₀, hk₀⟩ := exists_cumLoss_eq_minCumLoss ℓ T
    rw [← hk₀, ← hconst k₀]
    exact ruleRegret_le_modRegret p ℓ T ⟨k₀, rfl⟩

/-- Internal regret equals `max_{a, b} ∑ t < T, p t a * (ℓ t a - ℓ t b)`
[BlumMansour2007AGT, §4.2, p. 82]. -/
theorem internalRegret_eq_sup [DecidableEq ι] [Nonempty ι] (p ℓ : ℕ → ι → ℝ) (T : ℕ) :
    internalRegret p ℓ T =
      (univ ×ˢ univ : Finset (ι × ι)).sup' (univ_nonempty.product univ_nonempty)
        fun ab => ∑ t ∈ range T, p t ab.1 * (ℓ t ab.1 - ℓ t ab.2) := by
  obtain ⟨a₀⟩ := ‹Nonempty ι›
  have hne : (internalRules ι).Nonempty := ⟨switchRule a₀ a₀, a₀, a₀, rfl⟩
  apply le_antisymm
  · rw [internalRegret, modRegret_le_iff hne]
    rintro _ ⟨a, b, rfl⟩
    rw [ruleRegret_switchRule]
    have hab : (a, b) ∈ (univ ×ˢ univ : Finset (ι × ι)) := mem_product.mpr ⟨mem_univ a, mem_univ b⟩
    exact le_sup' (fun ab : ι × ι => ∑ t ∈ range T, p t ab.1 * (ℓ t ab.1 - ℓ t ab.2)) hab
  · refine Finset.sup'_le _ _ fun ab _ => ?_
    rw [← ruleRegret_switchRule]
    exact ruleRegret_le_modRegret p ℓ T ⟨ab.1, ab.2, rfl⟩

/-- Swap regret decomposes coordinatewise as
`∑ i, max_j ∑ t < T, p t i * (ℓ t i - ℓ t j)` [BlumMansour2007AGT, §4.2, p. 82]. -/
theorem swapRegret_eq_sum_sup [Nonempty ι] (p ℓ : ℕ → ι → ℝ) (T : ℕ) :
    swapRegret p ℓ T =
      ∑ i, univ.sup' univ_nonempty fun j => ∑ t ∈ range T, p t i * (ℓ t i - ℓ t j) := by
  have hswap : ∀ f : ι → ι, ruleRegret p ℓ T f =
      ∑ i, ∑ t ∈ range T, p t i * (ℓ t i - ℓ t (f i)) := fun f => by
    unfold ruleRegret
    exact sum_comm
  apply le_antisymm
  · rw [swapRegret_le_iff]
    intro f
    rw [hswap f]
    exact sum_le_sum fun i _ =>
      le_sup' (fun j => ∑ t ∈ range T, p t i * (ℓ t i - ℓ t j)) (mem_univ (f i))
  · -- Choose `f* i` maximizing `∑ t < T, p t i * (ℓ t i - ℓ t j)` for each `i`.
    have hmax : ∀ i : ι, ∃ j : ι,
        univ.sup' univ_nonempty (fun k => ∑ t ∈ range T, p t i * (ℓ t i - ℓ t k)) =
          ∑ t ∈ range T, p t i * (ℓ t i - ℓ t j) := fun i => by
      obtain ⟨j, _, hj⟩ := exists_mem_eq_sup' univ_nonempty
        (fun k => ∑ t ∈ range T, p t i * (ℓ t i - ℓ t k))
      exact ⟨j, hj⟩
    choose f hf using hmax
    have hle := ruleRegret_le_modRegret (F := swapRules ι) p ℓ T (Set.mem_univ f)
    rw [hswap f] at hle
    refine (le_of_eq ?_).trans hle
    exact sum_congr rfl fun i _ => hf i

/-! ### Exercise 4.1: Swap regret vs. internal regret -/

/-- **Swap regret is at most `N` times internal regret** [BlumMansour2007AGT, Exercise 4.1,
p. 101]. -/
theorem swapRegret_le_card_mul_internalRegret [DecidableEq ι] (p ℓ : ℕ → ι → ℝ) (T : ℕ) :
    swapRegret p ℓ T ≤ Fintype.card ι * internalRegret p ℓ T := by
  rcases isEmpty_or_nonempty ι with hEmpty | hNe
  · have hsub : Subsingleton (ι → ι) := inferInstance
    have hf : swapRules ι = {id} := Set.ext fun f => by
      simp only [swapRules, Set.mem_univ, Set.mem_singleton_iff, Subsingleton.elim f id]
    simp only [swapRegret, modRegret, hf, Set.image_singleton, ruleRegret_id, csSup_singleton,
      Fintype.card_eq_zero, Nat.cast_zero, zero_mul, le_rfl]
  · rw [swapRegret_eq_sum_sup]
    calc ∑ i, univ.sup' univ_nonempty (fun j => ∑ t ∈ range T, p t i * (ℓ t i - ℓ t j))
        ≤ ∑ _i : ι, internalRegret p ℓ T := sum_le_sum fun i _ => by
            refine Finset.sup'_le _ _ fun j _ => ?_
            rw [← ruleRegret_switchRule]
            exact ruleRegret_le_modRegret p ℓ T ⟨i, j, rfl⟩
      _ = Fintype.card ι * internalRegret p ℓ T := by
          rw [sum_const, card_univ, nsmul_eq_mul]

/-- **Tightness of Exercise 4.1**: for every `N ≥ 2`, on `Fin N` over `T = N` rounds, uniform play
against the constant `{0, 1}` loss vector `(0, 1, …, 1)` has `internalRegret = 1` and
`swapRegret = N - 1` (showing an `Ω(N)` gap between internal and swap regret). -/
theorem exists_swapRegret_eq_pred_card_mul_internalRegret {N : ℕ} (hN : 2 ≤ N) :
    ∃ (p ℓ : ℕ → Fin N → ℝ),
      (∀ t < N, (∀ i, 0 ≤ p t i) ∧ ∑ i, p t i = 1) ∧
      (∀ t < N, ∀ i, ℓ t i = 0 ∨ ℓ t i = 1) ∧
      internalRegret p ℓ N = 1 ∧
      swapRegret p ℓ N = (N : ℝ) - 1 := by
  have : NeZero N := ⟨by omega⟩
  have hN_pos : (0 : ℝ) < N := by positivity
  let p : ℕ → Fin N → ℝ := fun _ _ => 1 / (N : ℝ)
  let ℓ : ℕ → Fin N → ℝ := fun _ i => if i = 0 then 0 else 1
  refine ⟨p, ℓ, ?_, ?_, ?_, ?_⟩
  · intro _ _
    refine ⟨fun _ => by positivity, ?_⟩
    simp only [p, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · intro _ _ i
    dsimp only [ℓ]
    split_ifs <;> simp
  · -- `internalRegret p ℓ N = 1`:
    have hterm : ∀ a b : Fin N,
        ∑ t ∈ range N, p t a * (ℓ t a - ℓ t b) =
          (if a = 0 then 0 else 1) - if b = 0 then 0 else 1 := by
      intro a b
      simp only [p, ℓ, sum_const, card_range, nsmul_eq_mul]
      field_simp
    apply le_antisymm
    · have hne : (internalRules (Fin N)).Nonempty := ⟨switchRule 0 0, 0, 0, rfl⟩
      rw [internalRegret, modRegret_le_iff hne]
      rintro _ ⟨a, b, rfl⟩
      rw [ruleRegret_switchRule, hterm a b]
      split_ifs <;> norm_num
    · let a₁ : Fin N := ⟨1, by omega⟩
      have ha₁ : a₁ ≠ 0 := by simp [a₁, Fin.ext_iff]
      have hle := ruleRegret_le_modRegret (F := internalRules (Fin N)) p ℓ N ⟨a₁, 0, rfl⟩
      rw [ruleRegret_switchRule, hterm a₁ 0] at hle
      simp only [ha₁, ↓reduceIte, sub_zero] at hle
      exact hle
  · -- `swapRegret p ℓ N = N - 1`:
    rw [swapRegret_eq_sum_sup]
    have hsup : ∀ i : Fin N,
        univ.sup' univ_nonempty (fun j => ∑ t ∈ range N, p t i * (ℓ t i - ℓ t j)) =
          if i = 0 then 0 else 1 := by
      intro i
      have hterm : ∀ j : Fin N,
          ∑ t ∈ range N, p t i * (ℓ t i - ℓ t j) =
            (if i = 0 then 0 else 1) - if j = 0 then 0 else 1 := fun j => by
        simp only [p, ℓ, sum_const, card_range, nsmul_eq_mul]
        field_simp
      apply le_antisymm
      · refine Finset.sup'_le _ _ fun j _ => ?_
        rw [hterm j]
        split_ifs <;> norm_num
      · have h0 := le_sup' (fun j => ∑ t ∈ range N, p t i * (ℓ t i - ℓ t j)) (mem_univ (0 : Fin N))
        rw [hterm 0] at h0
        simp only [↓reduceIte, sub_zero] at h0
        exact h0
    simp only [hsup]
    rw [← add_sum_erase _ _ (mem_univ (0 : Fin N))]
    simp only [↓reduceIte, zero_add]
    have herase : ∑ i ∈ univ.erase (0 : Fin N), (if i = 0 then (0 : ℝ) else 1) =
        ∑ _i ∈ univ.erase (0 : Fin N), (1 : ℝ) :=
      sum_congr rfl fun i hi => by simp [ne_of_mem_erase hi]
    rw [herase, sum_const, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, Nat.cast_sub (by omega), Nat.cast_one]

/-! ### Exercise 4.2: Unbounded swap-to-external regret ratio for `N = 3` -/

/-- Six-round `{0, 1}` loss cycle on `Fin 3` for Exercise 4.2. -/
private def ex42Loss (t : ℕ) : Fin 3 → ℝ :=
  match t % 6 with
  | 0 => ![1, 0, 1]
  | 1 => ![0, 0, 1]
  | 2 => ![1, 1, 0]
  | 3 => ![1, 0, 0]
  | 4 => ![0, 1, 1]
  | _ => ![0, 1, 0]

/-- Deterministic play cycle on `Fin 3` for Exercise 4.2 (`0, 0, 1, 1, 2, 2` mod `6`). -/
private def ex42Play (t : ℕ) : Fin 3 → ℝ :=
  match t % 6 with
  | 0 | 1 => ![1, 0, 0]
  | 2 | 3 => ![0, 1, 0]
  | _ => ![0, 0, 1]

private theorem ex42_six_step_learner (b : ℕ) :
    ∑ r ∈ range 6, ∑ i : Fin 3, ex42Play (6 * b + r) i * ex42Loss (6 * b + r) i = 3 := by
  have hm : ∀ r, (6 * b + r) % 6 = r % 6 := Nat.mul_add_mod_self_left 6 b
  have heq : ∑ r ∈ range 6, ∑ i : Fin 3, ex42Play (6 * b + r) i * ex42Loss (6 * b + r) i =
      ∑ r ∈ range 6, ∑ i : Fin 3, ex42Play r i * ex42Loss r i :=
    sum_congr rfl fun r _ => sum_congr rfl fun i _ => by simp only [ex42Play, ex42Loss, hm r]
  rw [heq]
  norm_num [sum_range_succ, Fin.sum_univ_three, ex42Play, ex42Loss]

private theorem ex42_six_step_action (b : ℕ) (k : Fin 3) :
    ∑ r ∈ range 6, ex42Loss (6 * b + r) k = 3 := by
  have hm : ∀ r, (6 * b + r) % 6 = r % 6 := Nat.mul_add_mod_self_left 6 b
  have heq : ∑ r ∈ range 6, ex42Loss (6 * b + r) k = ∑ r ∈ range 6, ex42Loss r k :=
    sum_congr rfl fun r _ => by simp only [ex42Loss, hm r]
  rw [heq]
  fin_cases k <;> norm_num [sum_range_succ, ex42Loss]

private theorem ex42_six_step_shift (b : ℕ) :
    ∑ r ∈ range 6, ∑ i : Fin 3, ex42Play (6 * b + r) i * ex42Loss (6 * b + r) (![1, 2, 0] i) =
      0 := by
  have hm : ∀ r, (6 * b + r) % 6 = r % 6 := Nat.mul_add_mod_self_left 6 b
  have heq :
      ∑ r ∈ range 6, ∑ i : Fin 3, ex42Play (6 * b + r) i * ex42Loss (6 * b + r) (![1, 2, 0] i) =
      ∑ r ∈ range 6, ∑ i : Fin 3, ex42Play r i * ex42Loss r (![1, 2, 0] i) :=
    sum_congr rfl fun r _ => sum_congr rfl fun i _ => by simp only [ex42Play, ex42Loss, hm r]
  rw [heq]
  norm_num [sum_range_succ, Fin.sum_univ_three, ex42Play, ex42Loss]

private theorem ex42Play_binary (t : ℕ) (i : Fin 3) :
    ex42Play t i = 0 ∨ ex42Play t i = 1 := by
  have hmod : t % 6 < 6 := Nat.mod_lt t (by decide)
  generalize hq : t % 6 = q at hmod
  unfold ex42Play
  rw [hq]
  interval_cases q <;> fin_cases i <;> simp

private theorem ex42Play_nonneg (t : ℕ) (i : Fin 3) : 0 ≤ ex42Play t i := by
  rcases ex42Play_binary t i with h0 | h1 <;> linarith

private theorem ex42Play_sum (t : ℕ) : ∑ i : Fin 3, ex42Play t i = 1 := by
  have hmod : t % 6 < 6 := Nat.mod_lt t (by decide)
  generalize hq : t % 6 = q at hmod
  unfold ex42Play
  rw [hq]
  interval_cases q <;> norm_num [Fin.sum_univ_three]

private theorem ex42Loss_binary (t : ℕ) (i : Fin 3) :
    ex42Loss t i = 0 ∨ ex42Loss t i = 1 := by
  have hmod : t % 6 < 6 := Nat.mod_lt t (by decide)
  generalize hq : t % 6 = q at hmod
  unfold ex42Loss
  rw [hq]
  interval_cases q <;> fin_cases i <;> simp

private theorem ex42Loss_nonneg (t : ℕ) (i : Fin 3) : 0 ≤ ex42Loss t i := by
  rcases ex42Loss_binary t i with h0 | h1 <;> linarith

private theorem ex42_learner_six_mul (m : ℕ) :
    ∑ t ∈ range (6 * m), ∑ i : Fin 3, ex42Play t i * ex42Loss t i = 3 * (m : ℝ) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [show 6 * (k + 1) = 6 * k + 6 by omega, sum_range_add, ih, ex42_six_step_learner k]
    push_cast
    ring

private theorem ex42_cumLoss_six_mul (m : ℕ) (j : Fin 3) :
    cumLoss ex42Loss (6 * m) j = 3 * (m : ℝ) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [show 6 * (k + 1) = 6 * k + 6 by omega, cumLoss, sum_range_add, ← cumLoss, ih,
      ex42_six_step_action k j]
    push_cast
    ring

private theorem ex42_shift_six_mul (m : ℕ) :
    ∑ t ∈ range (6 * m), ∑ i : Fin 3, ex42Play t i * ex42Loss t (![1, 2, 0] i) = 0 := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [show 6 * (k + 1) = 6 * k + 6 by omega, sum_range_add, ih, ex42_six_step_shift k, add_zero]

/-- **Zero external regret with arbitrarily large swap regret for `N = 3`**
[BlumMansour2007AGT, Exercise 4.2, p. 101]: for every `m : ℕ`, over `T = 6 * m` rounds on `Fin 3`
there exist `{0, 1}`-valued deterministic plays `p` and `{0, 1}`-valued losses `ℓ` with
`externalRegret p ℓ (6 * m) = 0` and `swapRegret p ℓ (6 * m) = 3 * m`. -/
theorem exists_externalRegret_zero_and_swapRegret_eq (m : ℕ) :
    ∃ (p ℓ : ℕ → Fin 3 → ℝ),
      (∀ t < 6 * m, (∀ i, p t i = 0 ∨ p t i = 1) ∧ ∑ i, p t i = 1) ∧
      (∀ t < 6 * m, ∀ i, ℓ t i = 0 ∨ ℓ t i = 1) ∧
      externalRegret p ℓ (6 * m) = 0 ∧
      swapRegret p ℓ (6 * m) = 3 * (m : ℝ) := by
  refine ⟨ex42Play, ex42Loss, fun t _ => ⟨ex42Play_binary t, ex42Play_sum t⟩,
    fun t _ => ex42Loss_binary t, ?_, ?_⟩
  · rw [externalRegret_eq_sub_minCumLoss (fun t _ => ex42Play_sum t), ex42_learner_six_mul m]
    have hmin : minCumLoss ex42Loss (6 * m) = 3 * (m : ℝ) := by
      apply le_antisymm
      · exact (minCumLoss_le _ _ 0).trans_eq (ex42_cumLoss_six_mul m 0)
      · exact le_minCumLoss_iff.mpr fun j => (ex42_cumLoss_six_mul m j).symm.le
    rw [hmin, sub_self]
  · apply le_antisymm
    · rw [swapRegret_le_iff]
      intro δ
      rw [ruleRegret_eq_sub, ex42_learner_six_mul m]
      have hnn : 0 ≤ ∑ t ∈ range (6 * m), ∑ i : Fin 3, ex42Play t i * ex42Loss t (δ i) :=
        sum_nonneg fun t _ => sum_nonneg fun i _ =>
          mul_nonneg (ex42Play_nonneg t i) (ex42Loss_nonneg t (δ i))
      linarith
    · have hle := ruleRegret_le_modRegret (F := swapRules (Fin 3)) ex42Play ex42Loss (6 * m)
        (Set.mem_univ ![1, 2, 0])
      rw [ruleRegret_eq_sub, ex42_learner_six_mul m, ex42_shift_six_mul m, sub_zero] at hle
      exact hle

/-- **Unbounded ratio between swap regret and positive external regret for `N = 3`**
[BlumMansour2007AGT, Exercise 4.2, p. 101]: for every real `M`, there exist a horizon `T`,
deterministic plays `p`, and `{0, 1}` losses `ℓ` on `Fin 3` such that `0 < externalRegret p ℓ T`
and `M * externalRegret p ℓ T < swapRegret p ℓ T`. -/
theorem exists_unbounded_swapRegret_div_externalRegret (M : ℝ) :
    ∃ (T : ℕ) (p ℓ : ℕ → Fin 3 → ℝ),
      (∀ t < T, (∀ i, 0 ≤ p t i) ∧ ∑ i, p t i = 1) ∧
      (∀ t < T, ∀ i, ℓ t i = 0 ∨ ℓ t i = 1) ∧
      0 < externalRegret p ℓ T ∧
      M * externalRegret p ℓ T < swapRegret p ℓ T := by
  obtain ⟨m, hm⟩ := exists_nat_gt M
  set T := 6 * m + 1
  have hlast_play : ex42Play (6 * m) = ![1, 0, 0] := by
    simp [ex42Play, Nat.mul_mod_right]
  have hlast_loss : ex42Loss (6 * m) = ![1, 0, 1] := by
    simp [ex42Loss, Nat.mul_mod_right]
  have hlearnerT : ∑ t ∈ range T, ∑ i : Fin 3, ex42Play t i * ex42Loss t i = 3 * (m : ℝ) + 1 := by
    dsimp only [T]
    rw [sum_range_succ, ex42_learner_six_mul m, hlast_play, hlast_loss]
    norm_num [Fin.sum_univ_three]
  have hminT : minCumLoss ex42Loss T = 3 * (m : ℝ) := by
    apply le_antisymm
    · calc minCumLoss ex42Loss T ≤ cumLoss ex42Loss (6 * m + 1) 1 := minCumLoss_le _ _ 1
        _ = 3 * (m : ℝ) := by rw [cumLoss_succ, ex42_cumLoss_six_mul m 1, hlast_loss]; simp
    · refine le_minCumLoss_iff.mpr fun j => ?_
      dsimp only [T]
      rw [cumLoss_succ, ex42_cumLoss_six_mul m j, hlast_loss]
      fin_cases j <;> norm_num
  have hext : externalRegret ex42Play ex42Loss T = 1 := by
    rw [externalRegret_eq_sub_minCumLoss (fun t _ => ex42Play_sum t), hlearnerT, hminT]
    ring
  refine ⟨T, ex42Play, ex42Loss, fun t _ => ⟨ex42Play_nonneg t, ex42Play_sum t⟩,
    fun t _ => ex42Loss_binary t, ?_, ?_⟩
  · linarith
  · have hshiftT : ∑ t ∈ range T, ∑ i : Fin 3,
        ex42Play t i * ex42Loss t (![1, 2, 0] i) = 0 := by
      dsimp only [T]
      rw [sum_range_succ, ex42_shift_six_mul m, hlast_play, hlast_loss]
      norm_num [Fin.sum_univ_three]
    have hswap : 3 * (m : ℝ) + 1 ≤ swapRegret ex42Play ex42Loss T := by
      have hle := ruleRegret_le_modRegret (F := swapRules (Fin 3)) ex42Play ex42Loss T
        (Set.mem_univ ![1, 2, 0])
      rw [ruleRegret_eq_sub, hlearnerT, hshiftT, sub_zero] at hle
      exact hle
    rw [hext, mul_one]
    linarith

/-! ### Exercise 4.6: `O(√(N T log N))` swap regret via Hedge and Polynomial Weights copies -/

/-- Bridge from `blumMansour_swap_regret_le_sqrt` (`SwapRegret.lean`) to `swapRegret`: with Hedge
copies and `T ≥ N ln N`, `swapRegret` is at most `2 √(T N ln N)`. -/
theorem swapRegret_blumMansourProb_le_sqrt [DecidableEq ι] (hn : 2 ≤ Fintype.card ι) {T : ℕ}
    (hT : Fintype.card ι * log (Fintype.card ι) ≤ T) {ℓ : ℕ → ι → ℝ}
    (hℓ : ∀ s < T, ∀ i, |ℓ s i| ≤ 1) :
    swapRegret (blumMansourProb √(Fintype.card ι * log (Fintype.card ι) / T) ℓ) ℓ T ≤
      2 * √(T * (Fintype.card ι * log (Fintype.card ι))) := by
  rw [swapRegret_le_iff]
  intro δ
  rw [ruleRegret_eq_sub]
  linarith [blumMansour_swap_regret_le_sqrt hn hT hℓ δ]

section PolynomialWeightsCopies

variable [DecidableEq ι]

/-- Weights of the `N` Polynomial Weights (`mwFactor η`) copies in the Blum–Mansour swap-regret
reduction [BlumMansour2007AGT, §4.5 and Exercise 4.6, p. 101]. -/
private noncomputable def blumMansourPWWeight (η : ℝ) (ℓ : ℕ → ι → ℝ) : ℕ → ι → ι → ℝ
  | 0 => fun _ _ => 1
  | t + 1 => fun j i => blumMansourPWWeight η ℓ t j i *
      mwFactor η (stationaryVec (of fun j' i' =>
        blumMansourPWWeight η ℓ t j' i' / ∑ k, blumMansourPWWeight η ℓ t j' k) j * ℓ t i)

private noncomputable def blumMansourPWMatrix (η : ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) : Matrix ι ι ℝ :=
  of fun j i => blumMansourPWWeight η ℓ t j i / ∑ k, blumMansourPWWeight η ℓ t j k

/-- Learner distribution of the Blum–Mansour reduction instantiated with `N` Polynomial Weights
(`mwFactor η`) copies [BlumMansour2007AGT, Exercise 4.6, p. 101]. -/
noncomputable def blumMansourPWProb (η : ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) : ι → ℝ :=
  stationaryVec (blumMansourPWMatrix η ℓ t)

private noncomputable def blumMansourPWLoss (η : ℝ) (ℓ : ℕ → ι → ℝ) (j : ι) (t : ℕ) (i : ι) : ℝ :=
  blumMansourPWProb η ℓ t j * ℓ t i

private theorem blumMansourPWWeight_eq_weight (η : ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) (j : ι) :
    blumMansourPWWeight η ℓ t j = weight (mwFactor η) (blumMansourPWLoss η ℓ j) t := by
  induction t with
  | zero =>
    funext i
    rw [weight_zero]
    rfl
  | succ t ih =>
    funext i
    rw [weight_succ, ← ih]
    rfl

private theorem blumMansourPWMatrix_eq_prob (η : ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) (j : ι) :
    blumMansourPWMatrix η ℓ t j = prob (mwFactor η) (blumMansourPWLoss η ℓ j) t := by
  funext i
  simp only [blumMansourPWMatrix, of_apply, prob, potential, blumMansourPWWeight_eq_weight]

private theorem blumMansourPWWeight_congr {η : ℝ} {ℓ ℓ' : ℕ → ι → ℝ} {t : ℕ}
    (h : ∀ s < t, ℓ s = ℓ' s) :
    blumMansourPWWeight η ℓ t = blumMansourPWWeight η ℓ' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext j i
    dsimp only [blumMansourPWWeight]
    rw [ih fun s hs => h s (by omega), h t (by omega)]

/-- `blumMansourPWProb` depends only on past losses: it is an online algorithm. -/
theorem blumMansourPWProb_congr {η : ℝ} {ℓ ℓ' : ℕ → ι → ℝ} {t : ℕ} (h : ∀ s < t, ℓ s = ℓ' s) :
    blumMansourPWProb η ℓ t = blumMansourPWProb η ℓ' t := by
  simp only [blumMansourPWProb, blumMansourPWMatrix, blumMansourPWWeight_congr h]

private theorem blumMansourPW_rowStochastic_all [Nonempty ι] {η : ℝ} {ℓ : ℕ → ι → ℝ}
    (hη' : η ≤ 1 / 2) (hℓ : ∀ s i, ℓ s i ∈ Set.Icc (0 : ℝ) 1) :
    ∀ t, blumMansourPWMatrix η ℓ t ∈ rowStochastic ℝ ι := by
  intro t
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    have hφ : ∀ j, ∀ s < t, ∀ i, 0 < mwFactor η (blumMansourPWLoss η ℓ j s i) := by
      intro j s hs i
      have hMs := ih s hs
      have hp0 : 0 ≤ blumMansourPWProb η ℓ s j := stationaryVec_nonneg hMs j
      have hp1 : blumMansourPWProb η ℓ s j ≤ 1 :=
        (single_le_sum (fun m _ => stationaryVec_nonneg hMs m) (mem_univ j)).trans_eq
          (sum_stationaryVec hMs)
      have hli0 := (hℓ s i).1
      have hli1 := (hℓ s i).2
      have hprod : blumMansourPWLoss η ℓ j s i ≤ 1 := by
        dsimp only [blumMansourPWLoss]
        nlinarith
      have hnn : 0 ≤ blumMansourPWLoss η ℓ j s i := mul_nonneg hp0 hli0
      rw [mwFactor_apply]
      rcases le_or_gt η 0 with hη0 | hη0 <;> nlinarith
    refine mem_rowStochastic_iff_sum.2 ⟨fun j i => ?_, fun j => ?_⟩
    · rw [blumMansourPWMatrix_eq_prob]
      exact prob_nonneg (hφ j) i
    · rw [blumMansourPWMatrix_eq_prob]
      exact sum_prob (hφ j)

/-- **Blum–Mansour swap regret with Polynomial Weights (`mwFactor`) copies**
[BlumMansour2007AGT, Exercise 4.6, p. 101]: for `[0, 1]`-valued losses and `0 < η ≤ 1 / 2`,
the sum of the copies' second-order losses is bounded by `T`, yielding
`swapRegret (blumMansourPWProb η ℓ) ℓ T ≤ η * T + N * ln N / η`. -/
theorem blumMansourPW_swap_regret_le [Nonempty ι] {η : ℝ} {ℓ : ℕ → ι → ℝ} {T : ℕ}
    (hη : 0 < η) (hη' : η ≤ 1 / 2) (hℓ : ∀ s < T, ∀ i, ℓ s i ∈ Set.Icc (0 : ℝ) 1) :
    swapRegret (blumMansourPWProb η ℓ) ℓ T ≤
      η * T + Fintype.card ι * log (Fintype.card ι) / η := by
  let ℓ' : ℕ → ι → ℝ := fun s i => if s < T then ℓ s i else 0
  have hℓ'_all : ∀ s i, ℓ' s i ∈ Set.Icc (0 : ℝ) 1 := fun s i => by
    dsimp only [ℓ']
    by_cases hs : s < T
    · simp only [hs, ↓reduceIte]
      exact hℓ s hs i
    · simp only [hs, ↓reduceIte, Set.mem_Icc, le_refl, zero_le_one, and_self]
  have hM : ∀ t, blumMansourPWMatrix η ℓ' t ∈ rowStochastic ℝ ι :=
    blumMansourPW_rowStochastic_all hη' hℓ'_all
  have hp_eq : ∀ t < T, blumMansourPWProb η ℓ t = blumMansourPWProb η ℓ' t :=
    fun t ht => blumMansourPWProb_congr fun s hs => by
      funext i
      have hsT : s < T := lt_trans hs ht
      simp [ℓ', hsT]
  rw [swapRegret_le_iff]
  intro δ
  have hreg_eq : ruleRegret (blumMansourPWProb η ℓ) ℓ T δ =
      ruleRegret (blumMansourPWProb η ℓ') ℓ' T δ := by
    unfold ruleRegret
    refine sum_congr rfl fun t ht => ?_
    have ht' := mem_range.mp ht
    simp only [hp_eq t ht', ℓ', ht', ↓reduceIte]
  rw [hreg_eq, ruleRegret_eq_sub, sub_le_iff_le_add']
  refine (swap_regret_le_sum_regret (q := blumMansourPWMatrix η ℓ')
    (R := fun j => η * ∑ t ∈ range T, blumMansourPWProb η ℓ' t j + log (Fintype.card ι) / η)
    (fun t => stationaryVec_vecMul (hM t)) (fun j k => ?_) δ).trans ?_
  · have hbound : ∀ s < T, ∀ i, η * blumMansourPWLoss η ℓ' j s i ≤ 1 / 2 := fun s _ i => by
      have hp0 : 0 ≤ blumMansourPWProb η ℓ' s j := stationaryVec_nonneg (hM s) j
      have hp1 : blumMansourPWProb η ℓ' s j ≤ 1 :=
        (single_le_sum (fun m _ => stationaryVec_nonneg (hM s) m) (mem_univ j)).trans_eq
          (sum_stationaryVec (hM s))
      have hli0 := (hℓ'_all s i).1
      have hli1 := (hℓ'_all s i).2
      have hprod : blumMansourPWLoss η ℓ' j s i ≤ 1 := by
        dsimp only [blumMansourPWLoss]
        nlinarith
      nlinarith
    have hmw := mw_regret_le_sq hη hbound k
    have hsq : ∑ t ∈ range T, blumMansourPWLoss η ℓ' j t k ^ 2 ≤
        ∑ t ∈ range T, blumMansourPWProb η ℓ' t j :=
      sum_le_sum fun t _ => by
        have hp0 : 0 ≤ blumMansourPWProb η ℓ' t j := stationaryVec_nonneg (hM t) j
        have hp1 : blumMansourPWProb η ℓ' t j ≤ 1 :=
          (single_le_sum (fun m _ => stationaryVec_nonneg (hM t) m) (mem_univ j)).trans_eq
            (sum_stationaryVec (hM t))
        have hlk0 := (hℓ'_all t k).1
        have hlk1 := (hℓ'_all t k).2
        have hlk_sq : ℓ' t k ^ 2 ≤ 1 := by nlinarith
        dsimp only [blumMansourPWLoss]
        rw [mul_pow]
        nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hp1),
          mul_nonneg (sq_nonneg (blumMansourPWProb η ℓ' t j)) (sub_nonneg.mpr hlk_sq)]
    simp only [← blumMansourPWMatrix_eq_prob, blumMansourPWLoss, blumMansourPWProb] at hmw hsq ⊢
    linarith [mul_le_mul_of_nonneg_left hsq hη.le]
  · have hsum_p : ∑ j, ∑ t ∈ range T, blumMansourPWProb η ℓ' t j = T := by
      rw [sum_comm]
      have h1 : ∀ t, ∑ j, blumMansourPWProb η ℓ' t j = 1 := fun t => sum_stationaryVec (hM t)
      simp only [h1, sum_const, card_range, nsmul_eq_mul, mul_one]
    have hR : ∑ j, (η * ∑ t ∈ range T, blumMansourPWProb η ℓ' t j + log (Fintype.card ι) / η) =
        η * T + Fintype.card ι * log (Fintype.card ι) / η := by
      rw [sum_add_distrib, ← mul_sum, hsum_p, sum_const, card_univ, nsmul_eq_mul, mul_div_assoc]
    dsimp only [blumMansourPWProb] at hR ⊢
    linarith

/-- **Tuned `2 √(T N ln N)` swap regret with Polynomial Weights copies**
[BlumMansour2007AGT, Exercise 4.6, p. 101]: for `N ≥ 2`, `T ≥ 4 N ln N`, and `[0, 1]`-valued
losses, `blumMansourPWProb` with `η = √(N ln N / T)` achieves swap regret at most
`2 √(T N ln N)`. -/
theorem blumMansourPW_swap_regret_le_sqrt (hn : 2 ≤ Fintype.card ι) {T : ℕ}
    (hT : 4 * (Fintype.card ι * log (Fintype.card ι)) ≤ T) {ℓ : ℕ → ι → ℝ}
    (hℓ : ∀ s < T, ∀ i, ℓ s i ∈ Set.Icc (0 : ℝ) 1) :
    swapRegret (blumMansourPWProb √(Fintype.card ι * log (Fintype.card ι) / T) ℓ) ℓ T ≤
      2 * √(T * (Fintype.card ι * log (Fintype.card ι))) := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  set L := (Fintype.card ι : ℝ) * log (Fintype.card ι)
  have hL : 0 < L := mul_pos (Nat.cast_pos.mpr (by omega)) (log_pos (by exact_mod_cast hn))
  have hT0 : (0 : ℝ) < T := by linarith
  have hη : 0 < √(L / T) := sqrt_pos.mpr (div_pos hL hT0)
  have hη' : √(L / T) ≤ 1 / 2 := by
    rw [show (1 / 2 : ℝ) = √(1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt (by rw [div_le_iff₀ hT0]; linarith)
  refine (blumMansourPW_swap_regret_le hη hη' hℓ).trans_eq ?_
  exact sqrt_div_mul_add_div_sqrt_div hL hT0

end PolynomialWeightsCopies

end Cslib.MachineLearning.OnlineLearning.Experts
