/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.OnlineLearning.Greedy
public import CslibFrontier.MachineLearning.OnlineLearning.Hedge
public import CslibFrontier.MachineLearning.OnlineLearning.MultiplicativeWeights
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Modification rules, internal/swap regret separations, and dominated-action weight decay

This module formalizes the memoryless modification-rule framework `R_F` of
[BlumMansour2007AGT, §4.2, pp. 81–82], specializing to external regret
(`Set.range (Function.const ι)`), pairwise internal regret (`internalRules ι`), and swap regret
(`Set.univ`), together with Exercises 4.1, 4.2, and 4.8 ([BlumMansour2007AGT, §4.4.4, pp. 91–92,
and p. 101]):

* **Modification-rule regret and bridges** (`modRegret`, `internalRules`, `modRegret_le_iff`,
  `modRegret_univ_le_iff`, `modRegret_univ_eq_sum_sup`, `modRegret_range_const`,
  `modRegret_internalRules_le_iff` — [BlumMansour2007AGT, §4.2, pp. 81–82]):
  For a family `F : Set (ι → ι)` of memoryless modification rules, `modRegret F p ℓ T` is
  `sup_{f ∈ F} (L_H^T - L_{H, f}^T)`. Specializing `F` to `Set.univ` bridges directly via
  `modRegret_univ_le_iff` (`@[simp]`) to the universal swap-regret inequality of `SwapRegret.lean`
  and decomposes coordinatewise as `∑ i, max_j ∑ t < T, p t i * (ℓ t i - ℓ t j)`
  (`modRegret_univ_eq_sum_sup`). Specializing `F` to `Set.range (Function.const ι)` recovers
  `(∑ t < T, ⟨p t, ℓ t⟩) - minCumLoss ℓ T` (`modRegret_range_const`), while `internalRules ι`
  consists of the single-action switches `Function.update id a b` (including `a = b`, matching the
  displayed formula `max_{i, j ∈ X} ∑_t p_i^t (ℓ_i^t - ℓ_j^t)` on p. 82 so that internal regret is
  nonnegative).
* **Exercise 4.1 and tightness** (`modRegret_univ_le_card_mul_internalRules`,
  `exists_modRegret_univ_eq_sub_one` — [BlumMansour2007AGT, Exercise 4.1, p. 101]):
  Swap regret is at most `N` times internal regret, and an original tightness construction on
  `Fin N` (`N ≥ 2`) with uniform play and `{0, 1}` losses achieves internal regret `1` and swap
  regret `N - 1`.
* **Exercise 4.2** (`exists_modRegret_const_zero_and_univ_eq`,
  `exists_unbounded_modRegret_univ_div_const` — [BlumMansour2007AGT, Exercise 4.2, p. 101]):
  On `Fin 3` (`N = 3`) with deterministic `{0, 1}` play and `{0, 1}` losses, external regret can
  vanish while swap regret equals `3 m` for arbitrary `m : ℕ`, and appending one round makes
  external regret equal to `1 > 0` while the ratio of swap regret to external regret exceeds any
  prescribed real bound `M`.
* **Exercise 4.8** (`sum_prob_hedgeFactor_le_of_dominated`, `sum_prob_mwFactor_le_of_dominated`,
  `exists_nonpos_external_regret_dominated_weight` — [BlumMansour2007AGT, §4.4.4, pp. 91–92, and
  Exercise 4.8, p. 101]):
  Under `hedgeFactor η` (which also covers `[0, 1]` Randomized Weighted Majority `(1 - η') ^ ℓ` via
  `η = -log (1 - η')`), the total probability assigned over any horizon `T` to an action
  `ε`-dominated by a mixed strategy is at most `1 / (1 - exp (-(η * ε)))`. Under Polynomial Weights
  (`mwFactor η`, coinciding with RWM on `{0, 1}` losses), the total probability assigned to an
  action pure-`ε`-dominated by `k` is at most `1 / (η * ε)`. By contrast, low external regret alone
  does not suppress dominated actions: on `Fin 3`, deterministic play can achieve nonpositive
  external regret while placing time-average weight `1 / 2` on an `ε`-dominated action.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.Experts.modRegret`: cumulative regret `R_F` against a
  family `F : Set (ι → ι)` of memoryless modification rules.
* `Cslib.MachineLearning.OnlineLearning.Experts.internalRules`: the family `F^in` of single-action
  switch rules `Function.update id a b`.

## Main results

* `Cslib.MachineLearning.OnlineLearning.Experts.modRegret_le_iff`,
  `Cslib.MachineLearning.OnlineLearning.Experts.modRegret_mono`: characterization and monotonicity
  of `modRegret`.
* `Cslib.MachineLearning.OnlineLearning.Experts.modRegret_univ_le_iff`,
  `Cslib.MachineLearning.OnlineLearning.Experts.modRegret_univ_eq_sum_sup`,
  `Cslib.MachineLearning.OnlineLearning.Experts.modRegret_range_const`,
  `Cslib.MachineLearning.OnlineLearning.Experts.modRegret_range_const_le_iff`,
  `Cslib.MachineLearning.OnlineLearning.Experts.modRegret_internalRules_le_iff`: bridges from
  `R_F` to swap regret, `minCumLoss` external regret, and pairwise internal regret
  ([BlumMansour2007AGT, §4.2]).
* `Cslib.MachineLearning.OnlineLearning.Experts.modRegret_univ_le_card_mul_internalRules`:
  [BlumMansour2007AGT, Exercise 4.1].
* `Cslib.MachineLearning.OnlineLearning.Experts.exists_modRegret_univ_eq_sub_one`:
  original `N - 1` tightness witness for Exercise 4.1.
* `Cslib.MachineLearning.OnlineLearning.Experts.exists_modRegret_const_zero_and_univ_eq`,
  `Cslib.MachineLearning.OnlineLearning.Experts.exists_unbounded_modRegret_univ_div_const`:
  [BlumMansour2007AGT, Exercise 4.2].
* `Cslib.MachineLearning.OnlineLearning.Experts.sum_prob_hedgeFactor_le_of_dominated`,
  `Cslib.MachineLearning.OnlineLearning.Experts.sum_prob_mwFactor_le_of_dominated`,
  `Cslib.MachineLearning.OnlineLearning.Experts.exists_nonpos_external_regret_dominated_weight`:
  [BlumMansour2007AGT, Exercise 4.8].

## References

* [A. Blum and Y. Mansour, *Learning, Regret Minimization, and Equilibria*][BlumMansour2007AGT]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.Experts

open Finset Function Real

variable {ι : Type*} [Fintype ι]

/-! ### Memoryless modification rules and `F`-regret -/

/-- Cumulative regret `R_F = sup_{f ∈ F} (L_H^T - L_{H, f}^T)` of round weights `p` against a
family `F : Set (ι → ι)` of memoryless modification rules over `T` rounds
[BlumMansour2007AGT, §4.2, p. 82]. -/
noncomputable def modRegret (F : Set (ι → ι)) (p ℓ : ℕ → ι → ℝ) (T : ℕ) : ℝ :=
  sSup ((fun f : ι → ι =>
    (∑ t ∈ range T, ∑ i, p t i * ℓ t i) - ∑ t ∈ range T, ∑ i, p t i * ℓ t (f i)) '' F)

private theorem bddAbove_modRegret_image (F : Set (ι → ι)) (p ℓ : ℕ → ι → ℝ) (T : ℕ) :
    BddAbove ((fun f : ι → ι =>
      (∑ t ∈ range T, ∑ i, p t i * ℓ t i) - ∑ t ∈ range T, ∑ i, p t i * ℓ t (f i)) '' F) :=
  (Set.toFinite _).bddAbove

/-- Regret against any single rule `f ∈ F` is bounded by `modRegret F p ℓ T`. -/
theorem sub_le_modRegret {F : Set (ι → ι)} (p ℓ : ℕ → ι → ℝ) (T : ℕ) {f : ι → ι} (hf : f ∈ F) :
    (∑ t ∈ range T, ∑ i, p t i * ℓ t i) - ∑ t ∈ range T, ∑ i, p t i * ℓ t (f i) ≤
      modRegret F p ℓ T :=
  le_csSup (bddAbove_modRegret_image F p ℓ T) ⟨f, hf, rfl⟩

/-- For nonempty `F`, `modRegret F p ℓ T ≤ R` iff shifting actions by any `f ∈ F` reduces total
expected loss by at most `R`. -/
theorem modRegret_le_iff {F : Set (ι → ι)} (hF : F.Nonempty) {p ℓ : ℕ → ι → ℝ} {T : ℕ} {R : ℝ} :
    modRegret F p ℓ T ≤ R ↔
      ∀ f ∈ F, ∑ t ∈ range T, ∑ i, p t i * ℓ t i ≤
        ∑ t ∈ range T, ∑ i, p t i * ℓ t (f i) + R := by
  unfold modRegret
  rw [csSup_le_iff (bddAbove_modRegret_image F p ℓ T) (hF.image _)]
  simp only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    sub_le_iff_le_add']

/-- Larger modification-rule families have larger `modRegret`
[BlumMansour2007AGT, §4.2, p. 82]. -/
theorem modRegret_mono {F₁ F₂ : Set (ι → ι)} (hF₁ : F₁.Nonempty) (hsub : F₁ ⊆ F₂)
    (p ℓ : ℕ → ι → ℝ) (T : ℕ) :
    modRegret F₁ p ℓ T ≤ modRegret F₂ p ℓ T :=
  csSup_le_csSup (bddAbove_modRegret_image F₂ p ℓ T) (hF₁.image _) (Set.image_mono hsub)

/-- Any rule family containing `id` has nonnegative `modRegret`. -/
theorem modRegret_nonneg_of_id_mem {F : Set (ι → ι)} (hid : id ∈ F)
    (p ℓ : ℕ → ι → ℝ) (T : ℕ) : 0 ≤ modRegret F p ℓ T := by
  have h := sub_le_modRegret p ℓ T hid
  simpa only [id_eq, sub_self] using h

/-! ### Bridges to swap regret, external regret, and internal regret -/

/-- Bridge from `modRegret Set.univ` (`R_{F^sw}`) to the universal swap-regret inequality of
`SwapRegret.lean` [BlumMansour2007AGT, §4.2, p. 82]. -/
@[simp] theorem modRegret_univ_le_iff {p ℓ : ℕ → ι → ℝ} {T : ℕ} {R : ℝ} :
    modRegret Set.univ p ℓ T ≤ R ↔
      ∀ δ : ι → ι, ∑ t ∈ range T, ∑ i, p t i * ℓ t i ≤
        ∑ t ∈ range T, ∑ i, p t i * ℓ t (δ i) + R := by
  rw [modRegret_le_iff ⟨id, Set.mem_univ _⟩]
  exact ⟨fun h δ => h δ (Set.mem_univ δ), fun h δ _ => h δ⟩

/-- Coordinatewise closed form of swap regret `modRegret Set.univ`:
`∑ i, max_j ∑ t < T, p t i * (ℓ t i - ℓ t j)` [BlumMansour2007AGT, §4.2, p. 82]. -/
theorem modRegret_univ_eq_sum_sup [Nonempty ι] (p ℓ : ℕ → ι → ℝ) (T : ℕ) :
    modRegret Set.univ p ℓ T =
      ∑ i, univ.sup' univ_nonempty fun j => ∑ t ∈ range T, p t i * (ℓ t i - ℓ t j) := by
  have hswap : ∀ f : ι → ι,
      (∑ t ∈ range T, ∑ i, p t i * ℓ t i) - ∑ t ∈ range T, ∑ i, p t i * ℓ t (f i) =
        ∑ i, ∑ t ∈ range T, p t i * (ℓ t i - ℓ t (f i)) := fun f => by
    calc (∑ t ∈ range T, ∑ i, p t i * ℓ t i) - ∑ t ∈ range T, ∑ i, p t i * ℓ t (f i)
        = ∑ t ∈ range T, ∑ i, p t i * (ℓ t i - ℓ t (f i)) := by simp only [mul_sub, sum_sub_distrib]
      _ = ∑ i, ∑ t ∈ range T, p t i * (ℓ t i - ℓ t (f i)) := sum_comm
  apply le_antisymm
  · rw [modRegret_univ_le_iff]
    intro f
    rw [← sub_le_iff_le_add', hswap f]
    exact sum_le_sum fun i _ =>
      le_sup' (fun j => ∑ t ∈ range T, p t i * (ℓ t i - ℓ t j)) (mem_univ (f i))
  · have hmax : ∀ i : ι, ∃ j : ι,
        univ.sup' univ_nonempty (fun k => ∑ t ∈ range T, p t i * (ℓ t i - ℓ t k)) =
          ∑ t ∈ range T, p t i * (ℓ t i - ℓ t j) := fun i => by
      obtain ⟨j, _, hj⟩ := exists_mem_eq_sup' univ_nonempty
        (fun k => ∑ t ∈ range T, p t i * (ℓ t i - ℓ t k))
      exact ⟨j, hj⟩
    choose f hf using hmax
    have hle := sub_le_modRegret (F := Set.univ) p ℓ T (Set.mem_univ f)
    rw [hswap f] at hle
    exact (sum_congr rfl fun i _ => hf i).le.trans hle

/-- When `p t` sums to `1` in every round `t < T`, `modRegret` over the constant modification rules
`Set.range (Function.const ι)` (`F^ex`) equals `(∑ t < T, ⟨p t, ℓ t⟩) - minCumLoss ℓ T`
[BlumMansour2007AGT, §4.2, pp. 81–82]. -/
theorem modRegret_range_const [Nonempty ι] {p ℓ : ℕ → ι → ℝ} {T : ℕ}
    (hp : ∀ t < T, ∑ i, p t i = 1) :
    modRegret (Set.range (Function.const ι)) p ℓ T =
      (∑ t ∈ range T, ∑ i, p t i * ℓ t i) - minCumLoss ℓ T := by
  have hconst : ∀ k : ι,
      (∑ t ∈ range T, ∑ i, p t i * ℓ t i) -
          ∑ t ∈ range T, ∑ i, p t i * ℓ t (Function.const ι k i) =
        (∑ t ∈ range T, ∑ i, p t i * ℓ t i) - ∑ t ∈ range T, ℓ t k := fun k => by
    congr 1
    refine sum_congr rfl fun t ht => ?_
    simp only [const_apply, ← sum_mul, hp t (mem_range.mp ht), one_mul]
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hne : (Set.range (Function.const ι)).Nonempty := ⟨Function.const ι i₀, i₀, rfl⟩
  apply le_antisymm
  · rw [modRegret_le_iff hne]
    rintro _ ⟨k, rfl⟩
    have hk := minCumLoss_le ℓ T k
    have hc := hconst k
    linarith
  · obtain ⟨k₀, hk₀⟩ := exists_sum_eq_minCumLoss ℓ T
    rw [← hk₀, ← hconst k₀]
    exact sub_le_modRegret p ℓ T ⟨k₀, rfl⟩

/-- Characterization of bounded external regret via `modRegret (Set.range (Function.const ι))` when
`p t` sums to `1` in every round `t < T`. -/
theorem modRegret_range_const_le_iff [Nonempty ι] {p ℓ : ℕ → ι → ℝ} {T : ℕ} {R : ℝ}
    (hp : ∀ t < T, ∑ i, p t i = 1) :
    modRegret (Set.range (Function.const ι)) p ℓ T ≤ R ↔
      ∀ k : ι, ∑ t ∈ range T, ∑ i, p t i * ℓ t i ≤ (∑ t ∈ range T, ℓ t k) + R := by
  rw [modRegret_range_const hp, sub_le_iff_le_add']
  constructor
  · intro h k
    linarith [minCumLoss_le ℓ T k]
  · intro h
    have hle : (∑ t ∈ range T, ∑ i, p t i * ℓ t i) - R ≤ minCumLoss ℓ T :=
      le_minCumLoss_iff.mpr fun k => by linarith [h k]
    linarith

/-- The family `F^in` of pairwise single-action switch modification rules `Function.update id a b`,
replacing action `a` by `b` and leaving all other actions fixed [BlumMansour2007AGT, §4.2, p. 82,
and §4.4.3, p. 90]. Includes `a = b` (`id`), matching the displayed formula
`max_{i, j ∈ X} ∑_t p_i^t (ℓ_i^t - ℓ_j^t)` on p. 82 so that internal regret is always
nonnegative. -/
def internalRules (ι : Type*) [DecidableEq ι] : Set (ι → ι) :=
  {f | ∃ a b : ι, f = update id a b}

omit [Fintype ι] in
@[simp] theorem mem_internalRules [DecidableEq ι] {f : ι → ι} :
    f ∈ internalRules ι ↔ ∃ a b : ι, f = update id a b :=
  Iff.rfl

private theorem sub_loss_update_id [DecidableEq ι] (p ℓ : ℕ → ι → ℝ) (T : ℕ) (a b : ι) :
    (∑ t ∈ range T, ∑ i, p t i * ℓ t i) -
        ∑ t ∈ range T, ∑ i, p t i * ℓ t (update id a b i) =
      ∑ t ∈ range T, p t a * (ℓ t a - ℓ t b) := by
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun t _ => ?_
  rw [← sum_sub_distrib]
  have hterm : ∀ i, p t i * ℓ t i - p t i * ℓ t (update id a b i) =
      if i = a then p t a * (ℓ t a - ℓ t b) else 0 := fun i => by
    by_cases hia : i = a
    · subst hia
      simp only [update_self, ↓reduceIte, mul_sub]
    · simp only [update_of_ne hia, id_eq, sub_self, hia, ↓reduceIte]
  simp only [hterm, sum_ite_eq', mem_univ, ↓reduceIte]

/-- Pairwise characterization of internal regret `modRegret (internalRules ι)`
[BlumMansour2007AGT, §4.2, p. 82]. -/
@[simp] theorem modRegret_internalRules_le_iff [DecidableEq ι] [Nonempty ι]
    {p ℓ : ℕ → ι → ℝ} {T : ℕ} {R : ℝ} :
    modRegret (internalRules ι) p ℓ T ≤ R ↔
      ∀ a b : ι, ∑ t ∈ range T, p t a * (ℓ t a - ℓ t b) ≤ R := by
  obtain ⟨a₀⟩ := ‹Nonempty ι›
  have hne : (internalRules ι).Nonempty := ⟨update id a₀ a₀, a₀, a₀, rfl⟩
  rw [modRegret_le_iff hne]
  constructor
  · intro h a b
    have hab := h (update id a b) ⟨a, b, rfl⟩
    have hsub := sub_loss_update_id p ℓ T a b
    linarith
  · rintro h _ ⟨a, b, rfl⟩
    have hsub := sub_loss_update_id p ℓ T a b
    linarith [h a b]

/-! ### Exercise 4.1: Swap regret vs. internal regret -/

/-- **Swap regret is at most `N` times internal regret**
[BlumMansour2007AGT, Exercise 4.1, p. 101]. -/
theorem modRegret_univ_le_card_mul_internalRules [DecidableEq ι] (p ℓ : ℕ → ι → ℝ) (T : ℕ) :
    modRegret Set.univ p ℓ T ≤ Fintype.card ι * modRegret (internalRules ι) p ℓ T := by
  rcases isEmpty_or_nonempty ι with hEmpty | hNe
  · have : Subsingleton (ι → ι) := inferInstance
    have huniv : (Set.univ : Set (ι → ι)) = {id} := Set.ext fun f => by
      simp only [Set.mem_univ, Set.mem_singleton_iff, Subsingleton.elim f id]
    simp only [modRegret, huniv, Set.image_singleton, id_eq, sub_self, csSup_singleton,
      Fintype.card_eq_zero, Nat.cast_zero, zero_mul, le_rfl]
  · rw [modRegret_univ_eq_sum_sup]
    calc ∑ i, univ.sup' univ_nonempty (fun j => ∑ t ∈ range T, p t i * (ℓ t i - ℓ t j))
        ≤ ∑ _i : ι, modRegret (internalRules ι) p ℓ T := sum_le_sum fun i _ => by
            refine Finset.sup'_le _ _ fun j _ => ?_
            rw [← sub_loss_update_id]
            exact sub_le_modRegret p ℓ T ⟨i, j, rfl⟩
      _ = Fintype.card ι * modRegret (internalRules ι) p ℓ T := by
          rw [sum_const, card_univ, nsmul_eq_mul]

/-- Original `Ω(N)` tightness witness complementing [BlumMansour2007AGT, Exercise 4.1, p. 101]:
for every `N ≥ 2`, uniform play over `T = N` rounds on `Fin N` against the constant `{0, 1}` loss
vector `(0, 1, …, 1)` achieves internal regret `1` and swap regret `N - 1`. -/
theorem exists_modRegret_univ_eq_sub_one {N : ℕ} (hN : 2 ≤ N) :
    ∃ (p ℓ : ℕ → Fin N → ℝ),
      (∀ t < N, (∀ i, 0 ≤ p t i) ∧ ∑ i, p t i = 1) ∧
      (∀ t < N, ∀ i, ℓ t i = 0 ∨ ℓ t i = 1) ∧
      modRegret (internalRules (Fin N)) p ℓ N = 1 ∧
      modRegret Set.univ p ℓ N = (N : ℝ) - 1 := by
  have : NeZero N := ⟨by omega⟩
  have hN_pos : (0 : ℝ) < N := by positivity
  let p : ℕ → Fin N → ℝ := fun _ _ => 1 / (N : ℝ)
  let ℓ : ℕ → Fin N → ℝ := fun _ i => if i = 0 then 0 else 1
  have hterm : ∀ a b : Fin N,
      ∑ t ∈ range N, p t a * (ℓ t a - ℓ t b) =
        (if a = 0 then 0 else 1) - if b = 0 then 0 else 1 := fun a b => by
    simp only [p, ℓ, sum_const, card_range, nsmul_eq_mul]
    field_simp
  refine ⟨p, ℓ, ?_, ?_, ?_, ?_⟩
  · intro _ _
    refine ⟨fun _ => by positivity, ?_⟩
    simp only [p, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · intro _ _ i
    dsimp only [ℓ]
    split_ifs with h
    · exact Or.inl rfl
    · exact Or.inr rfl
  · apply le_antisymm
    · rw [modRegret_internalRules_le_iff]
      intro a b
      rw [hterm a b]
      split_ifs <;> norm_num
    · let a₁ : Fin N := ⟨1, by omega⟩
      have ha₁ : a₁ ≠ 0 := by simp only [a₁, ne_eq, Fin.ext_iff, Fin.val_zero, one_ne_zero,
        not_false_eq_true]
      have hle := sub_le_modRegret (F := internalRules (Fin N)) p ℓ N ⟨a₁, 0, rfl⟩
      rw [sub_loss_update_id, hterm a₁ 0] at hle
      simpa only [ha₁, ↓reduceIte, sub_zero] using hle
  · rw [modRegret_univ_eq_sum_sup]
    have hsup : ∀ i : Fin N,
        univ.sup' univ_nonempty (fun j => ∑ t ∈ range N, p t i * (ℓ t i - ℓ t j)) =
          if i = 0 then 0 else 1 := fun i => by
      apply le_antisymm
      · refine Finset.sup'_le _ _ fun j _ => ?_
        rw [hterm i j]
        split_ifs <;> norm_num
      · have h0 := le_sup' (fun j => ∑ t ∈ range N, p t i * (ℓ t i - ℓ t j)) (mem_univ (0 : Fin N))
        rw [hterm i 0] at h0
        simpa only [↓reduceIte, sub_zero] using h0
    simp only [hsup]
    rw [← add_sum_erase _ _ (mem_univ (0 : Fin N))]
    simp only [↓reduceIte, zero_add]
    have herase : ∑ i ∈ univ.erase (0 : Fin N), (if i = 0 then (0 : ℝ) else 1) =
        ∑ _i ∈ univ.erase (0 : Fin N), (1 : ℝ) :=
      sum_congr rfl fun i hi => by simp only [ne_of_mem_erase hi, ↓reduceIte]
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

/-- Deterministic `{0, 1}` play cycle on `Fin 3` for Exercise 4.2 (`0, 0, 1, 1, 2, 2` mod `6`). -/
private def ex42Play (t : ℕ) : Fin 3 → ℝ :=
  match t % 6 with
  | 0 | 1 => ![1, 0, 0]
  | 2 | 3 => ![0, 1, 0]
  | _ => ![0, 0, 1]

private theorem ex42Loss_add_six (t : ℕ) : ex42Loss (t + 6) = ex42Loss t := by
  simp only [ex42Loss, Nat.add_mod_right]

private theorem ex42Play_add_six (t : ℕ) : ex42Play (t + 6) = ex42Play t := by
  simp only [ex42Play, Nat.add_mod_right]

private theorem sum_range_six_mul_of_periodic {g : ℕ → ℝ} (hg : ∀ t, g (t + 6) = g t) (m : ℕ) :
    ∑ t ∈ range (6 * m), g t = (m : ℝ) * ∑ r ∈ range 6, g r := by
  have hshift : ∀ k r, g (6 * k + r) = g r := fun k r => by
    induction k with
    | zero => simp only [mul_zero, zero_add]
    | succ k' ihk => rw [show 6 * (k' + 1) + r = (6 * k' + r) + 6 by omega, hg, ihk]
  induction m with
  | zero => simp only [mul_zero, range_zero, sum_empty, Nat.cast_zero, zero_mul]
  | succ k ih =>
    rw [show 6 * (k + 1) = 6 * k + 6 by omega, sum_range_add, ih,
      sum_congr rfl fun r _ => hshift k r]
    push_cast
    ring

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
  rw [sum_range_six_mul_of_periodic (fun t => by simp only [ex42Play_add_six, ex42Loss_add_six])]
  have h6 : (∑ r ∈ range 6, ∑ i : Fin 3, ex42Play r i * ex42Loss r i) = 3 := by
    norm_num [sum_range_succ, Fin.sum_univ_three, ex42Play, ex42Loss]
  rw [h6]
  ring

private theorem ex42_action_six_mul (m : ℕ) (j : Fin 3) :
    ∑ t ∈ range (6 * m), ex42Loss t j = 3 * (m : ℝ) := by
  rw [sum_range_six_mul_of_periodic (fun t => by simp only [ex42Loss_add_six])]
  have h6 : (∑ r ∈ range 6, ex42Loss r j) = 3 := by
    fin_cases j <;> norm_num [sum_range_succ, ex42Loss]
  rw [h6]
  ring

private theorem ex42_shift_six_mul (m : ℕ) :
    ∑ t ∈ range (6 * m), ∑ i : Fin 3, ex42Play t i * ex42Loss t (![1, 2, 0] i) = 0 := by
  rw [sum_range_six_mul_of_periodic (fun t => by simp only [ex42Play_add_six, ex42Loss_add_six])]
  have h6 : (∑ r ∈ range 6, ∑ i : Fin 3, ex42Play r i * ex42Loss r (![1, 2, 0] i)) = 0 := by
    norm_num [sum_range_succ, Fin.sum_univ_three, ex42Play, ex42Loss]
  rw [h6, mul_zero]

/-- **Zero external regret with arbitrarily large swap regret for `N = 3`**
[BlumMansour2007AGT, Exercise 4.2, p. 101]: for every `m : ℕ`, over `T = 6 * m` rounds on `Fin 3`
there exist deterministic `{0, 1}` plays `p` and `{0, 1}` losses `ℓ` with
`modRegret (Set.range (Function.const (Fin 3))) p ℓ (6 * m) = 0` and
`modRegret Set.univ p ℓ (6 * m) = 3 * m`. -/
theorem exists_modRegret_const_zero_and_univ_eq (m : ℕ) :
    ∃ (p ℓ : ℕ → Fin 3 → ℝ),
      (∀ t < 6 * m, (∀ i, p t i = 0 ∨ p t i = 1) ∧ ∑ i, p t i = 1) ∧
      (∀ t < 6 * m, ∀ i, ℓ t i = 0 ∨ ℓ t i = 1) ∧
      modRegret (Set.range (Function.const (Fin 3))) p ℓ (6 * m) = 0 ∧
      modRegret Set.univ p ℓ (6 * m) = 3 * (m : ℝ) := by
  refine ⟨ex42Play, ex42Loss, fun t _ => ⟨ex42Play_binary t, ex42Play_sum t⟩,
    fun t _ => ex42Loss_binary t, ?_, ?_⟩
  · rw [modRegret_range_const (fun t _ => ex42Play_sum t), ex42_learner_six_mul m]
    have hmin : minCumLoss ex42Loss (6 * m) = 3 * (m : ℝ) := by
      apply le_antisymm
      · exact (minCumLoss_le _ _ 0).trans_eq (ex42_action_six_mul m 0)
      · exact le_minCumLoss_iff.mpr fun j => (ex42_action_six_mul m j).symm.le
    rw [hmin, sub_self]
  · apply le_antisymm
    · rw [modRegret_univ_le_iff]
      intro δ
      rw [ex42_learner_six_mul m]
      have hnn : 0 ≤ ∑ t ∈ range (6 * m), ∑ i : Fin 3, ex42Play t i * ex42Loss t (δ i) :=
        sum_nonneg fun t _ => sum_nonneg fun i _ =>
          mul_nonneg (ex42Play_nonneg t i) (ex42Loss_nonneg t (δ i))
      linarith
    · have hle := sub_le_modRegret (F := Set.univ) ex42Play ex42Loss (6 * m)
        (Set.mem_univ ![1, 2, 0])
      rwa [ex42_learner_six_mul m, ex42_shift_six_mul m, sub_zero] at hle

/-- **Unbounded ratio between swap regret and positive external regret for `N = 3`**
[BlumMansour2007AGT, Exercise 4.2, p. 101]: for every real `M`, there exist a horizon `T`,
deterministic `{0, 1}` plays `p`, and `{0, 1}` losses `ℓ` on `Fin 3` such that external regret is
strictly positive and the ratio of swap regret to external regret strictly exceeds `M`. -/
theorem exists_unbounded_modRegret_univ_div_const (M : ℝ) :
    ∃ (T : ℕ) (p ℓ : ℕ → Fin 3 → ℝ),
      (∀ t < T, (∀ i, p t i = 0 ∨ p t i = 1) ∧ ∑ i, p t i = 1) ∧
      (∀ t < T, ∀ i, ℓ t i = 0 ∨ ℓ t i = 1) ∧
      0 < modRegret (Set.range (Function.const (Fin 3))) p ℓ T ∧
      M < modRegret Set.univ p ℓ T /
        modRegret (Set.range (Function.const (Fin 3))) p ℓ T := by
  obtain ⟨m, hm⟩ := exists_nat_gt M
  set T := 6 * m + 1
  have hlast_play : ex42Play (6 * m) = ![1, 0, 0] := by
    simp only [ex42Play, Nat.mul_mod_right]
  have hlast_loss : ex42Loss (6 * m) = ![1, 0, 1] := by
    simp only [ex42Loss, Nat.mul_mod_right]
  have hlearnerT : ∑ t ∈ range T, ∑ i : Fin 3, ex42Play t i * ex42Loss t i = 3 * (m : ℝ) + 1 := by
    dsimp only [T]
    rw [sum_range_succ, ex42_learner_six_mul m, hlast_play, hlast_loss]
    norm_num [Fin.sum_univ_three]
  have hminT : minCumLoss ex42Loss T = 3 * (m : ℝ) := by
    apply le_antisymm
    · calc minCumLoss ex42Loss T ≤ ∑ t ∈ range (6 * m + 1), ex42Loss t 1 := minCumLoss_le _ _ 1
        _ = 3 * (m : ℝ) := by
          rw [sum_range_succ, ex42_action_six_mul m 1, hlast_loss]
          norm_num
    · refine le_minCumLoss_iff.mpr fun j => ?_
      dsimp only [T]
      rw [sum_range_succ, ex42_action_six_mul m j, hlast_loss]
      fin_cases j <;> norm_num
  have hext : modRegret (Set.range (Function.const (Fin 3))) ex42Play ex42Loss T = 1 := by
    rw [modRegret_range_const (fun t _ => ex42Play_sum t), hlearnerT, hminT]
    ring
  refine ⟨T, ex42Play, ex42Loss, fun t _ => ⟨ex42Play_binary t, ex42Play_sum t⟩,
    fun t _ => ex42Loss_binary t, ?_, ?_⟩
  · linarith
  · have hshiftT : ∑ t ∈ range T, ∑ i : Fin 3,
        ex42Play t i * ex42Loss t (![1, 2, 0] i) = 0 := by
      dsimp only [T]
      rw [sum_range_succ, ex42_shift_six_mul m, hlast_play, hlast_loss]
      norm_num [Fin.sum_univ_three]
    have hswap : 3 * (m : ℝ) + 1 ≤ modRegret Set.univ ex42Play ex42Loss T := by
      have hle := sub_le_modRegret (F := Set.univ) ex42Play ex42Loss T (Set.mem_univ ![1, 2, 0])
      rwa [hlearnerT, hshiftT, sub_zero] at hle
    rw [hext, div_one]
    linarith

/-! ### Exercise 4.8: Multiplicative weight decay on `ε`-dominated actions vs. external regret -/

private theorem prob_le_weight_div_weight {φ : ℝ → ℝ} {ℓ : ℕ → ι → ℝ} {t : ℕ}
    (hφ : ∀ s < t, ∀ i, 0 < φ (ℓ s i)) (j k : ι) :
    prob φ ℓ t j ≤ weight φ ℓ t j / weight φ ℓ t k :=
  div_le_div_of_nonneg_left (weight_pos hφ j).le (weight_pos hφ k)
    (single_le_sum (fun i _ => (weight_pos hφ i).le) (mem_univ k))

private theorem prob_hedgeFactor_le_of_dominated {η ε : ℝ} (hη : 0 ≤ η)
    {ℓ : ℕ → ι → ℝ} {t : ℕ} {j : ι} {y : ι → ℝ}
    (hy0 : ∀ i, 0 ≤ y i) (hy1 : ∑ i, y i = 1)
    (hdom : ∀ s < t, ∑ i, y i * ℓ s i + ε ≤ ℓ s j) :
    prob (hedgeFactor η) ℓ t j ≤ (exp (-(η * ε))) ^ t := by
  have : Nonempty ι := ⟨j⟩
  have hφ : ∀ s < t, ∀ i, 0 < hedgeFactor η (ℓ s i) := fun _ _ _ => by
    rw [hedgeFactor_apply]
    exact exp_pos _
  obtain ⟨k, hk⟩ := exists_sum_eq_minCumLoss ℓ t
  have hcum_dom : (∑ s ∈ range t, ℓ s k) + (t : ℝ) * ε ≤ ∑ s ∈ range t, ℓ s j := by
    have hsum : ∑ s ∈ range t, (∑ i, y i * ℓ s i + ε) ≤ ∑ s ∈ range t, ℓ s j :=
      sum_le_sum fun s hs => hdom s (mem_range.mp hs)
    rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, sum_comm] at hsum
    have hy_sum : ∑ i, ∑ s ∈ range t, y i * ℓ s i = ∑ i, y i * ∑ s ∈ range t, ℓ s i :=
      sum_congr rfl fun i _ => (mul_sum _ _ _).symm
    have hmin_le : ∑ s ∈ range t, ℓ s k ≤ ∑ i, y i * ∑ s ∈ range t, ℓ s i := by
      calc ∑ s ∈ range t, ℓ s k = ∑ i, y i * ∑ s ∈ range t, ℓ s k := by rw [← sum_mul, hy1, one_mul]
        _ ≤ ∑ i, y i * ∑ s ∈ range t, ℓ s i := sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (hk.trans_le (minCumLoss_le ℓ t i)) (hy0 i)
    linarith
  have hw_eq : ∀ i, weight (hedgeFactor η) ℓ t i = exp (-(η * ∑ s ∈ range t, ℓ s i)) := fun i => by
    simp only [weight, hedgeFactor_apply, ← exp_sum, sum_neg_distrib, ← mul_sum]
  calc prob (hedgeFactor η) ℓ t j
      ≤ weight (hedgeFactor η) ℓ t j / weight (hedgeFactor η) ℓ t k :=
        prob_le_weight_div_weight hφ j k
    _ = exp (-(η * ∑ s ∈ range t, ℓ s j) - -(η * ∑ s ∈ range t, ℓ s k)) := by
        rw [hw_eq j, hw_eq k, exp_sub]
    _ ≤ exp ((t : ℝ) * -(η * ε)) := by
        refine exp_le_exp.mpr ?_
        have hmul := mul_le_mul_of_nonneg_left hcum_dom hη
        linarith
    _ = (exp (-(η * ε))) ^ t := exp_nat_mul _ _

/-- **Cumulative Hedge weight on an action `ε`-dominated by a mixed strategy**
[BlumMansour2007AGT, §4.4.4 and Exercise 4.8, pp. 91–92, 101]: if `0 < η`, `0 < ε`, and in every
round `s < T` action `j` incurs loss at least `ε` above a fixed mixed strategy `y`
(`∑ i, y i * ℓ s i + ε ≤ ℓ s j`), then the total probability mass assigned to `j` by
`prob (hedgeFactor η)` over all `T` rounds is at most `1 / (1 - exp (-(η * ε)))`.
Since `(1 - η') ^ x = hedgeFactor (-log (1 - η')) x` for `0 < η' < 1`, this also covers the
`[0, 1]` Randomized Weighted Majority update `w_i ← w_i (1 - η') ^ ℓ_i`. -/
theorem sum_prob_hedgeFactor_le_of_dominated {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε)
    {ℓ : ℕ → ι → ℝ} {T : ℕ} {j : ι} {y : ι → ℝ}
    (hy0 : ∀ i, 0 ≤ y i) (hy1 : ∑ i, y i = 1)
    (hdom : ∀ s < T, ∑ i, y i * ℓ s i + ε ≤ ℓ s j) :
    ∑ t ∈ range T, prob (hedgeFactor η) ℓ t j ≤ 1 / (1 - exp (-(η * ε))) := by
  have hstep : ∀ t ∈ range T, prob (hedgeFactor η) ℓ t j ≤ (exp (-(η * ε))) ^ t := fun t ht =>
    prob_hedgeFactor_le_of_dominated hη.le hy0 hy1 fun s hs =>
      hdom s (lt_trans hs (mem_range.mp ht))
  have hlt1 : exp (-(η * ε)) < 1 := exp_lt_one_iff.mpr (by nlinarith)
  have hgeom : ∑ t ∈ range T, (exp (-(η * ε))) ^ t ≤ 1 / (1 - exp (-(η * ε))) := by
    simpa only [Nat.Ico_zero_eq_range, pow_zero] using
      geom_sum_Ico_le_of_lt_one (m := 0) (n := T) (exp_pos _).le hlt1
  exact (sum_le_sum hstep).trans hgeom

private theorem prob_mwFactor_le_of_dominated {η ε : ℝ} (hη : 0 ≤ η) (hε : 0 ≤ ε)
    {ℓ : ℕ → ι → ℝ} {t : ℕ} {j k : ι}
    (hpos : ∀ s < t, ∀ i, 0 < mwFactor η (ℓ s i))
    (hk0 : ∀ s < t, 0 ≤ ℓ s k) (hdom : ∀ s < t, ℓ s k + ε ≤ ℓ s j) :
    prob (mwFactor η) ℓ t j ≤ (1 - η * ε) ^ t := by
  have hprod : weight (mwFactor η) ℓ t j ≤ (1 - η * ε) ^ t * weight (mwFactor η) ℓ t k := by
    induction t with
    | zero => simp only [weight_zero, pow_zero, one_mul, le_rfl]
    | succ s ih =>
      rw [weight_succ, weight_succ, pow_succ]
      have hsub := ih (fun u hu i => hpos u (by omega) i) (fun u hu => hk0 u (by omega))
        (fun u hu => hdom u (by omega))
      have hfactor : mwFactor η (ℓ s j) ≤ (1 - η * ε) * mwFactor η (ℓ s k) := by
        simp only [mwFactor_apply]
        have hd := hdom s (by omega)
        have hk := hk0 s (by omega)
        nlinarith [mul_nonneg hη hε, mul_nonneg (sq_nonneg η) (mul_nonneg hε hk)]
      have hpos_f : 0 < mwFactor η (ℓ s k) := hpos s (by omega) k
      have h1ηε : 0 ≤ 1 - η * ε :=
        nonneg_of_mul_nonneg_left ((hpos s (by omega) j).le.trans hfactor) hpos_f
      have hmul := mul_le_mul hsub hfactor (hpos s (by omega) j).le
        (mul_nonneg (pow_nonneg h1ηε s)
          (weight_pos (fun u hu i => hpos u (by omega) i) k).le)
      linarith [show (1 - η * ε) ^ s * weight (mwFactor η) ℓ s k *
          ((1 - η * ε) * mwFactor η (ℓ s k)) =
          (1 - η * ε) ^ s * (1 - η * ε) * (weight (mwFactor η) ℓ s k * mwFactor η (ℓ s k)) by
        ring]
  exact (prob_le_weight_div_weight hpos j k).trans ((div_le_iff₀ (weight_pos hpos k)).mpr hprod)

/-- **Cumulative Polynomial Weights (`mwFactor`) weight on a pure-`ε`-dominated action**
[BlumMansour2007AGT, §4.4.4 and Exercise 4.8, pp. 91–92, 101]: if `0 < η`, `0 < ε`, all
`mwFactor η` factors before `T` are positive, and in every round `s < T` action `k` has
nonnegative loss with `ℓ s k + ε ≤ ℓ s j`, then the total probability mass assigned to `j` by
`prob (mwFactor η)` over all `T` rounds is at most `1 / (η * ε)`. On `{0, 1}` losses `mwFactor`
coincides with Randomized Weighted Majority, so this covers both PW and `{0, 1}`-RWM. -/
theorem sum_prob_mwFactor_le_of_dominated {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε)
    {ℓ : ℕ → ι → ℝ} {T : ℕ} {j k : ι}
    (hpos : ∀ s < T, ∀ i, 0 < mwFactor η (ℓ s i))
    (hk0 : ∀ s < T, 0 ≤ ℓ s k) (hdom : ∀ s < T, ℓ s k + ε ≤ ℓ s j) :
    ∑ t ∈ range T, prob (mwFactor η) ℓ t j ≤ 1 / (η * ε) := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp only [range_zero, sum_empty]
    positivity
  · have hpos0 : 0 < 1 - η * ℓ 0 j := by simpa only [mwFactor_apply] using hpos 0 hT j
    have hk00 := hk0 0 hT
    have hdom0 := hdom 0 hT
    have h0le : 0 ≤ 1 - η * ε := by nlinarith
    have hlt1 : 1 - η * ε < 1 := by nlinarith
    have hstep : ∀ t ∈ range T, prob (mwFactor η) ℓ t j ≤ (1 - η * ε) ^ t := fun t ht =>
      prob_mwFactor_le_of_dominated hη.le hε.le
        (fun s hs i => hpos s (lt_trans hs (mem_range.mp ht)) i)
        (fun s hs => hk0 s (lt_trans hs (mem_range.mp ht)))
        (fun s hs => hdom s (lt_trans hs (mem_range.mp ht)))
    have hgeom : ∑ t ∈ range T, (1 - η * ε) ^ t ≤ 1 / (η * ε) := by
      have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := T) h0le hlt1
      simpa only [Nat.Ico_zero_eq_range, pow_zero, sub_sub_cancel] using h
    exact (sum_le_sum hstep).trans hgeom

/-- **Low external regret does not prevent high weight on an `ε`-dominated action**
[BlumMansour2007AGT, §4.4.4 and Exercise 4.8, pp. 92, 101]: for every `ε ∈ [0, 1 / 2]` and
`m : ℕ`, over `T = 2 * m` rounds on `Fin 3` there exist deterministic `{0, 1}` plays `p` and
`[0, 1]` losses `ℓ` in which action `2` is `ε`-dominated by action `0` in every round
(`ℓ t 0 + ε ≤ ℓ t 2`), external regret is nonpositive
(`modRegret (Set.range (Function.const (Fin 3))) p ℓ (2 * m) ≤ 0`), and cumulative weight on
action `2` equals `m` (time-average weight `1 / 2`). -/
theorem exists_nonpos_external_regret_dominated_weight {ε : ℝ}
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2) (m : ℕ) :
    ∃ (p ℓ : ℕ → Fin 3 → ℝ),
      (∀ t, (∀ i, p t i = 0 ∨ p t i = 1) ∧ ∑ i, p t i = 1) ∧
      (∀ t i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ t, ℓ t 0 + ε ≤ ℓ t 2) ∧
      modRegret (Set.range (Function.const (Fin 3))) p ℓ (2 * m) ≤ 0 ∧
      ∑ t ∈ range (2 * m), p t 2 = m := by
  let ℓ : ℕ → Fin 3 → ℝ := fun t i =>
    if t % 2 = 0 then
      if i = 0 then 0 else if i = 1 then 1 else ε
    else
      if i = 0 then 1 - ε else if i = 1 then 0 else 1
  let p : ℕ → Fin 3 → ℝ := fun t i =>
    if t % 2 = 0 then (if i = 2 then 1 else 0) else (if i = 1 then 1 else 0)
  have hpair : ∀ (f : ℕ → ℝ) (a b : ℝ),
      (∀ k, f (2 * k) = a) → (∀ k, f (2 * k + 1) = b) →
      ∑ t ∈ range (2 * m), f t = (m : ℝ) * (a + b) := fun f a b ha hb => by
    induction m with
    | zero => simp only [mul_zero, range_zero, sum_empty, Nat.cast_zero, zero_mul]
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, sum_range_succ, sum_range_succ, ih,
        ha k, hb k]
      push_cast
      ring
  have hp_sum : ∀ t, ∑ i : Fin 3, p t i = 1 := fun t => by
    by_cases he : t % 2 = 0 <;> norm_num [p, he, Fin.sum_univ_three]
  refine ⟨p, ℓ, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    refine ⟨fun i => ?_, hp_sum t⟩
    dsimp only [p]
    split_ifs <;> simp
  · intro t i
    dsimp only [ℓ]
    split_ifs <;> exact ⟨by linarith, by linarith⟩
  · intro t
    by_cases he : t % 2 = 0 <;>
      simp only [ℓ, he, ↓reduceIte, show ¬ (2 : Fin 3) = 0 by decide,
        show ¬ (2 : Fin 3) = 1 by decide] <;>
      linarith
  · rw [modRegret_range_const (fun t _ => hp_sum t), sub_nonpos]
    have h0_odd : ∀ k : ℕ, (2 * k + 1) % 2 = 1 := fun k => by omega
    have hloss : ∑ t ∈ range (2 * m), ∑ i : Fin 3, p t i * ℓ t i = (m : ℝ) * (ε + 0) :=
      hpair _ ε 0
        (fun k => by norm_num [p, ℓ, Nat.mul_mod_right, Fin.sum_univ_three])
        (fun k => by norm_num [p, ℓ, h0_odd k, Fin.sum_univ_three])
    have hc0 : ∑ t ∈ range (2 * m), ℓ t 0 = (m : ℝ) * (0 + (1 - ε)) :=
      hpair (fun t => ℓ t 0) 0 (1 - ε)
        (fun k => by simp only [ℓ, Nat.mul_mod_right, ↓reduceIte])
        (fun k => by simp only [ℓ, h0_odd k, one_ne_zero, ↓reduceIte])
    have hc1 : ∑ t ∈ range (2 * m), ℓ t 1 = (m : ℝ) * (1 + 0) :=
      hpair (fun t => ℓ t 1) 1 0
        (fun k => by simp only [ℓ, Nat.mul_mod_right, ↓reduceIte, one_ne_zero])
        (fun k => by simp only [ℓ, h0_odd k, one_ne_zero, ↓reduceIte])
    have hc2 : ∑ t ∈ range (2 * m), ℓ t 2 = (m : ℝ) * (ε + 1) :=
      hpair (fun t => ℓ t 2) ε 1
        (fun k => by simp only [ℓ, Nat.mul_mod_right, ↓reduceIte,
          show ¬ (2 : Fin 3) = 0 by decide, show ¬ (2 : Fin 3) = 1 by decide])
        (fun k => by simp only [ℓ, h0_odd k, one_ne_zero, ↓reduceIte,
          show ¬ (2 : Fin 3) = 0 by decide, show ¬ (2 : Fin 3) = 1 by decide])
    rw [hloss]
    refine le_minCumLoss_iff.mpr fun i => ?_
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rcases show i = 0 ∨ i = 1 ∨ i = 2 by omega with rfl | rfl | rfl
    · rw [hc0]; nlinarith
    · rw [hc1]; nlinarith
    · rw [hc2]; nlinarith
  · have h0_odd : ∀ k : ℕ, (2 * k + 1) % 2 = 1 := fun k => by omega
    have hw := hpair (fun t => p t 2) 1 0
      (fun k => by simp only [p, Nat.mul_mod_right, ↓reduceIte])
      (fun k => by simp only [p, h0_odd k, one_ne_zero, ↓reduceIte,
        show ¬ (2 : Fin 3) = 1 by decide])
    linarith

end Cslib.MachineLearning.OnlineLearning.Experts
