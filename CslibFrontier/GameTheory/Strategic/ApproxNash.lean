/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Bimatrix.CostGame
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Multiset.Count
import CslibFrontier.GameTheory.Bimatrix.Existence
import CslibFrontier.Probability.Concentration
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Approximate Nash equilibria and equilibria with small support

An **`ε`-approximate Nash equilibrium** is a profile of mixed strategies from which no player can
gain more than an additive `ε` by deviating ([Papadimitriou2007], Section 2.6.6, p. 45;
[Kearns2007], Section 7.2, p. 162). This module defines the notion for strategic cost games
(`CostGame.IsApproxMixedNash`) and for bimatrix games (`BimatrixGame.IsApproxNash`), relates the
two (`BimatrixGame.isApproxNash_iff_isApproxMixedNash`), and proves two existence results for
bimatrix games with payoffs in `[0, 1]`. Both are statements about the existence and the support
of approximate equilibria; no running time is claimed.

* **A `1/2`-approximate equilibrium with support of size at most two.** Take any row `i₀`, a
  best-response column `j₀` to `i₀`, and a best-response row `i₁` to `j₀`. Then
  `((1/2) e_{i₀} + (1/2) e_{i₁}, e_{j₀})` is a `1/2`-approximate Nash equilibrium
  (`BimatrixGame.isApproxNash_half_dmp`). This is the construction of
  [DaskalakisMehtaPapadimitriou2006], Section 3, Theorem 1 (covering the game-theoretic output
  guarantee for `[0, 1]` payoffs and two successive pure best responses, without machine runtime);
  [Papadimitriou2007], Section 2.6.6, p. 45, reports that `1/2`-approximate equilibria are easy to
  compute and does not print the construction.
* **`ε`-approximate equilibria that are uniform on small multisets**
  ([TardosVazirani2007], Exercise 1.6, p. 27; sampling argument after
  [LiptonMarkakisMehta2003], Section 3). For every `ε > 0` and every integer
  `k > 2 ln(2(|M| + |N|)) / ε²` on a nonempty rectangular game `M × N` with payoffs in `[0, 1]`,
  there are multisets of `k` rows and of `k` columns whose uniform distributions
  (`uniformMultiset`) form an `ε`-approximate Nash equilibrium
  (`BimatrixGame.exists_uniformMultiset_isApproxNash_of_lt`); the explicit size
  `BimatrixGame.lmmSampleSize M N ε = ⌊2 ln(2(|M| + |N|)) / ε²⌋₊ + 1` works
  (`BimatrixGame.exists_uniformMultiset_isApproxNash`). For payoffs in `[0, K]` (`K ≥ 0`), scaling
  at the same multiset size gives an `(ε * K)`-approximate equilibrium, matching Exercise 1.6's
  payoff convention (`BimatrixGame.exists_uniformMultiset_isApproxNash_of_nonneg`). The proof
  samples `k` times from an exact Nash equilibrium and applies Hoeffding's inequality with a union
  bound (following [LiptonMarkakisMehta2003], Section 3, whose Theorem 1 starts from each specified
  exact Nash equilibrium and also approximates both of its payoffs).

## Main definitions

* `Cslib.GameTheory.CostGame.IsApproxMixedNash`: `ε`-approximate mixed Nash equilibrium of a cost
  game.
* `Cslib.GameTheory.BimatrixGame.IsApproxBestResponse₁`,
  `Cslib.GameTheory.BimatrixGame.IsApproxBestResponse₂`,
  `Cslib.GameTheory.BimatrixGame.IsApproxNash`: `ε`-approximate best responses and Nash equilibria
  of a bimatrix game.
* `Cslib.GameTheory.uniformMultiset`: the mixed strategy choosing uniformly at random from a
  multiset of pure strategies.
* `Cslib.GameTheory.BimatrixGame.lmmSampleSize`: the multiset size
  `⌊2 ln(2(|M| + |N|)) / ε²⌋₊ + 1`.

## Main results

* `Cslib.GameTheory.BimatrixGame.isApproxNash_iff_isApproxMixedNash`: the bimatrix notion agrees
  with the cost-game notion on `BimatrixGame.toCostGame`.
* `Cslib.GameTheory.BimatrixGame.isApproxNash_half_dmp`,
  `Cslib.GameTheory.BimatrixGame.exists_dmp_half_isApproxNash`: a `1/2`-approximate Nash
  equilibrium in which one player mixes two rows evenly and the other plays a column.
* `Cslib.GameTheory.BimatrixGame.exists_uniformMultiset_isApproxNash_of_lt`,
  `Cslib.GameTheory.BimatrixGame.exists_uniformMultiset_isApproxNash`,
  `Cslib.GameTheory.BimatrixGame.exists_uniformMultiset_isApproxNash_of_nonneg`: existence of
  `ε`-approximate Nash equilibria that are uniform on multisets of logarithmic size.

## References

* [C. Daskalakis, A. Mehta, and C. H. Papadimitriou, *A Note on Approximate Nash
  Equilibria*][DaskalakisMehtaPapadimitriou2006]
* [M. Kearns, *Graphical Games*][Kearns2007]
* [R. J. Lipton, E. Markakis, and A. Mehta, *Playing Large Games Using Simple
  Strategies*][LiptonMarkakisMehta2003]
* [C. H. Papadimitriou, *The Complexity of Finding Nash Equilibria*][Papadimitriou2007]
* [É. Tardos and V. V. Vazirani, *Basic Solution Concepts and Computational
  Issues*][TardosVazirani2007]
-/

public section

namespace Cslib.GameTheory

open Finset Function Matrix

/-! ### Approximate mixed Nash equilibria in `CostGame` -/

namespace CostGame

section ApproxMixedNash

variable {ι : Type*} {S : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)]
  (G : CostGame ι S)

/-- An **`ε`-approximate mixed Nash equilibrium** of a cost-minimization game
([Papadimitriou2007], Section 2.6.6, p. 45; [Kearns2007], Section 7.2, p. 162): every player uses a
mixed strategy, and no player can lower its expected cost by more than `ε` by deviating to a pure
strategy. -/
@[expose] def IsApproxMixedNash (ε : ℝ) (p : ∀ i, S i → ℝ) : Prop :=
  (∀ i, IsMixedStrategy (p i)) ∧ ∀ i a, G.expectedCost p i ≤ G.deviationCost p i a + ε

variable {G}

/-- At `ε = 0`, an approximate mixed Nash equilibrium is an exact mixed Nash equilibrium. -/
@[simp]
theorem isApproxMixedNash_zero_iff {p : ∀ i, S i → ℝ} :
    G.IsApproxMixedNash 0 p ↔ G.IsMixedNash p := by
  simp only [IsApproxMixedNash, IsMixedNash, add_zero]

theorem IsMixedNash.isApproxMixedNash {p : ∀ i, S i → ℝ} (h : G.IsMixedNash p) {ε : ℝ}
    (hε : 0 ≤ ε) : G.IsApproxMixedNash ε p :=
  ⟨h.1, fun i a => (h.2 i a).trans (le_add_of_nonneg_right hε)⟩

theorem IsApproxMixedNash.mono {ε ε' : ℝ} {p : ∀ i, S i → ℝ} (h : G.IsApproxMixedNash ε p)
    (hle : ε ≤ ε') : G.IsApproxMixedNash ε' p :=
  ⟨h.1, fun i a => by linarith [h.2 i a]⟩

/-- In an `ε`-approximate mixed Nash equilibrium, mixed-strategy deviations cannot lower expected
cost by more than `ε` either. -/
theorem IsApproxMixedNash.expectedCost_le_update {ε : ℝ} {p : ∀ i, S i → ℝ}
    (h : G.IsApproxMixedNash ε p) (i : ι) {q : S i → ℝ} (hq : IsMixedStrategy q) :
    G.expectedCost p i ≤ G.expectedCost (update p i q) i + ε := by
  have hq' : ∑ b, update p i q i b = 1 := by
    rw [update_self]
    exact hq.sum_eq_one
  rw [← G.sum_mul_deviationCost_eq_expectedCost (update p i q) hq']
  calc G.expectedCost p i
      = ∑ b, q b * G.expectedCost p i := by rw [← sum_mul, hq.sum_eq_one, one_mul]
    _ ≤ ∑ b, q b * (G.deviationCost p i b + ε) :=
        sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (h.2 i b) (hq.nonneg b)
    _ = (∑ b, q b * G.deviationCost p i b) + ε := by
        simp only [mul_add, sum_add_distrib, ← sum_mul, hq.sum_eq_one, one_mul]
    _ = (∑ b, update p i q i b * G.deviationCost (update p i q) i b) + ε := by
        congr 1
        refine sum_congr rfl fun b _ => ?_
        rw [update_self, G.deviationCost_update_self p
          (by rw [hq.sum_eq_one, (h.1 i).sum_eq_one]) b]

end ApproxMixedNash

end CostGame

/-! ### Uniform-multiset mixed strategies -/

section UniformMultiset

/-- The mixed strategy that chooses uniformly at random from a multiset `m : Multiset α`
([TardosVazirani2007], Exercise 1.6, p. 27; [LiptonMarkakisMehta2003]): pure strategy
`a` receives probability `(m.count a : ℝ) / m.card`. -/
noncomputable def uniformMultiset {α : Type*} [DecidableEq α] (m : Multiset α) (a : α) :
    ℝ :=
  (m.count a : ℝ) / m.card

@[simp]
theorem uniformMultiset_apply {α : Type*} [DecidableEq α] (m : Multiset α) (a : α) :
    uniformMultiset m a = (m.count a : ℝ) / m.card := by rfl

private theorem sum_multiset_count_mul {α : Type*} [Fintype α] [DecidableEq α]
    (m : Multiset α) (f : α → ℝ) :
    ∑ a : α, (m.count a : ℝ) * f a = (m.map f).sum := by
  rw [Finset.sum_multiset_map_count]
  symm
  refine (Finset.sum_subset (subset_univ _) fun a _ ha => ?_).trans
    (sum_congr rfl fun a _ => nsmul_eq_mul _ _)
  rw [Multiset.count_eq_zero.2 (mt Multiset.mem_toFinset.2 ha), zero_smul]

/-- For any nonempty multiset `m`, `uniformMultiset m` is a valid mixed strategy. -/
theorem isMixedStrategy_uniformMultiset {α : Type*} [Fintype α] [DecidableEq α]
    {m : Multiset α} (hm : m ≠ 0) : IsMixedStrategy (uniformMultiset m) := by
  have hcard : (0 : ℝ) < m.card := Nat.cast_pos.2 (Multiset.card_pos.2 hm)
  refine isMixedStrategy_iff.2 ⟨fun a => div_nonneg (Nat.cast_nonneg _) hcard.le, ?_⟩
  dsimp only [uniformMultiset]
  rw [← sum_div, ← Nat.cast_sum, Multiset.sum_count_eq_card (fun _ _ => mem_univ _),
    div_self hcard.ne']

/-- The support of `uniformMultiset m` has size at most `m.card`. -/
theorem ncard_support_uniformMultiset_le {α : Type*} [DecidableEq α]
    (m : Multiset α) : (Function.support (uniformMultiset m)).ncard ≤ m.card := by
  have hsub : Function.support (uniformMultiset m) ⊆ (m.toFinset : Set α) := fun a ha => by
    rw [Function.mem_support, uniformMultiset, div_ne_zero_iff] at ha
    exact Multiset.mem_toFinset.2 (Multiset.count_ne_zero.1 (by exact_mod_cast ha.1))
  calc (Function.support (uniformMultiset m)).ncard
      ≤ (m.toFinset : Set α).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = m.toFinset.card := Set.ncard_coe_finset m.toFinset
    _ ≤ m.card := Multiset.toFinset_card_le m

private theorem uniformMultiset_dotProduct_of_map_univ {α : Type*} [Fintype α] [DecidableEq α]
    {k : ℕ} (ω : Fin k → α) (f : α → ℝ) :
    uniformMultiset ((univ : Finset (Fin k)).val.map ω) ⬝ᵥ f = (∑ t : Fin k, f (ω t)) / k := by
  change ∑ a : α, _ = _
  simp_rw [uniformMultiset_apply, div_mul_eq_mul_div, ← sum_div, sum_multiset_count_mul]
  simp [Finset.sum, Function.comp_def]

end UniformMultiset

/-! ### Approximate Nash equilibria in bimatrix games, DMP `1/2`-Nash, and small-support `ε`-Nash -/

namespace BimatrixGame

variable {M N : Type*} [Fintype M] [Fintype N] (G : BimatrixGame M N)

/-- `x` is an **`ε`-approximate best response** of player 1 to `y`: a mixed strategy achieving
within `ε` of the maximum possible expected payoff against `y`. -/
@[expose] def IsApproxBestResponse₁ (ε : ℝ) (x : M → ℝ) (y : N → ℝ) : Prop :=
  IsMixedStrategy x ∧ ∀ x', IsMixedStrategy x' → G.payoff₁ x' y ≤ G.payoff₁ x y + ε

/-- `y` is an **`ε`-approximate best response** of player 2 to `x`: a mixed strategy achieving
within `ε` of the maximum possible expected payoff against `x`. -/
@[expose] def IsApproxBestResponse₂ (ε : ℝ) (y : N → ℝ) (x : M → ℝ) : Prop :=
  IsMixedStrategy y ∧ ∀ y', IsMixedStrategy y' → G.payoff₂ x y' ≤ G.payoff₂ x y + ε

/-- `(x, y)` is an **`ε`-approximate Nash equilibrium** of the bimatrix game `G`
([Papadimitriou2007], Section 2.6.6, p. 45): each player's strategy is an `ε`-approximate best
response to the other's. -/
@[expose] def IsApproxNash (ε : ℝ) (x : M → ℝ) (y : N → ℝ) : Prop :=
  G.IsApproxBestResponse₁ ε x y ∧ G.IsApproxBestResponse₂ ε y x

variable {G} {x : M → ℝ} {y : N → ℝ} {ε : ℝ}

/-- Pure-row characterization of `IsApproxBestResponse₁`: `x` is an `ε`-approximate best response to
`y` iff `x` is a mixed strategy and no pure row beats `G.payoff₁ x y` by more than `ε`. -/
theorem isApproxBestResponse₁_iff_pure :
    G.IsApproxBestResponse₁ ε x y ↔
      IsMixedStrategy x ∧ ∀ i : M, (G.A *ᵥ y) i ≤ G.payoff₁ x y + ε := by
  classical
  refine and_congr_right fun _ => ⟨fun h i => ?_, fun h x' hx' =>
    G.payoff₁_eq_dotProduct x' y ▸ hx'.dotProduct_le_of_forall_le h⟩
  simpa only [payoff₁_eq_dotProduct, single_dotProduct, one_mul] using
    h _ (isMixedStrategy_single i)

/-- Pure-column characterization of `IsApproxBestResponse₂`. -/
theorem isApproxBestResponse₂_iff_pure :
    G.IsApproxBestResponse₂ ε y x ↔
      IsMixedStrategy y ∧ ∀ j : N, (x ᵥ* G.B) j ≤ G.payoff₂ x y + ε := by
  classical
  refine and_congr_right fun _ => ⟨fun h j => ?_, fun h y' hy' =>
    G.payoff₂_eq_dotProduct x y' ▸ hy'.dotProduct_le_of_forall_le h⟩
  simpa only [payoff₂_eq_dotProduct, single_dotProduct, one_mul] using
    h _ (isMixedStrategy_single j)

/-- Pure-deviation characterization of `IsApproxNash`. -/
theorem isApproxNash_iff_pure :
    G.IsApproxNash ε x y ↔
      (IsMixedStrategy x ∧ ∀ i : M, (G.A *ᵥ y) i ≤ G.payoff₁ x y + ε) ∧
        (IsMixedStrategy y ∧ ∀ j : N, (x ᵥ* G.B) j ≤ G.payoff₂ x y + ε) :=
  and_congr isApproxBestResponse₁_iff_pure isApproxBestResponse₂_iff_pure

@[simp]
theorem isApproxBestResponse₁_zero_iff :
    G.IsApproxBestResponse₁ 0 x y ↔ G.IsBestResponse₁ x y := by
  rw [IsApproxBestResponse₁, isBestResponse₁_iff]
  refine and_congr_right fun hx => ?_
  simp only [add_zero, payoff₁_eq_dotProduct, isPureBestResponse₁_iff]
  exact hx.forall_dotProduct_le_iff

@[simp]
theorem isApproxBestResponse₂_zero_iff :
    G.IsApproxBestResponse₂ 0 y x ↔ G.IsBestResponse₂ y x := by
  rw [IsApproxBestResponse₂, isBestResponse₂_iff]
  refine and_congr_right fun hy => ?_
  simp only [add_zero, payoff₂_eq_dotProduct, isPureBestResponse₂_iff]
  exact hy.forall_dotProduct_le_iff

/-- At `ε = 0`, an approximate Nash equilibrium of a bimatrix game is an exact Nash equilibrium. -/
@[simp]
theorem isApproxNash_zero_iff : G.IsApproxNash 0 x y ↔ G.IsNash x y := by
  rw [IsApproxNash, isNash_iff, isApproxBestResponse₁_zero_iff, isApproxBestResponse₂_zero_iff]

theorem IsApproxNash.mono {ε' : ℝ} (h : G.IsApproxNash ε x y) (hle : ε ≤ ε') :
    G.IsApproxNash ε' x y := by
  obtain ⟨⟨hx, hbr₁⟩, ⟨hy, hbr₂⟩⟩ := h
  exact ⟨⟨hx, fun x' hx' => by linarith [hbr₁ x' hx']⟩,
    ⟨hy, fun y' hy' => by linarith [hbr₂ y' hy']⟩⟩

theorem IsNash.isApproxNash (h : G.IsNash x y) (hε : 0 ≤ ε) : G.IsApproxNash ε x y :=
  (isApproxNash_zero_iff.2 h).mono hε

/-- Scaling both payoff matrices of a bimatrix game by `c ≥ 0` scales the approximation error of an
`ε`-approximate Nash equilibrium by `c`. -/
theorem IsApproxNash.smul {c : ℝ} (hc : 0 ≤ c) (h : G.IsApproxNash ε x y) :
    (⟨c • G.A, c • G.B⟩ : BimatrixGame M N).IsApproxNash (c * ε) x y := by
  obtain ⟨⟨hx, hbr₁⟩, ⟨hy, hbr₂⟩⟩ := isApproxNash_iff_pure.1 h
  refine isApproxNash_iff_pure.2 ⟨⟨hx, fun i => ?_⟩, ⟨hy, fun j => ?_⟩⟩
  · have hi := mul_le_mul_of_nonneg_left (hbr₁ i) hc
    simp only [payoff₁_eq_dotProduct, Matrix.smul_mulVec, dotProduct_smul, Pi.smul_apply,
      smul_eq_mul] at hi ⊢
    linarith
  · have hj := mul_le_mul_of_nonneg_left (hbr₂ j) hc
    simp only [payoff₂_eq_dotProduct, Matrix.vecMul_smul, dotProduct_smul, Pi.smul_apply,
      smul_eq_mul] at hj ⊢
    linarith

/-- An `ε`-approximate Nash equilibrium of a bimatrix game `G` is equivalently an `ε`-approximate
mixed Nash equilibrium of `G.toCostGame`. -/
theorem isApproxNash_iff_isApproxMixedNash :
    G.IsApproxNash ε x y ↔ G.toCostGame.IsApproxMixedNash ε (profile x y) := by
  rw [isApproxNash_iff_pure, CostGame.IsApproxMixedNash, Bool.forall_bool, Bool.forall_bool,
    isMixedStrategy_profile_false_iff, isMixedStrategy_profile_true_iff]
  refine ⟨fun ⟨⟨hx, h₁⟩, ⟨hy, h₂⟩⟩ => ⟨⟨hx, hy⟩, fun ⟨i⟩ => ?_, fun ⟨j⟩ => ?_⟩,
    fun ⟨⟨hx, hy⟩, h₁, h₂⟩ => ⟨⟨hx, fun i => ?_⟩, ⟨hy, fun j => ?_⟩⟩⟩
  · rw [expectedCost_toCostGame_false G y hx.sum_eq_one,
      deviationCost_toCostGame_row G y hx.sum_eq_one i]
    linarith [h₁ i]
  · rw [expectedCost_toCostGame_true G x hy.sum_eq_one,
      deviationCost_toCostGame_column G x hy.sum_eq_one j]
    linarith [h₂ j]
  · have hi := h₁ (ULift.up i)
    rw [expectedCost_toCostGame_false G y hx.sum_eq_one,
      deviationCost_toCostGame_row G y hx.sum_eq_one i] at hi
    linarith
  · have hj := h₂ (ULift.up j)
    rw [expectedCost_toCostGame_true G x hy.sum_eq_one,
      deviationCost_toCostGame_column G x hy.sum_eq_one j] at hj
    linarith

/-! #### Daskalakis–Mehta–Papadimitriou `1/2`-approximate Nash equilibrium -/

/-- **Daskalakis–Mehta–Papadimitriou `(1/2)`-Nash theorem** ([DaskalakisMehtaPapadimitriou2006],
Section 3, Theorem 1; cited in [Papadimitriou2007], Section 2.6.6, p. 45): in any bimatrix game
with payoffs in `[0, 1]`, if `i₀` is any row, `j₀` maximizes `G.B i₀ ·` (pure best response of
player 2 to `i₀`), and `i₁` maximizes `G.A · j₀` (pure best response of player 1 to `j₀`), then
`((1/2) e_{i₀} + (1/2) e_{i₁}, e_{j₀})` is an additive `(1/2)`-approximate Nash equilibrium. This
covers the game-theoretic output guarantee without a machine running-time claim. -/
theorem isApproxNash_half_dmp [DecidableEq M] [DecidableEq N]
    (hA : ∀ i j, G.A i j ∈ Set.Icc 0 1) (hB : ∀ i j, G.B i j ∈ Set.Icc 0 1)
    (i₀ : M) {j₀ : N} (hj₀ : ∀ j, G.B i₀ j ≤ G.B i₀ j₀)
    {i₁ : M} (hi₁ : ∀ i, G.A i j₀ ≤ G.A i₁ j₀) :
    G.IsApproxNash (1 / 2) ((1 / 2 : ℝ) • Pi.single i₀ 1 + (1 / 2 : ℝ) • Pi.single i₁ 1)
      (Pi.single j₀ 1) := by
  set x : M → ℝ := (1 / 2 : ℝ) • Pi.single i₀ 1 + (1 / 2 : ℝ) • Pi.single i₁ 1
  set y : N → ℝ := Pi.single j₀ 1
  have hx : IsMixedStrategy x := by
    refine isMixedStrategy_iff.2 ⟨fun i => ?_, ?_⟩
    · exact add_nonneg
        (mul_nonneg (by norm_num) ((isMixedStrategy_single i₀).nonneg i))
        (mul_nonneg (by norm_num) ((isMixedStrategy_single i₁).nonneg i))
    · simp only [x, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum,
        (isMixedStrategy_single i₀).sum_eq_one, (isMixedStrategy_single i₁).sum_eq_one]
      norm_num
  have hAy : ∀ i, (G.A *ᵥ y) i = G.A i j₀ := fun i => by
    change G.A i ⬝ᵥ Pi.single j₀ 1 = G.A i j₀
    rw [dotProduct_single, mul_one]
  have hpay₁ : G.payoff₁ x y = (1 / 2) * G.A i₀ j₀ + (1 / 2) * G.A i₁ j₀ := by
    rw [payoff₁_eq_dotProduct]
    simp only [x, add_dotProduct, smul_dotProduct, single_dotProduct, smul_eq_mul, one_mul, hAy]
  have hxB : ∀ j, (x ᵥ* G.B) j = (1 / 2) * G.B i₀ j + (1 / 2) * G.B i₁ j := fun j => by
    simp only [x, add_vecMul, smul_vecMul, single_vecMul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      one_mul, Matrix.row_apply]
  have hpay₂ : G.payoff₂ x y = (1 / 2) * G.B i₀ j₀ + (1 / 2) * G.B i₁ j₀ := by
    rw [payoff₂_eq_dotProduct, single_dotProduct, one_mul, hxB]
  refine isApproxNash_iff_pure.2 ⟨⟨hx, fun i => ?_⟩, ⟨isMixedStrategy_single j₀, fun j => ?_⟩⟩
  · rw [hAy, hpay₁]
    linarith [hi₁ i, (hA i₀ j₀).1, (hA i₁ j₀).2]
  · rw [hxB, hpay₂]
    linarith [hj₀ j, (hB i₁ j).2, (hB i₁ j₀).1]

/-- Existence corollary of `isApproxNash_half_dmp`: every nonempty finite bimatrix game with
payoffs in `[0, 1]` has a `(1/2)`-approximate Nash equilibrium in which player 1 mixes evenly over
at most two pure strategies and player 2 plays a pure strategy. -/
theorem exists_dmp_half_isApproxNash [DecidableEq M] [DecidableEq N] [Nonempty M] [Nonempty N]
    (G : BimatrixGame M N) (hA : ∀ i j, G.A i j ∈ Set.Icc 0 1)
    (hB : ∀ i j, G.B i j ∈ Set.Icc 0 1) :
    ∃ (i₀ i₁ : M) (j₀ : N),
      G.IsApproxNash (1 / 2) ((1 / 2 : ℝ) • Pi.single i₀ 1 + (1 / 2 : ℝ) • Pi.single i₁ 1)
        (Pi.single j₀ 1) := by
  let i₀ : M := Classical.arbitrary M
  obtain ⟨j₀, -, hj₀⟩ := univ.exists_max_image (fun j => G.B i₀ j) univ_nonempty
  obtain ⟨i₁, -, hi₁⟩ := univ.exists_max_image (fun i => G.A i j₀) univ_nonempty
  exact ⟨i₀, i₁, j₀, G.isApproxNash_half_dmp hA hB i₀ (fun j => hj₀ j (mem_univ j))
    (fun i => hi₁ i (mem_univ i))⟩

/-! #### Uniform-multiset small-support `ε`-approximate Nash existence -/

section LiptonMarkakisMehta

open Cslib.Probability.PMF

/-- Concrete multiset cardinality `k = ⌊2 ln(2(|M| + |N|)) / ε²⌋₊ + 1 = O(ln(|M| + |N|) / ε²)`
for small-support `ε`-approximate Nash equilibrium existence ([TardosVazirani2007], Exercise 1.6,
p. 27; empirical-sampling bound after [LiptonMarkakisMehta2003], Section 3; see also
[Papadimitriou2007], Section 2.6.6, p. 45). -/
noncomputable def lmmSampleSize (M N : Type*) [Fintype M] [Fintype N] (ε : ℝ) : ℕ :=
  ⌊2 * Real.log (2 * (Fintype.card M + Fintype.card N)) / ε ^ 2⌋₊ + 1

theorem lt_lmmSampleSize (M N : Type*) [Fintype M] [Fintype N] (ε : ℝ) :
    2 * Real.log (2 * (Fintype.card M + Fintype.card N)) / ε ^ 2 < lmmSampleSize M N ε := by
  dsimp only [lmmSampleSize]
  push_cast
  exact Nat.lt_floor_add_one _

theorem lmmSampleSize_pos (M N : Type*) [Fintype M] [Fintype N] (ε : ℝ) :
    0 < lmmSampleSize M N ε :=
  Nat.succ_pos _

theorem lmmSampleSize_le (M N : Type*) [Fintype M] [Fintype N] [Nonempty M] [Nonempty N]
    {ε : ℝ} (hε : 0 < ε) :
    (lmmSampleSize M N ε : ℝ) ≤
      2 * Real.log (2 * (Fintype.card M + Fintype.card N)) / ε ^ 2 + 1 := by
  have hM : 1 ≤ Fintype.card M := Fintype.card_pos
  have hN : 1 ≤ Fintype.card N := Fintype.card_pos
  have hlog : 0 ≤ Real.log (2 * (Fintype.card M + Fintype.card N)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * (Fintype.card M + Fintype.card N) by omega))
  have hnn : 0 ≤ 2 * Real.log (2 * (Fintype.card M + Fintype.card N)) / ε ^ 2 :=
    div_nonneg (by positivity) (by positivity)
  dsimp only [lmmSampleSize]
  push_cast
  linarith [Nat.floor_le hnn]

private noncomputable def mixedToPMF {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : IsMixedStrategy p) : _root_.PMF α :=
  PMF.ofFintype (fun a => ENNReal.ofReal (p a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun a _ => hp.nonneg a, hp.sum_eq_one, ENNReal.ofReal_one])

private theorem mixedToPMF_toReal {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : IsMixedStrategy p) (a : α) : ((mixedToPMF hp) a).toReal = p a :=
  ENNReal.toReal_ofReal (hp.nonneg a)

private theorem mem_support_mixedToPMF_iff {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : IsMixedStrategy p) (a : α) : a ∈ (mixedToPMF hp).support ↔ 0 < p a := by
  rw [PMF.mem_support_iff]
  change ENNReal.ofReal (p a) ≠ 0 ↔ 0 < p a
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]

/-- Probabilistic empirical-sampling lemma: for a mixed strategy `p` on `β`, a `[0, 1]`-valued
family of functions `g : α → β → ℝ` indexed by finite `α`, `δ > 0`, and `k : ℕ` with
`2 * card α * exp (-2 k δ²) < 1` and `0 < k`, there exists a `k`-tuple `ω : Fin k → β` supported
within `support p` whose empirical average approximates `p ⬝ᵥ g i` within `δ` simultaneously for all
`i : α`. -/
private theorem exists_empirical_tuple {α β : Type*} [Fintype α] [Fintype β]
    {p : β → ℝ} (hp : IsMixedStrategy p) (g : α → β → ℝ)
    (hg : ∀ i b, g i b ∈ Set.Icc 0 1) {δ : ℝ} (hδ : 0 < δ) {k : ℕ} (hk : 0 < k)
    (htail : 2 * (Fintype.card α : ℝ) * Real.exp (-2 * (k : ℝ) * δ ^ 2) < 1) :
    ∃ ω : Fin k → β, (∀ t, 0 < p (ω t)) ∧
      ∀ i : α, |(∑ t : Fin k, g i (ω t)) / k - (p ⬝ᵥ g i)| ≤ δ := by
  let q : _root_.PMF β := mixedToPMF hp
  let μ : _root_.PMF (Fin k → β) := pi fun _ : Fin k => q
  let bad (i : α) : Set (Fin k → β) :=
    {ω | (k : ℝ) * δ ≤ |(∑ t : Fin k, g i (ω t)) - ∑ _t : Fin k, ∑ b : β, (q b).toReal * g i b|}
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hbad_each : ∀ i : α, (μ.toOuterMeasure (bad i)).toReal ≤
      2 * Real.exp (-2 * (k : ℝ) * δ ^ 2) := fun i => by
    simpa only [Fintype.card_fin] using
      pi_sum_abs_sub_mean_ge_card_mul (fun _ : Fin k => q) (fun _ b => g i b)
        (fun _ b _ => hg i b) hδ.le
  have hunion_le : (μ.toOuterMeasure (⋃ i : α, bad i)).toReal ≤
      2 * (Fintype.card α : ℝ) * Real.exp (-2 * (k : ℝ) * δ ^ 2) := by
    calc (μ.toOuterMeasure (⋃ i : α, bad i)).toReal
        ≤ ∑ i : α, (μ.toOuterMeasure (bad i)).toReal := by
          rw [← ENNReal.toReal_sum fun i _ => toOuterMeasure_ne_top μ (bad i)]
          exact ENNReal.toReal_mono
            (ENNReal.sum_ne_top.2 fun i _ => toOuterMeasure_ne_top μ (bad i))
            (MeasureTheory.measure_iUnion_fintype_le μ.toOuterMeasure bad)
      _ ≤ ∑ _i : α, 2 * Real.exp (-2 * (k : ℝ) * δ ^ 2) :=
          sum_le_sum fun i _ => hbad_each i
      _ = 2 * (Fintype.card α : ℝ) * Real.exp (-2 * (k : ℝ) * δ ^ 2) := by
          rw [sum_const, card_univ, nsmul_eq_mul]
          ring
  have hcompl_pos : 0 < (μ.toOuterMeasure (⋃ i : α, bad i)ᶜ).toReal := by
    linarith [toOuterMeasure_toReal_add_compl μ (⋃ i : α, bad i)]
  obtain ⟨ω, hω_good, hω_supp⟩ := (toOuterMeasure_toReal_pos_iff μ _).1 hcompl_pos
  refine ⟨ω, fun t => ?_, fun i => ?_⟩
  · exact (mem_support_mixedToPMF_iff hp (ω t)).1 ((mem_support_pi_iff _ ω).1 hω_supp t)
  · have hni : |(∑ t : Fin k, g i (ω t)) - ∑ _t : Fin k, ∑ b : β, (q b).toReal * g i b| <
        (k : ℝ) * δ := not_le.1 fun hi => hω_good (Set.mem_iUnion.2 ⟨i, hi⟩)
    have hlt : |(∑ t : Fin k, g i (ω t)) - (k : ℝ) * (p ⬝ᵥ g i)| < (k : ℝ) * δ := by
      simpa only [q, mixedToPMF_toReal hp, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
        dotProduct] using hni
    have heq : (∑ t : Fin k, g i (ω t)) / k - (p ⬝ᵥ g i) =
        ((∑ t : Fin k, g i (ω t)) - (k : ℝ) * (p ⬝ᵥ g i)) / k := by
      field_simp
    rw [heq, abs_div, abs_of_pos hk_pos, div_le_iff₀ hk_pos]
    linarith

/-- Auxiliary bound: transferring a uniform `ε / 2` payoff approximation on the empirical multiset
to an `ε`-approximate best-response inequality against a target equilibrium value `v`. -/
private theorem lmm_payoff_bound {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (hk : (0 : ℝ) < k) (ω : Fin k → α) (uStar uHat : α → ℝ) {v ε : ℝ}
    (happrox : ∀ a : α, |uHat a - uStar a| ≤ ε / 2)
    (heq_supp : ∀ t : Fin k, uStar (ω t) = v)
    (hub : ∀ a : α, uStar a ≤ v) (a : α) :
    uHat a ≤ uniformMultiset ((univ : Finset (Fin k)).val.map ω) ⬝ᵥ uHat + ε := by
  have hlb : v - ε / 2 ≤ uniformMultiset ((univ : Finset (Fin k)).val.map ω) ⬝ᵥ uHat := by
    rw [uniformMultiset_dotProduct_of_map_univ ω, le_div_iff₀' hk]
    simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] using
      sum_le_sum (s := univ) (f := fun _ => v - ε / 2) (g := fun t => uHat (ω t)) fun t _ =>
        by linarith [(abs_le.1 (happrox (ω t))).1, heq_supp t]
  linarith [(abs_le.1 (happrox a)).2, hub a]

/-- **Uniform-multiset small-support `ε`-approximate Nash existence (`[0, 1]`-normalized form of
[TardosVazirani2007], Exercise 1.6, p. 27)**: in any nonempty finite rectangular bimatrix game with
payoffs in `[0, 1]` and `ε > 0`, for every `k : ℕ` satisfying `2 ln(2(|M| + |N|)) / ε² < k`, there
exist multisets `m₁ : Multiset M` and `m₂ : Multiset N` of cardinality `k` whose uniform
distributions form an `ε`-approximate Nash equilibrium. The proof uses the empirical-sampling
argument of [LiptonMarkakisMehta2003], Section 3 (whose Theorem 1 starts from each specified exact
Nash equilibrium and also approximates both of its payoffs; see also [Papadimitriou2007],
Section 2.6.6, p. 45). This states game-theoretic existence and support size without a machine
running-time claim. -/
theorem exists_uniformMultiset_isApproxNash_of_lt [DecidableEq M] [DecidableEq N]
    [Nonempty M] [Nonempty N] (G : BimatrixGame M N)
    (hA : ∀ i j, G.A i j ∈ Set.Icc 0 1) (hB : ∀ i j, G.B i j ∈ Set.Icc 0 1)
    {ε : ℝ} (hε : 0 < ε) {k : ℕ}
    (hk : 2 * Real.log (2 * (Fintype.card M + Fintype.card N)) / ε ^ 2 < k) :
    ∃ (m₁ : Multiset M) (m₂ : Multiset N),
      m₁.card = k ∧ m₂.card = k ∧
        G.IsApproxNash ε (uniformMultiset m₁) (uniformMultiset m₂) := by
  have hM : (1 : ℝ) ≤ Fintype.card M := Nat.one_le_cast.2 Fintype.card_pos
  have hN : (1 : ℝ) ≤ Fintype.card N := Nat.one_le_cast.2 Fintype.card_pos
  set S : ℝ := 2 * (Fintype.card M + Fintype.card N) with hS
  have hS_pos : 0 < S := by linarith
  have hlog_pos : 0 < Real.log S := Real.log_pos (by linarith)
  have hk_real_pos : (0 : ℝ) < k := lt_trans (div_pos (by positivity) (by positivity)) hk
  have hk_pos : 0 < k := Nat.cast_pos.1 hk_real_pos
  have hexp_lt : Real.exp (-2 * (k : ℝ) * (ε / 2) ^ 2) < S⁻¹ := by
    rw [← Real.exp_log (inv_pos.2 hS_pos), Real.exp_lt_exp, Real.log_inv]
    rw [div_lt_iff₀ (sq_pos_of_pos hε)] at hk
    linarith
  have htail_of_lt : ∀ {c : ℝ}, 0 < c → c < S →
      c * Real.exp (-2 * (k : ℝ) * (ε / 2) ^ 2) < 1 := fun {c} hc hcS =>
    calc c * Real.exp (-2 * (k : ℝ) * (ε / 2) ^ 2)
        < c * S⁻¹ := mul_lt_mul_of_pos_left hexp_lt hc
      _ < S * S⁻¹ := mul_lt_mul_of_pos_right hcS (inv_pos.2 hS_pos)
      _ = 1 := mul_inv_cancel₀ hS_pos.ne'
  have htail_M : 2 * (Fintype.card M : ℝ) * Real.exp (-2 * (k : ℝ) * (ε / 2) ^ 2) < 1 :=
    htail_of_lt (by positivity) (by linarith)
  have htail_N : 2 * (Fintype.card N : ℝ) * Real.exp (-2 * (k : ℝ) * (ε / 2) ^ 2) < 1 :=
    htail_of_lt (by positivity) (by linarith)
  obtain ⟨xStar, yStar, hNash⟩ := G.exists_isNash
  obtain ⟨hbr₁, hbr₂⟩ := isNash_iff.1 hNash
  obtain ⟨ω₂, hω₂_supp, hω₂_approx⟩ :=
    exists_empirical_tuple hbr₂.isMixedStrategy (fun i j => G.A i j) hA (half_pos hε) hk_pos
      htail_M
  obtain ⟨ω₁, hω₁_supp, hω₁_approx⟩ :=
    exists_empirical_tuple hbr₁.isMixedStrategy (fun j i => G.B i j) (fun j i => hB i j)
      (half_pos hε) hk_pos htail_N
  set m₁ : Multiset M := (univ : Finset (Fin k)).val.map ω₁
  set m₂ : Multiset N := (univ : Finset (Fin k)).val.map ω₂
  have hm₁_card : m₁.card = k := by simp [m₁]
  have hm₂_card : m₂.card = k := by simp [m₂]
  have hm₁_ne : m₁ ≠ 0 := Multiset.card_pos.1 (hm₁_card ▸ hk_pos)
  have hm₂_ne : m₂ ≠ 0 := Multiset.card_pos.1 (hm₂_card ▸ hk_pos)
  have hA_hat : ∀ i : M, |(G.A *ᵥ uniformMultiset m₂) i - (G.A *ᵥ yStar) i| ≤ ε / 2 := fun i => by
    change |G.A i ⬝ᵥ uniformMultiset m₂ - G.A i ⬝ᵥ yStar| ≤ ε / 2
    rw [dotProduct_comm, uniformMultiset_dotProduct_of_map_univ ω₂, dotProduct_comm]
    exact hω₂_approx i
  have hB_hat : ∀ j : N, |(uniformMultiset m₁ ᵥ* G.B) j - (xStar ᵥ* G.B) j| ≤ ε / 2 := fun j => by
    change |uniformMultiset m₁ ⬝ᵥ (fun i => G.B i j) - _| ≤ ε / 2
    rw [uniformMultiset_dotProduct_of_map_univ ω₁]
    exact hω₁_approx j
  refine ⟨m₁, m₂, hm₁_card, hm₂_card, isApproxNash_iff_pure.2
    ⟨⟨isMixedStrategy_uniformMultiset hm₁_ne, fun i => ?_⟩,
      ⟨isMixedStrategy_uniformMultiset hm₂_ne, fun j => ?_⟩⟩⟩
  · rw [payoff₁_eq_dotProduct]
    exact lmm_payoff_bound hk_real_pos ω₁ (G.A *ᵥ yStar) (G.A *ᵥ uniformMultiset m₂) hA_hat
      (fun t => (hbr₁.payoff₁_eq_of_pos (hω₁_supp t)).symm) hbr₁.le_payoff₁ i
  · rw [payoff₂_eq_dotProduct]
    exact lmm_payoff_bound hk_real_pos ω₂ (xStar ᵥ* G.B) (uniformMultiset m₁ ᵥ* G.B) hB_hat
      (fun t => (hbr₂.payoff₂_eq_of_pos (hω₂_supp t)).symm) hbr₂.le_payoff₂ j

/-- **Uniform-multiset small-support `ε`-approximate Nash existence at explicit sample size**
(`[0, 1]`-normalized form of [TardosVazirani2007], Exercise 1.6, p. 27, proved via the sampling
argument of [LiptonMarkakisMehta2003], Section 3): in any nonempty finite rectangular bimatrix game
with payoffs in `[0, 1]` and `ε > 0`, there exist multisets `m₁ : Multiset M` and `m₂ : Multiset N`
of exact size `lmmSampleSize M N ε = ⌊2 ln(2(|M| + |N|)) / ε²⌋₊ + 1` whose uniform empirical
distributions form an `ε`-approximate Nash equilibrium. -/
theorem exists_uniformMultiset_isApproxNash [DecidableEq M] [DecidableEq N]
    [Nonempty M] [Nonempty N] (G : BimatrixGame M N)
    (hA : ∀ i j, G.A i j ∈ Set.Icc 0 1) (hB : ∀ i j, G.B i j ∈ Set.Icc 0 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (m₁ : Multiset M) (m₂ : Multiset N),
      m₁.card = lmmSampleSize M N ε ∧ m₂.card = lmmSampleSize M N ε ∧
        G.IsApproxNash ε (uniformMultiset m₁) (uniformMultiset m₂) :=
  G.exists_uniformMultiset_isApproxNash_of_lt hA hB hε (lt_lmmSampleSize M N ε)

/-- **Small-support approximate Nash existence for nonnegative payoffs** ([TardosVazirani2007],
Exercise 1.6, p. 27, generalized to rectangular `M × N` games with explicit sample size via the
sampling argument of [LiptonMarkakisMehta2003], Section 3): if all payoffs of `G` lie in `[0, K]`
(`0 ≤ K`) and `ε > 0`, then there exist multisets `m₁ : Multiset M` and `m₂ : Multiset N` of exact
cardinality `lmmSampleSize M N ε` whose uniform empirical distributions form an
`(ε * K)`-approximate Nash equilibrium. -/
theorem exists_uniformMultiset_isApproxNash_of_nonneg [DecidableEq M] [DecidableEq N]
    [Nonempty M] [Nonempty N] (G : BimatrixGame M N) {K : ℝ} (hK : 0 ≤ K)
    (hA : ∀ i j, G.A i j ∈ Set.Icc 0 K) (hB : ∀ i j, G.B i j ∈ Set.Icc 0 K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (m₁ : Multiset M) (m₂ : Multiset N),
      m₁.card = lmmSampleSize M N ε ∧ m₂.card = lmmSampleSize M N ε ∧
        G.IsApproxNash (ε * K) (uniformMultiset m₁) (uniformMultiset m₂) := by
  let G' : BimatrixGame M N :=
    ⟨if K = 0 then 0 else K⁻¹ • G.A, if K = 0 then 0 else K⁻¹ • G.B⟩
  have hscale : ∀ (C : Matrix M N ℝ), (∀ i j, C i j ∈ Set.Icc 0 K) →
      ∀ i j, (if K = 0 then (0 : Matrix M N ℝ) else K⁻¹ • C) i j ∈ Set.Icc 0 1 := by
    intro C hC i j
    split_ifs with hK0
    · exact ⟨le_rfl, zero_le_one⟩
    · have hK_pos : 0 < K := lt_of_le_of_ne hK (Ne.symm hK0)
      exact ⟨mul_nonneg (inv_nonneg.2 hK_pos.le) (hC i j).1, by
        simpa only [Matrix.smul_apply, smul_eq_mul, inv_mul_cancel₀ hK0] using
          mul_le_mul_of_nonneg_left (hC i j).2 (inv_nonneg.2 hK_pos.le)⟩
  have hG' : (⟨K • G'.A, K • G'.B⟩ : BimatrixGame M N) = G := by
    cases G with
    | mk A B =>
      dsimp only [G']
      split_ifs with hK0
      · subst hK0
        simp only [zero_smul]
        congr 1 <;> ext i j
        exacts [(le_antisymm (hA i j).2 (hA i j).1).symm, (le_antisymm (hB i j).2 (hB i j).1).symm]
      · simp only [smul_smul, mul_inv_cancel₀ hK0, one_smul]
  obtain ⟨m₁, m₂, hm₁, hm₂, happrox⟩ :=
    G'.exists_uniformMultiset_isApproxNash (hscale G.A hA) (hscale G.B hB) hε
  exact ⟨m₁, m₂, hm₁, hm₂, mul_comm K ε ▸ hG' ▸ happrox.smul hK⟩

end LiptonMarkakisMehta

end BimatrixGame

end Cslib.GameTheory
