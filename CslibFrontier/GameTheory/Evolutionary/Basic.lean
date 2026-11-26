/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Bimatrix.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Evolutionarily stable strategies

In the classical model of evolutionary game theory ([Suri2007], Section 29.1.1) the members of an
infinite population are matched uniformly at random to play a fixed symmetric two-player game. An
organism playing the mixed strategy `s` that meets one playing `t` earns the fitness `F(s|t)`, and
its opponent earns `F(t|s)`.

Here the game is a bimatrix game `G : BimatrixGame α α` on a common set `α` of pure strategies, and
`F(s|t)` is player 1's expected payoff `G.payoff₁ s t`. The game is symmetric when `G.B = G.Aᵀ`;
then player 2's payoff `G.payoff₂ s t` is `F(t|s)`, so a single matrix describes both roles.

A mixed strategy `s` is *evolutionarily stable* (`BimatrixGame.IsESS`) if a population playing `s`
resists invasion by every other strategy `t`: once the share `ε` of mutants playing `t` is small
enough, the incumbents' expected fitness `(1 - ε) F(s|s) + ε F(s|t)` exceeds the mutants'
`(1 - ε) F(t|s) + ε F(t|t)`. The definition reads only player 1's payoff matrix; the results that
relate it to Nash equilibria assume that the game is symmetric.

## Main definitions

* `Cslib.GameTheory.BimatrixGame.IsESS`: an evolutionarily stable strategy ([Suri2007],
  Definition 29.1).
* `Cslib.GameTheory.BimatrixGame.hawkDove`: the game of Hawks and Doves ([Suri2007], Figure 29.1).

## Main results

* `Cslib.GameTheory.BimatrixGame.isESS_iff_forall_lt_or`: `s` is evolutionarily stable iff every
  other strategy `t` either does strictly worse against `s` than `s` itself, or does equally well
  against `s` and strictly worse than `s` against `t` ([Suri2007], Section 29.1.1, p. 719).
* `Cslib.GameTheory.BimatrixGame.isESS_iff_isNash_and_forall_lt`: in a symmetric game, `s` is
  evolutionarily stable iff `(s, s)` is a Nash equilibrium and `F(s|t) > F(t|t)` for every best
  response `t ≠ s` to `s` ([Suri2007], Theorem 29.2).
* `Cslib.GameTheory.BimatrixGame.isESS_fin_two_iff`: the evolutionarily stable strategies of a game
  with two pure strategies, in terms of the four payoffs ([Suri2007], Exercise 29.3), and
  `Cslib.GameTheory.BimatrixGame.exists_isESS_fin_two_iff`: such a game has one iff some column of
  the payoff matrix is not constant. The exercise's conclusion that every such game has one fails
  for the games with two constant columns.
* `Cslib.GameTheory.BimatrixGame.isESS_hawkDove_iff_of_lt`,
  `Cslib.GameTheory.BimatrixGame.isESS_hawkDove_iff_of_le`: Hawks and Doves with a positive
  resource value `V` has exactly one evolutionarily stable strategy: Hawk when the cost `C` of
  losing a fight is less than `V` ([Suri2007], p. 720), and Hawk with probability `V / C` when
  `V ≤ C` ([Suri2007], Exercise 29.2).

## References

* [S. Suri, *Computational Evolutionary Game Theory*][Suri2007]
-/

public section

open Matrix

namespace Cslib.GameTheory.BimatrixGame

variable {α : Type*} [Fintype α] {G : BimatrixGame α α} {s : α → ℝ}

variable (G) in
/-- The mixed strategy `s` is an *evolutionarily stable strategy* (ESS) of the game with fitness
function `F(x|y) = G.payoff₁ x y` ([Suri2007], Definition 29.1): for every mixed strategy `t ≠ s`
there is a threshold `ε₀ > 0` such that for every population share `0 < ε < ε₀` of mutants playing
`t`, the incumbents' expected fitness `(1 - ε) F(s|s) + ε F(s|t)` is greater than the mutants'
`(1 - ε) F(t|s) + ε F(t|t)`.

The threshold may depend on the mutant strategy `t`, as in the source; the source leaves its
positivity implicit. Only player 1's payoffs enter: this is the source's notion when `G` is
symmetric, `G.B = G.Aᵀ`. -/
def IsESS (s : α → ℝ) : Prop :=
  IsMixedStrategy s ∧ ∀ t, IsMixedStrategy t → t ≠ s → ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
    (1 - ε) * G.payoff₁ t s + ε * G.payoff₁ t t < (1 - ε) * G.payoff₁ s s + ε * G.payoff₁ s t

/-- Unfolding characterization of `IsESS` ([Suri2007], Definition 29.1). -/
theorem isESS_iff :
    G.IsESS s ↔ IsMixedStrategy s ∧ ∀ t, IsMixedStrategy t → t ≠ s → ∃ ε₀ > 0,
      ∀ ε, 0 < ε → ε < ε₀ →
        (1 - ε) * G.payoff₁ t s + ε * G.payoff₁ t t <
          (1 - ε) * G.payoff₁ s s + ε * G.payoff₁ s t :=
  Iff.rfl

/-- An evolutionarily stable strategy is a mixed strategy. -/
theorem IsESS.isMixedStrategy (h : G.IsESS s) : IsMixedStrategy s := h.1

/-- For real numbers, `(1 - ε) * c + ε * d < (1 - ε) * a + ε * b` holds for all small enough
positive `ε` iff `c < a`, or `c = a` and `d < b`. -/
private theorem exists_pos_forall_lt_iff (a b c d : ℝ) :
    (∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ → (1 - ε) * c + ε * d < (1 - ε) * a + ε * b) ↔
      c < a ∨ c = a ∧ d < b := by
  constructor
  · rintro ⟨ε₀, hε₀, h⟩
    have hca : c ≤ a := by
      by_contra hlt
      rw [not_le] at hlt
      have hden : 0 < 2 * (|b - d| + 1) := by positivity
      let ε := min (ε₀ / 2) (min (1 / 2) ((c - a) / (2 * (|b - d| + 1))))
      have hε : 0 < ε :=
        lt_min (half_pos hε₀) (lt_min one_half_pos (div_pos (sub_pos.2 hlt) hden))
      have h₁ := h ε hε ((min_le_left _ _).trans_lt (half_lt_self hε₀))
      have h₂ : ε * (b - d) ≤ ε * |b - d| := mul_le_mul_of_nonneg_left (le_abs_self _) hε.le
      have h₃ : 0 ≤ (1 / 2 - ε) * (c - a) :=
        mul_nonneg (sub_nonneg.2 ((min_le_right _ _).trans (min_le_left _ _))) (sub_pos.2 hlt).le
      have h₄ : ε * (2 * (|b - d| + 1)) ≤ c - a :=
        (le_div_iff₀ hden).1 ((min_le_right _ _).trans (min_le_right _ _))
      linarith
    rcases hca.lt_or_eq with hlt | rfl
    · exact Or.inl hlt
    · have h₁ := h (ε₀ / 2) (half_pos hε₀) (half_lt_self hε₀)
      exact Or.inr ⟨rfl, lt_of_mul_lt_mul_left (by linarith) (half_pos hε₀).le⟩
  · rintro (hlt | ⟨rfl, hlt⟩)
    · have hden : 0 < |b - d - (a - c)| + 1 := by positivity
      refine ⟨(a - c) / (|b - d - (a - c)| + 1), div_pos (sub_pos.2 hlt) hden, fun ε hε hε₁ => ?_⟩
      have h₁ : ε * (|b - d - (a - c)| + 1) < a - c := (lt_div_iff₀ hden).1 hε₁
      have h₂ : ε * -|b - d - (a - c)| ≤ ε * (b - d - (a - c)) :=
        mul_le_mul_of_nonneg_left (neg_abs_le _) hε.le
      linarith
    · exact ⟨1, one_pos, fun ε hε _ => by linarith [mul_lt_mul_of_pos_left hlt hε]⟩

/-- The two-condition form of evolutionary stability ([Suri2007], Section 29.1.1, p. 719, the
reformulation of Definition 29.1 from which the source derives Theorem 29.2): `s` is
evolutionarily stable iff every mixed strategy `t ≠ s` satisfies `F(t|s) < F(s|s)`, or
`F(t|s) = F(s|s)` and `F(t|t) < F(s|t)`. -/
theorem isESS_iff_forall_lt_or :
    G.IsESS s ↔ IsMixedStrategy s ∧ ∀ t, IsMixedStrategy t → t ≠ s →
      G.payoff₁ t s < G.payoff₁ s s ∨
        G.payoff₁ t s = G.payoff₁ s s ∧ G.payoff₁ t t < G.payoff₁ s t := by
  simp only [IsESS, exists_pos_forall_lt_iff]

/-- A best response of player 1 is a mixed strategy that no mixed deviation improves on. -/
private theorem isBestResponse₁_iff_forall_le {x y : α → ℝ} :
    G.IsBestResponse₁ x y ↔
      IsMixedStrategy x ∧ ∀ x', IsMixedStrategy x' → G.payoff₁ x' y ≤ G.payoff₁ x y := by
  rw [isBestResponse₁_iff]
  refine and_congr_right fun hx => ?_
  simp only [isPureBestResponse₁_iff, payoff₁_eq_dotProduct]
  exact hx.forall_dotProduct_le_iff.symm

/-- In a symmetric game, `(s, s)` is a Nash equilibrium iff `s` is a best response to itself. -/
private theorem isNash_self_iff (hG : G.B = G.Aᵀ) : G.IsNash s s ↔ G.IsBestResponse₁ s s := by
  have hswap : G.swap = G := by
    obtain ⟨A, B⟩ := G
    dsimp only at hG
    subst hG
    simp only [swap_mk, transpose_transpose]
  rw [isNash_iff, ← isBestResponse₁_swap, hswap, and_self]

/-- **Evolutionary stability refines symmetric Nash equilibrium** ([Suri2007], Theorem 29.2): in a
symmetric game, `s` is an evolutionarily stable strategy iff `(s, s)` is a Nash equilibrium and
every best response `t ≠ s` to `s` satisfies `F(t|t) < F(s|t)`. -/
theorem isESS_iff_isNash_and_forall_lt (hG : G.B = G.Aᵀ) :
    G.IsESS s ↔ G.IsNash s s ∧
      ∀ t, G.IsBestResponse₁ t s → t ≠ s → G.payoff₁ t t < G.payoff₁ s t := by
  rw [isESS_iff_forall_lt_or, isNash_self_iff hG]
  simp only [isBestResponse₁_iff_forall_le]
  constructor
  · rintro ⟨hs, h⟩
    refine ⟨⟨hs, fun t ht => ?_⟩, fun t ⟨ht, hbr⟩ hne => ?_⟩
    · rcases eq_or_ne t s with rfl | hne
      · exact le_rfl
      · rcases h t ht hne with hlt | ⟨heq, -⟩
        exacts [hlt.le, heq.le]
    · rcases h t ht hne with hlt | ⟨-, hlt⟩
      · exact absurd (hbr s hs) hlt.not_ge
      · exact hlt
  · rintro ⟨⟨hs, hbr⟩, hst⟩
    refine ⟨hs, fun t ht hne => ?_⟩
    rcases (hbr t ht).lt_or_eq with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr ⟨heq, hst t ⟨ht, fun x' hx' => heq ▸ hbr x' hx'⟩ hne⟩

/-! ### Two pure strategies -/

private theorem isMixedStrategy_fin_two_iff {x : Fin 2 → ℝ} :
    IsMixedStrategy x ↔ 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ x 1 = 1 - x 0 := by
  rw [isMixedStrategy_iff, Fin.forall_fin_two, Fin.sum_univ_two]
  constructor
  · rintro ⟨⟨h0, h1⟩, hs⟩
    exact ⟨h0, by linarith, by linarith⟩
  · rintro ⟨h0, h1, hs⟩
    exact ⟨⟨h0, by linarith⟩, by linarith⟩

/-- A mixed strategy on two pure strategies is determined by the probability of the first. -/
private theorem eq_vec_fin_two_iff {x : Fin 2 → ℝ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    x = ![p, 1 - p] ↔ IsMixedStrategy x ∧ x 0 = p := by
  rw [isMixedStrategy_fin_two_iff]
  constructor
  · rintro rfl
    exact ⟨⟨hp0, hp1, rfl⟩, rfl⟩
  · rintro ⟨⟨-, -, h1⟩, rfl⟩
    ext i
    fin_cases i
    · rfl
    · exact h1

/-- With two pure strategies, the payoff difference of two mixed strategies against a third. -/
private theorem payoff₁_sub_fin_two (G : BimatrixGame (Fin 2) (Fin 2)) {x y z : Fin 2 → ℝ}
    (hx : x 1 = 1 - x 0) (hy : y 1 = 1 - y 0) (hz : z 1 = 1 - z 0) :
    G.payoff₁ x z - G.payoff₁ y z =
      (x 0 - y 0) * ((G.A 0 0 - G.A 1 0) * z 0 + (G.A 0 1 - G.A 1 1) * (1 - z 0)) := by
  simp only [payoff₁_eq_dotProduct, dotProduct, mulVec, Fin.sum_univ_two, hx, hy, hz]
  ring

/-- The real-arithmetic core of `isESS_fin_two_iff`. Here `p` and `q` are the probabilities that
the incumbent and the mutant play the first strategy. -/
private theorem forall_stable_fin_two_iff {a b c d p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∀ q, 0 ≤ q → q ≤ 1 → q ≠ p →
        0 < (p - q) * ((a - c) * p + (b - d) * (1 - p)) ∨
          (p - q) * ((a - c) * p + (b - d) * (1 - p)) = 0 ∧
            0 < (p - q) * ((a - c) * q + (b - d) * (1 - q))) ↔
      p = 1 ∧ (c < a ∨ c = a ∧ d < b) ∨ p = 0 ∧ (b < d ∨ b = d ∧ a < c) ∨
        a < c ∧ d < b ∧ p = (b - d) / (c - a + (b - d)) := by
  constructor
  · intro h
    rcases hp1.lt_or_eq with hp1' | rfl
    · rcases hp0.lt_or_eq with hp0' | rfl
      · have h0 := h 0 le_rfl zero_le_one hp0'.ne
        have h1 := h 1 zero_le_one le_rfl hp1'.ne'
        have hL : (a - c) * p + (b - d) * (1 - p) = 0 := by
          rcases lt_trichotomy ((a - c) * p + (b - d) * (1 - p)) 0 with hneg | hL | hpos
          · rcases h0 with h0 | ⟨h0, -⟩ <;> linarith [mul_neg_of_pos_of_neg hp0' hneg]
          · exact hL
          · rcases h1 with h1 | ⟨h1, -⟩ <;> linarith [mul_neg_of_neg_of_pos (sub_neg.2 hp1') hpos]
        simp only [hL, sub_zero, mul_zero, sub_self, zero_add, add_zero, mul_one, lt_irrefl,
          false_or, true_and] at h0 h1
        have hdb : d < b := sub_pos.1 (pos_of_mul_pos_right h0 hp0'.le)
        have hac : a < c :=
          sub_pos.1 (pos_of_mul_pos_right (by linarith : 0 < (1 - p) * (c - a)) (sub_pos.2 hp1').le)
        exact Or.inr (Or.inr ⟨hac, hdb, (eq_div_iff (by linarith)).2 (by linarith)⟩)
      · refine Or.inr (Or.inl ⟨rfl, ?_⟩)
        rcases h 1 zero_le_one le_rfl one_ne_zero with h1 | ⟨h1, h1'⟩
        · exact Or.inl (by linarith)
        · exact Or.inr ⟨by linarith, by linarith⟩
    · refine Or.inl ⟨rfl, ?_⟩
      rcases h 0 le_rfl zero_le_one zero_ne_one with h0 | ⟨h0, h0'⟩
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by linarith, by linarith⟩
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨hac, hdb, hp⟩) q hq0 hq1 hq
    · have hq' : 0 < 1 - q := sub_pos.2 (lt_of_le_of_ne hq1 hq)
      rcases h with h | ⟨rfl, h⟩
      · exact Or.inl (mul_pos hq' (by linarith))
      · exact Or.inr ⟨by ring, by nlinarith [mul_pos hq' hq', sub_pos.2 h]⟩
    · have hq' : 0 < q := lt_of_le_of_ne hq0 hq.symm
      rcases h with h | ⟨rfl, h⟩
      · exact Or.inl (by nlinarith [mul_pos hq' (sub_pos.2 h)])
      · exact Or.inr ⟨by ring, by nlinarith [mul_pos hq' hq', sub_pos.2 h]⟩
    · have hden : 0 < c - a + (b - d) := by linarith
      have hL : (a - c) * p + (b - d) * (1 - p) = 0 := by
        rw [hp]
        field_simp
        ring
      have hsq : 0 < (p - q) ^ 2 := by positivity
      refine Or.inr ⟨by rw [hL, mul_zero], ?_⟩
      have : (p - q) * ((a - c) * q + (b - d) * (1 - q)) = (c - a + (b - d)) * (p - q) ^ 2 := by
        linear_combination (p - q) * hL
      rw [this]
      positivity

/-- **Evolutionarily stable strategies of a game with two pure strategies** (a characterization
answering [Suri2007], Exercise 29.3). Write `a b c d` for the payoffs `G.A 0 0`, `G.A 0 1`,
`G.A 1 0`, `G.A 1 1`. A mixed strategy `s` is evolutionarily stable iff one of the following holds:
`s` is the first pure strategy and `c < a`, or `c = a` and `d < b`; `s` is the second pure
strategy and `b < d`, or `b = d` and `a < c`; or `a < c`, `d < b` and `s` plays the first strategy
with probability `(b - d) / (c - a + (b - d))`. -/
theorem isESS_fin_two_iff {G : BimatrixGame (Fin 2) (Fin 2)} {s : Fin 2 → ℝ} :
    G.IsESS s ↔ IsMixedStrategy s ∧
      (s 0 = 1 ∧ (G.A 1 0 < G.A 0 0 ∨ G.A 1 0 = G.A 0 0 ∧ G.A 1 1 < G.A 0 1) ∨
        s 0 = 0 ∧ (G.A 0 1 < G.A 1 1 ∨ G.A 0 1 = G.A 1 1 ∧ G.A 0 0 < G.A 1 0) ∨
        G.A 0 0 < G.A 1 0 ∧ G.A 1 1 < G.A 0 1 ∧
          s 0 = (G.A 0 1 - G.A 1 1) / (G.A 1 0 - G.A 0 0 + (G.A 0 1 - G.A 1 1))) := by
  rw [isESS_iff_forall_lt_or]
  refine and_congr_right fun hs => ?_
  obtain ⟨hp0, hp1, hs1⟩ := isMixedStrategy_fin_two_iff.1 hs
  rw [← forall_stable_fin_two_iff hp0 hp1]
  constructor
  · intro h q hq0 hq1 hq
    have ht : IsMixedStrategy ![q, 1 - q] := ((eq_vec_fin_two_iff hq0 hq1).1 rfl).1
    have h₁ := payoff₁_sub_fin_two G hs1 (y := ![q, 1 - q]) rfl hs1
    have h₂ := payoff₁_sub_fin_two G hs1 (y := ![q, 1 - q]) (z := ![q, 1 - q]) rfl rfl
    simp only [cons_val_zero] at h₁ h₂
    rcases h _ ht fun hqs => hq (congrFun hqs 0) with hlt | ⟨heq, hlt⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, by linarith⟩
  · intro h t ht hne
    obtain ⟨hq0, hq1, ht1⟩ := isMixedStrategy_fin_two_iff.1 ht
    have hq : t 0 ≠ s 0 := fun h0 =>
      hne (((eq_vec_fin_two_iff hp0 hp1).2 ⟨ht, h0⟩).trans
        ((eq_vec_fin_two_iff hp0 hp1).2 ⟨hs, rfl⟩).symm)
    have h₁ := payoff₁_sub_fin_two G hs1 ht1 hs1
    have h₂ := payoff₁_sub_fin_two G hs1 ht1 ht1
    rcases h (t 0) hq0 hq1 hq with hlt | ⟨heq, hlt⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, by linarith⟩

/-- **Existence of an evolutionarily stable strategy with two pure strategies**: the game has one
iff some column of player 1's payoff matrix is not constant.

[Suri2007], Exercise 29.3 asks to conclude that every two-by-two symmetric game has an
evolutionarily stable strategy. That conclusion fails exactly for the games with two constant
columns, such as the game with all payoffs zero: there every strategy earns the same against every
opponent, so no strategy does strictly better than a mutant. -/
theorem exists_isESS_fin_two_iff {G : BimatrixGame (Fin 2) (Fin 2)} :
    (∃ s, G.IsESS s) ↔ G.A 0 0 ≠ G.A 1 0 ∨ G.A 0 1 ≠ G.A 1 1 := by
  constructor
  · rintro ⟨s, hs⟩
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    rcases (isESS_fin_two_iff.1 hs).2 with ⟨-, h | ⟨-, h⟩⟩ | ⟨-, h | ⟨-, h⟩⟩ | ⟨h, -, -⟩ <;>
      linarith [hcon.1, hcon.2]
  · intro h
    have hpure0 : IsMixedStrategy ![(1 : ℝ), 1 - 1] ∧ (![(1 : ℝ), 1 - 1] : Fin 2 → ℝ) 0 = 1 :=
      (eq_vec_fin_two_iff zero_le_one le_rfl).1 rfl
    have hpure1 : IsMixedStrategy ![(0 : ℝ), 1 - 0] ∧ (![(0 : ℝ), 1 - 0] : Fin 2 → ℝ) 0 = 0 :=
      (eq_vec_fin_two_iff le_rfl zero_le_one).1 rfl
    rcases lt_trichotomy (G.A 0 0) (G.A 1 0) with hac | hac | hac
    · rcases lt_trichotomy (G.A 1 1) (G.A 0 1) with hdb | hdb | hdb
      · have hden : 0 < G.A 1 0 - G.A 0 0 + (G.A 0 1 - G.A 1 1) := by linarith
        have hmix := (eq_vec_fin_two_iff (x := ![_, _])
          (div_nonneg (sub_nonneg.2 hdb.le) hden.le) ((div_le_one hden).2 (by linarith))).1 rfl
        exact ⟨_, isESS_fin_two_iff.2 ⟨hmix.1, Or.inr (Or.inr ⟨hac, hdb, hmix.2⟩)⟩⟩
      · exact ⟨_, isESS_fin_two_iff.2
          ⟨hpure1.1, Or.inr (Or.inl ⟨hpure1.2, Or.inr ⟨hdb.symm, hac⟩⟩)⟩⟩
      · exact ⟨_, isESS_fin_two_iff.2 ⟨hpure1.1, Or.inr (Or.inl ⟨hpure1.2, Or.inl hdb⟩)⟩⟩
    · rcases lt_trichotomy (G.A 1 1) (G.A 0 1) with hdb | hdb | hdb
      · exact ⟨_, isESS_fin_two_iff.2 ⟨hpure0.1, Or.inl ⟨hpure0.2, Or.inr ⟨hac.symm, hdb⟩⟩⟩⟩
      · exact absurd hdb.symm (h.resolve_left (not_not.2 hac))
      · exact ⟨_, isESS_fin_two_iff.2 ⟨hpure1.1, Or.inr (Or.inl ⟨hpure1.2, Or.inl hdb⟩)⟩⟩
    · exact ⟨_, isESS_fin_two_iff.2 ⟨hpure0.1, Or.inl ⟨hpure0.2, Or.inl hac⟩⟩⟩

/-! ### Hawks and Doves -/

/-- The game of *Hawks and Doves* ([Suri2007], Section 29.1.1, Figure 29.1, p. 719): two organisms
contest a resource worth `V`, and losing a fight costs `C`. Strategy `0` is Hawk and strategy `1`
is Dove. Two Hawks fight, each winning with probability `1 / 2`, for an expected fitness of
`(V - C) / 2`; a Hawk takes the whole resource from a Dove, who gets nothing; two Doves share the
resource. The game is symmetric: player 2's payoff matrix is the transpose of player 1's. -/
noncomputable def hawkDove (V C : ℝ) : BimatrixGame (Fin 2) (Fin 2) :=
  ⟨!![(V - C) / 2, V; 0, V / 2], !![(V - C) / 2, V; 0, V / 2]ᵀ⟩

@[simp]
theorem hawkDove_A (V C : ℝ) : (hawkDove V C).A = !![(V - C) / 2, V; 0, V / 2] := by
  rw [hawkDove]

/-- Hawks and Doves is a symmetric game. -/
theorem hawkDove_B (V C : ℝ) : (hawkDove V C).B = (hawkDove V C).Aᵀ := by
  rw [hawkDove]

/-- **Hawk is evolutionarily stable when the resource is worth more than the cost of a fight**
([Suri2007], Section 29.1.1, p. 720): in Hawks and Doves with `0 < V` and `C < V`, the pure
strategy Hawk is an evolutionarily stable strategy, and it is the only one. The source states
that Hawk is evolutionarily stable and leaves `0 < V` implicit; uniqueness is added here. -/
theorem isESS_hawkDove_iff_of_lt {V C : ℝ} (hV : 0 < V) (hCV : C < V) {s : Fin 2 → ℝ} :
    (hawkDove V C).IsESS s ↔ s = ![1, 0] := by
  have h10 : (![1, 0] : Fin 2 → ℝ) = ![1, 1 - 1] := by rw [sub_self]
  rw [h10, eq_vec_fin_two_iff zero_le_one le_rfl, isESS_fin_two_iff]
  refine and_congr_right fun _ => ?_
  simp only [hawkDove_A, of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_fin_one]
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h | ⟨h, -⟩⟩ | ⟨h, -, -⟩)
    · exact h
    all_goals linarith
  · exact fun h => Or.inl ⟨h, Or.inl (by linarith)⟩

/-- **The mixed evolutionarily stable strategy of Hawks and Doves** ([Suri2007], Exercise 29.2):
in Hawks and Doves with `0 < V ≤ C`, playing Hawk with probability `V / C` is an evolutionarily
stable strategy, and it is the only one. The exercise asks for stability; uniqueness is added
here, and the source leaves `0 < V` implicit. For `V = C` the strategy is pure Hawk. -/
theorem isESS_hawkDove_iff_of_le {V C : ℝ} (hV : 0 < V) (hVC : V ≤ C) {s : Fin 2 → ℝ} :
    (hawkDove V C).IsESS s ↔ s = ![V / C, 1 - V / C] := by
  have hC : 0 < C := hV.trans_le hVC
  rw [eq_vec_fin_two_iff (div_nonneg hV.le hC.le) ((div_le_one hC).2 hVC), isESS_fin_two_iff]
  refine and_congr_right fun _ => ?_
  simp only [hawkDove_A, of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_fin_one]
  have hratio : (V - V / 2) / (0 - (V - C) / 2 + (V - V / 2)) = V / C := by
    rw [div_eq_div_iff (by linarith) hC.ne']
    ring
  rw [hratio]
  constructor
  · rintro (⟨h, h' | ⟨h', -⟩⟩ | ⟨-, h | ⟨h, -⟩⟩ | ⟨-, -, h⟩)
    · linarith
    · exact h.trans ((div_eq_one_iff_eq hC.ne').2 (by linarith)).symm
    all_goals first | exact h | linarith
  · intro h
    rcases hVC.eq_or_lt with rfl | hlt
    · exact Or.inl ⟨by rw [h, div_self hV.ne'], Or.inr ⟨by ring, by linarith⟩⟩
    · exact Or.inr (Or.inr ⟨by linarith, by linarith, h⟩)

end Cslib.GameTheory.BimatrixGame
