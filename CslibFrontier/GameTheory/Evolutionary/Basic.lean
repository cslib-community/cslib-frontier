/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Bimatrix.Basic
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Evolutionarily stable strategies in symmetric two-player games

This module introduces symmetric two-player games (`Cslib.GameTheory.SymmetricGame`) and the
classical notion of an *evolutionarily stable strategy (ESS)* following Suri [Suri2007],
Section 29.1.1 (pp. 717–720, Exercises 29.1–29.4).

A symmetric two-player game over pure strategies `α` is given by a single payoff matrix
`payoff : Matrix α α ℝ`. Its associated `BimatrixGame α α` (`SymmetricGame.toBimatrixGame`) gives
the row player `payoff` and the column player `payoffᵀ`, so when a `s`-player meets a `t`-player the
expected fitness is `fitness G s t = s ⬝ᵥ (G.payoff *ᵥ t)`.

In [Suri2007], Exercise 29.3 asks to show that *every* `2 × 2` symmetric game has an ESS. That
unqualified claim has a standard textbook erratum: the degenerate indifferent games satisfying
`payoff 0 0 = payoff 1 0` and `payoff 0 1 = payoff 1 1` (for instance the zero matrix) admit no
ESS, because every mutant matches the incumbent's fitness against every population. We prove the
exact characterization `SymmetricGame.isESS_twoByTwo_iff` and its corollary
`SymmetricGame.hasESS_twoByTwo_iff`: a `2 × 2` symmetric game has an ESS if and only if
`¬(payoff 0 0 = payoff 1 0 ∧ payoff 0 1 = payoff 1 1)`.

## Main definitions

* `Cslib.GameTheory.SymmetricGame`: a finite two-player symmetric game in strategic form.
* `Cslib.GameTheory.SymmetricGame.toBimatrixGame`: embedding into `BimatrixGame α α` as `(M, Mᵀ)`.
* `Cslib.GameTheory.SymmetricGame.fitness`: expected fitness `F(s | t) = s ⬝ᵥ (M *ᵥ t)`.
* `Cslib.GameTheory.SymmetricGame.IsBestResponse`,
  `Cslib.GameTheory.SymmetricGame.IsPureBestResponse`: symmetric best responses.
* `Cslib.GameTheory.SymmetricGame.IsESS`: evolutionarily stable strategy ([Suri2007],
  Definition 29.1).
* `Cslib.GameTheory.SymmetricGame.HasESS`: existence of an evolutionarily stable strategy.
* `Cslib.GameTheory.SymmetricGame.addConst`, `Cslib.GameTheory.SymmetricGame.smul`,
  `Cslib.GameTheory.SymmetricGame.reindex`: payoff shifting, positive scaling, and action
  reindexing.
* `Cslib.GameTheory.SymmetricGame.prisonersDilemma`,
  `Cslib.GameTheory.SymmetricGame.hawksAndDoves`,
  `Cslib.GameTheory.SymmetricGame.rockPaperScissors`,
  `Cslib.GameTheory.SymmetricGame.rockPaperScissorsTie`: classical `2 × 2` and `3 × 3` symmetric
  games.

## Main results

* `Cslib.GameTheory.SymmetricGame.isESS_iff_nash_and_stability`: **Theorem 29.2** ([Suri2007],
  p. 719): `s` is an ESS iff `(s, s)` is a symmetric Nash equilibrium and `F(t | t) < F(s | t)`
  for every alternative best response `t ≠ s` to `s`.
* `Cslib.GameTheory.SymmetricGame.isESS_iff_strict_or_eq`: Maynard Smith's two-clause ESS
  characterization (`F(t | s) < F(s | s)` or `F(t | s) = F(s | s) ∧ F(t | t) < F(s | t)`).
* `Cslib.GameTheory.SymmetricGame.isESS_reindex_iff`: reindexing preserves `IsESS`.
* `Cslib.GameTheory.SymmetricGame.isESS_addConst`,
  `Cslib.GameTheory.SymmetricGame.isESS_smul`: adding a constant or scaling by a positive constant
  preserves `IsESS`.
* `Cslib.GameTheory.SymmetricGame.isESS_twoByTwo_iff`,
  `Cslib.GameTheory.SymmetricGame.hasESS_twoByTwo_iff`: exact characterization of ESS in `2 × 2`
  symmetric games ([Suri2007], Exercise 29.3, with the degenerate indifference case noted).
* `Cslib.GameTheory.SymmetricGame.isESS_prisonersDilemma_iff`: Prisoner's Dilemma has Defect as
  its unique ESS ([Suri2007], Exercise 29.1).
* `Cslib.GameTheory.SymmetricGame.isESS_hawksAndDoves_iff_of_lt`,
  `Cslib.GameTheory.SymmetricGame.isESS_hawksAndDoves_iff_of_le`: Hawks and Doves ESS
  classification ([Suri2007], Section 29.1.1 and Exercise 29.2).
* `Cslib.GameTheory.SymmetricGame.not_hasESS_rockPaperScissors`,
  `Cslib.GameTheory.SymmetricGame.isESS_rockPaperScissorsTie_uniform_iff`: Rock–Paper–Scissors
  has a unique symmetric Nash equilibrium (`1/3, 1/3, 1/3`) and no ESS ([Suri2007], Exercise 29.4),
  while adding a positive tie penalty turns `(1/3, 1/3, 1/3)` into an ESS.

## References

* [S. Suri, *Computational Evolutionary Game Theory*, Ch. 29 of *Algorithmic Game Theory*,
  pp. 717–736][Suri2007]
-/

public section

open Finset Matrix

namespace Cslib.GameTheory

/-- A two-player *symmetric game* over pure strategies `α`, defined by a payoff matrix
`payoff : Matrix α α ℝ`. If player 1 chooses `i` and player 2 chooses `j`, player 1 earns
`payoff i j` and player 2 earns `payoff j i` ([Suri2007], Section 29.1.1). -/
structure SymmetricGame (α : Type*) where
  /-- `payoff i j` is the fitness earned by an organism playing `i` against an opponent playing `j`. -/
  payoff : Matrix α α ℝ

namespace SymmetricGame

variable {α β : Type*} [Fintype α] [Fintype β] (G : SymmetricGame α)

/-- View a symmetric game `G` as a `BimatrixGame α α` with row payoffs `G.payoff` and column
payoffs `G.payoffᵀ`. -/
@[expose] def toBimatrixGame : BimatrixGame α α :=
  ⟨G.payoff, G.payoffᵀ⟩

/-- The expected fitness `F(s | t) = s ⬝ᵥ (G.payoff *ᵥ t)` of a player playing mixed strategy `s`
against an opponent playing mixed strategy `t` ([Suri2007], Section 29.1.1). -/
@[expose] def fitness (s t : α → ℝ) : ℝ :=
  s ⬝ᵥ (G.payoff *ᵥ t)

/-- `s` is a *best response* to `t` in the symmetric game `G`. -/
def IsBestResponse (s t : α → ℝ) : Prop :=
  IsMixedStrategy s ∧ ∀ s', IsMixedStrategy s' → G.fitness s' t ≤ G.fitness s t

/-- The pure strategy `i` is a *pure best response* to `t`. -/
def IsPureBestResponse (t : α → ℝ) (i : α) : Prop :=
  ∀ i', (G.payoff *ᵥ t) i' ≤ (G.payoff *ᵥ t) i

/-- **Definition 29.1** ([Suri2007], p. 719): `s` is an *evolutionarily stable strategy (ESS)* of
the symmetric game `G` if `s` is a mixed strategy and for every mutant strategy `t ≠ s`, there is
an invasion barrier `ε₀ > 0` such that `s` strictly outperforms `t` against the mixed post-entry
population `(1 - ε) • s + ε • t` for all `0 < ε < ε₀`. -/
def IsESS (s : α → ℝ) : Prop :=
  IsMixedStrategy s ∧
    ∀ t, IsMixedStrategy t → t ≠ s →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧
        ∀ ε : ℝ, 0 < ε → ε < ε₀ →
          G.fitness t ((1 - ε) • s + ε • t) < G.fitness s ((1 - ε) • s + ε • t)

/-- `G` possesses an evolutionarily stable strategy. -/
def HasESS : Prop :=
  ∃ s, G.IsESS s

/-! ### Basic algebra and relation to `BimatrixGame` -/

theorem toBimatrixGame_payoff₁ (s t : α → ℝ) :
    G.toBimatrixGame.payoff₁ s t = G.fitness s t := rfl

theorem toBimatrixGame_payoff₂ (s t : α → ℝ) :
    G.toBimatrixGame.payoff₂ s t = G.fitness t s := by
  simp only [BimatrixGame.payoff₂, toBimatrixGame, fitness, dotProduct_mulVec,
    Matrix.vecMul_transpose, dotProduct_comm]

theorem fitness_eq_sum (s t : α → ℝ) :
    G.fitness s t = ∑ i, ∑ j, s i * G.payoff i j * t j := by
  simp only [fitness, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem fitness_symm (hSym : G.payoff.IsSymm) (s t : α → ℝ) :
    G.fitness s t = G.fitness t s := by
  rw [← toBimatrixGame_payoff₂, BimatrixGame.payoff₂, toBimatrixGame, hSym.eq, fitness]

theorem fitness_add_left (s₁ s₂ t : α → ℝ) :
    G.fitness (s₁ + s₂) t = G.fitness s₁ t + G.fitness s₂ t :=
  add_dotProduct s₁ s₂ (G.payoff *ᵥ t)

theorem fitness_add_right (s t₁ t₂ : α → ℝ) :
    G.fitness s (t₁ + t₂) = G.fitness s t₁ + G.fitness s t₂ := by
  rw [fitness, mulVec_add, dotProduct_add, fitness, fitness]

theorem fitness_sub_left (s₁ s₂ t : α → ℝ) :
    G.fitness (s₁ - s₂) t = G.fitness s₁ t - G.fitness s₂ t :=
  sub_dotProduct s₁ s₂ (G.payoff *ᵥ t)

theorem fitness_sub_right (s t₁ t₂ : α → ℝ) :
    G.fitness s (t₁ - t₂) = G.fitness s t₁ - G.fitness s t₂ := by
  rw [fitness, mulVec_sub, dotProduct_sub, fitness, fitness]

theorem fitness_smul_left (c : ℝ) (s t : α → ℝ) :
    G.fitness (c • s) t = c * G.fitness s t := by
  rw [fitness, smul_dotProduct, smul_eq_mul, fitness]

theorem fitness_smul_right (c : ℝ) (s t : α → ℝ) :
    G.fitness s (c • t) = c * G.fitness s t := by
  rw [fitness, mulVec_smul, dotProduct_smul, smul_eq_mul, fitness]

theorem fitness_convex_right (ε : ℝ) (u s t : α → ℝ) :
    G.fitness u ((1 - ε) • s + ε • t) = (1 - ε) * G.fitness u s + ε * G.fitness u t := by
  rw [fitness_add_right, fitness_smul_right, fitness_smul_right]

theorem fitness_convex_left (ε : ℝ) (s t u : α → ℝ) :
    G.fitness ((1 - ε) • s + ε • t) u = (1 - ε) * G.fitness s u + ε * G.fitness t u := by
  rw [fitness_add_left, fitness_smul_left, fitness_smul_left]

@[simp]
theorem fitness_single_left [DecidableEq α] (i : α) (t : α → ℝ) :
    G.fitness (Pi.single i 1) t = (G.payoff *ᵥ t) i := by
  rw [fitness, single_dotProduct, one_mul]

@[simp]
theorem fitness_single_right [DecidableEq α] (s : α → ℝ) (j : α) :
    G.fitness s (Pi.single j 1) = ∑ i, s i * G.payoff i j := by
  simp only [fitness, dotProduct, mulVec_single, mul_one, Matrix.col_apply]

@[simp]
theorem fitness_single_single [DecidableEq α] (i j : α) :
    G.fitness (Pi.single i 1) (Pi.single j 1) = G.payoff i j := by
  simp only [fitness_single_left, mulVec_single, mul_one, Matrix.col_apply]

/-- A convex combination of two mixed strategies is a mixed strategy. -/
theorem isMixedStrategy_convex {s t : α → ℝ} (hs : IsMixedStrategy s) (ht : IsMixedStrategy t)
    {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    IsMixedStrategy ((1 - ε) • s + ε • t) := by
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg (by linarith) (hs.nonneg i)) (mul_nonneg h0 (ht.nonneg i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
      hs.sum_eq_one, ht.sum_eq_one]
    ring

theorem isBestResponse_iff_isBestResponse₁ (s t : α → ℝ) :
    G.IsBestResponse s t ↔ G.toBimatrixGame.IsBestResponse₁ s t :=
  Iff.rfl

theorem isBestResponse_iff_isBestResponse₂ (s t : α → ℝ) :
    G.IsBestResponse s t ↔ G.toBimatrixGame.IsBestResponse₂ s t := by
  simp only [IsBestResponse, BimatrixGame.IsBestResponse₂, toBimatrixGame_payoff₂]

/-- `(s, s)` is a symmetric Nash equilibrium of `G.toBimatrixGame` iff `s` is a best response to
itself. -/
theorem toBimatrixGame_isNash_self_iff (s : α → ℝ) :
    G.toBimatrixGame.IsNash s s ↔ G.IsBestResponse s s := by
  rw [BimatrixGame.isNash_iff, ← isBestResponse_iff_isBestResponse₁,
    ← isBestResponse_iff_isBestResponse₂, and_self]

/-- Support characterization of best responses: a mixed strategy `s` is a best response to `t` iff
every pure strategy in its support is a pure best response to `t`. -/
theorem isBestResponse_iff (s t : α → ℝ) :
    G.IsBestResponse s t ↔ IsMixedStrategy s ∧ ∀ i, 0 < s i → G.IsPureBestResponse t i :=
  G.toBimatrixGame.isBestResponse₁_iff

/-- Every pure strategy in the support of a best response to `t` achieves the same fitness
`G.fitness s t` (used in the hint to [Suri2007], Exercise 29.2). -/
theorem IsBestResponse.fitness_eq_of_pos [DecidableEq α] {G : SymmetricGame α} {s t : α → ℝ}
    (h : G.IsBestResponse s t) {i : α} (hi : 0 < s i) :
    G.fitness (Pi.single i 1) t = G.fitness s t := by
  rw [fitness_single_left]
  exact ((G.isBestResponse_iff_isBestResponse₁ s t).1 h).payoff₁_eq_of_pos hi |>.symm

theorem IsBestResponse.le_fitness {G : SymmetricGame α} {s t : α → ℝ}
    (h : G.IsBestResponse s t) (i : α) :
    (G.payoff *ᵥ t) i ≤ G.fitness s t :=
  ((G.isBestResponse_iff_isBestResponse₁ s t).1 h).le_payoff₁ i

/-! ### Characterization of ESS (Theorem 29.2) -/

/-- Equivalent linear-inequality form of Definition 29.1, matching [Suri2007], p. 719, with the
invasion barrier constrained to `(0, 1]`. -/
theorem isESS_iff_linear {s : α → ℝ} :
    G.IsESS s ↔ IsMixedStrategy s ∧
      ∀ t, IsMixedStrategy t → t ≠ s →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧
          ∀ ε : ℝ, 0 < ε → ε < ε₀ →
            (1 - ε) * G.fitness t s + ε * G.fitness t t <
              (1 - ε) * G.fitness s s + ε * G.fitness s t := by
  simp only [IsESS, fitness_convex_right]
  refine and_congr_right fun _ => forall_congr' fun t => imp_congr_right fun _ =>
    imp_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨ε₀, hε₀, h⟩
    exact ⟨min ε₀ 1, lt_min hε₀ zero_lt_one, min_le_right _ _,
      fun ε h0 hlt => h ε h0 (lt_of_lt_of_le hlt (min_le_left _ _))⟩
  · rintro ⟨ε₀, hε₀, _, h⟩
    exact ⟨ε₀, hε₀, h⟩

/-- Two-clause characterization of evolutionarily stable strategies ([Suri2007], p. 719):
`s` is an ESS iff for every alternative strategy `t ≠ s`, either `F(t | s) < F(s | s)`, or
`F(t | s) = F(s | s)` and `F(t | t) < F(s | t)`. -/
theorem isESS_iff_strict_or_eq {s : α → ℝ} :
    G.IsESS s ↔ IsMixedStrategy s ∧
      ∀ t, IsMixedStrategy t → t ≠ s →
        G.fitness t s < G.fitness s s ∨
          (G.fitness t s = G.fitness s s ∧ G.fitness t t < G.fitness s t) := by
  simp only [IsESS, fitness_convex_right]
  refine and_congr_right fun _ => forall_congr' fun t => imp_congr_right fun _ =>
    imp_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨ε₀, hε₀, h⟩
    set d₁ := G.fitness s s - G.fitness t s
    set d₂ := G.fitness s t - G.fitness t t
    have hpos : ∀ ε : ℝ, 0 < ε → ε < ε₀ → 0 < d₁ + ε * (d₂ - d₁) := by
      intro ε h0 hlt
      have := h ε h0 hlt
      linarith
    have hd₁ : 0 ≤ d₁ := by
      by_contra hlt
      push Not at hlt
      rcases le_or_gt (d₂ - d₁) 0 with hd | hd
      · have := hpos (ε₀ / 2) (by linarith) (by linarith)
        nlinarith
      · set ε := min (ε₀ / 2) (-d₁ / (2 * (d₂ - d₁)))
        have hε_pos : 0 < ε := lt_min (by linarith) (div_pos (by linarith) (by linarith))
        have hε_lt : ε < ε₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
        have hε_le : ε ≤ -d₁ / (2 * (d₂ - d₁)) := min_le_right _ _
        have hmul : ε * (d₂ - d₁) ≤ -d₁ / 2 := by
          have := mul_le_mul_of_nonneg_right hε_le hd.le
          have heq : -d₁ / (2 * (d₂ - d₁)) * (d₂ - d₁) = -d₁ / 2 := by
            field_simp [hd.ne']
          linarith
        have := hpos ε hε_pos hε_lt
        linarith
    rcases hd₁.eq_or_lt with heq | hlt
    · right
      refine ⟨by linarith, ?_⟩
      have := hpos (ε₀ / 2) (by linarith) (by linarith)
      have : 0 < ε₀ / 2 * d₂ := by linarith
      have : 0 < d₂ := pos_of_mul_pos_right this (by linarith)
      linarith
    · left
      linarith
  · rintro (hlt | ⟨heq, hlt⟩)
    · set d₁ := G.fitness s s - G.fitness t s
      set d₂ := G.fitness s t - G.fitness t t
      have hd₁ : 0 < d₁ := sub_pos.2 hlt
      set B := |d₁ - d₂| + 1
      have hB : 0 < B := by positivity
      refine ⟨d₁ / B, div_pos hd₁ hB, fun ε h0 hlt' => ?_⟩
      have hmul : ε * (d₁ - d₂) ≤ ε * B :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans (by linarith)) h0.le
      have hltB : ε * B < d₁ := (lt_div_iff₀ hB).1 hlt'
      linarith
    · refine ⟨1, zero_lt_one, fun ε h0 _ => ?_⟩
      nlinarith

/-- **Theorem 29.2** ([Suri2007], p. 719): `s` is an evolutionarily stable strategy of `G` if and
only if `(s, s)` is a symmetric Nash equilibrium of `G.toBimatrixGame` and for every best response
`t ≠ s` to `s`, `F(t | t) < F(s | t)`. -/
theorem isESS_iff_nash_and_stability {s : α → ℝ} :
    G.IsESS s ↔
      G.toBimatrixGame.IsNash s s ∧
        ∀ t, IsMixedStrategy t → t ≠ s →
          G.fitness t s = G.fitness s s → G.fitness t t < G.fitness s t := by
  rw [isESS_iff_strict_or_eq, toBimatrixGame_isNash_self_iff, IsBestResponse]
  constructor
  · rintro ⟨hs, h⟩
    refine ⟨⟨hs, fun t ht => ?_⟩, fun t ht hne heq => ?_⟩
    · by_cases hts : t = s
      · subst hts; exact le_rfl
      · rcases h t ht hts with hlt | ⟨heq, _⟩
        · exact hlt.le
        · exact heq.le
    · rcases h t ht hne with hlt | ⟨_, hlt⟩
      · exact absurd heq hlt.ne
      · exact hlt
  · rintro ⟨⟨hs, hbr⟩, hst⟩
    refine ⟨hs, fun t ht hne => ?_⟩
    rcases (hbr t ht).lt_or_eq with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr ⟨heq, hst t ht hne heq⟩

theorem IsESS.isMixedStrategy {G : SymmetricGame α} {s : α → ℝ} (h : G.IsESS s) :
    IsMixedStrategy s := h.1

theorem IsESS.isNash {G : SymmetricGame α} {s : α → ℝ} (h : G.IsESS s) :
    G.toBimatrixGame.IsNash s s :=
  (G.isESS_iff_nash_and_stability.1 h).1

theorem IsESS.isBestResponse {G : SymmetricGame α} {s : α → ℝ} (h : G.IsESS s) :
    G.IsBestResponse s s :=
  (G.toBimatrixGame_isNash_self_iff s).1 h.isNash

theorem IsESS.fitness_le_self {G : SymmetricGame α} {s t : α → ℝ} (h : G.IsESS s)
    (ht : IsMixedStrategy t) : G.fitness t s ≤ G.fitness s s :=
  h.isBestResponse.2 t ht

theorem IsESS.fitness_lt_of_eq {G : SymmetricGame α} {s t : α → ℝ} (h : G.IsESS s)
    (ht : IsMixedStrategy t) (hne : t ≠ s) (heq : G.fitness t s = G.fitness s s) :
    G.fitness t t < G.fitness s t :=
  (G.isESS_iff_nash_and_stability.1 h).2 t ht hne heq

/-- A strict symmetric Nash equilibrium (`F(t | s) < F(s | s)` for all `t ≠ s`) is an ESS. -/
theorem isESS_of_strict_nash {G : SymmetricGame α} {s : α → ℝ} (hs : IsMixedStrategy s)
    (h : ∀ t, IsMixedStrategy t → t ≠ s → G.fitness t s < G.fitness s s) :
    G.IsESS s :=
  G.isESS_iff_strict_or_eq.2 ⟨hs, fun t ht hne => Or.inl (h t ht hne)⟩

/-- A strict pure best response to itself is a pure ESS. -/
theorem isESS_single_of_forall_lt [DecidableEq α] {G : SymmetricGame α} {i : α}
    (h : ∀ j, j ≠ i → G.payoff j i < G.payoff i i) :
    G.IsESS (Pi.single i 1) := by
  refine isESS_of_strict_nash (isMixedStrategy_single i) fun t ht hne => ?_
  rw [fitness_single_single, fitness_single_right]
  have hlt_one : t i < 1 := by
    rcases (show t i ≤ 1 by
      calc t i ≤ ∑ j, t j := Finset.single_le_sum (fun j _ => ht.nonneg j) (Finset.mem_univ i)
        _ = 1 := ht.sum_eq_one).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      apply hne
      ext j
      by_cases hji : j = i
      · subst hji; simp only [heq, Pi.single_eq_same]
      · have hrest : ∑ k ∈ Finset.univ.erase i, t k = 0 := by
          have := Finset.add_sum_erase (Finset.univ : Finset α) t (Finset.mem_univ i)
          linarith [ht.sum_eq_one]
        have hzero : t j = 0 :=
          Finset.sum_eq_zero_iff_of_nonneg (fun k _ => ht.nonneg k) |>.1 hrest j
            (Finset.mem_erase.2 ⟨hji, Finset.mem_univ j⟩)
        simp only [hzero, Pi.single_eq_of_ne hji]
  obtain ⟨j, hjne, hjpos⟩ : ∃ j, j ≠ i ∧ 0 < t j := by
    by_contra hall
    push Not at hall
    have hsum : ∑ j, t j = t i := by
      refine Finset.sum_eq_single i (fun j _ hj => le_antisymm (hall j hj) (ht.nonneg j))
        (fun hm => absurd (Finset.mem_univ i) hm)
    linarith [ht.sum_eq_one]
  calc ∑ k, t k * G.payoff k i
      < ∑ k, t k * G.payoff i i := by
        refine Finset.sum_lt_sum (fun k _ => ?_)
          ⟨j, Finset.mem_univ j, mul_lt_mul_of_pos_left (h j hjne) hjpos⟩
        by_cases hki : k = i
        · subst hki; exact le_rfl
        · exact mul_le_mul_of_nonneg_left (h k hki).le (ht.nonneg k)
    _ = G.payoff i i := by rw [← Finset.sum_mul, ht.sum_eq_one, one_mul]

/-- Every one-action game has its unique pure strategy as an ESS vacuously. -/
theorem isESS_single_of_subsingleton [Subsingleton α] [DecidableEq α] (i : α) :
    G.IsESS (Pi.single i 1) := by
  refine G.isESS_iff_strict_or_eq.2 ⟨isMixedStrategy_single i, fun t ht hne => ?_⟩
  exfalso
  apply hne
  ext j
  have hji : j = i := Subsingleton.elim j i
  subst hji
  have hsum : ∑ k : α, t k = t j :=
    Finset.sum_eq_single j (fun k _ hk => absurd (Subsingleton.elim k j) hk)
      (fun hm => absurd (Finset.mem_univ j) hm)
  simp only [Pi.single_eq_same, ← hsum, ht.sum_eq_one]

/-- Adding a constant `c` to every entry of a symmetric game. -/
@[expose] def addConst (c : ℝ) : SymmetricGame α :=
  ⟨G.payoff + Matrix.of fun _ _ => c⟩

/-- Scaling every entry of a symmetric game by `c`. -/
@[expose] def smul (c : ℝ) : SymmetricGame α :=
  ⟨c • G.payoff⟩

/-- Reindexing a symmetric game along a bijection `e : β ≃ α`. -/
@[expose] def reindex (e : β ≃ α) : SymmetricGame β :=
  ⟨G.payoff.submatrix e e⟩

theorem fitness_addConst (c : ℝ) {s t : α → ℝ} (hs : IsMixedStrategy s)
    (ht : IsMixedStrategy t) :
    (G.addConst c).fitness s t = G.fitness s t + c := by
  simp only [fitness, addConst, add_mulVec, dotProduct_add]
  congr 1
  simp only [dotProduct, mulVec, Matrix.of_apply, ← Finset.mul_sum, ht.sum_eq_one, mul_one,
    ← Finset.sum_mul, hs.sum_eq_one, one_mul]

@[simp]
theorem isESS_addConst (c : ℝ) (s : α → ℝ) :
    (G.addConst c).IsESS s ↔ G.IsESS s := by
  simp only [isESS_iff_strict_or_eq]
  refine and_congr_right fun hs => forall_congr' fun t => imp_congr_right fun ht =>
    imp_congr_right fun _ => ?_
  rw [G.fitness_addConst c ht hs, G.fitness_addConst c hs hs,
    G.fitness_addConst c ht ht, G.fitness_addConst c hs ht]
  simp only [add_lt_add_iff_right, add_left_inj]

@[simp]
theorem hasESS_addConst (c : ℝ) : (G.addConst c).HasESS ↔ G.HasESS :=
  exists_congr fun s => G.isESS_addConst c s

theorem fitness_smul (c : ℝ) (s t : α → ℝ) :
    (G.smul c).fitness s t = c * G.fitness s t := by
  simp only [fitness, smul, smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem isESS_smul {c : ℝ} (hc : 0 < c) (s : α → ℝ) :
    (G.smul c).IsESS s ↔ G.IsESS s := by
  simp only [isESS_iff_strict_or_eq, fitness_smul]
  refine and_congr_right fun _ => forall_congr' fun t => imp_congr_right fun _ =>
    imp_congr_right fun _ => ?_
  simp only [mul_lt_mul_iff_right₀ hc, mul_eq_mul_left_iff, hc.ne', or_false]

theorem hasESS_smul {c : ℝ} (hc : 0 < c) : (G.smul c).HasESS ↔ G.HasESS :=
  exists_congr fun s => G.isESS_smul hc s

theorem isMixedStrategy_comp_equiv (e : β ≃ α) (s : α → ℝ) :
    IsMixedStrategy (s ∘ e) ↔ IsMixedStrategy s := by
  refine and_congr (e.forall_congr_left' ) ?_
  simp only [Function.comp_apply, Equiv.sum_comp]

theorem fitness_reindex (e : β ≃ α) (s t : α → ℝ) :
    (G.reindex e).fitness (s ∘ e) (t ∘ e) = G.fitness s t := by
  simp only [fitness, reindex, dotProduct, mulVec, Matrix.submatrix_apply, Function.comp_apply]
  have inner : ∀ b : β, ∑ c : β, G.payoff (e b) (e c) * t (e c) =
      ∑ j : α, G.payoff (e b) j * t j := fun b =>
    e.sum_comp fun j => G.payoff (e b) j * t j
  simp_rw [inner]
  exact e.sum_comp fun i => s i * ∑ j, G.payoff i j * t j

theorem isESS_reindex_iff (e : β ≃ α) (s : α → ℝ) :
    (G.reindex e).IsESS (s ∘ e) ↔ G.IsESS s := by
  simp only [isESS_iff_strict_or_eq, isMixedStrategy_comp_equiv]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h t ht hne
    have ht' : IsMixedStrategy (t ∘ e) := (isMixedStrategy_comp_equiv e t).2 ht
    have hne' : t ∘ e ≠ s ∘ e := fun heq => hne (by
      ext a
      have := congrFun heq (e.symm a)
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using this)
    simpa only [fitness_reindex] using h (t ∘ e) ht' hne'
  · intro h t ht hne
    let t' : α → ℝ := t ∘ e.symm
    have ht_eq : t' ∘ e = t := by ext b; simp [t']
    have ht' : IsMixedStrategy t' :=
      (isMixedStrategy_comp_equiv e t').1 (by rwa [ht_eq])
    have hne' : t' ≠ s := fun heq => hne (by rw [← ht_eq, heq])
    simpa only [ht_eq, fitness_reindex] using h t' ht' hne'

theorem hasESS_reindex_iff (e : β ≃ α) :
    (G.reindex e).HasESS ↔ G.HasESS := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s ∘ e.symm, (G.isESS_reindex_iff e (s ∘ e.symm)).1 ?_⟩
    convert hs using 1
    ext b
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
  · rintro ⟨s, hs⟩
    exact ⟨s ∘ e, (G.isESS_reindex_iff e s).2 hs⟩

/-- In a skew-symmetric game (`payoffᵀ = -payoff`), no strictly mixed strategy (having at least two
distinct pure strategies in its support) can be an ESS. -/
theorem not_isESS_of_skewSymm_of_exists_two {G : SymmetricGame α}
    (hskew : G.payoffᵀ = -G.payoff) {s : α → ℝ} {i j : α} (hij : i ≠ j)
    (hi : 0 < s i) (hj : 0 < s j) : ¬ G.IsESS s := by
  classical
  intro hess
  have hzero : ∀ u v, G.fitness u v + G.fitness v u = 0 := by
    intro u v
    have h2 : G.fitness v u = -G.fitness u v := by
      rw [← G.toBimatrixGame_payoff₂, BimatrixGame.payoff₂, toBimatrixGame, hskew,
        neg_mulVec, dotProduct_neg, fitness]
    linarith
  have hne : Pi.single i (1 : ℝ) ≠ s := by
    intro heq
    have h0 : (Pi.single i (1 : ℝ)) j = s j := congrFun heq j
    simp only [Pi.single_eq_of_ne hij.symm] at h0
    linarith
  have heq : G.fitness (Pi.single i 1) s = G.fitness s s :=
    hess.isBestResponse.fitness_eq_of_pos hi
  have hlt := hess.fitness_lt_of_eq (isMixedStrategy_single i) hne heq
  have h1 := hzero s s
  have h2 := hzero (Pi.single i 1) (Pi.single i 1)
  have h3 := hzero s (Pi.single i 1)
  linarith

/-! ### Complete `2 × 2` characterization (Exercise 29.3) -/

private theorem fitness_sub_twoByTwo (G : SymmetricGame (Fin 2)) {s t : Fin 2 → ℝ}
    (hs : s 0 + s 1 = 1) (ht : t 0 + t 1 = 1) :
    G.fitness s t - G.fitness t t =
      (s 0 - t 0) * ((G.payoff 0 0 - G.payoff 1 0) * t 0 +
        (G.payoff 0 1 - G.payoff 1 1) * (1 - t 0)) := by
  have hs1 : s 1 = 1 - s 0 := by linarith
  have ht1 : t 1 = 1 - t 0 := by linarith
  simp only [fitness, dotProduct, mulVec, Fin.sum_univ_two, hs1, ht1]
  ring

private theorem fitness_sub_left_twoByTwo (G : SymmetricGame (Fin 2)) {s t : Fin 2 → ℝ}
    (hs : s 0 + s 1 = 1) (ht : t 0 + t 1 = 1) :
    G.fitness s s - G.fitness t s =
      (s 0 - t 0) * ((G.payoff 0 0 - G.payoff 1 0) * s 0 +
        (G.payoff 0 1 - G.payoff 1 1) * (1 - s 0)) := by
  have hs1 : s 1 = 1 - s 0 := by linarith
  have ht1 : t 1 = 1 - t 0 := by linarith
  simp only [fitness, dotProduct, mulVec, Fin.sum_univ_two, hs1, ht1]
  ring

private theorem isMixedStrategy_fin2_iff {s : Fin 2 → ℝ} :
    IsMixedStrategy s ↔ 0 ≤ s 0 ∧ s 0 ≤ 1 ∧ s 1 = 1 - s 0 := by
  rw [isMixedStrategy_iff, Fin.forall_fin_two, Fin.sum_univ_two]
  constructor
  · rintro ⟨⟨h0, h1⟩, hs⟩
    exact ⟨h0, by linarith, by linarith⟩
  · rintro ⟨h0, h1, hs⟩
    exact ⟨⟨h0, by linarith⟩, by linarith⟩

private theorem fin2_eq_iff_zero {s t : Fin 2 → ℝ} (hs : s 0 + s 1 = 1) (ht : t 0 + t 1 = 1) :
    s = t ↔ s 0 = t 0 := by
  constructor
  · intro h; rw [h]
  · intro h
    ext i
    fin_cases i
    · exact h
    · change s 1 = t 1; linarith

/-- **Exercise 29.3** ([Suri2007], p. 735): exact characterization of every ESS in a `2 × 2`
symmetric game `G` with payoff matrix `![![a, b], ![c, d]]`. -/
theorem isESS_twoByTwo_iff (G : SymmetricGame (Fin 2)) (s : Fin 2 → ℝ) :
    G.IsESS s ↔
      IsMixedStrategy s ∧
        ((s 0 = 1 ∧ (G.payoff 1 0 < G.payoff 0 0 ∨
            (G.payoff 1 0 = G.payoff 0 0 ∧ G.payoff 1 1 < G.payoff 0 1))) ∨
         (s 0 = 0 ∧ (G.payoff 0 1 < G.payoff 1 1 ∨
            (G.payoff 0 1 = G.payoff 1 1 ∧ G.payoff 0 0 < G.payoff 1 0))) ∨
         (G.payoff 0 0 < G.payoff 1 0 ∧ G.payoff 1 1 < G.payoff 0 1 ∧
            s 0 = (G.payoff 0 1 - G.payoff 1 1) /
              ((G.payoff 1 0 - G.payoff 0 0) + (G.payoff 0 1 - G.payoff 1 1)))) := by
  set a := G.payoff 0 0
  set b := G.payoff 0 1
  set c := G.payoff 1 0
  set d := G.payoff 1 1
  rw [isESS_iff_strict_or_eq]
  refine and_congr_right fun hs => ?_
  have hs_sum : s 0 + s 1 = 1 := by simpa only [Fin.sum_univ_two] using hs.sum_eq_one
  have hs0_ge : 0 ≤ s 0 := hs.nonneg 0
  have hs0_le : s 0 ≤ 1 := (isMixedStrategy_fin2_iff.1 hs).2.1
  constructor
  · intro h
    set p := s 0
    have hdiff : ∀ q : ℝ, 0 ≤ q → q ≤ 1 → q ≠ p →
        0 < (p - q) * ((a - c) * p + (b - d) * (1 - p)) ∨
          ((p - q) * ((a - c) * p + (b - d) * (1 - p)) = 0 ∧
            0 < (p - q) * ((a - c) * q + (b - d) * (1 - q))) := by
      intro q hq0 hq1 hqp
      let t : Fin 2 → ℝ := ![q, 1 - q]
      have ht : IsMixedStrategy t := isMixedStrategy_fin2_iff.2 ⟨hq0, hq1, rfl⟩
      have ht_sum : t 0 + t 1 = 1 := by simp [t]
      have hts : t ≠ s := fun heq => hqp (congrFun heq 0)
      rcases h t ht hts with hlt | ⟨heq, hlt⟩
      · left
        have := fitness_sub_left_twoByTwo G hs_sum ht_sum
        change G.fitness s s - G.fitness t s =
          (p - q) * ((a - c) * p + (b - d) * (1 - p)) at this
        linarith
      · right
        have h1 := fitness_sub_left_twoByTwo G hs_sum ht_sum
        have h2 := fitness_sub_twoByTwo G hs_sum ht_sum
        change G.fitness s s - G.fitness t s =
          (p - q) * ((a - c) * p + (b - d) * (1 - p)) at h1
        change G.fitness s t - G.fitness t t =
          (p - q) * ((a - c) * q + (b - d) * (1 - q)) at h2
        exact ⟨by linarith, by linarith⟩
    rcases hs0_le.lt_or_eq with hp_lt1 | hp_eq1
    · rcases hs0_ge.lt_or_eq with hp_pos | hp_eq0
      · -- Interior strategy `0 < p < 1`
        have h0 := hdiff 0 le_rfl (by norm_num) hp_pos.ne'
        have h1 := hdiff 1 (by norm_num) le_rfl hp_lt1.ne'
        set L := (a - c) * p + (b - d) * (1 - p)
        have hL0 : L = 0 := by
          have hge : 0 ≤ L := by
            rcases h0 with hlt | ⟨heq, _⟩
            · exact (pos_of_mul_pos_right hlt (by linarith)).le
            · rcases mul_eq_zero.1 heq with hzero | hzero
              · linarith
              · exact hzero.le
          have hle : L ≤ 0 := by
            rcases h1 with hlt | ⟨heq, _⟩
            · nlinarith
            · rcases mul_eq_zero.1 heq with hzero | hzero
              · linarith
              · exact hzero.le
          linarith
        have hgt0 : 0 < p * (b - d) := by
          rcases h0 with hlt | ⟨_, hlt⟩
          · rw [hL0, mul_zero] at hlt; linarith
          · simpa only [sub_zero, mul_zero, zero_add, mul_one] using hlt
        have hgt1 : 0 < (p - 1) * (a - c) := by
          rcases h1 with hlt | ⟨_, hlt⟩
          · rw [hL0, mul_zero] at hlt; linarith
          · simpa only [mul_one, sub_self, mul_zero, add_zero] using hlt
        have hbd : d < b := by nlinarith
        have hac : a < c := by nlinarith
        right; right
        refine ⟨hac, hbd, ?_⟩
        have hden : (c - a) + (b - d) ≠ 0 := by linarith
        apply (eq_div_iff hden).2
        linarith
      · -- Pure action 1: `p = 0`
        left_or_mid : right; left
        refine ⟨hp_eq0.symm, ?_⟩
        rcases hdiff 1 (by norm_num) le_rfl (by linarith) with hlt | ⟨heq, hlt⟩
        · left; nlinarith
        · right
          have hbd : b = d := by nlinarith
          have hac : a < c := by nlinarith
          exact ⟨hbd, hac⟩
    · -- Pure action 0: `p = 1`
      left
      refine ⟨hp_eq1, ?_⟩
      rcases hdiff 0 le_rfl (by norm_num) (by linarith) with hlt | ⟨heq, hlt⟩
      · left; nlinarith
      · right
        have hac : c = a := by nlinarith
        have hbd : d < b := by nlinarith
        exact ⟨hac, hbd⟩
  · intro h t ht hts
    have ht_sum : t 0 + t 1 = 1 := by simpa only [Fin.sum_univ_two] using ht.sum_eq_one
    have hneq : t 0 ≠ s 0 := fun heq => hts ((fin2_eq_iff_zero ht_sum hs_sum).2 heq)
    have ht0_ge : 0 ≤ t 0 := ht.nonneg 0
    have ht0_le : t 0 ≤ 1 := (isMixedStrategy_fin2_iff.1 ht).2.1
    have h1 := fitness_sub_left_twoByTwo G hs_sum ht_sum
    have h2 := fitness_sub_twoByTwo G hs_sum ht_sum
    rcases h with ⟨hp, hca | ⟨hca, hdb⟩⟩ | ⟨hp, hbd | ⟨hbd, hac⟩⟩ | ⟨hac, hdb, hp⟩
    · left
      have hpos : 0 < 1 - t 0 := by linarith
      rw [hp] at h1
      nlinarith
    · right
      have hpos : 0 < 1 - t 0 := by linarith
      rw [hp] at h1 h2
      exact ⟨by nlinarith, by nlinarith⟩
    · left
      have hpos : 0 < t 0 := by linarith
      rw [hp] at h1
      nlinarith
    · right
      have hpos : 0 < t 0 := by linarith
      rw [hp] at h1 h2
      exact ⟨by nlinarith, by nlinarith⟩
    · right
      have hden_pos : 0 < (c - a) + (b - d) := by linarith
      have hlin : (a - c) * s 0 + (b - d) * (1 - s 0) = 0 := by
        rw [hp]
        field_simp [hden_pos.ne']
        ring
      have hfac : (s 0 - t 0) * ((a - c) * t 0 + (b - d) * (1 - t 0)) =
          ((c - a) + (b - d)) * (s 0 - t 0) ^ 2 := by
        linear_combination -(s 0 - t 0) * hlin
      have hsq : 0 < (s 0 - t 0) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.2 hneq.symm)
      exact ⟨by linarith, by nlinarith⟩

/-- **Exercise 29.3 existence corollary**: a `2 × 2` symmetric game has an ESS if and only if
player 1 is not indifferent against both pure actions (`¬(payoff 0 0 = payoff 1 0 ∧
payoff 0 1 = payoff 1 1)`).

Note on source erratum: [Suri2007], Exercise 29.3 (p. 735) states without qualification that every
`2 × 2` symmetric game has an ESS; games satisfying `payoff 0 0 = payoff 1 0` and
`payoff 0 1 = payoff 1 1` (such as the zero game) have none because every two mixed strategies earn
identical fitness against every opponent. -/
theorem hasESS_twoByTwo_iff (G : SymmetricGame (Fin 2)) :
    G.HasESS ↔ ¬ (G.payoff 0 0 = G.payoff 1 0 ∧ G.payoff 0 1 = G.payoff 1 1) := by
  set a := G.payoff 0 0
  set b := G.payoff 0 1
  set c := G.payoff 1 0
  set d := G.payoff 1 1
  constructor
  · rintro ⟨s, hs⟩ ⟨hac, hbd⟩
    rcases (isESS_twoByTwo_iff G s).1 hs with ⟨_, h⟩
    rcases h with ⟨_, hlt | ⟨_, hlt⟩⟩ | ⟨_, hlt | ⟨_, hlt⟩⟩ | ⟨hlt, _, _⟩ <;> linarith
  · intro hne
    rcases lt_trichotomy a c with hac | hac | hac
    · rcases lt_trichotomy d b with hdb | hdb | hdb
      · set denom := (c - a) + (b - d)
        have hdpos : 0 < denom := by linarith
        set p := (b - d) / denom
        refine ⟨![p, 1 - p], (isESS_twoByTwo_iff G ![p, 1 - p]).2 ?_⟩
        refine ⟨isMixedStrategy_fin2_iff.2 ⟨div_nonneg (by linarith) hdpos.le,
          (div_le_one hdpos).2 (by linarith), rfl⟩, Or.inr (Or.inr ⟨hac, hdb, rfl⟩)⟩
      · refine ⟨![0, 1], (isESS_twoByTwo_iff G ![0, 1]).2 ?_⟩
        exact ⟨isMixedStrategy_fin2_iff.2 ⟨le_rfl, by norm_num, by norm_num⟩,
          Or.inr (Or.inl ⟨rfl, Or.inr ⟨hdb.symm, hac⟩⟩)⟩
      · refine ⟨![0, 1], (isESS_twoByTwo_iff G ![0, 1]).2 ?_⟩
        exact ⟨isMixedStrategy_fin2_iff.2 ⟨le_rfl, by norm_num, by norm_num⟩,
          Or.inr (Or.inl ⟨rfl, Or.inl hdb⟩)⟩
    · rcases lt_trichotomy d b with hdb | hdb | hdb
      · refine ⟨![1, 0], (isESS_twoByTwo_iff G ![1, 0]).2 ?_⟩
        exact ⟨isMixedStrategy_fin2_iff.2 ⟨by norm_num, le_rfl, by norm_num⟩,
          Or.inl ⟨rfl, Or.inr ⟨hac.symm, hdb⟩⟩⟩
      · exact absurd ⟨hac, hdb.symm⟩ hne
      · refine ⟨![0, 1], (isESS_twoByTwo_iff G ![0, 1]).2 ?_⟩
        exact ⟨isMixedStrategy_fin2_iff.2 ⟨le_rfl, by norm_num, by norm_num⟩,
          Or.inr (Or.inl ⟨rfl, Or.inl hdb⟩)⟩
    · refine ⟨![1, 0], (isESS_twoByTwo_iff G ![1, 0]).2 ?_⟩
      exact ⟨isMixedStrategy_fin2_iff.2 ⟨by norm_num, le_rfl, by norm_num⟩,
        Or.inl ⟨rfl, Or.inl hac⟩⟩

/-! ### Classical `2 × 2` examples (Exercises 29.1 and 29.2) -/

/-- The **Prisoner's Dilemma** in symmetric payoff form with action `0` = Cooperate and
action `1` = Defect: `![![R, S], ![T, P]]` (`T > R > P > S` is the classical ranking). -/
@[expose] def prisonersDilemma (R S T P : ℝ) : SymmetricGame (Fin 2) :=
  ⟨Matrix.of ![![R, S], ![T, P]]⟩

/-- **Exercise 29.1** ([Suri2007], p. 735): in the Prisoner's Dilemma with `R < T` and `S < P`,
pure defection (`Pi.single 1 1`) is the unique ESS. -/
theorem isESS_prisonersDilemma_iff {R S T P : ℝ} (hRT : R < T) (hSP : S < P) (s : Fin 2 → ℝ) :
    (prisonersDilemma R S T P).IsESS s ↔ s = Pi.single 1 1 := by
  rw [isESS_twoByTwo_iff]
  change (IsMixedStrategy s ∧
      ((s 0 = 1 ∧ (T < R ∨ (T = R ∧ P < S))) ∨
       (s 0 = 0 ∧ (S < P ∨ (S = P ∧ R < T))) ∨
       (R < T ∧ P < S ∧ s 0 = (S - P) / ((T - R) + (S - P))))) ↔ s = Pi.single 1 1
  constructor
  · rintro ⟨hs, h⟩
    have hs0 : s 0 = 0 := by
      rcases h with ⟨_, hlt | ⟨_, hlt⟩⟩ | ⟨hs0, _⟩ | ⟨_, hlt, _⟩ <;> linarith
    ext i
    fin_cases i
    · simpa only [Pi.single_apply, Fin.reduceEq, ↓reduceIte] using hs0
    · have hs1 : s 1 = 1 - s 0 := (isMixedStrategy_fin2_iff.1 hs).2.2
      simp only [Fin.isValue, Pi.single_eq_same]
      linarith
  · rintro rfl
    exact ⟨isMixedStrategy_single 1,
      Or.inr (Or.inl ⟨by simp [Pi.single_apply], Or.inl hSP⟩)⟩

theorem isESS_prisonersDilemma_defect {R S T P : ℝ} (hRT : R < T) (hSP : S < P) :
    (prisonersDilemma R S T P).IsESS (Pi.single 1 1) :=
  (isESS_prisonersDilemma_iff hRT hSP _).2 rfl

/-- The **Hawks and Doves** game ([Suri2007], Figure 29.1, p. 719): action `0` = Hawk (`H`),
action `1` = Dove (`D`). -/
@[expose] def hawksAndDoves (V C : ℝ) : SymmetricGame (Fin 2) :=
  ⟨Matrix.of ![![(V - C) / 2, V], ![0, V / 2]]⟩

/-- Pure Dove `(D, D)` is not a Nash equilibrium when `V > 0` ([Suri2007], p. 719). -/
theorem hawksAndDoves_not_isNash_dove {V C : ℝ} (hV : 0 < V) :
    ¬ (hawksAndDoves V C).toBimatrixGame.IsNash (Pi.single 1 1) (Pi.single 1 1) := by
  intro h
  have hbr := (hawksAndDoves V C).toBimatrixGame_isNash_self_iff (Pi.single 1 1) |>.1 h
  have hle := hbr.2 (Pi.single 0 1) (isMixedStrategy_single 0)
  simp only [fitness_single_single, hawksAndDoves, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one] at hle
  linarith

/-- In **Hawks and Doves**, when `V > C` (and `V > 0`), pure Hawk (`Pi.single 0 1`) is the
unique ESS ([Suri2007], Section 29.1.1, p. 720). -/
theorem isESS_hawksAndDoves_iff_of_lt {V C : ℝ} (hV : 0 < V) (hCV : C < V) (s : Fin 2 → ℝ) :
    (hawksAndDoves V C).IsESS s ↔ s = Pi.single 0 1 := by
  rw [isESS_twoByTwo_iff]
  change (IsMixedStrategy s ∧
      ((s 0 = 1 ∧ (0 < (V - C) / 2 ∨ (0 = (V - C) / 2 ∧ V / 2 < V))) ∨
       (s 0 = 0 ∧ (V < V / 2 ∨ (V = V / 2 ∧ (V - C) / 2 < 0))) ∨
       ((V - C) / 2 < 0 ∧ V / 2 < V ∧
         s 0 = (V - V / 2) / ((0 - (V - C) / 2) + (V - V / 2))))) ↔ s = Pi.single 0 1
  constructor
  · rintro ⟨hs, h⟩
    have hs0 : s 0 = 1 := by
      rcases h with ⟨h0, _⟩ | ⟨_, hlt | ⟨heq, _⟩⟩ | ⟨hlt, _, _⟩ <;> linarith
    ext i
    fin_cases i
    · simpa only [Pi.single_eq_same] using hs0
    · have hs1 : s 1 = 1 - s 0 := (isMixedStrategy_fin2_iff.1 hs).2.2
      simp only [Fin.isValue, Pi.single_apply, Fin.reduceEq, ↓reduceIte]
      linarith
  · rintro rfl
    exact ⟨isMixedStrategy_single 0, Or.inl ⟨rfl, Or.inl (by linarith)⟩⟩

/-- **Exercise 29.2** ([Suri2007], p. 735): in **Hawks and Doves**, when `0 < V ≤ C`, the
strategy `![V / C, 1 - V / C]` playing Hawk with probability `V / C` is the unique ESS
(covering both the strictly mixed case `V < C` and the boundary case `V = C`, where `V / C = 1`). -/
theorem isESS_hawksAndDoves_iff_of_le {V C : ℝ} (hV : 0 < V) (hVC : V ≤ C) (s : Fin 2 → ℝ) :
    (hawksAndDoves V C).IsESS s ↔ s = ![V / C, 1 - V / C] := by
  have hC : 0 < C := lt_of_lt_of_le hV hVC
  rw [isESS_twoByTwo_iff]
  change (IsMixedStrategy s ∧
      ((s 0 = 1 ∧ (0 < (V - C) / 2 ∨ (0 = (V - C) / 2 ∧ V / 2 < V))) ∨
       (s 0 = 0 ∧ (V < V / 2 ∨ (V = V / 2 ∧ (V - C) / 2 < 0))) ∨
       ((V - C) / 2 < 0 ∧ V / 2 < V ∧
         s 0 = (V - V / 2) / ((0 - (V - C) / 2) + (V - V / 2))))) ↔
    s = ![V / C, 1 - V / C]
  have hratio : (V - V / 2) / ((0 - (V - C) / 2) + (V - V / 2)) = V / C := by
    field_simp [hC.ne']
    ring
  constructor
  · rintro ⟨hs, h⟩
    have hs0 : s 0 = V / C := by
      rcases hVC.eq_or_lt with hEq | hLt
      · subst hEq
        have : s 0 = 1 := by
          rcases h with ⟨h0, _⟩ | ⟨_, hlt | ⟨heq, _⟩⟩ | ⟨hlt, _, _⟩ <;> linarith
        rw [this, div_self hV.ne']
      · rcases h with ⟨_, hlt | ⟨heq, _⟩⟩ | ⟨_, hlt | ⟨heq, _⟩⟩ | ⟨_, _, heq⟩
        · linarith
        · linarith
        · linarith
        · linarith
        · exact heq.trans hratio
    ext i
    fin_cases i
    · exact hs0
    · have hs1 : s 1 = 1 - s 0 := (isMixedStrategy_fin2_iff.1 hs).2.2
      simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      linarith
  · rintro rfl
    refine ⟨isMixedStrategy_fin2_iff.2 ⟨div_nonneg hV.le hC.le, (div_le_one hC).2 hVC, rfl⟩, ?_⟩
    rcases hVC.eq_or_lt with hEq | hLt
    · subst hEq
      left
      exact ⟨div_self hV.ne', Or.inr ⟨by ring, by linarith⟩⟩
    · right; right
      exact ⟨by linarith, by linarith, hratio.symm⟩

/-! ### Rock–Paper–Scissors and tie-penalty variant (Exercise 29.4) -/

/-- The `3 × 3` **Rock–Paper–Scissors** game with tie penalty `-δ`: diagonal entries are `-δ`
(`0` yields the standard zero-sum skew-symmetric game). Action `0` = Rock, `1` = Paper,
`2` = Scissors. -/
@[expose] def rockPaperScissorsTie (δ : ℝ) : SymmetricGame (Fin 3) :=
  ⟨Matrix.of ![![-δ, -1, 1], ![1, -δ, -1], ![-1, 1, -δ]]⟩

/-- The standard **Rock–Paper–Scissors** game (`δ = 0`). -/
@[expose] def rockPaperScissors : SymmetricGame (Fin 3) :=
  rockPaperScissorsTie 0

theorem rockPaperScissors_isSkewSymm :
    rockPaperScissors.payoffᵀ = -rockPaperScissors.payoff := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rockPaperScissors, rockPaperScissorsTie]

/-- The uniform mixed strategy `![1/3, 1/3, 1/3]` on `Fin 3`. -/
@[expose] def uniformThree : Fin 3 → ℝ := ![1 / 3, 1 / 3, 1 / 3]

theorem isMixedStrategy_uniformThree : IsMixedStrategy uniformThree := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> norm_num [uniformThree]
  · simp only [Fin.sum_univ_three, uniformThree]
    norm_num

private theorem rockPaperScissorsTie_mulVec_uniform (δ : ℝ) (i : Fin 3) :
    ((rockPaperScissorsTie δ).payoff *ᵥ uniformThree) i = -δ / 3 := by
  fin_cases i <;>
    simp only [mulVec, dotProduct, Fin.sum_univ_three, rockPaperScissorsTie, Matrix.of_apply,
      uniformThree, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;>
    ring

private theorem rockPaperScissorsTie_fitness_self (δ : ℝ) (t : Fin 3 → ℝ) :
    (rockPaperScissorsTie δ).fitness t t = -δ * (t 0 ^ 2 + t 1 ^ 2 + t 2 ^ 2) := by
  simp only [fitness, dotProduct, mulVec, Fin.sum_univ_three, rockPaperScissorsTie,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

private theorem rockPaperScissorsTie_fitness_uniform_left (δ : ℝ) {t : Fin 3 → ℝ}
    (ht : t 0 + t 1 + t 2 = 1) :
    (rockPaperScissorsTie δ).fitness uniformThree t = -δ / 3 := by
  have hcalc : (rockPaperScissorsTie δ).fitness uniformThree t =
      (-δ / 3) * (t 0 + t 1 + t 2) := by
    simp only [fitness, dotProduct, mulVec, Fin.sum_univ_three, rockPaperScissorsTie,
      Matrix.of_apply, uniformThree, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring
  rw [hcalc, ht, mul_one]

/-- Uniform mixing `(1/3, 1/3, 1/3)` is the unique symmetric Nash equilibrium of `rockPaperScissors`. -/
theorem isNash_rockPaperScissors_iff (s : Fin 3 → ℝ) :
    rockPaperScissors.toBimatrixGame.IsNash s s ↔ s = uniformThree := by
  rw [toBimatrixGame_isNash_self_iff]
  constructor
  · intro hbr
    have hsum : s 0 + s 1 + s 2 = 1 := by
      simpa only [Fin.sum_univ_three] using hbr.1.sum_eq_one
    have hself : rockPaperScissors.fitness s s = 0 := by
      rw [rockPaperScissors, rockPaperScissorsTie_fitness_self]
      ring
    have h0 := hbr.le_fitness 0
    have h1 := hbr.le_fitness 1
    have h2 := hbr.le_fitness 2
    rw [hself] at h0 h1 h2
    simp only [mulVec, dotProduct, Fin.sum_univ_three, rockPaperScissors, rockPaperScissorsTie,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h0 h1 h2
    ext i
    fin_cases i <;> simp only [Fin.isValue, uniformThree, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val] <;> linarith
  · rintro rfl
    refine ⟨isMixedStrategy_uniformThree, fun s' hs' => ?_⟩
    have hsum : s' 0 + s' 1 + s' 2 = 1 := by
      simpa only [Fin.sum_univ_three] using hs'.sum_eq_one
    have hu : rockPaperScissors.fitness uniformThree uniformThree = 0 := by
      rw [rockPaperScissors, rockPaperScissorsTie_fitness_self]
      ring
    have hs'u : rockPaperScissors.fitness s' uniformThree = 0 := by
      simp only [fitness, dotProduct, Fin.sum_univ_three, rockPaperScissors,
        rockPaperScissorsTie_mulVec_uniform]
      ring
    linarith

/-- Uniform mixing is a symmetric Nash equilibrium of `rockPaperScissorsTie δ` for every `δ`. -/
theorem isNash_rockPaperScissorsTie_uniform (δ : ℝ) :
    (rockPaperScissorsTie δ).toBimatrixGame.IsNash uniformThree uniformThree := by
  rw [toBimatrixGame_isNash_self_iff]
  refine ⟨isMixedStrategy_uniformThree, fun s' hs' => ?_⟩
  have hsum : s' 0 + s' 1 + s' 2 = 1 := by
    simpa only [Fin.sum_univ_three] using hs'.sum_eq_one
  have h1 : (rockPaperScissorsTie δ).fitness s' uniformThree = -δ / 3 := by
    have : (rockPaperScissorsTie δ).fitness s' uniformThree =
        (s' 0 + s' 1 + s' 2) * (-δ / 3) := by
      simp only [fitness, dotProduct, Fin.sum_univ_three, rockPaperScissorsTie_mulVec_uniform]
      ring
    rw [this, hsum, one_mul]
  have h2 : (rockPaperScissorsTie δ).fitness uniformThree uniformThree = -δ / 3 :=
    rockPaperScissorsTie_fitness_uniform_left δ (by norm_num [uniformThree])
  linarith

/-- In the tie-penalty variant of Rock–Paper–Scissors, uniform mixing `(1/3, 1/3, 1/3)` is an ESS
if and only if ties are strictly penalized (`0 < δ`). -/
theorem isESS_rockPaperScissorsTie_uniform_iff (δ : ℝ) :
    (rockPaperScissorsTie δ).IsESS uniformThree ↔ 0 < δ := by
  rw [isESS_iff_nash_and_stability]
  have hU := isNash_rockPaperScissorsTie_uniform δ
  have hu : (rockPaperScissorsTie δ).fitness uniformThree uniformThree = -δ / 3 :=
    rockPaperScissorsTie_fitness_uniform_left δ (by norm_num [uniformThree])
  constructor
  · intro ⟨_, hst⟩
    have h0ne : (Pi.single (0 : Fin 3) (1 : ℝ)) ≠ uniformThree := by
      intro heq
      have := congrFun heq 0
      norm_num [uniformThree] at this
    have h0eq : (rockPaperScissorsTie δ).fitness (Pi.single 0 1) uniformThree = -δ / 3 := by
      rw [fitness_single_left, rockPaperScissorsTie_mulVec_uniform]
    have hlt := hst (Pi.single 0 1) (isMixedStrategy_single 0) h0ne (by linarith)
    rw [rockPaperScissorsTie_fitness_uniform_left δ (by simp),
      rockPaperScissorsTie_fitness_self] at hlt
    norm_num [Pi.single_apply] at hlt
    linarith
  · intro hδ
    refine ⟨hU, fun t ht hne _ => ?_⟩
    have ht_sum : t 0 + t 1 + t 2 = 1 := by
      simpa only [Fin.sum_univ_three] using ht.sum_eq_one
    rw [rockPaperScissorsTie_fitness_self, rockPaperScissorsTie_fitness_uniform_left δ ht_sum]
    have hvar : t 0 ^ 2 + t 1 ^ 2 + t 2 ^ 2 - 1 / 3 =
        (t 0 - 1 / 3) ^ 2 + (t 1 - 1 / 3) ^ 2 + (t 2 - 1 / 3) ^ 2 := by
      linear_combination (2 / 3) * (ht_sum - 1)
    have hpos : 0 < (t 0 - 1 / 3) ^ 2 + (t 1 - 1 / 3) ^ 2 + (t 2 - 1 / 3) ^ 2 := by
      by_contra hle
      push Not at hle
      have h0 : t 0 - 1 / 3 = 0 := by nlinarith [sq_nonneg (t 0 - 1 / 3),
        sq_nonneg (t 1 - 1 / 3), sq_nonneg (t 2 - 1 / 3)]
      have h1 : t 1 - 1 / 3 = 0 := by nlinarith [sq_nonneg (t 0 - 1 / 3),
        sq_nonneg (t 1 - 1 / 3), sq_nonneg (t 2 - 1 / 3)]
      have h2 : t 2 - 1 / 3 = 0 := by nlinarith [sq_nonneg (t 0 - 1 / 3),
        sq_nonneg (t 1 - 1 / 3), sq_nonneg (t 2 - 1 / 3)]
      apply hne
      ext i
      fin_cases i <;> simp only [Fin.isValue, uniformThree, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val] <;> linarith
    nlinarith

/-- **Exercise 29.4** ([Suri2007], p. 735): Rock–Paper–Scissors has no evolutionarily stable
strategy. -/
theorem not_hasESS_rockPaperScissors : ¬ rockPaperScissors.HasESS := by
  rintro ⟨s, hs⟩
  have heq : s = uniformThree := (isNash_rockPaperScissors_iff s).1 hs.isNash
  subst heq
  exact not_lt_of_ge le_rfl ((isESS_rockPaperScissorsTie_uniform_iff 0).1 hs)

/-- **Exercise 29.4** ([Suri2007], p. 735): there exists a finite symmetric two-player game
possessing a symmetric Nash equilibrium but no ESS. -/
theorem exists_symmetricGame_isNash_and_not_hasESS :
    ∃ (G : SymmetricGame (Fin 3)) (s : Fin 3 → ℝ),
      G.toBimatrixGame.IsNash s s ∧ ¬ G.HasESS :=
  ⟨rockPaperScissors, uniformThree, (isNash_rockPaperScissors_iff uniformThree).2 rfl,
    not_hasESS_rockPaperScissors⟩

end SymmetricGame

end Cslib.GameTheory
