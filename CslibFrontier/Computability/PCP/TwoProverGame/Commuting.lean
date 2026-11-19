/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.CHSH
public import CslibFrontier.Computability.PCP.TwoProverGame.Quantum
public import CslibFrontier.Foundations.Quantum.Algebra.Measurement
public import CslibFrontier.Foundations.Quantum.Algebra.Tsirelson
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Commuting-operator strategies

A *commuting-operator strategy* (`Cslib.PCP.CommutingStrategy`) for a two-prover one-round game
plays in an algebra of observables `𝒜`: a state `φ` on `𝒜`, a measurement `{P_x^a}_a` in `𝒜` for
each question `x` of Alice and `{Q_y^b}_b` for each question `y` of Bob, and every effect of Alice
commutes with every effect of Bob. On questions `(x, y)` the players answer `(a, b)` with
probability `Re φ(P_x^a Q_y^b)` (`Cslib.PCP.CommutingStrategy.prob`). Commutation is what makes
these numbers a probability distribution (`Cslib.PCP.CommutingStrategy.answers`): in an algebra
with a continuous functional calculus, such as the matrix algebras or any C⋆-algebra, commuting
nonnegative elements have a nonnegative product.

This is the commuting-operator model of nonlocal games, in algebraic form: by the GNS construction
a state on a C⋆-algebra is a vector state of a representation on a Hilbert space. The
finite-dimensional tensor-product model is the instance on the matrix algebra of `ℂ^ι ⊗ ℂ^κ` with
the effects `E ⊗ 1` and `1 ⊗ F` and a vector state (`Cslib.PCP.QuantumStrategy.toCommuting`), and
it has the same answer distribution (`Cslib.PCP.QuantumStrategy.answers_toCommuting`) and winning
probability (`Cslib.PCP.TwoProverGame.commutingWinProb_toCommuting`). A theorem about commuting
strategies therefore applies to both models.

**Tsirelson's bound** holds in this model: every commuting-operator strategy wins CHSH with
probability at most `cos²(π/8)` (`Cslib.PCP.TwoProverGame.commutingWinProb_chsh_le`), as a
consequence of Tsirelson's inequality for states (`Cslib.Quantum.AlgState.re_chsh_le`)
[Cirel'son][Cirelson1980].

## Main definitions

* `Cslib.PCP.CommutingStrategy`: a commuting-operator strategy.
* `Cslib.PCP.CommutingStrategy.answers`: the distribution of the answers.
* `Cslib.PCP.TwoProverGame.commutingWinProb`: the winning probability.
* `Cslib.PCP.QuantumStrategy.toCommuting`: a tensor-product strategy as a commuting-operator
  strategy.

## Main results

* `Cslib.PCP.TwoProverGame.commutingWinProb_toCommuting`: the tensor-product model is an instance.
* `Cslib.PCP.CommutingStrategy.sum_ite_prob_eq`: the probability that the first player's bit
  matches a function of the other answer, as a correlation.
* `Cslib.PCP.TwoProverGame.commutingWinProb_chsh_le`: Tsirelson's bound for commuting-operator
  strategies.

## References

* [B. S. Cirel'son, *Quantum generalizations of Bell's inequality*][Cirelson1980]
* [R. Cleve, P. Høyer, B. Toner, J. Watrous, *Consequences and limits of nonlocal
  strategies*][CleveHoyerTonerWatrous2004]
-/

@[expose] public section

namespace Cslib.PCP

open Finset Quantum
open scoped Real

/-- A **commuting-operator strategy** for a game with questions `X`, `Y` and answers `A`, `B`, in
the algebra of observables `𝒜`: a state, a measurement for each question of each player, and
every effect of Alice commutes with every effect of Bob. -/
structure CommutingStrategy (X Y A B 𝒜 : Type*) [Fintype A] [Fintype B] [Ring 𝒜]
    [PartialOrder 𝒜] [Algebra ℂ 𝒜] where
  /-- The shared state. -/
  state : AlgState 𝒜
  /-- Alice's measurement on question `x`. -/
  alice : X → Measurement A 𝒜
  /-- Bob's measurement on question `y`. -/
  bob : Y → Measurement B 𝒜
  /-- Alice's effects commute with Bob's. -/
  commute : ∀ x y a b, Commute ((alice x).effect a) ((bob y).effect b)

namespace CommutingStrategy

variable {X Y A B 𝒜 : Type*} [Fintype A] [Fintype B]

section Ring

variable [Ring 𝒜] [PartialOrder 𝒜] [Algebra ℂ 𝒜]

/-- The probability `Re φ(P_x^a Q_y^b)` that the players answer `(a, b)` on questions `(x, y)`. -/
noncomputable def prob (S : CommutingStrategy X Y A B 𝒜) (x : X) (y : Y) (a : A) (b : B) : ℝ :=
  (S.state ((S.alice x).effect a * (S.bob y).effect b)).re

/-- Summing over Bob's answer gives Alice's marginal, independent of Bob's question. -/
theorem sum_prob_bob (S : CommutingStrategy X Y A B 𝒜) (x : X) (y : Y) (a : A) :
    ∑ b, S.prob x y a b = (S.state ((S.alice x).effect a)).re := by
  simp only [prob, ← Complex.re_sum, ← map_sum, ← mul_sum, (S.bob y).sum_effect, mul_one]

/-- Summing over Alice's answer gives Bob's marginal, independent of Alice's question. -/
theorem sum_prob_alice (S : CommutingStrategy X Y A B 𝒜) (x : X) (y : Y) (b : B) :
    ∑ a, S.prob x y a b = (S.state ((S.bob y).effect b)).re := by
  simp only [prob, ← Complex.re_sum, ← map_sum, ← sum_mul, (S.alice x).sum_effect, one_mul]

/-- Exchange the two physical players of a commuting strategy. -/
def swap (S : CommutingStrategy X Y A B 𝒜) : CommutingStrategy Y X B A 𝒜 where
  state := S.state
  alice := S.bob
  bob := S.alice
  commute y x b a := (S.commute x y a b).symm

@[simp] theorem prob_swap (S : CommutingStrategy X Y A B 𝒜) (x : X) (y : Y) (a : A) (b : B) :
    S.swap.prob y x b a = S.prob x y a b := by
  unfold prob
  rw [(S.commute x y a b).eq]
  rfl

theorem sum_prob (S : CommutingStrategy X Y A B 𝒜) (x : X) (y : Y) :
    ∑ a, ∑ b, S.prob x y a b = 1 := by
  simp only [S.sum_prob_bob, ← Complex.re_sum, ← map_sum, (S.alice x).sum_effect,
    AlgState.map_one, Complex.one_re]

end Ring

section CFC

variable [Ring 𝒜] [StarRing 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Algebra ℂ 𝒜]
  [TopologicalSpace 𝒜] [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint]
  [NonnegSpectrumClass ℝ 𝒜]

theorem effect_mul_effect_nonneg (S : CommutingStrategy X Y A B 𝒜) (x : X) (y : Y) (a : A)
    (b : B) : 0 ≤ (S.alice x).effect a * (S.bob y).effect b :=
  Commute.mul_nonneg ((S.alice x).nonneg a) ((S.bob y).nonneg b) (S.commute x y a b)

theorem prob_nonneg (S : CommutingStrategy X Y A B 𝒜) (x : X) (y : Y) (a : A) (b : B) :
    0 ≤ S.prob x y a b :=
  S.state.re_apply_nonneg (S.effect_mul_effect_nonneg x y a b)

/-- The distribution of the answers on questions `(x, y)`. -/
noncomputable def answers (S : CommutingStrategy X Y A B 𝒜) (x : X) (y : Y) : PMF (A × B) :=
  PMF.ofFintype (fun ab => ENNReal.ofReal (S.prob x y ab.1 ab.2)) <| by
    rw [← ENNReal.ofReal_sum_of_nonneg fun ab _ => S.prob_nonneg x y ab.1 ab.2,
      Fintype.sum_prod_type, S.sum_prob, ENNReal.ofReal_one]

theorem answers_apply (S : CommutingStrategy X Y A B 𝒜) (x : X) (y : Y) (a : A) (b : B) :
    S.answers x y (a, b) = ENNReal.ofReal (S.prob x y a b) := by
  rw [answers, PMF.ofFintype_apply]

end CFC

/-! ### Correlations of binary strategies -/

section Correlation

variable [Ring 𝒜] [PartialOrder 𝒜] [Algebra ℂ 𝒜] [StarRing 𝒜]

/-- The correlation `Re φ(A_x B_y)` of the observables `A_x = P_x^0 - P_x^1` and
`B_y = Q_y^0 - Q_y^1` of a strategy with binary answers. -/
noncomputable def correlation (S : CommutingStrategy X Y Bool Bool 𝒜) (x : X) (y : Y) : ℝ :=
  (S.state ((S.alice x).observable * (S.bob y).observable)).re

omit [StarRing 𝒜] in
/-- The correlation is `Pr[a = b] - Pr[a ≠ b]`. -/
theorem correlation_eq (S : CommutingStrategy X Y Bool Bool 𝒜) (x : X) (y : Y) :
    S.correlation x y = S.prob x y false false - S.prob x y false true -
      S.prob x y true false + S.prob x y true true := by
  simp only [correlation, prob, Measurement.observable, sub_mul, mul_sub, map_sub,
    Complex.sub_re]
  ring

variable [StarOrderedRing 𝒜] {B : Type*} [Fintype B] in
/-- The first player's observable commutes with every post-processed observable of the second. -/
theorem commute_observable_map (S : CommutingStrategy X Y Bool B 𝒜) (g : B → Bool) (x : X)
    (y : Y) : Commute (((S.bob y).map g).observable) ((S.alice x).observable) := by
  classical
  simp only [Measurement.observable, Measurement.map_effect]
  refine (Commute.sub_left ?_ ?_) <;> refine Commute.sum_left _ _ _ fun r _ => ?_ <;>
    exact ((S.commute x y false r).sub_left (S.commute x y true r)).symm

variable [StarOrderedRing 𝒜] {B : Type*} [Fintype B] in
/-- The probability that the bit `γ` of the first player equals `g(r)` for the answer `r` of the
second is the correlation of their observables: `(1 + Re φ(A_x G_y)) / 2`, where `G_y` is the
observable of the second player's measurement post-processed by `g`. -/
theorem sum_ite_prob_eq (S : CommutingStrategy X Y Bool B 𝒜) (g : B → Bool) (x : X) (y : Y) :
    ∑ γ, ∑ r, (if γ = g r then S.prob x y γ r else 0) =
      (1 + (S.state ((S.alice x).observable * ((S.bob y).map g).observable)).re) / 2 := by
  classical
  have h : ∀ γ, ∑ r, (if γ = g r then S.prob x y γ r else 0) =
      (S.state ((S.alice x).effect γ * ((S.bob y).map g).effect γ)).re := by
    intro γ
    rw [Measurement.map_effect, mul_sum, map_sum, Complex.re_sum, sum_filter]
    refine sum_congr rfl fun r _ => ?_
    simp only [prob, eq_comm]
  simp only [h, Fintype.sum_bool]
  set s := (S.alice x).effect false
  set t := (S.alice x).effect true
  set u := ((S.bob y).map g).effect false
  set v := ((S.bob y).map g).effect true
  have hst : t = 1 - s := by
    have := (S.alice x).sum_effect
    rw [Fintype.sum_bool] at this
    exact eq_sub_of_add_eq this
  have huv : v = 1 - u := by
    have := ((S.bob y).map g).sum_effect
    rw [Fintype.sum_bool] at this
    exact eq_sub_of_add_eq this
  have key : 1 + (s - t) * (u - v) = (t * v + s * u) + (t * v + s * u) := by
    rw [hst, huv]; noncomm_ring
  rw [Measurement.observable, Measurement.observable, ← Complex.add_re, ← map_add]
  change _ = (1 + (S.state ((s - t) * (u - v))).re) / 2
  have h1 : (1 : ℝ) = (S.state 1).re := by rw [S.state.map_one, Complex.one_re]
  rw [h1, ← Complex.add_re, ← map_add, key]
  simp only [map_add, Complex.add_re]
  ring

end Correlation

end CommutingStrategy

namespace TwoProverGame

variable {X Y A B 𝒜 : Type*} (G : TwoProverGame X Y A B) [Fintype A] [Fintype B]
  [Ring 𝒜] [StarRing 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Algebra ℂ 𝒜]
  [TopologicalSpace 𝒜] [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint]
  [NonnegSpectrumClass ℝ 𝒜]

/-- The probability that the commuting-operator strategy `S` wins `G`. -/
noncomputable def commutingWinProb (S : CommutingStrategy X Y A B 𝒜) : ℝ :=
  G.answersWinProb S.answers

theorem commutingWinProb_nonneg (S : CommutingStrategy X Y A B 𝒜) : 0 ≤ G.commutingWinProb S :=
  G.answersWinProb_nonneg _

theorem commutingWinProb_le_one (S : CommutingStrategy X Y A B 𝒜) :
    G.commutingWinProb S ≤ 1 :=
  G.answersWinProb_le_one _

/-- The winning probability of a commuting-operator strategy:
`∑_{x,y} π(x,y) ∑_{a,b} V(a,b|x,y) Re φ(P_x^a Q_y^b)`. -/
theorem commutingWinProb_eq_sum [Fintype X] [Fintype Y]
    [∀ x y a b, Decidable (G.accepts x y a b)] (S : CommutingStrategy X Y A B 𝒜) :
    G.commutingWinProb S = ∑ x, ∑ y, (G.questions (x, y)).toReal * ∑ a, ∑ b,
      if G.accepts x y a b then S.prob x y a b else 0 :=
  G.answersWinProb_eq_sum_of_ofReal _ _ S.prob_nonneg S.answers_apply

/-- The winning probability of a commuting-operator strategy for CHSH in terms of its
correlations. -/
theorem commutingWinProb_chsh (S : CommutingStrategy Bool Bool Bool Bool 𝒜) :
    chsh.commutingWinProb S = 1 / 2 + (S.correlation false false + S.correlation false true +
      S.correlation true false - S.correlation true true) / 8 := by
  rw [commutingWinProb_eq_sum]
  simp only [chsh_questions_apply, Fintype.sum_bool]
  simp only [chsh, Bool.xor_true, Bool.xor_false, Bool.not_true, Bool.not_false, Bool.and_true,
    Bool.and_false, Bool.true_eq_false, Bool.false_eq_true, ite_true, ite_false]
  have h1 := S.correlation_eq false false
  have h2 := S.correlation_eq false true
  have h3 := S.correlation_eq true false
  have h4 := S.correlation_eq true true
  have h5 := S.sum_prob false false
  have h6 := S.sum_prob false true
  have h7 := S.sum_prob true false
  have h8 := S.sum_prob true true
  simp only [Fintype.sum_bool] at h5 h6 h7 h8
  linarith

variable [StarModule ℂ 𝒜] [SelfAdjointDecompose 𝒜]

/-- **Tsirelson's inequality** for commuting-operator strategies. -/
theorem _root_.Cslib.PCP.CommutingStrategy.chsh_correlation_le
    (S : CommutingStrategy X Y Bool Bool 𝒜) (x₀ x₁ : X) (y₀ y₁ : Y) :
    S.correlation x₀ y₀ + S.correlation x₀ y₁ + S.correlation x₁ y₀ - S.correlation x₁ y₁ ≤
      2 * √2 := by
  have h := S.state.re_chsh_le ((S.alice x₀).isSelfAdjoint_observable)
    ((S.alice x₁).isSelfAdjoint_observable) ((S.alice x₀).star_observable_mul_self_le_one)
    ((S.alice x₁).star_observable_mul_self_le_one) ((S.bob y₀).star_observable_mul_self_le_one)
    ((S.bob y₁).star_observable_mul_self_le_one)
  simpa only [CommutingStrategy.correlation, map_add, map_sub, Complex.add_re,
    Complex.sub_re] using h

/-- **Tsirelson's bound** in the commuting-operator model: every commuting-operator strategy wins
CHSH with probability at most `cos²(π/8)`. -/
theorem commutingWinProb_chsh_le (S : CommutingStrategy Bool Bool Bool Bool 𝒜) :
    chsh.commutingWinProb S ≤ Real.cos (π / 8) ^ 2 := by
  rw [commutingWinProb_chsh, Real.cos_sq_pi_div_eight]
  linarith [S.chsh_correlation_le false true false true]

end TwoProverGame

/-! ### The tensor-product model as an instance -/

namespace QuantumStrategy

open Matrix
open scoped Kronecker MatrixOrder ComplexOrder

private theorem sum_kronecker_one {α ι κ : Type*} [Fintype α] [DecidableEq κ]
    (f : α → Matrix ι ι ℂ) :
    (∑ a, f a) ⊗ₖ (1 : Matrix κ κ ℂ) = ∑ a, f a ⊗ₖ (1 : Matrix κ κ ℂ) := by
  ext ⟨i, k⟩ ⟨i', k'⟩
  simp [Matrix.sum_apply, Finset.sum_mul]

private theorem one_kronecker_sum {α ι κ : Type*} [Fintype α] [DecidableEq ι]
    (f : α → Matrix κ κ ℂ) :
    (1 : Matrix ι ι ℂ) ⊗ₖ (∑ a, f a) = ∑ a, (1 : Matrix ι ι ℂ) ⊗ₖ f a := by
  ext ⟨i, k⟩ ⟨i', k'⟩
  simp [Matrix.sum_apply, Finset.mul_sum]

variable {X Y A B ι κ : Type*} [Fintype A] [Fintype B] [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ]

/-- Alice's measurement `E ⊗ 1` on the bipartite system. -/
noncomputable def leftMeasurement (M : POVM A ι) : Measurement A (Matrix (ι × κ) (ι × κ) ℂ) where
  effect a := M.effect a ⊗ₖ 1
  nonneg a := Matrix.nonneg_iff_posSemidef.mpr ((M.posSemidef a).kronecker PosSemidef.one)
  sum_effect := by rw [← sum_kronecker_one, M.sum_effect, one_kronecker_one]

/-- Bob's measurement `1 ⊗ F` on the bipartite system. -/
noncomputable def rightMeasurement (N : POVM B κ) : Measurement B (Matrix (ι × κ) (ι × κ) ℂ) where
  effect b := 1 ⊗ₖ N.effect b
  nonneg b := Matrix.nonneg_iff_posSemidef.mpr (PosSemidef.one.kronecker (N.posSemidef b))
  sum_effect := by rw [← one_kronecker_sum, N.sum_effect, one_kronecker_one]

/-- A tensor-product strategy as a commuting-operator strategy on the matrix algebra of
`ℂ^ι ⊗ ℂ^κ`: the effects `E ⊗ 1` and `1 ⊗ F` and the vector state of the shared state. -/
noncomputable def toCommuting (S : QuantumStrategy X Y A B ι κ) :
    CommutingStrategy X Y A B (Matrix (ι × κ) (ι × κ) ℂ) where
  state := AlgState.vector S.state S.norm_state
  alice x := leftMeasurement (S.alice x)
  bob y := rightMeasurement (S.bob y)
  commute x y a b := by
    change Commute ((S.alice x).effect a ⊗ₖ 1) (1 ⊗ₖ (S.bob y).effect b)
    simp only [Commute, SemiconjBy, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

theorem prob_toCommuting (S : QuantumStrategy X Y A B ι κ) (x : X) (y : Y) (a : A) (b : B) :
    S.toCommuting.prob x y a b = S.prob x y a b := by
  rw [CommutingStrategy.prob, prob_eq]
  change (star S.state.ofLp ⬝ᵥ (((S.alice x).effect a ⊗ₖ 1 * 1 ⊗ₖ (S.bob y).effect b) *ᵥ
    S.state.ofLp)).re = _
  rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

/-- The tensor-product strategy and its commuting-operator form answer alike. -/
theorem answers_toCommuting (S : QuantumStrategy X Y A B ι κ) (x : X) (y : Y) :
    S.toCommuting.answers x y = S.answers x y := by
  ext ⟨a, b⟩
  rw [CommutingStrategy.answers_apply, answers_apply, prob_toCommuting, prob_eq]

end QuantumStrategy

namespace TwoProverGame

open scoped MatrixOrder ComplexOrder

variable {X Y A B ι κ : Type*} (G : TwoProverGame X Y A B) [Fintype A] [Fintype B] [Fintype ι]
  [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The tensor-product model is an instance of the commuting-operator model: a strategy and its
commuting-operator form win with the same probability. -/
theorem commutingWinProb_toCommuting (S : QuantumStrategy X Y A B ι κ) :
    G.commutingWinProb S.toCommuting = G.quantumWinProb S := by
  rw [commutingWinProb, quantumWinProb]
  congr 1
  funext x y
  exact QuantumStrategy.answers_toCommuting S x y

end TwoProverGame

end Cslib.PCP
