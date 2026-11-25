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
public import CslibFrontier.Foundations.Quantum.Algebra.SuccessfulAgreement
import CslibFrontier.Probability.PMF.Event
public import CslibFrontier.Foundations.Quantum.Algebra.Tsirelson
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Trigonometric.Basic
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Foundations.Quantum.Algebra.MaxEntangled
import CslibFrontier.Foundations.Quantum.Algebra.TensorState

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
@[ext] structure CommutingStrategy (X Y A B 𝒜 : Type*) [Fintype A] [Fintype B] [Ring 𝒜]
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
  simp [prob, swap, (S.commute x y a b).eq]

theorem sum_prob (S : CommutingStrategy X Y A B 𝒜) (x : X) (y : Y) :
    ∑ a, ∑ b, S.prob x y a b = 1 :=
  Measurement.sum_re_effect_mul_effect S.state (S.alice x) (S.bob y)

/-- Pull back each player's questions and post-process each player's outcomes independently. -/
noncomputable def relabel {X' Y' A' B' : Type*} [Fintype A'] [Fintype B']
    [IsOrderedAddMonoid 𝒜] (S : CommutingStrategy X Y A B 𝒜)
    (qx : X' → X) (qy : Y' → Y) (fa : A → A') (fb : B → B') :
    CommutingStrategy X' Y' A' B' 𝒜 := by
  classical
  exact
    { state := S.state
      alice := fun x => (S.alice (qx x)).map fa
      bob := fun y => (S.bob (qy y)).map fb
      commute := fun x y =>
        Measurement.commute_map_map (S.alice (qx x)) (S.bob (qy y))
          (S.commute (qx x) (qy y)) fa fb }

variable [IsOrderedAddMonoid 𝒜]

/-- Restrict the questions and postprocess the answers of both players, keeping the same
state. Each answer effect is a sum of mutually cross-player commuting effects. -/
def map {X' Y' A' B' : Type*} [Fintype A'] [Fintype B'] [DecidableEq A'] [DecidableEq B']
    (S : CommutingStrategy X Y A B 𝒜) (questionAlice : X' → X) (questionBob : Y' → Y)
    (answerAlice : X' → A → A') (answerBob : Y' → B → B') :
    CommutingStrategy X' Y' A' B' 𝒜 where
  state := S.state
  alice x := (S.alice (questionAlice x)).map (answerAlice x)
  bob y := (S.bob (questionBob y)).map (answerBob y)
  commute x y :=
    Measurement.commute_map_map (S.alice (questionAlice x)) (S.bob (questionBob y))
      (S.commute (questionAlice x) (questionBob y)) (answerAlice x) (answerBob y)

/-- Postprocessed answer probabilities sum the original probabilities over the two
decoder fibers. -/
theorem prob_map {X' Y' A' B' : Type*} [Fintype A'] [Fintype B']
    [DecidableEq A'] [DecidableEq B'] (S : CommutingStrategy X Y A B 𝒜)
    (questionAlice : X' → X) (questionBob : Y' → Y)
    (answerAlice : X' → A → A') (answerBob : Y' → B → B') (x : X') (y : Y')
    (a : A') (b : B') :
    (S.map questionAlice questionBob answerAlice answerBob).prob x y a b =
      ∑ a' with answerAlice x a' = a, ∑ b' with answerBob y b' = b,
        S.prob (questionAlice x) (questionBob y) a' b' := by
  simp only [prob, map, Measurement.map_effect, sum_mul, mul_sum, map_sum, Complex.re_sum]
  exact sum_comm

/-- Checking decoded answers in the postprocessed strategy gives the same score as
checking them directly in the original joint distribution. -/
theorem sum_ite_prob_map {X' Y' A' B' : Type*} [Fintype A'] [Fintype B']
    [DecidableEq A'] [DecidableEq B'] (S : CommutingStrategy X Y A B 𝒜)
    (questionAlice : X' → X) (questionBob : Y' → Y)
    (answerAlice : X' → A → A') (answerBob : Y' → B → B') (x : X') (y : Y')
    (accepts : A' → B' → Prop) [∀ a b, Decidable (accepts a b)] :
    (∑ a, ∑ b, if accepts a b then
      (S.map questionAlice questionBob answerAlice answerBob).prob x y a b else 0) =
    ∑ a, ∑ b, if accepts (answerAlice x a) (answerBob y b) then
      S.prob (questionAlice x) (questionBob y) a b else 0 := by
  conv_rhs => rw [← sum_fiberwise univ (answerAlice x)]
  refine sum_congr rfl fun a _ => ?_
  simp_rw [← sum_fiberwise univ (answerBob y)]
  rw [sum_comm]
  refine sum_congr rfl fun b _ => ?_
  rw [prob_map]
  trans ∑ a' with answerAlice x a' = a, ∑ b' with answerBob y b' = b,
    if accepts a b then S.prob (questionAlice x) (questionBob y) a' b' else 0
  · split_ifs <;> simp
  exact sum_congr rfl fun a' ha => sum_congr rfl fun b' hb => by
    rw [(mem_filter.mp ha).2, (mem_filter.mp hb).2]

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

/-- The distribution of relabeled answers is the pushforward of the original
distribution at the corresponding questions. -/
theorem answers_relabel {X' Y' A' B' : Type*} [Fintype A'] [Fintype B']
    [IsOrderedAddMonoid 𝒜] (S : CommutingStrategy X Y A B 𝒜)
    (qx : X' → X) (qy : Y' → Y) (fa : A → A') (fb : B → B') (x : X') (y : Y') :
    (S.relabel qx qy fa fb).answers x y =
      (S.answers (qx x) (qy y)).map (Prod.map fa fb) := by
  classical
  ext ⟨a, b⟩
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [answers_apply, ENNReal.toReal_ofReal ((S.relabel qx qy fa fb).prob_nonneg x y a b),
    Cslib.Probability.PMF.map_apply_toReal, Fintype.sum_prod_type]
  simp only [relabel, prob, Measurement.map_effect, Finset.sum_mul, Finset.mul_sum, map_sum,
    Complex.re_sum, Finset.sum_filter, Prod.map_apply, Prod.mk.injEq]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun a' _ => sum_congr rfl fun b' _ => ?_
  rw [answers_apply, ENNReal.toReal_ofReal (S.prob_nonneg (qx x) (qy y) a' b')]
  by_cases ha : a = fa a' <;> by_cases hb : b = fb b' <;> simp_all [prob, eq_comm]

/-- Alice's answer marginal is her measurement law and is independent of Bob's question. -/
theorem answers_map_fst (S : CommutingStrategy X Y A B 𝒜) (x : X) (y : Y) :
    (S.answers x y).map Prod.fst = (S.alice x).distribution S.state := by
  classical
  ext a
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Measurement.distribution_apply,
    Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, S.answers_apply,
    ← ENNReal.ofReal_sum_of_nonneg fun b _ => S.prob_nonneg x y a b]
  simp only [prob, ← Complex.re_sum, ← map_sum, ← Finset.mul_sum, (S.bob y).sum_effect,
    mul_one, Measurement.prob]

/-- The successful mismatch of decoded measurements is the joint probability
that the first decoded answer succeeds and differs from the second. -/
theorem successfulMismatch_map_map_eq_event {C : Type*} [Fintype C] [DecidableEq C]
    [IsOrderedAddMonoid 𝒜] (S : CommutingStrategy X Y A B 𝒜) (x : X) (y : Y)
    (f : A → Option C) (g : B → C) :
    Measurement.successfulMismatch S.state ((S.alice x).map f) ((S.bob y).map g) =
      ((S.answers x y).toOuterMeasure {ab | ∃ c, f ab.1 = some c ∧ c ≠ g ab.2}).toReal := by
  classical
  rw [Measurement.successfulMismatch_map_map, Cslib.Probability.PMF.toOuterMeasure_apply_toReal,
    Fintype.sum_prod_type]
  simp only [Set.mem_ofPred_eq, answers_apply]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [ENNReal.toReal_ofReal (S.prob_nonneg x y a b)]
  rfl

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

omit [StarRing 𝒜] in
/-- The observables of a binary commuting strategy commute across players. -/
theorem commute_observable (S : CommutingStrategy X Y Bool Bool 𝒜) (x : X) (y : Y) :
    Commute (S.alice x).observable (S.bob y).observable := by
  exact ((S.commute x y false false).sub_right (S.commute x y false true)).sub_left
    ((S.commute x y true false).sub_right (S.commute x y true true))

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
  have h (γ : Bool) : ∑ r, (if γ = g r then S.prob x y γ r else 0) =
      (S.state ((S.alice x).effect γ * ((S.bob y).map g).effect γ)).re := by
    rw [Measurement.map_effect, mul_sum, map_sum, Complex.re_sum, sum_filter]
    exact sum_congr rfl fun r _ => by simp only [prob, eq_comm]
  simp only [h, Fintype.sum_bool]
  set s := (S.alice x).effect false
  set t := (S.alice x).effect true
  set u := ((S.bob y).map g).effect false
  set v := ((S.bob y).map g).effect true
  have hst : t = 1 - s :=
    eq_sub_of_add_eq (by simpa [Fintype.sum_bool] using (S.alice x).sum_effect)
  have huv : v = 1 - u :=
    eq_sub_of_add_eq (by simpa [Fintype.sum_bool] using ((S.bob y).map g).sum_effect)
  rw [Measurement.observable, Measurement.observable, ← Complex.add_re, ← map_add]
  change _ = (1 + (S.state ((s - t) * (u - v))).re) / 2
  have hring : 1 + (s - t) * (u - v) = (t * v + s * u) + (t * v + s * u) := by
    rw [hst, huv]
    noncomm_ring
  rw [show (1 : ℝ) = (S.state 1).re by rw [S.state.map_one, Complex.one_re],
    ← Complex.add_re, ← map_add, hring]
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
  have h5 := S.sum_prob false false
  have h6 := S.sum_prob false true
  have h7 := S.sum_prob true false
  have h8 := S.sum_prob true true
  simp only [Fintype.sum_bool] at h5 h6 h7 h8
  linarith [S.correlation_eq false false, S.correlation_eq false true,
    S.correlation_eq true false, S.correlation_eq true true]

variable [StarModule ℂ 𝒜] [SelfAdjointDecompose 𝒜]

/-- **Tsirelson's inequality** for commuting-operator strategies. -/
theorem _root_.Cslib.PCP.CommutingStrategy.chsh_correlation_le
    (S : CommutingStrategy X Y Bool Bool 𝒜) (x₀ x₁ : X) (y₀ y₁ : Y) :
    S.correlation x₀ y₀ + S.correlation x₀ y₁ + S.correlation x₁ y₀ - S.correlation x₁ y₁ ≤
      2 * √2 := by
  simpa only [CommutingStrategy.correlation, map_add, map_sub, Complex.add_re,
    Complex.sub_re] using S.state.re_chsh_le (S.alice x₀).isSelfAdjoint_observable
      (S.alice x₁).isSelfAdjoint_observable (S.alice x₀).star_observable_mul_self_le_one
      (S.alice x₁).star_observable_mul_self_le_one (S.bob y₀).star_observable_mul_self_le_one
      (S.bob y₁).star_observable_mul_self_le_one

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

/-- Any left tensor-factor effect commutes with any right tensor-factor effect. -/
theorem commute_liftedEffects (L : POVM A ι) (R : POVM B κ) (a : A) (b : B) :
    Commute ((leftMeasurement (κ := κ) L).effect a) ((rightMeasurement (ι := ι) R).effect b) := by
  change Commute (L.effect a ⊗ₖ (1 : Matrix κ κ ℂ)) ((1 : Matrix ι ι ℂ) ⊗ₖ R.effect b)
  simpa only [kroneckerOne_apply, oneKronecker_apply] using
    commute_kroneckerOne_oneKronecker (L.effect a) (R.effect b)

/-- A projective local measurement stays projective on the first tensor factor. -/
theorem leftMeasurement_isProjective (M : POVM A ι) (h : M.toMeasurement.IsProjective) :
    (leftMeasurement (κ := κ) M).IsProjective := by
  intro a
  change (M.effect a ⊗ₖ (1 : Matrix κ κ ℂ)) * (M.effect a ⊗ₖ 1) = M.effect a ⊗ₖ 1
  rw [← mul_kronecker_mul, Matrix.one_mul]
  exact congrArg (· ⊗ₖ (1 : Matrix κ κ ℂ)) (h a)

/-- A projective local measurement stays projective on the second tensor factor. -/
theorem rightMeasurement_isProjective (M : POVM B κ) (h : M.toMeasurement.IsProjective) :
    (rightMeasurement (ι := ι) M).IsProjective := by
  intro a
  change ((1 : Matrix ι ι ℂ) ⊗ₖ M.effect a) * (1 ⊗ₖ M.effect a) = 1 ⊗ₖ M.effect a
  rw [← mul_kronecker_mul, Matrix.one_mul]
  exact congrArg ((1 : Matrix ι ι ℂ) ⊗ₖ ·) (h a)

/-- A tensor-product strategy as a commuting-operator strategy on the matrix algebra of
`ℂ^ι ⊗ ℂ^κ`: the effects `E ⊗ 1` and `1 ⊗ F` and the vector state of the shared state. -/
noncomputable def toCommuting (S : QuantumStrategy X Y A B ι κ) :
    CommutingStrategy X Y A B (Matrix (ι × κ) (ι × κ) ℂ) where
  state := AlgState.vector S.state S.norm_state
  alice x := leftMeasurement (S.alice x)
  bob y := rightMeasurement (S.bob y)
  commute x y := commute_liftedEffects (S.alice x) (S.bob y)

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

/-- Swapping questions and answers preserves the correlations of a symmetric strategy. -/
theorem prob_toCommuting_swap_of_symmetric {Q C J : Type*}
    [Fintype C] [Fintype J] [DecidableEq J]
    (S : QuantumStrategy Q Q C C J J) (hM : S.bob = S.alice)
    (hψ : ∀ a b, S.state.ofLp (a, b) = S.state.ofLp (b, a))
    (x y : Q) (a b : C) :
    S.toCommuting.prob y x b a = S.toCommuting.prob x y a b := by
  rw [prob_toCommuting, prob_toCommuting]
  simp only [prob_eq, hM]
  exact congrArg Complex.re (AlgState.vector_kronecker_swap S.state S.norm_state hψ
    ((S.alice y).effect b) ((S.alice x).effect a))

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
  exact congrArg G.answersWinProb (funext fun x => funext (QuantumStrategy.answers_toCommuting S x))

/-- Exchanging the players of a symmetric tensor strategy preserves its score in
any game with the same question and answer alphabets on both sides. -/
theorem commutingWinProb_swap_of_symmetric {Q C J : Type*}
    [Fintype C] [Fintype J] [DecidableEq J]
    (G : TwoProverGame Q Q C C) (S : QuantumStrategy Q Q C C J J)
    (hM : S.bob = S.alice) (hψ : ∀ a b, S.state.ofLp (a, b) = S.state.ofLp (b, a)) :
    G.commutingWinProb S.toCommuting.swap = G.commutingWinProb S.toCommuting := by
  classical
  unfold commutingWinProb
  congr 1
  funext x y
  ext ⟨a, b⟩
  simp only [CommutingStrategy.answers_apply, CommutingStrategy.prob_swap,
    S.prob_toCommuting_swap_of_symmetric hM hψ x y a b]

end TwoProverGame

end Cslib.PCP
