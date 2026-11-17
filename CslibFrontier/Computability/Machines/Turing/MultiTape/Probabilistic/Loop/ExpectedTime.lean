/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Loop
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Composition.ExpectedTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Loop.Space
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map

/-!
# Loops that stop at random rounds

`Turing.MultiTapePTM.RunsWords.repeatUntilBlank` analyses `Turing.MultiTapePTM.repeatUntilBlank`
for a number of rounds fixed in advance, with a worst-case clock. A Las Vegas loop instead
repeats a randomized round until the round reports an answer, so the number of rounds is random
and unbounded. This file provides the round-by-round tail bounds for such loops, and the
geometric sum that turns per-round stopping probabilities into a bound on the expected running
time. They are applied to `Turing.MultiTapePTM.iterateWhile` in
`Turing.MultiTapePTM.tsum_toOuterMeasure_compl_iterateWhile_le`.

A round that halts early reaches the blank test early, which only lowers the probability of not
having halted (`Turing.MultiTapePTM.RunsWords.toOuterMeasure_compl_repeatUntilBlank_le`). The blank
test then halts on an empty word and restarts the body on any other word.

## Main results

* `Turing.MultiTapePTM.tsum_le_of_geometric`: geometric tails have a geometric sum.
* `Turing.MultiTapePTM.RunsWords.eval_runClosedConfigFrom`: the closed law of a `RunsWords` phase.
* `Turing.MultiTapePTM.RepeatUntilBlank.eval_runClosedConfigFrom_check_nil`,
  `Turing.MultiTapePTM.RepeatUntilBlank.eval_runClosedConfigFrom_check_ne_nil`: the blank test.
* `Turing.MultiTapePTM.RunsWords.toOuterMeasure_compl_repeatUntilBlank_le`: one round of
  `repeatUntilBlank`, followed by its blank test.
-/

public section

namespace Turing.MultiTapePTM

open Cslib Cslib.Probability MultiTapeMachine MultiTapeTM
open scoped ENNReal

variable {k : ℕ} {State : Type} {x : List Bool}

/-- **Geometric tails.** A sequence of probabilities that is at most `q ^ n` after `D + n * D`
steps sums to at most `D + D * (1 - q)⁻¹`. -/
theorem tsum_le_of_geometric {f : ℕ → ℝ≥0∞} {q : ℝ≥0∞} {D : ℕ} (hD : 0 < D) (hf : ∀ t, f t ≤ 1)
    (hgeom : ∀ n j, f (D + (n * D + j)) ≤ q ^ n) :
    ∑' t, f t ≤ D + D * (1 - q)⁻¹ := by
  have : NeZero D := ⟨hD.ne'⟩
  refine (tsum_le_add_of_shift (g := fun m => q ^ (m / D)) D hf fun m => ?_).trans_eq ?_
  · simpa only [Nat.div_add_mod'] using hgeom (m / D) (m % D)
  · congr 1
    have hdiv (n : ℕ) (j : Fin D) : (n * D + j) / D = n := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hD, Nat.div_eq_of_lt j.isLt, Nat.zero_add]
    rw [← (Nat.divModEquiv D).symm.tsum_eq]
    simp only [Nat.divModEquiv_symm_apply]
    rw [tsum_prod (f := fun n (j : Fin D) => q ^ ((n * D + j) / D))]
    simp only [hdiv, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-- A closed `RunsWords` phase whose program samples `p` has the configuration law of `p`. -/
theorem RunsWords.eval_runClosedConfigFrom {body : MultiTapePTM k Bool State}
    {ws₀ : Fin k → List Bool} {out₀ : List Bool} {t : ℕ} {α : Type} {p : ProbComp α}
    {ws₁ : α → Fin k → List Bool} {emit : α → List Bool}
    (h : body.RunsWords x ws₀ out₀ t (ProbOracleComp.sample p) ws₁ emit)
    (cfg : Config k Bool State Empty x)
    (hcfg : cfg.tapes = wordsCfg x (some body.initial) ws₀ out₀) :
    ProbComp.eval (body.runClosedConfigFrom t cfg) =
      (ProbComp.eval p).map fun a =>
        { tapes := wordsCfg x none (ws₁ a) (out₀ ++ emit a), channels := Empty.elim } := by
  have hlaw := (h Unit (fun q => q.1.elim) () cfg hcfg (fun op => op.elim)).1
  rw [runOracleConfigFrom_empty, ProbOracleComp.runWith_sample, ProbOracleComp.runWith_sample,
    PMF.map_comp, PMF.map_comp] at hlaw
  have hmk := congrArg (PMF.map fun pr : Cfg k Bool State x × Unit =>
    ({ tapes := pr.1, channels := Empty.elim } : Config k Bool State Empty x)) hlaw
  rw [PMF.map_comp, PMF.map_comp] at hmk
  refine Eq.trans ?_ hmk
  conv_lhs => rw [← PMF.map_id (ProbComp.eval (body.runClosedConfigFrom t cfg))]
  exact Cslib.Probability.PMF.map_congr_on_support _ _ _ fun c _ =>
    Config.ext rfl (Subsingleton.elim _ _)

/-- A step that ignores its coin has a point-mass distribution. -/
theorem eval_runClosedConfigFrom_one_of_step_eq {Symbol : Type} {input : List Symbol}
    (machine : MultiTapePTM k Symbol State) (c c' : Config k Symbol State Empty input)
    (h : ∀ bit, (machine.withCoin bit).step c = c') :
    ProbComp.eval (machine.runClosedConfigFrom 1 c) = PMF.pure c' := by
  rw [eval_runClosedConfigFrom_one, funext h]
  exact PMF.map_const _ c'

namespace RepeatUntilBlank

variable (i : Fin k) (body : MultiTapePTM k Bool State)

/-- The blank test on an empty word halts in one step. -/
theorem eval_runClosedConfigFrom_check_nil {ws : Fin k → List Bool} {out : List Bool}
    (hi : ws i = []) (t : ℕ) :
    ProbComp.eval ((MultiTapePTM.repeatUntilBlank i body).runClosedConfigFrom (1 + t)
      { tapes := wordsCfg x (some (.inr ())) ws out, channels := Empty.elim }) =
      PMF.pure { tapes := wordsCfg x none ws out, channels := Empty.elim } := by
  rw [eval_runClosedConfigFrom_add, eval_runClosedConfigFrom_one_of_step_eq _ _ _
      fun bit => step_withCoin_repeatUntilBlank_check_nil i body bit ws out hi _ rfl,
    PMF.pure_bind, eval_runClosedConfigFrom_of_halted _ _ _ rfl]

/-- The blank test on a non-empty word restarts the body in one step. -/
theorem eval_runClosedConfigFrom_check_ne_nil {ws : Fin k → List Bool} {out : List Bool}
    (hi : ws i ≠ []) (t : ℕ) :
    ProbComp.eval ((MultiTapePTM.repeatUntilBlank i body).runClosedConfigFrom (1 + t)
      { tapes := wordsCfg x (some (.inr ())) ws out, channels := Empty.elim }) =
      ProbComp.eval ((MultiTapePTM.repeatUntilBlank i body).runClosedConfigFrom t
        (runConfig
          { tapes := wordsCfg x (some body.initial) ws out, channels := Empty.elim })) := by
  rw [eval_runClosedConfigFrom_add, eval_runClosedConfigFrom_one_of_step_eq _ _ _
      fun bit => step_withCoin_repeatUntilBlank_check_ne_nil i body bit ws out hi _ rfl,
    PMF.pure_bind]

end RepeatUntilBlank

open RepeatUntilBlank in
/-- **One round of `repeatUntilBlank`.** If a round of `body` from the words `ws₀` realizes the
sampled program `p` within `t` steps, then after `t + (1 + rest)` steps the loop misses `good` at
most as often as the blank test on the round's result, run for `1 + rest` steps. -/
theorem RunsWords.toOuterMeasure_compl_repeatUntilBlank_le (i : Fin k)
    {body : MultiTapePTM k Bool State} {ws₀ : Fin k → List Bool} {out₀ : List Bool} {t : ℕ}
    {α : Type} {p : ProbComp α} {ws₁ : α → Fin k → List Bool} {emit : α → List Bool}
    (h : body.RunsWords x ws₀ out₀ t (ProbOracleComp.sample p) ws₁ emit)
    {good : Set (Config k Bool (State ⊕ Unit) Empty x)} (hgood : ∀ c ∈ good, c.tapes.state = none)
    (rest : ℕ) :
    (ProbComp.eval ((MultiTapePTM.repeatUntilBlank i body).runClosedConfigFrom (t + (1 + rest))
      (runConfig ⟨wordsCfg x (some body.initial) ws₀ out₀, Empty.elim⟩))).toOuterMeasure goodᶜ ≤
      ((ProbComp.eval p).bind fun a =>
        ProbComp.eval ((MultiTapePTM.repeatUntilBlank i body).runClosedConfigFrom (1 + rest)
          { tapes := wordsCfg x (some (.inr ())) (ws₁ a) (out₀ ++ emit a),
            channels := Empty.elim })).toOuterMeasure goodᶜ := by
  refine (toOuterMeasure_compl_add_le_bind (MultiTapePTM.repeatUntilBlank i body) runConfig
    (fun c hc => eval_runClosedConfigFrom_one_of_step _ _ c fun bit =>
      step_withCoin_repeatUntilBlank_live i body bit c hc) hgood t (1 + rest) _).trans_eq ?_
  rw [h.eval_runClosedConfigFrom _ rfl, PMF.bind_map]
  congr 2 with a : 1

end Turing.MultiTapePTM
