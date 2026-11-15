/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.DiffieHellman.SelfReduction.Family
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Tactic.PPT

/-!
# The DL and CDH self-reductions over a prime-order group family: checked instances

Clients of `CslibFrontier/Crypto/Computational/DiffieHellman/SelfReduction/Family.lean` under
module encapsulation, with ordinary imports. They apply its results, generically in the family `F`
and the group `d`, to the word-level adversary that always guesses the exponent `0`, which wins the
discrete-logarithm game in a group of order `q` with probability `1 / q`.

* The masked call, the checked loop with `n * (2 * q)` attempts and the CDH reduction of the
  derived CDH adversary are uniform strict PPT.
* One checked attempt of the masked guess finds every exponent `α` with probability at least
  `1 / q - 1 / 2 ^ n`, although the guess itself is right on the instance `0` only.
* With `invEps = q`, the hypotheses of `negligible_dlSelfReduceRetryAdversary_error` hold, so the
  loop finds the discrete logarithm of every instance sequence in a fixed group with negligible
  error.
* The loop outputs the empty word or a discrete logarithm, and the empty word on every word that
  encodes no group element.
* In a fixed group the masked guess wins the worst-case game within `1 / 2 ^ n` of `1 / q`, so the
  worst-case hypotheses of `discreteLog_of_worstCase` and `cdh_of_worstCase` fail there, as the
  assumptions they imply do.

`guessZero` and its two facts are private copies of the fixture in
`CslibFrontierTests/Crypto/AssumptionNonvacuity.lean`, which is not a `module` file and so cannot
be imported here.
-/

public section

namespace CslibFrontierTests.Crypto.DiffieHellmanSelfReductionFamily

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.PrimeOrderGroupFamily Turing.MultiTapeTM
open scoped NNReal ENNReal

variable (F : PrimeOrderGroupFamily) (d : F.Desc)

/-! ### The adversary that always guesses `0` -/

/-- Always guess the exponent `0`. -/
private noncomputable def guessZero : ℕ → F.Desc × List Bool → ProbComp (List Bool) :=
  fun _ _ => pure []

/-- Guessing `0` is uniform strict PPT: it is a constant. -/
private theorem guessZero_isPPT :
    IsPPTOn F.encDiscreteLogInput encBits
      (fun input => guessZero F input.1 input.2) :=
  (ComputableInPolyTime.const _).isPPTOn

/-- Guessing `0` against a fixed group of order `q` succeeds with probability exactly `1 / q`. -/
private theorem succProbability_discreteLogGame_guessZero (n : ℕ) :
    Game.succProbability (F.discreteLogGame (fun _ => PMF.pure d) (guessZero F) n) =
      (F.order d : ℝ≥0)⁻¹ := by
  have h := PMF.uniformOfFintype_bind_decide_eq_apply_true (0 : ZMod (F.order d))
  rw [ZMod.card] at h
  simp only [discreteLogGame, guessZero, ProbComp.eval_pure, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.pure_bind] at h ⊢
  simp only [ofBits, List.foldr_nil, Nat.cast_zero]
  rw [Game.succProbability, h, ENNReal.toNNReal_inv, ENNReal.toNNReal_natCast]

/-! ### Certificates -/

/-- The masked call of guessing `0` is uniform strict PPT. -/
example : IsPPTOn F.encDiscreteLogInput encBits
    (fun input => F.dlSelfReduceAdversary (guessZero F) input.1 input.2) :=
  F.isPPTOn_dlSelfReduceAdversary (guessZero_isPPT F)

/-- The loop with `n * (2 * q)` attempts of the masked guess is uniform strict PPT. -/
example : IsPPTOn F.encDiscreteLogInput encBits
    (fun input => F.dlSelfReduceRetryAdversary (guessZero F) (fun n => n * (2 * F.order d))
      input.1 input.2) :=
  F.isPPTOn_dlSelfReduceRetryAdversary_invEps (guessZero_isPPT F) (invEps := fun _ => F.order d)
    (by fun_prop)

/-- The CDH reduction of the CDH adversary derived from guessing `0` is uniform strict PPT. -/
example : (F.cdhSelfReduceAdversary (F.dlToCDHAdversary (guessZero F))).IsPPT :=
  F.isPPT_cdhSelfReduceAdversary (F.isPPT_dlToCDHAdversary (guessZero_isPPT F))

/-! ### Every instance -/

/-- One checked attempt of the masked guess finds every `α` with probability at least
`1 / q - 1 / 2 ^ n`, although guessing `0` is right on one instance only. -/
example (n : ℕ) (α : ZMod (F.order d)) :
    (((F.order d : ℝ≥0)⁻¹ - 1 / 2 ^ n : ℝ≥0) : ℝ≥0∞) ≤
      ProbComp.eval (F.discreteLogAdversary (F.dlSelfReduceRetryAdversary (guessZero F) fun _ => 1)
        n d (α • F.generator d)) α := by
  have h := F.le_eval_discreteLogAdversary_dlSelfReduceRetryAdversary_one (guessZero F) n d α
  rwa [← F.succProbability_discreteLogGame_pure, succProbability_discreteLogGame_guessZero] at h

/-- The hypotheses of `negligible_dlSelfReduceRetryAdversary_error` hold for guessing `0` with
`invEps = q`: the loop is a random search that errs with negligible probability on every sequence
of instances in a fixed group. -/
example (α : ℕ → ZMod (F.order d)) :
    Negligible fun n =>
      ((ProbComp.eval (F.discreteLogAdversary
        (F.dlSelfReduceRetryAdversary (guessZero F) fun n => n * (2 * F.order d)) n d
        (α n • F.generator d))).toOuterMeasure {x | x ≠ α n}).toNNReal :=
  F.negligible_dlSelfReduceRetryAdversary_error (adversary := guessZero F)
    (invEps := fun _ => F.order d) (by fun_prop) (fun _ => d) α
    (Filter.Eventually.of_forall fun _ => (F.prime_order d).pos)
    (Filter.Eventually.of_forall fun n => by
      rw [succProbability_discreteLogGame_guessZero]
      simp)

/-- The loop of the masked guess outputs the empty word or a discrete logarithm of its input. -/
example {k : ℕ → ℕ} {n : ℕ} {u : F.Carrier d} {out : List Bool}
    (hout : out ∈ (ProbComp.eval
      (F.dlSelfReduceRetryAdversary (guessZero F) k n (d, F.encode d u))).support) :
    out = [] ∨ (ofBits out : ZMod (F.order d)) • F.generator d = u :=
  F.eq_nil_or_smul_eq_of_mem_support_dlSelfReduceRetryAdversary hout

/-- On a word that encodes no element, the loop outputs the empty word. -/
example {k : ℕ → ℕ} {n : ℕ} {w out : List Bool} (hw : w ∉ Set.range (F.encode d))
    (hout : out ∈ (ProbComp.eval (F.dlSelfReduceRetryAdversary (guessZero F) k n (d, w))).support) :
    out = [] :=
  F.eq_nil_of_mem_support_dlSelfReduceRetryAdversary_of_not_mem_range hw hout

/-! ### Worst case in a fixed group -/

/-- In a fixed group, the masked guess wins the worst-case game on any instances within
`1 / 2 ^ n` of `1 / q`. -/
example (α : ∀ d : F.Desc, ZMod (F.order d)) (n : ℕ) :
    (F.order d : ℝ≥0)⁻¹ ≤
      Game.succProbability (F.dlWorstCaseGame (fun _ => PMF.pure d) α
        (F.dlSelfReduceAdversary (guessZero F)) n) + 1 / 2 ^ n := by
  rw [← succProbability_discreteLogGame_guessZero F d n]
  exact F.succProbability_discreteLogGame_le_dlWorstCaseGame _ α _ n

/-- The worst-case hypothesis of `discreteLog_of_worstCase` fails for a fixed group, as
`DiscreteLog` does: some PPT adversary wins the worst-case game with non-negligible
probability. -/
theorem not_dlWorstCase_const (α : ∀ d : F.Desc, ZMod (F.order d)) :
    ¬ ∀ adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool),
      IsPPTOn F.encDiscreteLogInput encBits
        (fun input => adversary input.1 input.2) →
      Negligible fun n =>
        Game.succProbability (F.dlWorstCaseGame (fun _ => PMF.pure d) α adversary n) := by
  intro hworst
  have hneg := F.discreteLog_of_worstCase α hworst (guessZero F) (guessZero_isPPT F)
  simp only [succProbability_discreteLogGame_guessZero] at hneg
  exact not_negligible_const (inv_ne_zero (Nat.cast_ne_zero.mpr (F.prime_order d).ne_zero)) hneg

/-- The worst-case hypothesis of `cdh_of_worstCase` fails for a fixed group, as `CDH` does. -/
theorem not_cdhWorstCase_const (α β : ∀ d : F.Desc, ZMod (F.order d)) :
    ¬ ∀ adversary : F.CDHAdversary, adversary.IsPPT →
      Negligible fun n =>
        Game.succProbability (F.cdhWorstCaseGame (fun _ => PMF.pure d) α β adversary n) := by
  intro hworst
  have hneg := (F.cdh_of_worstCase α β hworst).discreteLog (guessZero F) (guessZero_isPPT F)
  simp only [succProbability_discreteLogGame_guessZero] at hneg
  exact not_negligible_const (inv_ne_zero (Nat.cast_ne_zero.mpr (F.prime_order d).ne_zero)) hneg

end CslibFrontierTests.Crypto.DiffieHellmanSelfReductionFamily
