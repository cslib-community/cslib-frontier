/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.BitString
public import CslibFrontier.Crypto.Computational.KeyDerivation
public import CslibFrontier.Languages.Probabilistic.Oracle.RunState
public import CslibFrontier.Probability.Entropy.Guessing
public import Mathlib.Data.Fin.Tuple.Take
public import Mathlib.Data.List.GetD
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.UntilBad.Flag
import CslibFrontier.Probability.Guessing.Leakage
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.DensityBounds
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.UniformIndex
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Tactic.PMFSwap
import CslibFrontier.Tactic.SuppCases

/-!
# Guessing advantage and key derivation in the random-oracle model

Formalizes [BonehShoup2023], Section 8.10.1 (Attack Game 8.3 and its first and third motivating
examples, pp. 325–326, together with the independent uniform-component case matching Attack Game
11.3 in Section 11.5.2, pp. 448–449) and Section 8.10.2 (the list-guessing game, the
list-to-singleton reduction, and the two advantage bounds and list-length bound of Theorem 8.10 on
pp. 331–332 for wrappers `roToListGuess` and `roToGuess` that sample the whole oracle table
`S → T` eagerly; the elementary lazy-simulation wrapper remains open), built on top of
`Cslib.Crypto.KeyDerivation.realOutput` and `idealOutput`.

## Relation to `CslibFrontier/Probability/Entropy/Guessing.lean`

`CslibFrontier.Probability.Entropy.Guessing` defines the deterministic maximum a posteriori
estimator `Cslib.Probability.PMF.maxPosteriorGuess` for a joint distribution `joint : PMF (β × α)`
whose observation comes first, and proves `errorProb_maxPosteriorGuess_le` among deterministic
estimators `g : β → α` when `β` and `α` are finite. Here `guessAdvantage sample info A` measures
the success probability of an arbitrary randomized adversary `A : X → ProbComp S` trying to guess
`s ← sample` from `info s`. Taking `joint := sample.map fun s => (info s, s)`,
`guessAdvantage_le_pure_maxPosteriorGuess` and
`guessAdvantage_le_one_sub_errorProb_maxPosteriorGuess` show that `maxPosteriorGuess joint` also
achieves the maximum `guessAdvantage` among all randomized adversaries whenever `S` is finite and
nonempty (with no finiteness assumption on `X`).

## Differences from the printed book

1. **General `sample : PMF S` and `info : S → X`.** Attack Game 8.3 (p. 326) takes a probability
   distribution `P` on a finite set `S` and a function `I` on `S`. `guessOutput`,
   `listGuessOutput`, and the reductions work for arbitrary `S` and `X` where finiteness is not
   needed (for example, `guessOutput_apply_true` and `listGuessAdvantage_le_mul_guessAdvantage`).
2. **Eager finite random oracle `uniformOfFintype (S → T)`.** Following
   `CslibFrontier/Crypto/Primitives/PRF/RandomOracleModel.lean`, `roRealOutput` and
   `roIdealOutput` sample the entire oracle `table : S → T` eagerly for finite nonempty `S` and
   `T`, and `RODistinguisher X S T := X → T → ProbOracleComp (fun _ : S => T) Bool` uses
   `ProbOracleComp` with `D.IsOracleQueryBounded Q` counting oracle queries on every execution
   path. The proof of `roAdvantage_le_listGuessAdvantage` rewrites `roRealOutput` with
   `PMF.bind_uniformOfFintype_update` and applies `ProbOracleComp.IdenticalUntilBad` instead of
   the book's lazy associative array.
3. **Random-index tie-breaking with `List.getD`.** `listGuessToGuess Q B` hardcodes a uniform
   index draw below `Q` (`Fin.val <$> ProbComp.unifFin (Q - 1)`) and defaults to
   `Classical.arbitrary S` past the end of `B`'s list, holding for every `Q : ℕ` including
   `Q = 0` (unlike `ListCDH.listCDHToCDH`, which takes the index sampler as an argument so
   `listCDHToCDHAdversary` can carry an efficiency certificate; an efficient wrapper will likewise
   need a parameterized or binary-width sampler).
4. **Information-theoretic asymptotic bound over query budgets; honest milestone scope.**
   The book's Theorem 8.10 states that `B` and `B'` are elementary wrappers around `D`. Here
   `roToListGuess` and `roToGuess` sample the whole oracle table `S → T` eagerly in `ProbComp`,
   which is not polynomial time when `S` is exponential, so the theorem's elementary-wrapper
   claim remains open. Accordingly, `negligible_roAdvantage_of_negligible_guessAdvantage` takes
   `PolynomiallyBounded Q`, `(D n).IsOracleQueryBounded (Q n)`, and a guessing assumption
   `∀ A, Negligible …` ranging over all guessers with no efficiency bound, covering
   information-theoretically unpredictable sources (including Attack Game 11.3 in §11.5.2,
   pp. 448–449); applying a computational guessing assumption (such as the fourth example of
   §8.10.1, p. 326, or CDH in Theorem 11.4 of §11.5.1, p. 446) requires an efficient
   lazy-simulation wrapper with a polynomial-time certificate, which remains open.

## Main definitions

* `Cslib.Crypto.KeyDerivation.GuessAdversary`, `guessOutput`, `guessAdvantage`: Attack Game 8.3
  and `Guessadv[A, sample, info]`.
* `Cslib.Crypto.KeyDerivation.ListGuessAdversary`, `listGuessOutput`, `listGuessAdvantage`,
  `listGuessToGuess`: the list-guessing game, `ListGuessadv[B, sample, info]`, and the
  list-to-singleton wrapper.
* `Cslib.Crypto.KeyDerivation.RODistinguisher`, `RODistinguisher.IsOracleQueryBounded`,
  `roRealOutput`, `roIdealOutput`, `roAdvantage`: key derivation in the random-oracle model and
  `Dist^{ro}adv[D, sample, info]`.
* `Cslib.Crypto.KeyDerivation.roToListGuess`, `roToGuess`: the list-guessing and
  singleton-guessing wrappers of Theorem 8.10 (with eager table sampling).

## Main results

* `Cslib.Crypto.KeyDerivation.guessAdvantage_le_pure_maxPosteriorGuess`,
  `guessAdvantage_le_one_sub_errorProb_maxPosteriorGuess`: `maxPosteriorGuess` is optimal even
  over randomized `GuessAdversary` instances.
* `Cslib.Crypto.KeyDerivation.guessAdvantage_le_card_mul_of_mass_le`,
  `guessAdvantage_uniformOfFintype_const`, `guessAdvantage_bind_uniformOfFintype_fst_le`,
  `guessAdvantage_uniformOfFintype_take_le`: guessing bounds for the §8.10.1 examples and Attack
  Game 11.3.
* `Cslib.Crypto.KeyDerivation.listGuessAdvantage_le_mul_guessAdvantage`: list-to-singleton guessing
  reduction.
* `Cslib.Crypto.KeyDerivation.length_le_of_mem_support_roToListGuess`,
  `roAdvantage_le_listGuessAdvantage`, `roAdvantage_le_mul_guessAdvantage`,
  `negligible_roAdvantage_of_negligible_guessAdvantage`: the output-size, list-guessing,
  singleton-guessing, and asymptotic bounds of Theorem 8.10 for wrappers that sample the whole
  oracle table eagerly (the elementary lazy-simulation wrapper remains open).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 8.10.1 (Attack Game 8.3 and motivating examples, pp. 325–326), Section 8.10.2
  (Theorem 8.10, pp. 331–332), Section 11.5.1 (Theorem 11.4, p. 446, for the open CDH
  application), and Section 11.5.2 (Attack Game 11.3, pp. 448–449).
-/

public section

open Cslib Probability
open Cslib.Probability.PMF (uniformOfFintype)
open scoped ENNReal NNReal BigOperators

namespace Cslib.Crypto.KeyDerivation

variable {S X Y T : Type}

/-! ### 1. Attack Game 8.3: Guessing advantage and the examples of §8.10.1 -/

/-- A guessing adversary in Attack Game 8.3 ([BonehShoup2023], §8.10.1, p. 326): given the leaked
side information `info s : X`, it outputs a candidate secret in `S`. -/
abbrev GuessAdversary (X S : Type) : Type := X → ProbComp S

/-- Attack Game 8.3 ([BonehShoup2023], §8.10.1, p. 326): the challenger draws `s ← sample`, sends
`info s` to `A`, and `A` wins when its output equals `s`. -/
@[expose] noncomputable def guessOutput [DecidableEq S] (sample : PMF S) (info : S → X)
    (A : GuessAdversary X S) : Game :=
  sample.bind fun s => (ProbComp.eval (A (info s))).bind fun s' => PMF.pure (decide (s' = s))

/-- `Guessadv[A, sample, info]` ([BonehShoup2023], Attack Game 8.3, p. 326): the probability that
`A` guesses `s` given `info s`. -/
@[expose] noncomputable def guessAdvantage [DecidableEq S] (sample : PMF S) (info : S → X)
    (A : GuessAdversary X S) : ℝ≥0 :=
  Game.succProbability (guessOutput sample info A)

/-- The winning probability in `guessOutput` is
`∑' s, sample s * (ProbComp.eval (A (info s))) s`. -/
theorem guessOutput_apply_true [DecidableEq S] (sample : PMF S) (info : S → X)
    (A : GuessAdversary X S) :
    guessOutput sample info A true = ∑' s, sample s * ProbComp.eval (A (info s)) s := by
  unfold guessOutput
  rw [PMF.bind_apply]
  refine tsum_congr fun s => by rw [Probability.PMF.bind_pure_decide_eq_apply_true']

/-- For any deterministic guessing function `g : X → S`, its success probability in `guessOutput`
equals the probability of `{z | g z.1 = z.2}` under the joint law of `(info s, s)`. -/
theorem guessOutput_pure_apply_true [DecidableEq S] (sample : PMF S) (info : S → X)
    (g : X → S) :
    guessOutput sample info (fun x => pure (g x)) true =
      (sample.map fun s => (info s, s)).toOuterMeasure {z | g z.1 = z.2} := by
  classical
  rw [guessOutput_apply_true, PMF.toOuterMeasure_map_apply,
    Probability.PMF.toOuterMeasure_eq_tsum_mul_indicator]
  refine tsum_congr fun s => ?_
  by_cases hs : g (info s) = s
  · simp [hs]
  · simp [hs, Ne.symm hs]

/-- The maximum a posteriori estimator `Cslib.Probability.PMF.maxPosteriorGuess` of the joint
distribution of `(info s, s)` maximizes `guessAdvantage` among all randomized guessing
adversaries. -/
theorem guessAdvantage_le_pure_maxPosteriorGuess [Fintype S] [DecidableEq S] [Nonempty S]
    (sample : PMF S) (info : S → X) (A : GuessAdversary X S) :
    guessAdvantage sample info A ≤
      guessAdvantage sample info (fun x =>
        pure (Probability.PMF.maxPosteriorGuess (sample.map fun s => (info s, s)) x)) := by
  unfold guessAdvantage Game.succProbability
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) ?_
  set joint : PMF (X × S) := sample.map fun s => (info s, s)
  have hrew (B : GuessAdversary X S) :
      guessOutput sample info B =
        (joint.map Prod.fst).bind fun x =>
          (Probability.PMF.conditionalSnd joint x).bind fun s =>
            (ProbComp.eval (B x)).bind fun s' => PMF.pure (decide (s' = s)) := by
    have h1 : guessOutput sample info B =
        joint.bind fun z =>
          (ProbComp.eval (B z.1)).bind fun s' => PMF.pure (decide (s' = z.2)) := by
      simp only [pmf_norm, joint, guessOutput]
    rw [h1]
    conv_lhs => rw [← Probability.PMF.bind_conditionalSnd joint]
    simp only [pmf_norm]
  rw [hrew A, hrew (fun x => pure (Probability.PMF.maxPosteriorGuess joint x))]
  refine Probability.PMF.bind_apply_mono_on_support _ true fun x _ => ?_
  pmf_hoist (ProbComp.eval (A x))
  refine Probability.PMF.bind_apply_le_on_support _ fun s' _ => ?_
  rw [Probability.PMF.bind_pure_decide_eq_apply_true]
  have hrhs :
      ((Probability.PMF.conditionalSnd joint x).bind fun s =>
        (ProbComp.eval (pure (Probability.PMF.maxPosteriorGuess joint x))).bind fun s'' =>
          PMF.pure (decide (s'' = s))) true =
        Probability.PMF.conditionalSnd joint x (Probability.PMF.maxPosteriorGuess joint x) := by
    simp
  rw [hrhs]
  exact Probability.PMF.conditionalSnd_le_conditionalSnd_maxPosteriorGuess joint x s'

/-- Every randomized guessing adversary in Attack Game 8.3 has advantage at most one minus the
error probability of `Cslib.Probability.PMF.maxPosteriorGuess` on `(info s, s)`. -/
theorem guessAdvantage_le_one_sub_errorProb_maxPosteriorGuess [Fintype S] [DecidableEq S]
    [Nonempty S] (sample : PMF S) (info : S → X) (A : GuessAdversary X S) :
    (guessAdvantage sample info A : ℝ) ≤
      1 - ((sample.map fun s => (info s, s)).toOuterMeasure
        {z | Probability.PMF.maxPosteriorGuess (sample.map fun s => (info s, s)) z.1 ≠
          z.2}).toReal := by
  refine (NNReal.coe_le_coe.mpr (guessAdvantage_le_pure_maxPosteriorGuess sample info A)).trans ?_
  set joint : PMF (X × S) := sample.map fun s => (info s, s)
  rw [guessAdvantage, Game.coe_succProbability, guessOutput_pure_apply_true]
  have hcompl :
      {z : X × S | Probability.PMF.maxPosteriorGuess joint z.1 = z.2}ᶜ =
        {z : X × S | Probability.PMF.maxPosteriorGuess joint z.1 ≠ z.2} := by
    ext z
    simp
  have hadd := Probability.PMF.toOuterMeasure_toReal_add_compl joint
    {z : X × S | Probability.PMF.maxPosteriorGuess joint z.1 = z.2}
  rw [hcompl] at hadd
  linarith

/-- If every secret has probability at most `mass` and `info` takes values in a finite type `X`,
every guessing adversary has advantage at most `|X| * mass`. -/
theorem guessAdvantage_le_card_mul_of_mass_le [DecidableEq S] [Fintype X] (sample : PMF S)
    (info : S → X) {mass : ℝ≥0} (hmass : ∀ s, sample s ≤ mass) (A : GuessAdversary X S) :
    guessAdvantage sample info A ≤ Fintype.card X * mass := by
  unfold guessAdvantage Game.succProbability
  refine (ENNReal.toNNReal_mono (b := (Fintype.card X : ℝ≥0∞) * mass)
    (by finiteness) ?_).trans_eq (by simp)
  rw [guessOutput_apply_true]
  simpa using Probability.PMF.tsum_mul_apply_le_card_mul sample hmass info Finset.univ
    (fun _ => Finset.mem_univ _) (fun x => ProbComp.eval (A x))

/-- **§8.10.1, first example** ([BonehShoup2023], pp. 325–326): when the secret is uniformly
distributed over a nonempty finite dictionary `S` and `info` is constant (no side information),
every adversary has guessing advantage `(Fintype.card S)⁻¹`. -/
theorem guessAdvantage_uniformOfFintype_const [Fintype S] [DecidableEq S] [Nonempty S]
    (x₀ : X) (A : GuessAdversary X S) :
    guessAdvantage (uniformOfFintype S) (fun _ => x₀) A = (Fintype.card S : ℝ≥0)⁻¹ := by
  unfold guessAdvantage Game.succProbability
  have htrue : guessOutput (uniformOfFintype S) (fun _ => x₀) A true =
      (Fintype.card S : ℝ≥0∞)⁻¹ := by
    rw [guessOutput_apply_true]
    simp only [PMF.uniformOfFintype_apply, ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
  rw [htrue, ENNReal.toNNReal_inv, ENNReal.toNNReal_natCast]

/-- When the secret is a pair `(x, y)` whose second component is drawn uniformly from `Y`
independently of the leaked first component `x` ([BonehShoup2023], Attack Game 11.3 in §11.5.2,
pp. 448–449), every adversary has guessing advantage at most `(Fintype.card Y)⁻¹`. -/
theorem guessAdvantage_bind_uniformOfFintype_fst_le [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [Nonempty Y] (p : PMF X) (A : GuessAdversary X (X × Y)) :
    guessAdvantage (p.bind fun x => (uniformOfFintype Y).map (x, ·)) Prod.fst A ≤
      (Fintype.card Y : ℝ≥0)⁻¹ := by
  unfold guessAdvantage Game.succProbability
  rw [← ENNReal.toNNReal_natCast, ← ENNReal.toNNReal_inv]
  refine ENNReal.toNNReal_mono (by finiteness) ?_
  simp only [pmf_norm, guessOutput]
  refine Probability.PMF.bind_apply_le_on_support p fun x _ => ?_
  pmf_hoist (ProbComp.eval (A x))
  refine Probability.PMF.bind_apply_le_on_support _ fun s' _ => ?_
  exact Probability.PMF.uniformOfFintype_bind_pure_apply_true_le fun y₁ hy₁ y₂ hy₂ =>
    (Prod.mk.inj ((of_decide_eq_true hy₁).symm.trans (of_decide_eq_true hy₂))).2

/-- **§8.10.1, third example** ([BonehShoup2023], pp. 325–326): when the secret is a uniformly
distributed `BitString (k + m)` and `info` leaks the first `k` bits
(`Fin.take k (Nat.le_add_right k m)`), every adversary has guessing advantage at most `1 / 2 ^ m`
(for `k = 64, m = 64`, at most `1 / 2 ^ 64`). -/
theorem guessAdvantage_uniformOfFintype_take_le (k m : ℕ)
    (A : GuessAdversary (BitString k) (BitString (k + m))) :
    guessAdvantage (uniformOfFintype (BitString (k + m)))
      (Fin.take k (Nat.le_add_right k m)) A ≤ 1 / 2 ^ m := by
  let e : BitString k × BitString m ≃ BitString (k + m) := Fin.appendEquiv k m
  have htake (p : BitString k × BitString m) :
      Fin.take k (Nat.le_add_right k m) (e p) = p.1 := by
    ext i
    simp [e, Fin.appendEquiv, Fin.take_apply]
  have heq :
      guessAdvantage (uniformOfFintype (BitString (k + m)))
        (Fin.take k (Nat.le_add_right k m)) A =
      guessAdvantage ((uniformOfFintype (BitString k)).bind fun x =>
        (uniformOfFintype (BitString m)).map (x, ·)) Prod.fst
        (fun x => e.symm <$> A x) := by
    unfold guessAdvantage
    congr 1
    rw [Probability.PMF.uniformOfFintype_prod, ← Probability.PMF.uniformOfFintype_map_equiv e]
    simp only [pmf_norm, guessOutput, htake]
    pmf_swap with p s'
    exact congrArg PMF.pure (decide_eq_decide.mpr e.symm_apply_eq.symm)
  rw [heq]
  have h := guessAdvantage_bind_uniformOfFintype_fst_le (uniformOfFintype (BitString k))
    (fun x => e.symm <$> A x)
  simpa [BitString, one_div] using h

/-! ### 2. List guessing game and list-to-singleton reduction (§8.10.2, p. 331) -/

/-- A list-guessing adversary ([BonehShoup2023], §8.10.2, p. 331): given `info s : X`, it outputs a
list of candidate secrets in `S`. -/
abbrev ListGuessAdversary (X S : Type) : Type := X → ProbComp (List S)

/-- The list-guessing game ([BonehShoup2023], §8.10.2, p. 331): the challenger draws `s ← sample`,
sends `info s` to `B`, and `B` wins when `s` is a member of its output list. -/
@[expose] noncomputable def listGuessOutput [DecidableEq S] (sample : PMF S) (info : S → X)
    (B : ListGuessAdversary X S) : Game :=
  sample.bind fun s => (ProbComp.eval (B (info s))).bind fun l => PMF.pure (decide (s ∈ l))

/-- `ListGuessadv[B, sample, info]` ([BonehShoup2023], §8.10.2, p. 331): the probability that the
secret `s` lies in the list output by `B (info s)`. -/
@[expose] noncomputable def listGuessAdvantage [DecidableEq S] (sample : PMF S) (info : S → X)
    (B : ListGuessAdversary X S) : ℝ≥0 :=
  Game.succProbability (listGuessOutput sample info B)

/-- Convert a list-guessing adversary into a singleton-guessing adversary ([BonehShoup2023],
§8.10.2, p. 331): run `B x` to obtain a list of candidates, draw an index uniformly below `Q`
(`Fin.val <$> ProbComp.unifFin (Q - 1)`), and output the entry at that position (or an arbitrary
element of `S` when the index falls past the end of the list). -/
noncomputable def listGuessToGuess [Nonempty S] (Q : ℕ) (B : ListGuessAdversary X S)
    (x : X) : ProbComp S := do
  let l ← B x
  let i ← Fin.val <$> ProbComp.unifFin (Q - 1)
  return l.getD i (Classical.arbitrary S)

/-- **List-to-singleton guessing reduction** ([BonehShoup2023], §8.10.2, p. 331): if every list
output by `B` has length at most `Q`, then `listGuessAdvantage sample info B ≤
Q * guessAdvantage sample info (listGuessToGuess Q B)`. -/
theorem listGuessAdvantage_le_mul_guessAdvantage [DecidableEq S] [Nonempty S] (sample : PMF S)
    (info : S → X) {Q : ℕ} {B : ListGuessAdversary X S}
    (hB : ∀ x, ∀ l ∈ (ProbComp.eval (B x)).support, l.length ≤ Q) :
    listGuessAdvantage sample info B ≤
      Q * guessAdvantage sample info (listGuessToGuess Q B) := by
  unfold listGuessAdvantage guessAdvantage Game.succProbability
  rw [← ENNReal.toNNReal_natCast, ← ENNReal.toNNReal_mul]
  refine ENNReal.toNNReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    (PMF.apply_ne_top _ _)) ?_
  simp only [pmf_norm, ProbComp.eval_unifFin, listGuessOutput, guessOutput, listGuessToGuess]
  refine Probability.PMF.bind_apply_le_mul_bind_apply _ fun s => ?_
  refine Probability.PMF.bind_apply_le_mul_bind_apply_on_support _ fun l hl => ?_
  have hlen : l.length ≤ Q := hB (info s) l hl
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · simp [List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)]
  · obtain ⟨m, rfl⟩ : ∃ m, Q = m + 1 := ⟨Q - 1, (Nat.sub_add_cancel hQ).symm⟩
    rw [Nat.add_sub_cancel]
    have hmap :
        ((uniformOfFintype (Fin (m + 1))).bind fun i =>
          PMF.pure (decide (l.getD i.1 (Classical.arbitrary S) = s))) =
        ((uniformOfFintype (Fin (m + 1))).map
          (fun i : Fin (m + 1) => l.getD i.1 (Classical.arbitrary S))).bind
          fun s' => PMF.pure (decide (s' = s)) := by
      rw [PMF.bind_map]
      rfl
    rw [hmap, Probability.PMF.bind_pure_decide_eq_apply_true']
    by_cases hs : s ∈ l
    · have htake : s ∈ l.take (m + 1) := by rwa [List.take_of_length_le hlen]
      calc (PMF.pure (decide (s ∈ l))) true = 1 := by simp [hs]
        _ = ((m + 1 : ℕ) : ℝ≥0∞) * ((m + 1 : ℕ) : ℝ≥0∞)⁻¹ :=
            (ENNReal.mul_inv_cancel (by simp) (ENNReal.natCast_ne_top _)).symm
        _ ≤ _ := mul_le_mul' le_rfl
            (Probability.PMF.inv_le_map_uniformOfFintype_getD (Classical.arbitrary S) htake)
    · simp [hs]

/-! ### 3. Key derivation in the random-oracle model and Theorem 8.10 (§8.10.2, pp. 331–332) -/

/-- A key-derivation distinguisher in the random-oracle model ([BonehShoup2023], §8.10.2, p. 331):
given the side information `x : X` and a candidate key `t : T`, it runs an adaptive test with
private coins and oracle access to `S → T`. -/
abbrev RODistinguisher (X S T : Type) : Type := X → T → ProbOracleComp (fun _ : S => T) Bool

/-- `D` makes at most `Q` random-oracle queries on every path for every input `(x, t)`, whatever
its private samples and the oracle replies. -/
abbrev RODistinguisher.IsOracleQueryBounded (D : RODistinguisher X S T) (Q : ℕ) : Prop :=
  ∀ x t, (D x t).IsQueryBounded Q

/-- Experiment 0 of key derivation in the random-oracle model ([BonehShoup2023], §8.10.2, p. 331):
sample a random oracle `table : S → T`, then play `KeyDerivation.realOutput` with `derive = table`
and `D` answering oracle queries from `table`. -/
@[expose] noncomputable def roRealOutput [Fintype S] [DecidableEq S] [Fintype T] [Nonempty T]
    (sample : PMF S) (info : S → X) (D : RODistinguisher X S T) : Game :=
  (uniformOfFintype (S → T)).bind fun table =>
    realOutput sample info table fun x t =>
      ProbComp.eval ((D x t).run fun q => pure (table q))

/-- Experiment 1 of key derivation in the random-oracle model ([BonehShoup2023], §8.10.2, p. 331):
sample a random oracle `table : S → T`, then play `KeyDerivation.idealOutput` with a uniform key on
`T` and `D` answering oracle queries from `table`. -/
@[expose] noncomputable def roIdealOutput [Fintype S] [DecidableEq S] [Fintype T] [Nonempty T]
    (sample : PMF S) (info : S → X) (D : RODistinguisher X S T) : Game :=
  (uniformOfFintype (S → T)).bind fun table =>
    idealOutput sample info (uniformOfFintype T) fun x t =>
      ProbComp.eval ((D x t).run fun q => pure (table q))

/-- `Dist^{ro}adv[D, sample, info]` ([BonehShoup2023], §8.10.2, p. 331): the distinguishing
advantage of `D` between `(info s, O(s))` and `(info s, t)` when `O : S → T` is a random oracle. -/
@[expose] noncomputable def roAdvantage [Fintype S] [DecidableEq S] [Fintype T] [Nonempty T]
    (sample : PMF S) (info : S → X) (D : RODistinguisher X S T) : ℝ≥0 :=
  Game.advantage (roRealOutput sample info D) (roIdealOutput sample info D)

/-- The list-guessing wrapper `B` for Theorem 8.10 ([BonehShoup2023], §8.10.2, pp. 331–332):
given `x = info s`, sample a random oracle `table : S → T` and an independent key `t : T`, run
`D x t` against `table`, and output the list of points at which `D x t` queried `table`. Because it
samples the whole oracle table `S → T` eagerly in `ProbComp`, this gives the wrapper's law
without Theorem 8.10's claim that `B` is elementary (which remains open). -/
@[expose] noncomputable def roToListGuess [Fintype S] [DecidableEq S] [Fintype T] [Nonempty T]
    (D : RODistinguisher X S T) (x : X) : ProbComp (List S) := do
  let table ← ProbComp.uniform (S → T)
  let t ← ProbComp.uniform T
  let z ← (D x t).runLog fun q => pure (table q)
  return z.2.map Prod.fst

/-- The singleton-guessing wrapper `B'` for Theorem 8.10 ([BonehShoup2023], §8.10.2, p. 331):
run `roToListGuess D x` and select one of its first `Q` queried points uniformly at random. Because
`roToListGuess D` samples the whole oracle table `S → T` eagerly, this does not establish
Theorem 8.10's claim that `B'` is elementary (which remains open). -/
noncomputable abbrev roToGuess [Fintype S] [DecidableEq S] [Nonempty S] [Fintype T] [Nonempty T]
    (Q : ℕ) (D : RODistinguisher X S T) : GuessAdversary X S :=
  listGuessToGuess Q (roToListGuess D)

/-- **Theorem 8.10, output-size bound** ([BonehShoup2023], §8.10.2, p. 331): if `D` makes at most
`Q` random-oracle queries on every path, then `roToListGuess D` outputs a list of length at most
`Q` on every supported run. -/
theorem length_le_of_mem_support_roToListGuess [Fintype S] [DecidableEq S]
    [Fintype T] [Nonempty T] {D : RODistinguisher X S T} {Q : ℕ}
    (hQ : D.IsOracleQueryBounded Q) (x : X) {l : List S}
    (hl : l ∈ (ProbComp.eval (roToListGuess D x)).support) :
    l.length ≤ Q := by
  supp_cases hl [roToListGuess] with ⟨table, t, z, hz, rfl⟩
  simpa using (hQ x t).length_runLog_le (fun q => pure (table q)) z hz

section Tracking

/-- The logging handler of `runLog` for a deterministic oracle table `table : S → T`, at the `PMF`
level. -/
private noncomputable def logTable (table : S → T) (q : S) : StateT (List (S × T)) PMF T :=
  fun log => PMF.pure (table q, log ++ [(q, table q)])

private theorem eval_runLog_pure_table (table : S → T) {α : Type}
    (A : ProbOracleComp (fun _ : S => T) α) :
    ProbComp.eval (A.runLog fun q => pure (table q)) =
      ProbOracleComp.runWith (logTable table) A [] := by
  rw [ProbOracleComp.runLog, ProbOracleComp.eval_runState]
  rfl

private theorem runWith_logTable_map_fst (table : S → T) {α : Type}
    (A : ProbOracleComp (fun _ : S => T) α) (log : List (S × T)) :
    (ProbOracleComp.runWith (logTable table) A log).map Prod.fst =
      ProbComp.eval (A.run fun q => pure (table q)) := by
  have h := ProbOracleComp.runWith_map_state (logTable table)
    (fun q => StateT.lift (PMF.pure (table q))) (fun _ => ()) (fun q s => by
      simp [logTable, StateT.lift]) A log
  rw [ProbOracleComp.runWith_lift] at h
  have h' := congrArg (PMF.map Prod.fst) h
  rw [PMF.map_comp, PMF.map_comp] at h'
  have h1 : (Prod.fst ∘ fun x : α × List (S × T) => (x.1, ())) = Prod.fst := rfl
  have h2 : (Prod.fst ∘ fun x : α => (x, ())) = id := rfl
  rw [h1, h2, PMF.map_id] at h'
  exact h'.trans (by simp [ProbOracleComp.eval_run, OracleComp.evalWith_eq_interpret])

variable [DecidableEq S]

private theorem identicalUntilBad_logTable (s : S) (t : T) (table : S → T) :
    ProbOracleComp.IdenticalUntilBad (logTable (Function.update table s t))
      (logTable table) (fun log => s ∈ log.map Prod.fst) := by
  refine OracleComp.IdenticalUntilBad.probOracleComp ⟨fun q log _ a log' hlog' => ?_,
    fun q log hlog x hx => ?_, fun q log hlog x hx => ?_⟩
  · by_cases hqs : q = s
    · subst q
      have hne1 : log' ≠ log ++ [(s, t)] := fun h => hlog' (by simp [h])
      have hne2 : log' ≠ log ++ [(s, table s)] := fun h => hlog' (by simp [h])
      simp [logTable, PMF.pure_apply, hne1, hne2]
    · simp [logTable, Function.update_of_ne hqs]
  · supp_cases hx [logTable]
    simp [hlog]
  · supp_cases hx [logTable]
    simp [hlog]

private theorem toOuterMeasure_bad_eq_bind (s : S) (table : S → T)
    (A : ProbOracleComp (fun _ : S => T) Bool) :
    (ProbOracleComp.runWith (logTable table) A []).toOuterMeasure
        {z | s ∈ z.2.map Prod.fst} =
      ((ProbComp.eval (A.runLog fun q => pure (table q))).bind fun z =>
        PMF.pure (decide (s ∈ z.2.map Prod.fst))) true := by
  rw [eval_runLog_pure_table, PMF.toOuterMeasure_apply, PMF.bind_apply]
  refine tsum_congr fun z => ?_
  rw [Set.indicator_apply]
  split_ifs with hz
  · have hmem : s ∈ z.2.map Prod.fst := hz
    simp only [PMF.pure_apply, decide_eq_true hmem, ↓reduceIte, mul_one]
  · have hmem : s ∉ z.2.map Prod.fst := hz
    simp only [PMF.pure_apply, decide_eq_false hmem, Bool.true_eq_false, ↓reduceIte, mul_zero]

end Tracking

/-- **List-guessing inequality of Theorem 8.10** ([BonehShoup2023], §8.10.2, pp. 331–332): in
the random-oracle model, a KDF distinguisher's advantage is at most the list-guessing advantage
of `roToListGuess D`. Because `roToListGuess D` samples the whole oracle table `S → T` eagerly,
this establishes the inequality without Theorem 8.10's claim that the wrapper is elementary
(which remains open). -/
theorem roAdvantage_le_listGuessAdvantage [Fintype S] [DecidableEq S] [Fintype T] [Nonempty T]
    (sample : PMF S) (info : S → X) (D : RODistinguisher X S T) :
    roAdvantage sample info D ≤ listGuessAdvantage sample info (roToListGuess D) := by
  set G : X → T → (S → T) → Game := fun x t table =>
    ProbComp.eval ((D x t).run fun q => pure (table q))
  have hreal : roRealOutput sample info D =
      sample.bind fun s => (uniformOfFintype (S → T)).bind fun table =>
        (uniformOfFintype T).bind fun t => G (info s) t (Function.update table s t) := by
    unfold roRealOutput realOutput
    pmf_swap with s
    rw [Probability.PMF.bind_uniformOfFintype_update s (fun table => G (info s) (table s) table)]
    simp only [Function.update_self]
    pmf_swap
  have hideal : roIdealOutput sample info D =
      sample.bind fun s => (uniformOfFintype (S → T)).bind fun table =>
        (uniformOfFintype T).bind fun t => G (info s) t table := by
    unfold roIdealOutput idealOutput
    pmf_swap
  have hbad_law : listGuessOutput sample info (roToListGuess D) =
      sample.bind fun s => (uniformOfFintype (S → T)).bind fun table =>
        (uniformOfFintype T).bind fun t =>
          ((ProbComp.eval ((D (info s) t).runLog fun q => pure (table q))).bind fun z =>
            PMF.pure (decide (s ∈ z.2.map Prod.fst))) := by
    simp only [pmf_norm, ProbComp.eval_uniform, listGuessOutput, roToListGuess]
  rw [roAdvantage, listGuessAdvantage, hreal, hideal, hbad_law]
  refine Game.advantage_bind_le_succProbability_bind sample _ _ _ fun s =>
    Game.bind_apply_le_add_bind_apply (uniformOfFintype (S → T)) _ _ _ true fun table =>
      Game.bind_apply_le_add_bind_apply (uniformOfFintype T) _ _ _ true fun t => ?_
  have hub := identicalUntilBad_logTable s t table
  have h1 := hub.bind_apply_le (D (info s) t) [] (fun z => PMF.pure z.1) true
  have h2 := hub.symm.bind_apply_le (D (info s) t) [] (fun z => PMF.pure z.1) true
  rw [hub.bad_eq, toOuterMeasure_bad_eq_bind] at h1
  rw [toOuterMeasure_bad_eq_bind] at h2
  change (PMF.map Prod.fst _) true ≤ (PMF.map Prod.fst _) true + _ at h1 h2
  rw [runWith_logTable_map_fst, runWith_logTable_map_fst] at h1 h2
  exact ⟨h1, h2⟩

/-- **Singleton-guessing inequality of Theorem 8.10** ([BonehShoup2023], §8.10.2, p. 331): if
`D` makes at most `Q` random-oracle queries on every path, its KDF distinguishing advantage in
the random-oracle model is at most `Q * guessAdvantage sample info (roToGuess Q D)`. Because
`roToGuess Q D` samples the whole oracle table `S → T` eagerly, this establishes the inequality
without Theorem 8.10's claim that the wrapper is elementary (which remains open). -/
theorem roAdvantage_le_mul_guessAdvantage [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype T] [Nonempty T] (sample : PMF S) (info : S → X)
    {D : RODistinguisher X S T} {Q : ℕ} (hQ : D.IsOracleQueryBounded Q) :
    roAdvantage sample info D ≤ Q * guessAdvantage sample info (roToGuess Q D) :=
  (roAdvantage_le_listGuessAdvantage sample info D).trans
    (listGuessAdvantage_le_mul_guessAdvantage sample info
      (fun x _ hl => length_le_of_mem_support_roToListGuess hQ x hl))

/-- **Asymptotic random-oracle KDF transfer** ([BonehShoup2023], §8.10.2, p. 331, and
Attack Game 11.3 in §11.5.2, pp. 448–449): if a family of random-oracle KDF distinguishers
makes polynomially many random-oracle queries and every family of guessing adversaries has
negligible guessing advantage against the source, then the KDF distinguishing advantage is
negligible. The quantifier in `hguess` ranges over all guessers with no efficiency bound, so
this is the information-theoretic assumption (an unpredictable source); applying a computational
guessing assumption (such as the fourth example of Section 8.10.1, p. 326, or CDH in Theorem
11.4 of Section 11.5.1, p. 446) needs the efficient lazy-simulation wrapper, which this module
does not have. -/
theorem negligible_roAdvantage_of_negligible_guessAdvantage {S X T : ℕ → Type}
    [∀ n, Fintype (S n)] [∀ n, DecidableEq (S n)] [∀ n, Nonempty (S n)]
    [∀ n, Fintype (T n)] [∀ n, Nonempty (T n)]
    (sample : ∀ n, PMF (S n)) (info : ∀ n, S n → X n)
    {D : ∀ n, RODistinguisher (X n) (S n) (T n)} {Q : ℕ → ℕ}
    (hQ : PolynomiallyBounded Q) (hD : ∀ n, (D n).IsOracleQueryBounded (Q n))
    (hguess : ∀ A : ∀ n, GuessAdversary (X n) (S n),
      Negligible fun n => guessAdvantage (sample n) (info n) (A n)) :
    Negligible fun n => roAdvantage (sample n) (info n) (D n) := by
  refine negligible_of_le ((hguess fun n => roToGuess (Q n) (D n)).polynomiallyBounded_mul hQ)
    fun n => ?_
  simpa [mul_comm] using roAdvantage_le_mul_guessAdvantage (sample n) (info n) (hD n)

end Cslib.Crypto.KeyDerivation
