/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.SecondPreimageResistant.Relations
import CslibFrontier.Probability.PMF.Support
import CslibFrontier.Tactic.PolyTime

/-!
# Tests for second-preimage resistance implications and separations

Checks for `CslibFrontier/Crypto/Computational/SecondPreimageResistant/Relations.lean` as a
`module` client with ordinary imports:

* Concrete evaluations of `ignoreHeadBit`, `flipHeadBit`, and `plantEasyBranch`.
* The Section 8.11.1 separation (`not_secondPreimageResistant_ignoreHeadBit_id`) and the
  bit-string Exercise 8.23(c) separation (`secondPreimageResistant_plantEasyBranch_id` and
  `not_oneWay_plantEasyBranch_id`), giving an explicit unconditional function `plantEasyBranch 2 id`
  that is `SecondPreimageResistant` and `¬ OneWay`.
* Necessity of the super-polynomial compression premise in
  `SecondPreimageResistant.oneWay_of_outputLength`: for `f = id` (`outLen n = n`), `id` is
  `SecondPreimageResistant` (`secondPreimageResistant_id`) and satisfies `hlen`, yet `¬ OneWay id`
  because `2 ^ n / 2 ^ n = 1` is not negligible (`not_oneWay_id`).
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.SecondPreimageResistantRelations

open Cslib Cslib.Crypto Cslib.ProbComp Cslib.Probability
open Turing.MultiTapeTM
open scoped NNReal ENNReal

example : flipHeadBit [false, true] = [true, true] := rfl

example : flipHeadBit [] = [true] := rfl

example : ignoreHeadBit id [false, true] = ignoreHeadBit id (flipHeadBit [false, true]) := rfl

example : plantEasyBranch 2 id [false, false, true] = [true, true] := rfl

example : plantEasyBranch 2 id [true, false, true] = [false, true, false, true] := rfl

/-- The identity on bit strings is unconditionally `SecondPreimageResistant`. -/
theorem secondPreimageResistant_id : SecondPreimageResistant id :=
  SecondPreimageResistant.of_injective (ComputableInPolyTime.id' (encIn := encBits))
    Function.injective_id

/-- **Necessity of compression in `SecondPreimageResistant.oneWay_of_outputLength`**: `id` is
`SecondPreimageResistant` and length-preserving (`outLen n = n`), yet `¬ OneWay id`. -/
theorem not_oneWay_id : ¬ OneWay id :=
  not_oneWay_of_inverse id (fun _ y => y)
    (ComputableInPolyTime.id' (encIn := encBits)).isPPT (fun _ => rfl)

/-- `ignoreHeadBit id` is not second-preimage resistant. -/
theorem not_secondPreimageResistant_ignoreHeadBit_id :
    ¬ SecondPreimageResistant (ignoreHeadBit id) :=
  not_secondPreimageResistant_ignoreHeadBit id

/-- `ignoreHeadBit id` is not second-preimage resistant on `{0,1}ⁿ` either. -/
theorem not_secondPreimageResistantOn_ignoreHeadBit_id :
    ¬ SecondPreimageResistantOn (ignoreHeadBit id) (fun n w => decide (w.length = n)) :=
  not_secondPreimageResistantOn_ignoreHeadBit id <|
    Filter.eventually_ge_atTop 1 |>.mono fun n hn x hlen => by
      cases x with
      | nil => simp at hlen; omega
      | cons b xs => simpa [flipHeadBit] using hlen

/-- Explicit unconditional witness for Exercise 8.23(c) on bit strings: `plantEasyBranch 2 id` is
`SecondPreimageResistantOn`, `SecondPreimageResistant`, and `¬ OneWay`. -/
theorem secondPreimageResistantOn_plantEasyBranch_id (valid : ℕ → List Bool → Bool) :
    SecondPreimageResistantOn (plantEasyBranch 2 id) valid :=
  (SecondPreimageResistantOn.of_injective (ComputableInPolyTime.id' (encIn := encBits))
    Function.injective_id).plantEasyBranch 2

theorem secondPreimageResistant_plantEasyBranch_id :
    SecondPreimageResistant (plantEasyBranch 2 id) :=
  secondPreimageResistant_id.plantEasyBranch 2

theorem not_oneWay_plantEasyBranch_id : ¬ OneWay (plantEasyBranch 2 id) :=
  not_oneWay_plantEasyBranch 2 id

/-- Separation witness between `SecondPreimageResistantOn` (Definition 8.6 on `{0,1}ⁿ`) and the
any-length strengthening `SecondPreimageResistant`: strip a leading `false` bit. On fixed-length
words `{0,1}ⁿ` this function is injective, so `SecondPreimageResistantOn` holds unconditionally,
while cross-length collisions refute `SecondPreimageResistant` and allow trivial inversion. -/
private def stripFalseHead (w : List Bool) : List Bool :=
  if w.headD true then w else w.tail

private theorem stripFalseHead_injOn_length {x x' : List Bool} (hlen : x'.length = x.length)
    (heq : stripFalseHead x' = stripFalseHead x) : x' = x := by
  cases x with
  | nil =>
    cases x' with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons a as =>
    cases x' with
    | nil => simp at hlen
    | cons b bs =>
      have htlen : bs.length = as.length := by simpa using hlen
      cases a <;> cases b <;>
        simp only [stripFalseHead, List.headD_cons, Bool.false_eq_true, ↓reduceIte,
          List.tail_cons] at heq
      · rw [heq]
      · have hlen' := congrArg List.length heq
        simp at hlen'
        omega
      · have hlen' := congrArg List.length heq
        simp at hlen'
        omega
      · rw [(List.cons.inj heq).2]

theorem secondPreimageResistantOn_stripFalseHead :
    SecondPreimageResistantOn stripFalseHead (fun n w => decide (w.length = n)) := by
  have hpoly : ComputableInPolyTime stripFalseHead encBits encBits := by
    unfold stripFalseHead
    polytime
  refine SecondPreimageResistantOn.of_negligible hpoly fun adversary _ => ?_
  have hzero : ∀ n, Game.succProbability (ProbComp.eval
      (secondPreimageGameOn stripFalseHead (fun n w => decide (w.length = n)) adversary n)) = 0 :=
    fun n => by
      have heval : ProbComp.eval (secondPreimageGameOn stripFalseHead
          (fun n w => decide (w.length = n)) adversary n) = PMF.pure false := by
        unfold secondPreimageGameOn
        simp only [ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList]
        refine PMF.bind_eq_pure_of_forall_mem_support fun x hx => ?_
        have hlenx : x.length = n := BitString.mem_support_uniformList_iff.mp hx
        have hconst : ∀ x' : List Bool,
            (decide (x'.length = n) && (x' != x && stripFalseHead x' == stripFalseHead x)) =
              false := fun x' => by
          by_cases hln : x'.length = n
          · by_cases hne : x' = x
            · simp [hne]
            · have hne' : stripFalseHead x' ≠ stripFalseHead x := fun heq =>
                hne (stripFalseHead_injOn_length (hln.trans hlenx.symm) heq)
              simp [hne, hne']
          · simp [hln]
        simp_rw [hconst, PMF.bind_const]
      simp [heval, Game.succProbability]
  simpa only [hzero] using negligible_zero

theorem not_secondPreimageResistant_stripFalseHead : ¬ SecondPreimageResistant stripFalseHead := by
  let adv : SecondPreimageFinder := fun _ x => pure (false :: x)
  have hpoly : ComputableInPolyTime (fun x : List Bool => false :: x) encBits encBits := by polytime
  refine not_secondPreimageResistant_of_le_succProbability (c := (1 / 2 : ℝ≥0))
    (by norm_num) adv hpoly.isPPT fun n => ?_
  unfold secondPreimageGame secondPreimageExperiment adv
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList, PMF.pure_bind]
  have hhalf : (1 / 2 : ℝ≥0∞) ≤
      ((BitString.uniformList n).bind fun x =>
        PMF.pure
          ((false :: x != x) && (stripFalseHead (false :: x) == stripFalseHead x))) true := by
    have hsub : ∀ x : List Bool, x.headD true = true →
        ((false :: x != x) && (stripFalseHead (false :: x) == stripFalseHead x)) = true :=
      fun x hx => by
        have hne : false :: x ≠ x := ne_of_apply_ne List.length (by simp)
        cases x with
        | nil => simp [stripFalseHead]
        | cons b bs =>
          simp only [List.headD_cons] at hx
          subst hx
          simp [stripFalseHead, hne]
    cases n with
    | zero =>
      simp [hsub [] rfl]
    | succ k =>
      rw [BitString.uniformList_succ, PMF.bind_bind, PMF.bind_apply, tsum_bool]
      have ht : ((PMF.map (List.cons true) (BitString.uniformList k)).bind fun x =>
          PMF.pure ((false :: x != x) &&
            (stripFalseHead (false :: x) == stripFalseHead x))) true = 1 := by
        rw [PMF.bind_map]
        have hconst : (fun l : List Bool =>
            PMF.pure ((false :: (true :: l) != true :: l) &&
              (stripFalseHead (false :: true :: l) == stripFalseHead (true :: l)))) =
            fun _ => PMF.pure true := by
          ext l b
          simp [hsub (true :: l) rfl]
        change ((BitString.uniformList k).bind (fun l : List Bool =>
            PMF.pure ((false :: (true :: l) != true :: l) &&
              (stripFalseHead (false :: true :: l) == stripFalseHead (true :: l))))) true = 1
        simp only [hconst, PMF.bind_const, PMF.pure_apply_self]
      simp only [PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat, ht, mul_one,
        one_div, le_add_self]
  have h12 : (1 / 2 : ℝ≥0) = (1 / 2 : ℝ≥0∞).toNNReal := by simp [ENNReal.toNNReal_ofNat]
  rw [Game.succProbability, h12]
  exact ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) hhalf

theorem not_oneWay_stripFalseHead : ¬ OneWay stripFalseHead := by
  let inv : List Bool → List Bool := fun y => if y.headD false then y else false :: y
  have hinv_poly : ComputableInPolyTime inv encBits encBits := by
    unfold inv
    polytime
  have hright (w : List Bool) : stripFalseHead (inv w) = w := by
    cases w with
    | nil => simp [inv, stripFalseHead]
    | cons c cs => cases c <;> simp [inv, stripFalseHead]
  refine not_oneWay_of_inverse stripFalseHead (fun _ y => inv y) hinv_poly.isPPT fun x =>
    hright (stripFalseHead x)

end CslibFrontierTests.Crypto.SecondPreimageResistantRelations
