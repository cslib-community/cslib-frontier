/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.SecondPreimageResistant.Relations
import CslibFrontier.Crypto.Negligible
import CslibFrontier.Probability.PMF.Support
import CslibFrontier.Tactic.PolyTime

/-!
# Tests for second-preimage resistance implications and separations

Checks for `CslibFrontier/Crypto/Computational/SecondPreimageResistant/Relations.lean` as a
`module` client with ordinary imports:

* Concrete evaluations of `ignoreHeadBit`, `flipHeadBit`, and `plantEasyBranch`.
* The Section 8.11.1 separation (`not_secondPreimageResistant_ignoreHeadBit_id` and hypothesis-form
  `OneWayOn.ignoreHeadBit`) and the bit-string Exercise 8.23(c) separation
  (`secondPreimageResistant_plantEasyBranch_id`, `not_oneWayOn_plantEasyBranch_id`, and the
  compressing instance `exercise8_23c_compressing`).
* Necessity of the super-polynomial compression premise in
  `SecondPreimageResistantOn.oneWayOn_of_outputLength`: `id` is `SecondPreimageResistant` and
  length-preserving (`outLen n = n`), yet not one-way on `{0,1}ⁿ` because `2 ^ n / 2 ^ n = 1` is
  not negligible (`not_oneWayOn_id`).
* The composed `(8.17)` chain `HashFamily H → OneWay (keyDigest H)` and concrete `(n, d)` /
  `(n, r)` reduction bounds.
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

theorem not_oneWay_id : ¬ OneWay id :=
  not_oneWay_of_inverse id (fun _ y => y)
    (ComputableInPolyTime.id' (encIn := encBits)).isPPT (fun _ => rfl)

/-- **Necessity of compression in `SecondPreimageResistantOn.oneWayOn_of_outputLength`**: `id` is
`SecondPreimageResistant` (see `CslibFrontierTests/Crypto/SecondPreimageResistant.lean`) and
length-preserving (`outLen n = n`), yet not one-way on `{0,1}ⁿ`: for an injective function,
one-wayness on a domain containing the `n`-bit words is `OneWay`. -/
theorem not_oneWayOn_id : ¬ OneWayOn id (fun n w => decide (w.length = n)) := fun h =>
  not_oneWay_id (h.oneWay_of_injective Function.injective_id fun _ _ => decide_eq_true)

/-- `ignoreHeadBit id` is not second-preimage resistant. -/
theorem not_secondPreimageResistant_ignoreHeadBit_id :
    ¬ SecondPreimageResistant (ignoreHeadBit id) :=
  not_secondPreimageResistantOn_ignoreHeadBit id (Filter.Eventually.of_forall fun _ _ _ => rfl)

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
    fun _ _ _ _ _ h => h).plantEasyBranch 2

theorem secondPreimageResistant_plantEasyBranch_id :
    SecondPreimageResistant (plantEasyBranch 2 id) :=
  secondPreimageResistantOn_plantEasyBranch_id _

theorem not_oneWayOn_plantEasyBranch_id :
    ¬ OneWayOn (plantEasyBranch 2 id) (fun n w => decide (w.length = n)) :=
  not_oneWayOn_plantEasyBranch 2 id fun _ _ => decide_eq_true

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
  exact SecondPreimageResistantOn.of_injective hpoly fun n x x' hx hx' heq =>
    stripFalseHead_injOn_length ((of_decide_eq_true hx').trans hx.symm) heq

theorem not_secondPreimageResistant_stripFalseHead : ¬ SecondPreimageResistant stripFalseHead := by
  let adv : SecondPreimageFinder := fun _ x => pure (false :: x)
  have hpoly : ComputableInPolyTime (fun x : List Bool => false :: x) encBits encBits := by polytime
  refine not_secondPreimageResistantOn_of_le_succProbability (c := (1 / 2 : ℝ≥0))
    (by norm_num) adv hpoly.isPPT (Filter.Eventually.of_forall fun n => ?_)
  rw [← secondPreimageGame_eq_secondPreimageGameOn]
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

/-- Concrete compressing output-length check for `plantEasyBranch 2 (List.drop 2)` (`3 ↦ 2`). -/
example : (plantEasyBranch 2 (List.drop 2) [false, false, true]).length = 2 := rfl

example : (plantEasyBranch 2 (List.drop 2) [true, false, true]).length = 2 := rfl

theorem length_plantEasyBranch_drop (w : List Bool) (hw : 2 ≤ w.length) :
    (plantEasyBranch 2 (List.drop 2) w).length = w.length - 1 := by
  rw [length_plantEasyBranch]
  split_ifs
  · omega
  · simp
    omega

/-- **Exercise 8.23(c), compressing instance at `k = 2`**: given any `SecondPreimageResistant H`
compressing `n`-bit inputs to `(n - 2)`-bit digests (`n ≥ 2`), `plantEasyBranch 2 H` maps
`n`-bit inputs to `(n - 1)`-bit digests, remains `SecondPreimageResistant` (and
`SecondPreimageResistantOn` on every `valid`), and is not one-way on `{0,1}ⁿ`. -/
theorem exercise8_23c_compressing {H : List Bool → List Bool} (hH : SecondPreimageResistant H)
    (hlen : ∀ w : List Bool, 2 ≤ w.length → (H w).length = w.length - 2)
    (valid : ℕ → List Bool → Bool) :
    (∀ w : List Bool, 2 ≤ w.length → (plantEasyBranch 2 H w).length = w.length - 1) ∧
      SecondPreimageResistantOn (plantEasyBranch 2 H) valid ∧
      SecondPreimageResistant (plantEasyBranch 2 H) ∧
      ¬ OneWayOn (plantEasyBranch 2 H) (fun n w => decide (w.length = n)) := by
  refine ⟨fun w hw => ?_, (hH.mono fun _ _ _ => rfl).plantEasyBranch 2,
    hH.plantEasyBranch 2, not_oneWayOn_plantEasyBranch 2 H fun _ _ => decide_eq_true⟩
  rw [length_plantEasyBranch]
  split_ifs
  · omega
  · rw [hlen w hw]
    omega

/-- Composed **(8.17)** chain
`HashFamily H → SecondPreimageResistant (keyDigest H) → OneWay (keyDigest H)`: second-preimage
resistance on the domain that accepts every answer gives one-wayness on that domain, which is
`OneWay`. -/
example {H : List Bool → List Bool → List Bool} (hH : HashFamily H) :
    OneWay (CollisionResistantToOneWay.keyDigest H) := by
  refine oneWayOn_true_iff.mp (hH.secondPreimageResistant_keyDigest.oneWayOn_of_outputLength
    (outLen := fun n => 2 * (n / 3)) (fun n w hw => ?_) ?_)
  · simp [CollisionResistantToOneWay.keyDigest, hw, hH.length_eq, two_mul,
      Nat.min_eq_left (Nat.div_le_self n 3)]
  · have hhalf : Negligible fun n => (1 / 2 : ℝ≥0) ^ (n / 3) :=
      (negligible_geometric (by norm_num : (1 / 2 : ℝ≥0) < 1)).comp_of_polynomial_bound
        (bound := fun m => 3 * m + 2)
        (Filter.tendsto_atTop_atTop.mpr fun b => ⟨3 * b, fun n hn => by omega⟩)
        (by fun_prop) (Filter.Eventually.of_forall fun n => by omega)
    refine negligible_of_le hhalf fun n => ?_
    have hle : 2 * (n / 3) ≤ n := by omega
    calc
      (2 : ℝ≥0) ^ (2 * (n / 3)) / (2 : ℝ≥0) ^ n
          = (1 / 2 : ℝ≥0) ^ (n - 2 * (n / 3)) := by
              conv_lhs => rhs; rw [← Nat.add_sub_cancel' hle, pow_add]
              rw [div_mul_cancel_left₀ (pow_ne_zero _ two_ne_zero), one_div, inv_pow]
      _ ≤ (1 / 2 : ℝ≥0) ^ (n / 3) :=
            pow_le_pow_of_le_one zero_le (by norm_num) (by omega)

/-- Section 8.11.1 separation on `{0,1}ⁿ`: if `f` is one-way there, `ignoreHeadBit f` stays
one-way while failing second-preimage resistance. -/
example {f : List Bool → List Bool} (hf : OneWayOn f fun n w => decide (w.length = n)) :
    OneWayOn (ignoreHeadBit f) (fun n w => decide (w.length = n)) ∧
      ¬ SecondPreimageResistantOn (ignoreHeadBit f) (fun n w => decide (w.length = n)) :=
  ⟨hf.ignoreHeadBit fun n w hw => by
      simp only [decide_eq_true_eq, List.length_tail] at hw ⊢
      omega,
    not_secondPreimageResistantOn_ignoreHeadBit f <|
      Filter.eventually_ge_atTop 1 |>.mono fun n hn x hlen => by
        cases x with
        | nil => simp at hlen; omega
        | cons b xs => simpa [flipHeadBit] using hlen⟩

/-- Concrete `(n = 2, d = 1)` reduction bound for `List.take 1` on `{0,1}²`:
`OWadv ≤ SPRadv + 2¹ / 2²`. -/
example (adversary : Inverter) :
    Game.succProbability (ProbComp.eval
      (inversionGameOn (List.take 1) (fun n w => decide (w.length = n)) adversary 2)) ≤
      Game.succProbability
        (ProbComp.eval
          (secondPreimageGameOn (List.take 1) (fun n w => decide (w.length = n))
            (inverterToSecondPreimage (List.take 1) adversary) 2)) +
        (2 : ℝ≥0) ^ 1 / (2 : ℝ≥0) ^ 2 :=
  succProbability_inversionGameOn_le_secondPreimageGameOn_add (fun w hw => by simp [hw]) adversary

/-- Concrete `(n = 2, r = 1)` zero-loss second-preimage bound for `keyDigest H`. -/
example {H : List Bool → List Bool → List Bool}
    (hlen : ∀ key message, (H key message).length = key.length)
    (adversary : SecondPreimageFinder) :
    Game.succProbability
      (ProbComp.eval (secondPreimageGame (CollisionResistantToOneWay.keyDigest H) adversary 7)) ≤
      Game.succProbability
        (ProbComp.eval
          (collisionGame H (fun _ _ => true) (secondPreimageToCollisionFinder adversary 1) 2)) :=
  succProbability_secondPreimageGame_keyDigest_le hlen adversary 2 1 (by decide)

end CslibFrontierTests.Crypto.SecondPreimageResistantRelations
