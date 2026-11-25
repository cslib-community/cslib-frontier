/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.HardCore
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# No universal hard-core predicate

A polynomial-time predicate `b` is a *universal hard-core predicate* if it is a hard-core of every
one-way function. If one-way functions exist, no such predicate exists
[Goldreich, Exercise 7.8][Goldreich2007DraftR4]
(`Cslib.Crypto.OneWay.not_exists_universal_hardCore`).

The proof follows the guideline of the exercise. For a candidate `b` and a one-way function `f`,
the function `f'(x) = (f(x), b(x))` (`Cslib.Crypto.appendPredicate`, the pair written as `f x`
followed by the bit `b x`) is still one-way: an inverter for `f` guesses the missing bit and runs
an inverter for `f'`, losing at most a factor two
(`Cslib.Crypto.succProbability_inversionGame_appendPredicate_le`).
But `b` is not a hard-core of `f'`: reading the last bit of the image predicts `b x` with
certainty (`Cslib.Crypto.not_hardCore_appendPredicate`). The predictor ignores the length
parameter, so it also refutes Goldreich's Definition 7.6, whose predictor receives only `f'(x)`
(`Cslib.Crypto.OneWay.exists_oneWay_lastBit_eq`).

## Main definitions

* `Cslib.Crypto.appendPredicate`: `f'(x) = f(x) b(x)`.
* `Cslib.Crypto.guessBitInverter`: the inverter for `f` built from one for `f'`.

## Main results

* `Cslib.Crypto.OneWay.appendPredicate`: appending a polynomial-time bit preserves one-wayness.
* `Cslib.Crypto.not_hardCore_appendPredicate`: `b` is not a hard-core of `f'`.
* `Cslib.Crypto.OneWay.exists_oneWay_lastBit_eq`: Goldreich, Exercise 7.8, in the source's terms.
* `Cslib.Crypto.OneWay.not_exists_universal_hardCore`: the impossibility for the library's
  `HardCore`.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft `r4.pdf` of
  March 2007][Goldreich2007DraftR4], Exercise 7.8 (printed page 306, PDF page 42), with
  Definition 7.6 (printed page 275).
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

/-- The function `f'(x) = (f(x), b(x))` of the guideline to [Goldreich, Exercise 7.8]: the image
of `f` followed by the bit `b x`. Since the appended part is a single bit, this concatenation
encodes the pair. -/
def appendPredicate (f : List Bool → List Bool) (b : List Bool → Bool) (x : List Bool) :
    List Bool :=
  f x ++ [b x]

@[fun_prop]
theorem computableInPolyTime_appendPredicate {f : List Bool → List Bool}
    {b : List Bool → Bool} (hf : ComputableInPolyTime f encBits encBits)
    (hb : ComputableInPolyTime b encBits encBool) :
    ComputableInPolyTime (appendPredicate f b) encBits encBits := by
  unfold appendPredicate; polytime

/-- An inverter for `f` from an inverter for `appendPredicate f b`: guess the appended bit
uniformly and run the given inverter on the extended image. -/
noncomputable def guessBitInverter (adversary : Inverter) : Inverter :=
  fun n image => do
    let bit ← ProbComp.uniform Bool
    adversary n (image ++ [bit])

@[program_certificate]
theorem isPPT_guessBitInverter {adversary : Inverter} (ha : IsPPT encBits adversary) :
    IsPPT encBits (guessBitInverter adversary) := by
  apply IsPPTOn.isPPT
  have hp := ComputableInPolyTime.id' (encIn := encPair (encPair encUnary encBits) encBool)
  simpa only [guessBitInverter] using
    (isPPTOn_uniform_bool (encPair encUnary encBits)).bind_with
      (ha.preprocess hp.fst'.fst' (hp.fst'.snd'.bitsAppend
        (hp.snd'.bitsCons (ComputableInPolyTime.const []))))

/-- **Inversion reduction.** Guessing the appended bit loses at most a factor two: the guess is
right with probability one half, and then the extended image is distributed exactly as in the game
for `appendPredicate f b`, whose preimages are preimages for `f`. -/
theorem succProbability_inversionGame_appendPredicate_le (f : List Bool → List Bool)
    (b : List Bool → Bool) (adversary : Inverter) (n : ℕ) :
    Game.succProbability (ProbComp.eval (inversionGame (appendPredicate f b) adversary n)) ≤
      2 * Game.succProbability
        (ProbComp.eval (inversionGame f (guessBitInverter adversary) n)) := by
  have h : ProbComp.eval (inversionGame (appendPredicate f b) adversary n) true ≤
      2 * ProbComp.eval (inversionGame f (guessBitInverter adversary) n) true := by
    simp only [inversionGame, inversionExperiment, guessBitInverter, appendPredicate,
      ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform, BitString.eval_sampleList]
    rw [PMF.bind_apply, PMF.bind_apply, ← ENNReal.tsum_mul_left]
    refine tsum_le_tsum fun x => ?_
    rw [mul_left_comm]
    gcongr
    have key (bit : Bool) :
        ((adversary n (f x ++ [bit])).eval.bind fun z =>
          PMF.pure (f z ++ [b z] == f x ++ [bit])) true ≤
        ((adversary n (f x ++ [bit])).eval.bind fun z => PMF.pure (f z == f x)) true :=
      PMF.bind_apply_mono_on_support _ _ fun z _ => by
        by_cases h : f z ++ [b z] = f x ++ [bit]
        · rw [List.append_inj_left' h rfl, beq_self_eq_true, PMF.pure_apply_self]
          exact PMF.coe_le_one _ _
        · simp [beq_false_of_ne h]
    rw [PMF.bind_bind, PMF.bind_apply (PMF.uniformOfFintype Bool), tsum_bool]
    simp only [PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat]
    rw [mul_add, ← mul_assoc, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num),
      one_mul, one_mul]
    cases b x
    · exact (key false).trans le_self_add
    · exact (key true).trans le_add_self
  simpa [Game.succProbability, ENNReal.toNNReal_mul, ENNReal.toNNReal_ofNat] using
    ENNReal.toNNReal_mono (ENNReal.mul_ne_top (by simp) (PMF.apply_ne_top _ _)) h

/-- **Appending a polynomial-time bit preserves one-wayness.** If `f` is one-way and `b` is
computable in polynomial time, then `f'(x) = (f(x), b(x))` is one-way. -/
theorem OneWay.appendPredicate {f : List Bool → List Bool} {b : List Bool → Bool}
    (hf : OneWay f) (hb : ComputableInPolyTime b encBits encBool) :
    OneWay (appendPredicate f b) :=
  OneWay.of_inversion_negligible (computableInPolyTime_appendPredicate hf.polyTime hb)
    fun adversary ha => negligible_of_le
      ((hf.inversion_negligible _ (isPPT_guessBitInverter ha)).const_mul 2)
      (succProbability_inversionGame_appendPredicate_le f b adversary)

/-- Reading the last bit, with default `false`, is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_getLastD :
    ComputableInPolyTime (List.getLastD · false) encBits encBool := by
  simp only [List.getLastD_eq_getLast?, List.getLast?_eq_head?_reverse, ← List.headD_eq_head?_getD]
  exact (ComputableInPolyTime.headD false).comp ComputableInPolyTime.bitsReverse

/-- The predictor that outputs the last bit of the image and ignores the length parameter. -/
def lastBitPredictor : Distinguisher :=
  fun _ image => pure (image.getLastD false)

/-- The last-bit predictor always predicts `b` from `appendPredicate f b`. -/
theorem predictionAdvantage_lastBitPredictor (f : List Bool → List Bool) (b : List Bool → Bool)
    (n : ℕ) : predictionAdvantage (appendPredicate f b) b lastBitPredictor n = 1 / 2 := by
  have hgame : ProbComp.eval (predictionGame (appendPredicate f b) b lastBitPredictor n) =
      PMF.pure true := by
    simp only [predictionGame, predictionExperiment, lastBitPredictor, appendPredicate,
      List.getLastD_concat, bind_pure_comp, map_pure, BEq.rfl, ProbComp.eval_map]
    exact PMF.map_const _ _
  apply NNReal.coe_injective
  rw [predictionAdvantage, Game.coe_guessingAdvantage, Game.succProbability, hgame]
  norm_num

/-- `b` is not a hard-core of `f'(x) = (f(x), b(x))`: the last bit of the image is `b x`. The
witness predictor ignores the length parameter, so `b` is also not a hard-core of `f'` in the sense
of [Goldreich, Definition 7.6][Goldreich2007DraftR4], whose predictor receives only `f'(x)`. -/
theorem not_hardCore_appendPredicate (f : List Bool → List Bool) (b : List Bool → Bool) :
    ¬ HardCore (appendPredicate f b) b := fun h => by
  have hneg := h.unpredictable lastBitPredictor computableInPolyTime_getLastD.isPPT
  rw [funext (predictionAdvantage_lastBitPredictor f b)] at hneg
  exact not_negligible_const (by norm_num) hneg

/-- **[Goldreich, Exercise 7.8][Goldreich2007DraftR4]: no universal hard-core predicate, in the
source's terms.** If a one-way function exists, then for every polynomial-time predicate `b` some
one-way function `g` (`OneWay`, Definition 7.1) has `b x` as the last bit of `g x`. The last bit
is computed from `g x` alone by a deterministic polynomial-time algorithm
(`Cslib.Crypto.computableInPolyTime_getLastD`), which therefore guesses `b x` from `g x` with
probability one. So `b` is not a hard-core of `g` in the sense of Definition 7.6, where the
predictor receives only `g x` and must have success below `1/2 + 1/p(n)`. The library's
`HardCore` also gives the predictor `n`; `Cslib.Crypto.OneWay.not_exists_universal_hardCore`
states the conclusion for it. -/
theorem OneWay.exists_oneWay_lastBit_eq {f : List Bool → List Bool} (hf : OneWay f)
    {b : List Bool → Bool} (hb : ComputableInPolyTime b encBits encBool) :
    ∃ g : List Bool → List Bool, OneWay g ∧ ∀ x, (g x).getLastD false = b x :=
  ⟨Cslib.Crypto.appendPredicate f b, hf.appendPredicate hb, fun _ => List.getLastD_concat⟩

/-- **No universal predicate for the library's `HardCore`.** If a one-way function exists,
then no predicate `b` is a hard-core (`HardCore`) of every one-way function
(`OneWay`). For polynomial-time `b` the witness is `f'(x) = (f(x), b(x))`
(`Cslib.Crypto.OneWay.appendPredicate`, `Cslib.Crypto.not_hardCore_appendPredicate`); `HardCore`
includes polynomial-time computability of `b`. `HardCore` gives its predictors the length `n` as
well, so it is stronger than Definition 7.6 and this conclusion is formally weaker than the
source's. The constructive theorem `Cslib.Crypto.OneWay.exists_oneWay_lastBit_eq` matches
Goldreich's exercise. -/
theorem OneWay.not_exists_universal_hardCore {f : List Bool → List Bool} (hf : OneWay f) :
    ¬ ∃ b : List Bool → Bool, ∀ g : List Bool → List Bool, OneWay g → HardCore g b :=
  fun ⟨b, hb⟩ => not_hardCore_appendPredicate f b (hb _ (hf.appendPredicate (hb f hf).polyTime))

end Cslib.Crypto
