/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification
public import CslibFrontier.Computability.Circuit.Boolean.Synthesis
public import CslibFrontier.Probability.PMF.Expect
public import CslibFrontier.Probability.StatisticalDistance.ClosedForm
public import CslibFrontier.Probability.StatisticalDistance.Product

/-!
# Values of a hard function on independent samples

If no circuit of size `S` predicts a Boolean function `f` with advantage more than `ε`, then the
values `f(x₁) ⋯ f(xₘ)` on independent uniform inputs are within statistical distance `ε m` of
`m` uniform bits (`Cslib.Circuits.Boolean.dist_iid_map_uniformOfFintype_le`)
[Arora and Barak, Exercise 16.11][AroraBarak09], reading the exercise's undefined
"`(S, ε)`-hard" this way. The constant circuits already show that `f` is
`ε`-close to balanced, and independent coordinates add their distances
(`Cslib.Probability.PMF.dist_iid_le`).

## Main results

* `Cslib.Circuits.Boolean.dist_iid_map_uniformOfFintype_le`: Arora–Barak Exercise 16.11, under
  the interpretation of "`(S, ε)`-hard" stated below.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], draft of
  2007-01-08, Chapter 16, Exercise 11
-/

public section

namespace Cslib.Circuits.Boolean

open Finset Cslib.Probability.PMF PMF

variable {n : ℕ}

/-- **Samples of a hard function look uniform** [Arora and Barak, Exercise 16.11]. Let every
Boolean function of De Morgan circuit complexity at most `S` agree with `f` on at most a
`1 / 2 + ε` fraction of the inputs, where `S ≥ 1`, so that the constant functions (one gate each)
are among them. Then `f(x₁) ⋯ f(xₘ)`, for independent uniform `x₁, …, xₘ`, is within statistical
distance `ε m` of `m` uniform bits.

The draft does not define "`(S, ε)`-hard". The premise is this file's interpretation of it, with
two parameters: every function of complexity at most `S` agrees with `f` on at most a `1 / 2 + ε`
fraction of the inputs, and `S ≥ 1`. It is not derived from Definition 16.2, which concerns the
indistinguishability of distributions. With `ε = 1 / S` it is `IsAverageCaseHard f S`, the draft's
average-case hardness `H_avg(f) ≥ S` (Definition 16.7) with the strict bound `< 1 / 2 + 1 / S`
relaxed to `≤`; the relaxed premise is weaker, so the bound applies to every `f` with
`H_avg(f) ≥ S`. Separating `ε` from `S` allows advantages other than `1 / S`. -/
theorem dist_iid_map_uniformOfFintype_le {f : BooleanFunction n} {S : ℕ} {ε : ℝ} (hS : 1 ≤ S)
    (hf : ∀ g : BooleanFunction n, complexity interpretation (single g) ≤ S →
      (#{x | g x = f x} : ℝ) / 2 ^ n ≤ 1 / 2 + ε) (m : ℕ) :
    dist (iid ((uniformOfFintype (BitString n)).map f) m) (iid (uniformOfFintype Bool) m) ≤
      ε * m := by
  -- The constant functions bound the bias of `f`.
  have hconst (b : Bool) : (#{x : BitString n | b = f x} : ℝ) / 2 ^ n ≤ 1 / 2 + ε :=
    hf (fun _ => b)
      ((Synthesis.of_forall_eq_const (s := inputs n) b fun _ => rfl).complexity_le.trans hS)
  have hsplit : (#{x : BitString n | true = f x} : ℝ) / 2 ^ n +
      (#{x : BitString n | false = f x} : ℝ) / 2 ^ n = 1 := by
    have e : (univ.filter fun x : BitString n => ¬ true = f x) =
        univ.filter fun x => false = f x :=
      filter_congr fun x _ => by cases f x <;> decide
    have h : (#{x : BitString n | true = f x} : ℝ) + #{x : BitString n | false = f x} = 2 ^ n := by
      simpa [e, BitString] using congrArg (Nat.cast (R := ℝ))
        (card_filter_add_card_filter_not (s := (univ : Finset (BitString n))) (true = f ·))
    rw [← add_div, h, div_self (by positivity)]
  have hp : ((uniformOfFintype (BitString n)).map f true).toReal =
      (#{x : BitString n | true = f x} : ℝ) / 2 ^ n := by
    rw [toReal_uniformOfFintype_map_apply_true, dens, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin]
    simp only [eq_comm (b := true), Nat.cast_pow, Nat.cast_ofNat, NNRat.cast_div,
      NNRat.cast_natCast, NNRat.cast_pow, NNRat.cast_ofNat]
  have h1 : dist ((uniformOfFintype (BitString n)).map f) (uniformOfFintype Bool) ≤ ε := by
    have hu : ((uniformOfFintype Bool) true).toReal = 1 / 2 := by simp [uniformOfFintype_apply]
    rw [dist_bool, hp, hu, abs_le]
    exact ⟨by linarith [hconst false],
      by linarith [hconst true]⟩
  calc _ ≤ m * dist ((uniformOfFintype (BitString n)).map f) (uniformOfFintype Bool) :=
        dist_iid_le _ _ m
    _ ≤ m * ε := by gcongr
    _ = ε * m := mul_comm _ _

end Cslib.Circuits.Boolean
