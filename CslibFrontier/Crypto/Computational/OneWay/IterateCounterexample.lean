/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.OneWay
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Crypto.Computational.OneWay.Normalize
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Support
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Tactic.PolyTime
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# A one-way function whose iterates are not one-way

If one-way functions exist, then some one-way function `f` has iterates `x ↦ f^[k |x|] x` that
are not one-way, for every count `k` with `k n ≥ 2` for all large `n`
([AroraBarak07], Chapter 10, Exercise 4). In particular this holds for `k n = ⌈n ^ c⌉` with any
real `c > 0`. By contrast, iterating a one-way *permutation* by an efficiently computable count
that is eventually positive gives a one-way permutation; a count of zero gives the identity.

The construction starts from a one-way function `g` whose output length depends only on the
input length (`OneWay.exists_fixedOutputLength`). Call a word *low-zero* when its first
`⌊|w| / 2⌋` bits are all `false`. Then

* `f x = 0^(|x| + 2 |g x| + 1)` when `x` is low-zero, and
* `f x = 0^(|x| + |g x|) ++ 1 :: g x` otherwise.

Both branches have length `|x| + 2 |g x| + 1`, so `f` has a single output length `m n` at each
input length `n`, as in the family of Definition 10.1. Every image of `f` is low-zero, so
`f (f x)` is the all-zero word whose length depends only on `|x|`. All inputs of one length
therefore share their second image, and every later iterate. The inverter for any iterate with at
least two steps simply answers `0^n`. Inverting `f` itself still means inverting `g`, except on
low-zero inputs, which have probability at most `2^-(n / 2)`. The marker bit `1` makes the
challenge determine `g x`.

## Main definitions

* `Cslib.Crypto.IterateCounterexample.collapse`: the one-way function `f` built from `g`.

## Main results

* `Cslib.Crypto.IterateCounterexample.oneWay_collapse`: `f` is one-way when `g` is one-way, through
  the strict-PPT reduction `markInverter` (`isPPT_markInverter`).
* `Cslib.Crypto.IterateCounterexample.length_collapse`,
  `Cslib.Crypto.IterateCounterexample.iterate_collapse_eq`: fixed output length, and equal second
  images for inputs of equal length.
* `Cslib.Crypto.IterateCounterexample.not_oneWay_iterate_collapse`: every iterate with eventually
  at least two steps is not one-way.
* `Cslib.Crypto.exists_oneWay_not_oneWay_iterate`,
  `Cslib.Crypto.exists_oneWay_not_oneWay_iterate_ceil_rpow`: the exercise, with a witness of
  polynomial-time fixed output length.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft
  2007-01-08][AroraBarak07], Chapter 10, Exercise 4, printed p. 204 (PDF p. 220).
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

namespace IterateCounterexample

/-- A word is low-zero when its first `⌊|w| / 2⌋` bits are all `false`. -/
def lowZero (w : List Bool) : Bool :=
  decide (w.take (w.length / 2) = List.replicate (w.length / 2) false)

/-- The marked image of a value `w` at input length `n`: `n + |w|` zeros, a `true` marker, then
`w`. -/
def mark (n : ℕ) (w : List Bool) : List Bool :=
  List.replicate (n + w.length) false ++ true :: w

/-- The one-way function whose iterates collapse: on a low-zero input `x`, the all-zero word of
the marked image's length `|x| + 2 |g x| + 1`; otherwise the marked image of `g x`. -/
def collapse (g : List Bool → List Bool) (x : List Bool) : List Bool :=
  if lowZero x then List.replicate (x.length + 2 * (g x).length + 1) false
  else mark x.length (g x)

private theorem lowZero_replicate (m : ℕ) : lowZero (List.replicate m false) = true := by
  simp [lowZero, List.take_replicate, Nat.div_le_self]

private theorem lowZero_mark (n : ℕ) (w : List Bool) : lowZero (mark n w) = true := by
  have hle : (mark n w).length / 2 ≤ (List.replicate (n + w.length) false).length := by
    simp only [mark, List.length_append, List.length_replicate, List.length_cons]
    omega
  simp only [lowZero, decide_eq_true_eq]
  unfold mark at hle ⊢
  rw [List.take_append_of_le_length hle, List.take_replicate,
    Nat.min_eq_left (by simpa using hle)]

/-- Every image of `collapse g` is low-zero. -/
private theorem lowZero_collapse (g : List Bool → List Bool) (x : List Bool) :
    lowZero (collapse g x) = true := by
  unfold collapse
  split
  · exact lowZero_replicate _
  · exact lowZero_mark _ _

/-- A marked image determines its value. -/
private theorem eq_of_mark_eq {n m : ℕ} {u v : List Bool} (h : mark n u = mark m v) : u = v := by
  unfold mark at h
  generalize n + u.length = p at h
  generalize m + v.length = q at h
  induction p generalizing q with
  | zero => cases q <;> simp_all [List.replicate_succ]
  | succ p ih => cases q <;> simp_all [List.replicate_succ]

private theorem collapse_of_lowZero (g : List Bool → List Bool) {w : List Bool}
    (hw : lowZero w = true) :
    collapse g w = List.replicate (w.length + 2 * (g w).length + 1) false := by
  rw [collapse, ite_eq_left hw]

/-- Both branches of `collapse g` have length `|x| + 2 |g x| + 1`. With `g` of fixed output
length, `collapse g` therefore has fixed output length too. -/
theorem length_collapse (g : List Bool → List Bool) (x : List Bool) :
    (collapse g x).length = x.length + 2 * (g x).length + 1 := by
  unfold collapse mark
  split <;> simp only [List.length_replicate, List.length_append, List.length_cons]
  omega

/-- **Second images coincide.** If `g` has fixed output length, then at least two steps of
`collapse g` send all inputs of the same length to the same word. -/
theorem iterate_collapse_eq {g : List Bool → List Bool} {length : ℕ → ℕ}
    (hlen : ∀ input, (g input).length = length input.length) (j : ℕ) {x y : List Bool}
    (hxy : x.length = y.length) : (collapse g)^[j + 2] x = (collapse g)^[j + 2] y := by
  have hfirst : (collapse g x).length = (collapse g y).length := by
    rw [length_collapse, length_collapse, hlen, hlen, hxy]
  have hsecond : collapse g (collapse g x) = collapse g (collapse g y) := by
    rw [collapse_of_lowZero g (lowZero_collapse g x), collapse_of_lowZero g (lowZero_collapse g y),
      hlen (collapse g x), hlen (collapse g y), hfirst]
  rw [Function.iterate_add_apply, Function.iterate_add_apply]
  exact congrArg _ hsecond

/-- **Iterates of `collapse g` are not one-way.** For `g` of fixed output length and a count `k`
with `k n ≥ 2` for all large `n`, the constant inverter answering `0^n` inverts
`x ↦ (collapse g)^[k |x|] x` with probability one at every such length. -/
theorem not_oneWay_iterate_collapse {g : List Bool → List Bool} {length : ℕ → ℕ}
    (hlen : ∀ input, (g input).length = length input.length) {k : ℕ → ℕ}
    (hk : ∀ᶠ n in Filter.atTop, 2 ≤ k n) :
    ¬ OneWay (fun x => (collapse g)^[k x.length] x) := by
  intro hf
  have hzeros : ComputableInPolyTime (fun p : ℕ × List Bool => List.replicate p.1 false)
      (encPair encUnary encBits) encBits := by polytime
  have hPPT : IsPPT encBits
      (fun n _ => (pure (List.replicate n false) : ProbComp (List Bool))) := hzeros.isPPTOn
  refine not_negligible_const one_ne_zero ((hf.inversion_negligible _ hPPT).congr' ?_)
  filter_upwards [hk] with n hn
  obtain ⟨j, hj⟩ : ∃ j, k n = j + 2 := ⟨k n - 2, by omega⟩
  have hgame : ProbComp.eval (inversionGame (fun x => (collapse g)^[k x.length] x)
      (fun n _ => pure (List.replicate n false)) n) = PMF.pure true := by
    have heval : ProbComp.eval (inversionGame (fun x => (collapse g)^[k x.length] x)
        (fun n _ => pure (List.replicate n false)) n) =
        (BitString.uniformList n).map fun x =>
          (collapse g)^[k (List.replicate n false).length] (List.replicate n false) ==
            (collapse g)^[k x.length] x := by
      simp [inversionGame, inversionExperiment]
    refine heval.trans (Cslib.Probability.PMF.map_eq_pure_iff.mpr fun x hx => ?_)
    have hxn : x.length = n := BitString.length_of_mem_support_uniformList hx
    rw [List.length_replicate, hxn, hj, iterate_collapse_eq hlen j (x := List.replicate n false)
      (y := x) (by rw [List.length_replicate, hxn]), beq_self_eq_true]
  simp [Game.succProbability, hgame]

/-- The inverter for `g` built from an inverter for `collapse g`: mark the challenge. -/
def markInverter (adversary : Inverter) : Inverter :=
  fun n w => adversary n (mark n w)

/-- `markInverter adversary` is uniform strict PPT when `adversary` is. -/
theorem isPPT_markInverter {adversary : Inverter} (hadversary : IsPPT encBits adversary) :
    IsPPT encBits (markInverter adversary) := by
  have hprepare : ComputableInPolyTime (fun p : ℕ × List Bool => mark p.1 p.2)
      (encPair encUnary encBits) encBits := by
    unfold mark
    polytime
  exact hadversary.preprocess (ComputableInPolyTime.fst encUnary encBits) hprepare

/-- Inverting `collapse g` succeeds at most as often as inverting `g` with the marked challenge,
plus the probability `2^-(n / 2)` of a low-zero input. -/
theorem succProbability_inversionGame_collapse_le (g : List Bool → List Bool)
    (adversary : Inverter) (n : ℕ) :
    Game.succProbability (ProbComp.eval (inversionGame (collapse g) adversary n)) ≤
      Game.succProbability (ProbComp.eval (inversionGame g (markInverter adversary) n)) +
        (1 / 2) ^ (n / 2) := by
  have hlow : (BitString.uniformList n).bind (fun x => PMF.pure (lowZero x)) true ≤
      ((1 / 2 : ℝ≥0) ^ (n / 2) : ℝ≥0) := by
    have hcongr : (BitString.uniformList n).bind (fun x => PMF.pure (lowZero x)) =
        ((BitString.uniformList n).map (List.take (n / 2))).bind
          (fun w => PMF.pure (decide (w = List.replicate (n / 2) false))) := by
      rw [PMF.bind_map]
      refine PMF.bind_congr_on_support _ _ _ fun x hx => ?_
      rw [Function.comp_apply, lowZero, BitString.length_of_mem_support_uniformList hx]
    rw [hcongr, PMF.bind_pure_decide_eq_apply_true',
      BitString.uniformList_take (Nat.div_le_self n 2)]
    refine (BitString.uniformList_apply_le _ _).trans_eq ?_
    rw [ENNReal.coe_pow, one_div, one_div, ENNReal.coe_inv two_ne_zero, ENNReal.coe_ofNat,
      ENNReal.inv_pow]
  have key : ProbComp.eval (inversionGame (collapse g) adversary n) true ≤
      ProbComp.eval (inversionGame g (markInverter adversary) n) true +
        ((1 / 2 : ℝ≥0) ^ (n / 2) : ℝ≥0) := by
    refine le_trans ?_ (add_le_add le_rfl hlow)
    simp only [inversionGame, inversionExperiment, markInverter, ProbComp.eval_bind,
      ProbComp.eval_pure, BitString.eval_sampleList]
    refine PMF.bind_apply_le_add_on_support _ true fun x hx => ?_
    have hxn : x.length = n := BitString.length_of_mem_support_uniformList hx
    by_cases hx : lowZero x = true
    · rw [hx, PMF.pure_apply_self]
      exact le_add_left (PMF.coe_le_one _ _)
    · refine le_add_right ?_
      have himage : collapse g x = mark n (g x) := by rw [collapse, ite_eq_right hx, hxn]
      rw [himage]
      refine PMF.bind_apply_mono_on_support _ true fun candidate _ => ?_
      cases hwin : (collapse g candidate == mark n (g x))
      · simp
      · have heq := beq_iff_eq.1 hwin
        have hg : g candidate = g x := by
          unfold collapse at heq
          split at heq
          · exfalso
            have := congrArg (fun w => true ∈ w) heq
            simp [mark] at this
          · exact eq_of_mark_eq heq
        simp [hg]
  unfold Game.succProbability
  refine (ENNReal.toNNReal_mono (ENNReal.add_ne_top.2 ⟨PMF.apply_ne_top _ _, ENNReal.coe_ne_top⟩)
    key).trans_eq ?_
  rw [ENNReal.toNNReal_add (PMF.apply_ne_top _ _) ENNReal.coe_ne_top, ENNReal.toNNReal_coe]

/-- **`collapse g` is one-way** when `g` is one-way. -/
theorem oneWay_collapse {g : List Bool → List Bool} (hg : OneWay g) : OneWay (collapse g) := by
  have hpoly := hg.polyTime
  refine OneWay.of_inversion_negligible (by unfold collapse lowZero mark; polytime)
    fun adversary hadversary => ?_
  have hε := (hg.inversion_negligible _ (isPPT_markInverter hadversary)).add
    ((negligible_geometric (by norm_num : (1 / 2 : ℝ≥0) < 1)).div_const (by norm_num : 0 < 2))
  exact negligible_of_le hε fun n => succProbability_inversionGame_collapse_le g adversary n

end IterateCounterexample

open IterateCounterexample

/-- **Iterates of one-way functions need not be one-way** ([AroraBarak07], Chapter 10,
Exercise 4). If a one-way function exists, then some one-way function `f` has a single output
length `m n` for all inputs of length `n` (with `m` polynomial-time in unary), as in the family of
Definition 10.1, and `x ↦ f^[k |x|] x` is not one-way for every count `k` with `k n ≥ 2` for all
large `n`. -/
theorem exists_oneWay_not_oneWay_iterate (h : ∃ g : List Bool → List Bool, OneWay g) :
    ∃ f : List Bool → List Bool, OneWay f ∧
      (∃ m : ℕ → ℕ, (∀ x, (f x).length = m x.length) ∧
        ComputableInPolyTime m encUnary encUnary) ∧
      ∀ k : ℕ → ℕ, (∀ᶠ n in Filter.atTop, 2 ≤ k n) → ¬ OneWay (fun x => f^[k x.length] x) := by
  obtain ⟨g₀, hg₀⟩ := h
  obtain ⟨g, length, hg, hlen, hlength⟩ := hg₀.exists_fixedOutputLength
  refine ⟨collapse g, oneWay_collapse hg, ⟨fun n => n + 2 * length n + 1, fun x => ?_, by fun_prop⟩,
    fun k hk => not_oneWay_iterate_collapse hlen hk⟩
  rw [length_collapse, hlen]

/-- **The exercise's counts** ([AroraBarak07], Chapter 10, Exercise 4): if a one-way function
exists, then some one-way function `f` with polynomial-time fixed output length has
`x ↦ f^[⌈|x| ^ c⌉] x` not one-way for every real `c > 0`. -/
theorem exists_oneWay_not_oneWay_iterate_ceil_rpow (h : ∃ g : List Bool → List Bool, OneWay g) :
    ∃ f : List Bool → List Bool, OneWay f ∧
      (∃ m : ℕ → ℕ, (∀ x, (f x).length = m x.length) ∧
        ComputableInPolyTime m encUnary encUnary) ∧
      ∀ c : ℝ, 0 < c → ¬ OneWay (fun x => f^[⌈(x.length : ℝ) ^ c⌉₊] x) := by
  obtain ⟨f, hf, hm, hiter⟩ := exists_oneWay_not_oneWay_iterate h
  refine ⟨f, hf, hm, fun c hc => hiter (fun n => ⌈(n : ℝ) ^ c⌉₊) ?_⟩
  have hlim := (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually_ge_atTop 2] with n hn
  exact_mod_cast (show (2 : ℝ) ≤ ⌈(n : ℝ) ^ c⌉₊ from hn.trans (Nat.le_ceil _))

end Cslib.Crypto
