/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.OneWay.Weak
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# A weak one-way function that is not strongly one-way

If one-way functions exist, then some weak one-way function is not strongly one-way
[Goldreich, Exercise 7.3][Goldreich2007DraftR4]
(`Cslib.Crypto.OneWay.exists_weakOneWay_not_oneWay`).

The draft gives no guideline. The construction lets the first input bit choose between the
identity and `f`: `g(1 x) = 1 x` and `g(0 x) = 0 f(x)` (`Cslib.Crypto.OneWayEasyHalf.easyHalf`).
Returning the challenge inverts `g` whenever the first bit is `1`, so with probability at least
one half, and `g` is not one-way. An inverter for `g` that succeeded with probability at least
`3/4` would invert `f` on the challenges `0 f(x)` with probability at least one half
(`Cslib.Crypto.OneWayEasyHalf.succProbability_inversionGame_succ_le`), so `g` is weakly one-way
with the polynomial `p(n) = 4` of Definition 7.4.

## Main definitions

* `Cslib.Crypto.OneWayEasyHalf.easyHalf`: identity on inputs starting with `1`, `f` on the rest.
* `Cslib.Crypto.OneWayEasyHalf.tailInverter`: the inverter for `f` built from one for `easyHalf f`.

## Main results

* `Cslib.Crypto.OneWayEasyHalf.weakOneWay`: `easyHalf f` is weakly one-way when `f` is one-way.
* `Cslib.Crypto.OneWayEasyHalf.not_oneWay`: `easyHalf f` is never strongly one-way.
* `Cslib.Crypto.OneWay.exists_weakOneWay_not_oneWay`: Goldreich, Exercise 7.3.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft `r4.pdf` of
  March 2007][Goldreich2007DraftR4], Exercise 7.3 (printed page 305, PDF page 41), with
  Definitions 7.1 and 7.4 (printed pages 269–270).
-/

@[expose] public section

namespace Cslib.Crypto

open Filter Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

namespace OneWayEasyHalf

/-- Identity on inputs whose first bit is `1`; `0 f(x)` on an input `0 x` (and on the empty
input, read as `0` followed by the empty word). -/
def easyHalf (f : List Bool → List Bool) (w : List Bool) : List Bool :=
  if w.headD false then w else false :: f w.tail

@[fun_prop]
theorem computableInPolyTime_easyHalf {f : List Bool → List Bool}
    (hf : ComputableInPolyTime f encBits encBits) :
    ComputableInPolyTime (easyHalf f) encBits encBits := by
  unfold easyHalf
  polytime

@[simp]
theorem easyHalf_false_cons (f : List Bool → List Bool) (x : List Bool) :
    easyHalf f (false :: x) = false :: f x := by
  simp [easyHalf]

@[simp]
theorem easyHalf_true_cons (f : List Bool → List Bool) (x : List Bool) :
    easyHalf f (true :: x) = true :: x := by
  simp [easyHalf]

/-- A preimage of `0 f(x)` under `easyHalf f` has a tail that is a preimage of `f x`. -/
theorem easyHalf_eq_false_cons {f : List Bool → List Bool} {z y : List Bool}
    (h : easyHalf f z = false :: y) : f z.tail = y := by
  unfold easyHalf at h
  split at h
  · subst h
    simp_all
  · exact (List.cons.inj h).2

/-- The inverter for `f` from an inverter for `easyHalf f`: prefix the challenge with `0`, run the
given inverter one length up and drop the first bit of its candidate. -/
def tailInverter (adversary : Inverter) : Inverter :=
  fun n image => List.tail <$> adversary (n + 1) (false :: image)

@[program_certificate]
theorem isPPT_tailInverter {adversary : Inverter} (ha : IsPPT encBits adversary) :
    IsPPT encBits (tailInverter adversary) := by
  unfold tailInverter
  ppt

/-- **Inversion reduction.** At length `n + 1`, half of the inputs are easy, and on the other half
the inverter for `easyHalf f` is an inverter for `f` at length `n`. -/
theorem succProbability_inversionGame_succ_le (f : List Bool → List Bool) (adversary : Inverter)
    (n : ℕ) :
    (Game.succProbability (ProbComp.eval (inversionGame (easyHalf f) adversary (n + 1))) : ℝ) ≤
      1 / 2 + 1 / 2 *
        Game.succProbability (ProbComp.eval (inversionGame f (tailInverter adversary) n)) := by
  have h : ProbComp.eval (inversionGame (easyHalf f) adversary (n + 1)) true ≤
      2⁻¹ + 2⁻¹ * ProbComp.eval (inversionGame f (tailInverter adversary) n) true := by
    simp only [inversionGame, inversionExperiment, tailInverter, ProbComp.eval_bind,
      ProbComp.eval_pure, ProbComp.eval_map, BitString.eval_sampleList, BitString.uniformList_succ,
      PMF.bind_bind, PMF.bind_map]
    rw [PMF.bind_apply, tsum_bool]
    simp only [PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat]
    rw [add_comm]
    gcongr
    · exact mul_le_of_le_one_right' (PMF.coe_le_one _ _)
    · refine PMF.bind_apply_mono_on_support _ _ fun x _ => ?_
      simp only [Function.comp_apply, easyHalf_false_cons]
      refine PMF.bind_apply_mono_on_support _ _ fun z _ => ?_
      by_cases hz : easyHalf f z = false :: f x
      · rw [Function.comp_apply, easyHalf_eq_false_cons hz, beq_self_eq_true, PMF.pure_apply_self]
        exact PMF.coe_le_one _ _
      · rw [beq_false_of_ne hz]
        simp
  have hfin : 2⁻¹ * ProbComp.eval (inversionGame f (tailInverter adversary) n) true ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) (PMF.apply_ne_top _ _)
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨by simp, hfin⟩) h
  rw [ENNReal.toReal_add (by simp) hfin, ENNReal.toReal_mul,
    ENNReal.toReal_inv] at hreal
  simpa [Game.coe_succProbability] using hreal

/-- Returning the challenge inverts `easyHalf f` with probability at least one half at every
positive length. -/
theorem half_le_succProbability_inversionGame_id (f : List Bool → List Bool) (n : ℕ) :
    1 / 2 ≤ Game.succProbability
      (ProbComp.eval (inversionGame (easyHalf f) (fun _ image => pure image) (n + 1))) := by
  have h : (2⁻¹ : ℝ≥0∞) ≤
      ProbComp.eval (inversionGame (easyHalf f) (fun _ image => pure image) (n + 1)) true := by
    simp only [inversionGame, inversionExperiment, ProbComp.eval_bind, ProbComp.eval_pure,
      BitString.eval_sampleList, BitString.uniformList_succ, PMF.bind_bind, PMF.bind_map]
    rw [PMF.bind_apply, tsum_bool]
    simp [PMF.uniformOfFintype_apply]
  calc (1 / 2 : ℝ≥0) = (2⁻¹ : ℝ≥0∞).toNNReal := by simp [ENNReal.toNNReal_ofNat]
    _ ≤ _ := ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) h

/-- `easyHalf f` is weakly one-way when `f` is one-way: every efficient inverter fails with
probability strictly greater than `1/4` from some length on. -/
theorem weakOneWay {f : List Bool → List Bool} (hf : OneWay f) : WeakOneWay (easyHalf f) := by
  refine ⟨Polynomial.C 4, fun _ => by simp, ⟨computableInPolyTime_easyHalf hf.polyTime, ?_⟩⟩
  intro adversary ha
  obtain ⟨m, hm⟩ := eventually_atTop.1
    (hf.weakOneWayAt_half.weak _ (isPPT_tailInverter ha))
  filter_upwards [eventually_ge_atTop (m + 1)] with N hN
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hsmall := hm n (by omega)
  simp only [Polynomial.eval_C, Nat.cast_ofNat]
  linarith [succProbability_inversionGame_succ_le f adversary n]

/-- `easyHalf f` is not one-way, for every `f`: returning the challenge succeeds with probability
at least one half. -/
theorem not_oneWay (f : List Bool → List Bool) : ¬ OneWay (easyHalf f) := fun hf => by
  obtain ⟨m, hm⟩ := (negligible_iff _).1
    (hf.inversion_negligible (fun _ image => pure image) (by ppt)) 0 (1 / 2) (by norm_num)
  have := hm (m + 1) (by omega)
  rw [pow_zero, one_mul] at this
  exact (half_le_succProbability_inversionGame_id f m).not_gt this

end OneWayEasyHalf

open OneWayEasyHalf

/-- **[Goldreich, Exercise 7.3][Goldreich2007DraftR4]**: if one-way functions exist, then some
weak one-way function is not strongly one-way. Weak one-wayness is `Cslib.Crypto.WeakOneWay`
(Definition 7.4: some positive polynomial `p` bounds the failure probability of every uniform
strict PPT inverter below by `1 / p(n)` for all sufficiently large `n`); strong one-wayness is
`Cslib.Crypto.OneWay` (Definition 7.1). -/
theorem OneWay.exists_weakOneWay_not_oneWay {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ g : List Bool → List Bool, WeakOneWay g ∧ ¬ OneWay g :=
  ⟨easyHalf f, OneWayEasyHalf.weakOneWay hf, OneWayEasyHalf.not_oneWay f⟩

end Cslib.Crypto
