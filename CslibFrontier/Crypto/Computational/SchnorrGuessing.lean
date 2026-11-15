/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SchnorrEavesdrop
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip
import CslibFrontier.Foundations.Data.ZMod.NatCast
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PPT

/-!
# Guessing attacks on Schnorr identification

This module formalizes the word-level guessing impersonator against Schnorr identification
([BonehShoup2023], Section 19.1.1). Given a challenge-length schedule `k : ℕ → ℕ`, the
impersonator runs the word-level transcript simulator `schnorrSimulatedTranscript` on a uniform
`k n`-bit challenge, outputs the resulting commitment, stores the simulated response, and
returns it for every challenge.

## Main definitions

- `Cslib.Crypto.PrimeOrderGroupFamily.schnorrGuessingImpersonator`: the word-level guessing
  impersonator against `PrimeOrderGroupFamily.schnorrDirectGame`.

## Main results

- `Cslib.Crypto.PrimeOrderGroupFamily.inv_two_pow_le_succProbability_schnorrDirectGame`:
  the guessing impersonator wins `schnorrDirectGame setup k` with probability at least
  `1 / 2 ^ k n`, for every `setup` and without hypotheses on `k`.
- `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_schnorrGuessingImpersonator`: when `k` is
  computable in polynomial time in unary, `schnorrGuessingImpersonator k` is uniform strict PPT.
- `Cslib.Crypto.PrimeOrderGroupFamily.not_negligible_schnorrDirectGame_schnorrGuessingImpersonator`:
  if `1 / 2 ^ k n` is not negligible, the guessing impersonator's success probability is not
  negligible.
- `Cslib.Crypto.PrimeOrderGroupFamily.negligible_inv_two_pow_of_negligible_schnorrDirectGame`:
  if `k` is unary poly-time computable and every uniform strict PPT impersonator has negligible
  success probability, then `1 / 2 ^ k n` is negligible (converse to the challenge-length
  premise of `negligible_schnorrDirectGame`).

## References

* [BonehShoup2023] D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6, Section 19.1.1.
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Protocols
open scoped NNReal ENNReal

variable {F : PrimeOrderGroupFamily}

variable (F) in
/-- **The guessing impersonator against Schnorr identification** ([BonehShoup2023],
Section 19.1.1) with `k n`-bit challenges: prepare a simulated conversation `(t, c, z)` for a
uniform `k n`-bit challenge `c`, send `t`, keep `z` as the state, and answer every challenge with
`z`. -/
noncomputable def schnorrGuessingImpersonator (k : ℕ → ℕ) : F.SchnorrImpersonator where
  commit n input := do
    let (t, _, z) ← F.schnorrSimulatedTranscript n input.1 input.2 (k n)
    return (t, z)
  respond _ input := pure input.1

/-- **The guessing impersonator succeeds with probability at least `1 / 2 ^ k n`**
([BonehShoup2023], Section 19.1.1), for every setup and with no condition on `k`. -/
theorem inv_two_pow_le_succProbability_schnorrDirectGame (setup : ℕ → PMF F.Desc) (k : ℕ → ℕ)
    (n : ℕ) :
    (1 : ℝ≥0) / 2 ^ k n ≤
      Game.succProbability (F.schnorrDirectGame setup k (F.schnorrGuessingImpersonator k) n) := by
  have key : (1 : ℝ≥0∞) / 2 ^ k n ≤
      F.schnorrDirectGame setup k (F.schnorrGuessingImpersonator k) n true := by
    simp only [schnorrDirectGame, schnorrGuessingImpersonator, pmf_norm]
    refine PMF.le_bind_apply_on_support _ fun d _ => ?_
    refine PMF.le_bind_apply_on_support _ fun α _ => ?_
    rw [eval_schnorrSimulatedTranscript]
    simp only [PMF.bind_bind, PMF.map, PMF.pure_bind, Function.comp_apply]
    refine PMF.le_bind_apply_on_support _ fun c₀ hc₀ => ?_
    refine PMF.le_bind_apply_on_support _ fun z _ => ?_
    obtain ⟨r₀, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hc₀
    rw [BitString.uniformList, PMF.map, PMF.bind_bind, PMF.bind_apply]
    refine le_trans ?_ (le_tsum _ r₀)
    simp [PMF.uniformOfFintype_apply]
  rw [Game.succProbability, ← ENNReal.toNNReal_coe ((1 : ℝ≥0) / 2 ^ k n)]
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) ?_
  rwa [ENNReal.coe_div (by positivity), ENNReal.coe_one, ENNReal.coe_pow, ENNReal.coe_ofNat]

/-- **The guessing impersonator is uniform strict PPT** when the challenge length is computable in
polynomial time. -/
theorem isPPT_schnorrGuessingImpersonator {k : ℕ → ℕ}
    (hk : ComputableInPolyTime k encUnary encUnary) : (F.schnorrGuessingImpersonator k).IsPPT := by
  have hk' := hk.tidy
  refine ⟨?_, ?_⟩
  · have h := F.isPPTOn_schnorrSimulatedTranscript
      (encIn := encPair encUnary (encPair F.encDesc encBits))
      (n := fun p => p.1) (d := fun p => p.2.1) (u := fun p => p.2.2) (m := fun p => k p.1)
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    exact h.bind_with ((ComputableInPolyTime.tidy (by fun_prop)).isPPTOn)
  · exact (ComputableInPolyTime.tidy (by fun_prop)).isPPTOn

/-- **Short challenges make Schnorr identification insecure** ([BonehShoup2023], Section 19.1.1):
if `1 / 2 ^ k n` is not negligible, the guessing impersonator's success probability is not
negligible. With `isPPT_schnorrGuessingImpersonator` this shows that the hypothesis `hchallenge`
of `negligible_schnorrDirectGame` is necessary. -/
theorem not_negligible_schnorrDirectGame_schnorrGuessingImpersonator (setup : ℕ → PMF F.Desc)
    {k : ℕ → ℕ} (hchallenge : ¬ Negligible fun n => (1 : ℝ≥0) / 2 ^ k n) :
    ¬ Negligible fun n =>
      Game.succProbability (F.schnorrDirectGame setup k (F.schnorrGuessingImpersonator k) n) :=
  fun h => hchallenge (negligible_of_le h
    fun n => inv_two_pow_le_succProbability_schnorrDirectGame setup k n)

/-- **Negligible `1 / 2 ^ k n` is necessary for security against direct attacks**: if every uniform
strict PPT impersonator succeeds with negligible probability, the challenge space is of
super-polynomial size. The proof instantiates the universal quantifier at
`schnorrGuessingImpersonator k`, using `isPPT_schnorrGuessingImpersonator hk` to discharge its
uniform strict-PPT hypothesis. The converse, under the discrete-logarithm assumption, is
`negligible_schnorrDirectGame`. -/
theorem negligible_inv_two_pow_of_negligible_schnorrDirectGame (setup : ℕ → PMF F.Desc) {k : ℕ → ℕ}
    (hk : ComputableInPolyTime k encUnary encUnary)
    (h : ∀ A : F.SchnorrImpersonator, A.IsPPT →
      Negligible fun n => Game.succProbability (F.schnorrDirectGame setup k A n)) :
    Negligible fun n => (1 : ℝ≥0) / 2 ^ k n :=
  negligible_of_le (h _ (isPPT_schnorrGuessingImpersonator hk))
    fun n => inv_two_pow_le_succProbability_schnorrDirectGame setup k n

end Cslib.Crypto.PrimeOrderGroupFamily
