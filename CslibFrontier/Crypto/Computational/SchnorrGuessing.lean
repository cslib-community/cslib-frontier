/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SchnorrEavesdrop
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PPT

/-!
# Guessing attacks on Schnorr identification

This module formalizes the word-level guessing impersonator against Schnorr identification
([BonehShoup2023], Section 19.1.1). Given a challenge-length schedule `m : ℕ → ℕ`, the
impersonator runs the word-level transcript simulator `schnorrSimulatedTranscript` on a uniform
`m n`-bit challenge, outputs the resulting commitment, stores the simulated response, and
returns it for every challenge.

## Main definitions

- `Cslib.Crypto.PrimeOrderGroupFamily.schnorrGuessingImpersonator`: the word-level guessing
  impersonator against `PrimeOrderGroupFamily.schnorrDirectGame`.

## Main results

- `Cslib.Crypto.PrimeOrderGroupFamily.inv_two_pow_le_succProbability_schnorrDirectGame`:
  for every `setup`, `k`, `m`, and `n` with `m n ≤ k n`, `schnorrGuessingImpersonator m` wins
  `schnorrDirectGame setup k` with probability at least `1 / 2 ^ k n` (a lower bound where
  Section 19.1.1 / Exercise 19.7 states probability `1/|C|`).
- `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_schnorrGuessingImpersonator`: when `m` is
  computable in polynomial time in unary (`ComputableInPolyTime m encUnary encUnary`),
  `schnorrGuessingImpersonator m` is uniform strict PPT.
- `Cslib.Crypto.PrimeOrderGroupFamily.negligible_inv_two_pow_of_negligible_schnorrDirectGame`:
  for every `setup` and `k : ℕ → ℕ`, if every uniform strict-PPT impersonator has negligible
  success probability in `schnorrDirectGame setup k`, then `1 / 2 ^ k n` is negligible
  (proved at `m := fun _ => 0`, requiring no efficiency hypothesis on `k`).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 19.1.1.
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
([BonehShoup2023], Section 19.1.1) whenever the prepared-challenge length satisfies `m n ≤ k n`
(proved here as a lower bound where Exercise 19.7 says "probability `1/|C|`"). The bound allows a
separate schedule `m` because `ofBits` zero-pads shorter simulated challenges so they match a
verifier challenge with probability at least `1 / 2 ^ k n` even for `m = fun _ => 0`; when
`m n > k n`, `ofBits` on an `m n`-bit simulated challenge can lie outside the range of `k n`-bit
verifier challenges, so `hm` cannot be dropped. -/
theorem inv_two_pow_le_succProbability_schnorrDirectGame (setup : ℕ → PMF F.Desc)
    (k m : ℕ → ℕ) (n : ℕ) (hm : m n ≤ k n) :
    (1 : ℝ≥0) / 2 ^ k n ≤
      Game.succProbability (F.schnorrDirectGame setup k (F.schnorrGuessingImpersonator m) n) := by
  have key : (1 : ℝ≥0∞) / 2 ^ k n ≤
      F.schnorrDirectGame setup k (F.schnorrGuessingImpersonator m) n true := by
    simp only [schnorrDirectGame, schnorrGuessingImpersonator, pmf_norm]
    refine PMF.le_bind_apply_on_support _ fun d _ => ?_
    refine PMF.le_bind_apply_on_support _ fun α _ => ?_
    rw [eval_schnorrSimulatedTranscript]
    simp only [PMF.bind_bind, PMF.map, PMF.pure_bind, Function.comp_apply]
    refine PMF.le_bind_apply_on_support _ fun c₀ hc₀ => ?_
    refine PMF.le_bind_apply_on_support _ fun z _ => ?_
    obtain ⟨r₀, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hc₀
    rw [BitString.uniformList, PMF.map, PMF.bind_bind, PMF.bind_apply]
    have hpad :
        ofBits (List.ofFn fun i : Fin (k n) => if h : i.1 < m n then r₀ ⟨i, h⟩ else false) =
          ofBits (List.ofFn r₀) := by
      have hlist :
          (List.ofFn fun i : Fin (k n) => if h : i.1 < m n then r₀ ⟨i, h⟩ else false) =
            List.ofFn r₀ ++ List.replicate (k n - m n) false := by
        refine List.ext_getElem (by simp; omega) fun i h₁ h₂ => ?_
        by_cases hi : i < m n <;> simp [List.getElem_append, hi]
      rw [hlist, ofBits_append, ofBits_replicate_false]
      simp
    refine le_trans ?_
      (le_tsum _ fun i : Fin (k n) => if h : i.1 < m n then r₀ ⟨i, h⟩ else false)
    simp [PMF.uniformOfFintype_apply, hpad]
  rw [Game.succProbability, ← ENNReal.toNNReal_coe ((1 : ℝ≥0) / 2 ^ k n)]
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) ?_
  rwa [ENNReal.coe_div (by positivity), ENNReal.coe_one, ENNReal.coe_pow, ENNReal.coe_ofNat]

/-- **The guessing impersonator is uniform strict PPT** when its challenge length is computable in
polynomial time (`ComputableInPolyTime m encUnary encUnary`). -/
theorem isPPT_schnorrGuessingImpersonator {m : ℕ → ℕ}
    (hm : ComputableInPolyTime m encUnary encUnary) : (F.schnorrGuessingImpersonator m).IsPPT := by
  have hm' := hm.tidy
  refine ⟨?_, ?_⟩
  · have h := F.isPPTOn_schnorrSimulatedTranscript
      (encIn := encPair encUnary (encPair F.encDesc encBits))
      (n := fun p => p.1) (d := fun p => p.2.1) (u := fun p => p.2.2) (m := fun p => m p.1)
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    exact h.bind_with ((ComputableInPolyTime.tidy (by fun_prop)).isPPTOn)
  · exact (ComputableInPolyTime.tidy (by fun_prop)).isPPTOn

/-- **Negligible `1 / 2 ^ k n` is necessary for security against direct attacks**: for every
`setup` and `k : ℕ → ℕ`, if every uniform strict-PPT impersonator wins
`schnorrDirectGame setup k` with negligible probability, then `1 / 2 ^ k n` is negligible. The
proof instantiates the universal quantifier at `schnorrGuessingImpersonator fun _ => 0` using
`inv_two_pow_le_succProbability_schnorrDirectGame` and `isPPT_schnorrGuessingImpersonator` (no
efficiency condition on `k` is needed). The converse, under the discrete-logarithm assumption, is
`negligible_schnorrDirectGame`. -/
theorem negligible_inv_two_pow_of_negligible_schnorrDirectGame (setup : ℕ → PMF F.Desc) {k : ℕ → ℕ}
    (h : ∀ A : F.SchnorrImpersonator, A.IsPPT →
      Negligible fun n => Game.succProbability (F.schnorrDirectGame setup k A n)) :
    Negligible fun n => (1 : ℝ≥0) / 2 ^ k n :=
  negligible_of_le
    (h _ (isPPT_schnorrGuessingImpersonator (m := fun _ => 0) (by fun_prop)))
    fun n => inv_two_pow_le_succProbability_schnorrDirectGame setup k (fun _ => 0) n (Nat.zero_le _)

end Cslib.Crypto.PrimeOrderGroupFamily
