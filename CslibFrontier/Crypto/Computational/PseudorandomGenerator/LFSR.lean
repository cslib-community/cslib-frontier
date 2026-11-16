/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomGenerator
public import CslibFrontier.Crypto.Primitives.PRG.LFSR
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString.Dot
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Tactic.PPT

/-!
# No linear feedback shift register is a pseudorandom generator

A family of linear feedback shift registers is a word function: on a seed of length `n` it runs
the `n`-bit register with tap mask `taps n` for `ℓ n` clock cycles
(`Cslib.Crypto.PRG.LFSR.output`). The tap masks are public: they depend only on the seed length.

[Boneh and Shoup, Section 3.8, p. 75][BonehShoup2023] observe that a single LFSR is insecure as a
generator, because `n` consecutive output bits determine all later ones. This file states that
for uniform probabilistic polynomial-time distinguishers. The distinguisher runs the generator on
the first `n` bits of a word and accepts when it reproduces bit `n`. On words of the output length
it is the test built from `Cslib.Crypto.PRG.LFSR.predictor`, which accepts every output word and
a uniform word with probability `1 / 2`. It is a polynomial-time program whenever the generator
is, so the theorem that no LFSR family is a pseudorandom generator has no hypothesis. Every seed
is allowed, including the all-zero seed that [BonehShoup2023] excludes.

## Main definitions

* `Cslib.Crypto.PRG.LFSR.wordGenerator`: the LFSR family as a word function.
* `Cslib.Crypto.PRG.LFSR.rerunDistinguisher`: the distinguisher that re-runs the generator.

## Main results

* `Cslib.Crypto.PRG.LFSR.isPPT_rerunDistinguisher`: the distinguisher is a uniform
  polynomial-time program when the generator runs in polynomial time.
* `Cslib.Crypto.PRG.LFSR.eval_rerunDistinguisher_ofFn`: on words of the output length it is the
  test built from the predictor for position `n`.
* `Cslib.Crypto.PRG.LFSR.not_pseudorandomGenerator`: no LFSR family is a pseudorandom generator.
* `Cslib.Crypto.PRG.LFSR.not_computationallyIndistinguishable`: for a polynomial-time family with
  `n < ℓ n`, the output is not computationally indistinguishable from uniform.
* `Cslib.Crypto.PRG.LFSR.computableInPolyTime_wordGenerator`: the LFSR family is computable in
  polynomial time when its tap masks and output length are, so for a stretching `ℓ` security is
  the only condition of a pseudorandom generator that fails.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 3.8, p. 75.
-/

public section

namespace Cslib.Crypto.PRG.LFSR

open Probability Turing.MultiTapeTM
open Cslib.BitString (listDot)

/-- The LFSR family as a word function: on a seed of length `n` it runs the `n`-bit register
with the public tap mask `taps n` for `ℓ n` clock cycles. -/
@[expose] def wordGenerator (taps : ℕ → List Bool) (ℓ : ℕ → ℕ) (seed : List Bool) : List Bool :=
  output (taps seed.length) (ℓ seed.length) seed

@[simp] theorem length_wordGenerator (taps : ℕ → List Bool) (ℓ : ℕ → ℕ) (seed : List Bool) :
    (wordGenerator taps ℓ seed).length = ℓ seed.length :=
  length_output ..

/-- The finite family of the word generator is the typed generator at each seed length. -/
theorem wordFamily_wordGenerator (taps : ℕ → List Bool) (ℓ : ℕ → ℕ) (n : ℕ) :
    wordFamily (wordGenerator taps ℓ) ℓ n = generator (taps n) n (ℓ n) := by
  ext seed : 2
  simp [wordFamily, wordGenerator, generator]

/-- The distinguisher that uses the generator as a black box: run the register on the first `n`
bits of the word and accept exactly when it reproduces bit `n`. -/
def rerunDistinguisher (taps : ℕ → List Bool) (ℓ : ℕ → ℕ) : Distinguisher := fun n word =>
  pure (decide ((wordGenerator taps ℓ (word.take n)).getD n false = word.getD n false))

/-- Re-running a polynomial-time generator is one uniform polynomial-time program. -/
@[program_certificate]
theorem isPPT_rerunDistinguisher {taps : ℕ → List Bool} {ℓ : ℕ → ℕ}
    (hg : ComputableInPolyTime (wordGenerator taps ℓ) encBits encBits) :
    IsPPT encBool (rerunDistinguisher taps ℓ) := by
  unfold rerunDistinguisher
  ppt

/-- On words of the output length, re-running the register is the test of Attack Game 3.1 built
from the predictor for position `n`. -/
theorem eval_rerunDistinguisher_ofFn (taps : ℕ → List Bool) {ℓ : ℕ → ℕ} {n : ℕ} (hℓ : n < ℓ n)
    (bits : BitString (ℓ n)) :
    ProbComp.eval (rerunDistinguisher taps ℓ n (List.ofFn bits)) =
      predictionTest ⟨n, hℓ⟩ (predictor (taps n) n n) bits := by
  have hlen : ((List.ofFn bits).take n).length = n := by simp [hℓ.le]
  have hbit := getD_output_length (taps n) (ℓ := ℓ n) (state := (List.ofFn bits).take n)
    (by rw [hlen]; exact hℓ)
  rw [hlen] at hbit
  rw [rerunDistinguisher, wordGenerator, hlen, hbit]
  simp [predictionTest, predictor, Fin.ofFn_take_eq_take_ofFn, List.getD_eq_getElem?_getD, hℓ,
    PMF.pure_map]

/-- The tests built from the predictor for position `n` are realized by one uniform
polynomial-time program when the generator runs in polynomial time. -/
theorem isPPTBitStringTest_predictionTest_predictor {taps : ℕ → List Bool} {ℓ : ℕ → ℕ}
    (hg : ComputableInPolyTime (wordGenerator taps ℓ) encBits encBits) (hℓ : ∀ n, n < ℓ n) :
    IsPPTBitStringTest (length := ℓ)
      fun n => predictionTest ⟨n, hℓ n⟩ (predictor (taps n) n n) :=
  ⟨rerunDistinguisher taps ℓ, isPPT_rerunDistinguisher hg, fun _ bits =>
    eval_rerunDistinguisher_ofFn taps (hℓ _) bits⟩

/-- **No LFSR family is a pseudorandom generator**
[Boneh and Shoup, Section 3.8, p. 75][BonehShoup2023]. No hypothesis on the tap masks is needed:
when the generator runs in polynomial time, re-running it on the first `n` bits of a word is a
polynomial-time test, and it is the test built from the predictor, with advantage `1 / 2`. -/
theorem not_pseudorandomGenerator (taps : ℕ → List Bool) (ℓ : ℕ → ℕ) :
    ¬ PseudorandomGenerator (wordGenerator taps ℓ) ℓ := by
  intro h
  have hdecay := h.secure _ (isPPTBitStringTest_predictionTest_predictor h.polyTime h.stretch)
  have hadv (n : ℕ) : (wordFamily (wordGenerator taps ℓ) ℓ n).advantage
      (predictionTest ⟨n, h.stretch n⟩ (predictor (taps n) n n)) = 1 / 2 := by
    rw [wordFamily_wordGenerator,
      advantage_predictionTest_predictor (taps n) ⟨n, h.stretch n⟩ le_rfl]
  have ht := hdecay 0
  simp only [hadv, pow_zero, one_mul] at ht
  exact absurd (tendsto_nhds_unique tendsto_const_nhds ht) (by norm_num)

/-- For a polynomial-time LFSR family with output length `ℓ n > n`, the output on a uniform seed
is not computationally indistinguishable from a uniform word. -/
theorem not_computationallyIndistinguishable {taps : ℕ → List Bool} {ℓ : ℕ → ℕ}
    (hg : ComputableInPolyTime (wordGenerator taps ℓ) encBits encBits) (hℓ : ∀ n, n < ℓ n) :
    ¬ ComputationallyIndistinguishable (generatorEnsemble (wordGenerator taps ℓ))
      (fun n => BitString.uniformList (ℓ n)) := fun h =>
  not_pseudorandomGenerator taps ℓ (.of_indistinguishable hg (length_wordGenerator taps ℓ) hℓ h)

/-- One clock cycle together with the output so far: append the output bit and step the
register. -/
private def clock (taps : List Bool) (p : List Bool × List Bool) : List Bool × List Bool :=
  (p.1 ++ [p.2.headD false], step taps p.2)

private theorem iterate_clock (taps : List Bool) (k : ℕ) (acc state : List Bool) :
    (clock taps)^[k] (acc, state) = (acc ++ output taps k state, (step taps)^[k] state) := by
  induction k generalizing acc state with
  | zero => simp only [Function.iterate_zero, id_eq, output_zero, List.append_nil]
  | succ k ih =>
    rw [Function.iterate_succ_apply, clock, ih, output_succ, Function.iterate_succ_apply]
    simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- The LFSR family is computable in polynomial time when its tap masks and its output length
are. With `length_wordGenerator` this gives every condition of
`Cslib.Crypto.PseudorandomGenerator` except security, for every stretching `ℓ`. -/
@[program_certificate]
theorem computableInPolyTime_wordGenerator {taps : ℕ → List Bool} {ℓ : ℕ → ℕ}
    (htaps : ComputableInPolyTime taps encUnary encBits)
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary) :
    ComputableInPolyTime (wordGenerator taps ℓ) encBits encBits := by
  have hloop : ComputableInPolyTime
      (fun seed : List Bool => (clock (taps seed.length))^[ℓ seed.length] ([], seed))
      encBits (encPair encBits encBits) :=
    ComputableInPolyTime.iterateWith_of_bounded_growth (par := fun seed => taps seed.length)
      (count := fun seed => ℓ seed.length) (init := fun seed => ([], seed)) (step := clock)
      (by fun_prop) (by fun_prop) (by fun_prop) (by unfold clock step; fun_prop)
      (growth := fun _ => 2) (.const 2) (fun seed state => by
        simp only [clock, step, encPair_apply, encBits_apply, List.length_append, length_frame,
          List.length_cons, List.length_nil, zero_add, List.length_tail, add_tsub_cancel_right]
        omega)
  have h : wordGenerator taps ℓ =
      fun seed => ((clock (taps seed.length))^[ℓ seed.length] ([], seed)).1 := by
    funext seed
    simp only [wordGenerator, iterate_clock, List.nil_append]
  rw [h]
  fun_prop

end Cslib.Crypto.PRG.LFSR
