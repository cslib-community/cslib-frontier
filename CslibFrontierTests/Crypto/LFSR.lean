/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.PseudorandomGenerator.LFSR
import CslibFrontier.Tactic.PolyTime

/-!
# Tests for linear feedback shift registers

The register of [Boneh and Shoup, Figure 3.10, p. 75][BonehShoup2023] reproduces the printed
output, its later bits are recomputed from eight consecutive ones, and the all-zero seed gives
the all-zero output. The predictor wins Attack Game 3.2 on that register, so the register is
neither secure nor unpredictable with error `1 / 3`, and a concrete family satisfies every
condition of `PseudorandomGenerator` except security. The remaining examples show that the
hypotheses are needed: positions before `n` are not predicted, and a register that does not
stretch is secure.
-/

public section

namespace CslibFrontierTests.Crypto.LFSR

open Cslib Cslib.Crypto Cslib.Crypto.PRG Cslib.Probability Turing.MultiTapeTM
open Cslib.BitString (listDot)

/-- The tap positions `{4, 3, 2, 0}` of Figure 3.10 as a mask on positions `0, …, 7`. -/
def figureTaps : List Bool := [true, false, true, true, true, false, false, false]

/-- The register `1 0 0 1 0 1 1 0` of Figure 3.10, read from position `0`. -/
def figureSeed : List Bool := [false, true, true, false, true, false, false, true]

/-- The output `0110100100010100` printed in Figure 3.10. -/
def figureOutput : List Bool :=
  [false, true, true, false, true, false, false, true,
   false, false, false, true, false, true, false, false]

/-- The model reproduces the output printed in Figure 3.10. -/
example : LFSR.output figureTaps 16 figureSeed = figureOutput := by decide

/-- One clock cycle of the register of Figure 3.10: the feedback bit `b₄ ⊕ b₃ ⊕ b₂ ⊕ b₀ = 0`
enters at position `7`. -/
example : LFSR.step figureTaps figureSeed =
    [true, true, false, true, false, false, true, false] := by decide

/-- Bits `4, …, 11` of the output determine bits `4, …, 15`: the headline applied to the
figure. -/
example : figureOutput.drop 4 = LFSR.output figureTaps 12 ((figureOutput.drop 4).take 8) :=
  LFSR.drop_output_eq_output_take_drop figureTaps 4 16 figureSeed

/-- The recurrence on the figure: bit `12` is the feedback bit of bits `4, …, 11`. -/
example : figureOutput.getD 12 false = listDot figureTaps ((figureOutput.drop 4).take 8) :=
  LFSR.getD_output_add figureTaps (t := 4) (ℓ := 16) (state := figureSeed) (by decide)

/-- Started in the all-zero state, the register outputs only zeros (p. 75). The statements about
prediction hold for this seed too. -/
example : LFSR.output figureTaps 16 (List.replicate 8 false) = List.replicate 16 false := by
  decide

/-- Mask bits beyond the register length are ignored. -/
example : LFSR.output [true, true, true] 5 [true, false] =
    LFSR.output [true, true] 5 [true, false] := by
  decide

/-- A register without taps shifts in zeros. -/
example : LFSR.output [] 5 [true, true] = [true, true, false, false, false] := by decide

/-- The predictor wins Attack Game 3.2 at position `12` of the 16 output bits of the 8-bit
register of Figure 3.10. -/
example : (LFSR.generator figureTaps 8 16).predictionExperiment 12
    (LFSR.predictor figureTaps 8 12) = PMF.pure true :=
  LFSR.predictionExperiment_predictor figureTaps 12 (by decide)

/-- No test class that admits the test built from the predictor makes that register secure with
error below `1 / 2`. -/
example {Admissible : Adversary (BitString 16) → Prop}
    (h : Admissible (predictionTest 12 (LFSR.predictor figureTaps 8 12))) :
    ¬ (LFSR.generator figureTaps 8 16).Secure Admissible (1 / 3) := by
  intro hsecure
  have hadv : (LFSR.generator figureTaps 8 16).advantage
      (predictionTest 12 (LFSR.predictor figureTaps 8 12)) = 1 / 2 :=
    LFSR.advantage_predictionTest_predictor figureTaps 12 (by decide)
  have hle := hsecure _ h
  rw [hadv] at hle
  norm_num at hle

/-- Definition 3.3: no predictor class that admits the predictor makes the register of
Figure 3.10 unpredictable with error `1 / 3`. -/
example {Admissible : (i : Fin 16) → Adversary (Fin i → Bool) → Prop}
    (h : Admissible 12 (LFSR.predictor figureTaps 8 12)) :
    ¬ (LFSR.generator figureTaps 8 16).Unpredictable Admissible (1 / 3) := by
  intro hunpred
  have hadv : (LFSR.generator figureTaps 8 16).predictionAdvantage 12
      (LFSR.predictor figureTaps 8 12) = 1 / 2 :=
    LFSR.predictionAdvantage_predictor figureTaps 12 (by decide)
  have hle := hunpred 12 _ h
  rw [hadv] at hle
  norm_num at hle

/-- `h` of `getD_output_length` and of `getD_output_add` is needed: there is no output bit at
position `ℓ`. -/
example : (LFSR.output [true] 1 [true]).getD 1 false ≠ listDot [true] [true] := by decide

/-- `hk` of `take_output` is needed: beyond the seed the output continues with feedback bits. -/
example : (LFSR.output [true] 2 [true]).take 2 ≠ [true].take 2 := by decide

/-- `h` of `take_drop_output` is needed: a window that runs past the output is shorter than the
state. -/
example : ((LFSR.output [true] 1 [true, false]).drop 0).take 2 ≠
    (LFSR.step [true])^[0] [true, false] := by
  decide

/-- `hi` of `predictionExperiment_predictor` is needed: at position `0 < n` the predictor of a
one-bit register is wrong on the seed `1`. -/
example : (LFSR.generator [true] 1 2).predictionExperiment 0 (LFSR.predictor [true] 1 0) ≠
    PMF.pure true := by
  intro h
  have hmem : false ∈
      ((LFSR.generator [true] 1 2).predictionExperiment 0 (LFSR.predictor [true] 1 0)).support := by
    rw [Generator.predictionExperiment_eq_bind, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff]
    refine ⟨LFSR.generator [true] 1 2 ![true], ?_, ?_⟩
    · rw [Generator.outputDist, PMF.mem_support_map_iff]
      exact ⟨![true], by simp, rfl⟩
    · rw [LFSR.predictor, PMF.pure_map, PMF.support_pure, Set.mem_singleton_iff]
      decide
  rw [h, PMF.support_pure] at hmem
  exact Bool.false_ne_true hmem

/-! ### The word generator -/

/-- The family with every position tapped and one extra output bit. -/
def allTaps (n : ℕ) : List Bool := List.replicate n true

/-- The masks of the family are computable in polynomial time. -/
theorem computableInPolyTime_allTaps : ComputableInPolyTime allTaps encUnary encBits := by
  unfold allTaps
  fun_prop

/-- The family is a polynomial-time generator. -/
theorem computableInPolyTime_wordGenerator_allTaps :
    ComputableInPolyTime (LFSR.wordGenerator allTaps (· + 1)) encBits encBits :=
  LFSR.computableInPolyTime_wordGenerator computableInPolyTime_allTaps (by fun_prop)

/-- Re-running it is one uniform polynomial-time program. -/
example : IsPPT encBool (LFSR.rerunDistinguisher allTaps (· + 1)) :=
  LFSR.isPPT_rerunDistinguisher computableInPolyTime_wordGenerator_allTaps

/-- The program accepts a generated word: bit `2` of `1 0 1` is the feedback bit `1 ⊕ 0`. -/
example : ProbComp.eval (LFSR.rerunDistinguisher allTaps (· + 1) 2
    (List.ofFn ![true, false, true])) = PMF.pure true :=
  (LFSR.eval_rerunDistinguisher_ofFn allTaps (ℓ := (· + 1)) (n := 2) (by decide)
    ![true, false, true]).trans
    (by simp [predictionTest, LFSR.predictor, allTaps, listDot, Fin.init])

/-- The program rejects the same word with bit `2` flipped. -/
example : ProbComp.eval (LFSR.rerunDistinguisher allTaps (· + 1) 2
    (List.ofFn ![true, false, false])) = PMF.pure false :=
  (LFSR.eval_rerunDistinguisher_ofFn allTaps (ℓ := (· + 1)) (n := 2) (by decide)
    ![true, false, false]).trans
    (by simp [predictionTest, LFSR.predictor, allTaps, listDot, Fin.init])

/-- The tests built from the predictor are admissible for the family. -/
example : IsPPTBitStringTest (length := (· + 1)) fun n =>
    predictionTest ⟨n, n.lt_succ_self⟩ (LFSR.predictor (allTaps n) n n) :=
  LFSR.isPPTBitStringTest_predictionTest_predictor computableInPolyTime_wordGenerator_allTaps
    fun n => n.lt_succ_self

/-- The family meets every condition of `PseudorandomGenerator` except security: it is computable
in polynomial time, has exact output length and stretches, and its finite family is not secure
against uniformly realizable tests. -/
example :
    ComputableInPolyTime (LFSR.wordGenerator allTaps (· + 1)) encBits encBits ∧
    (∀ word, (LFSR.wordGenerator allTaps (· + 1) word).length = word.length + 1) ∧
    (∀ n, n < n + 1) ∧
    ¬ (wordFamily (LFSR.wordGenerator allTaps (· + 1)) (· + 1)).Secure IsPPTBitStringTest :=
  ⟨computableInPolyTime_wordGenerator_allTaps, LFSR.length_wordGenerator allTaps (· + 1),
    fun n => n.lt_succ_self, fun h => LFSR.not_pseudorandomGenerator allTaps (· + 1)
      ⟨computableInPolyTime_wordGenerator_allTaps, LFSR.length_wordGenerator allTaps (· + 1),
        fun n => n.lt_succ_self, h⟩⟩

/-- The headline for that family, and for every other. -/
example : ¬ PseudorandomGenerator (LFSR.wordGenerator allTaps (· + 1)) (· + 1) :=
  LFSR.not_pseudorandomGenerator _ _

/-- The fixed taps of Figure 3.10 at every seed length, with twice as many output bits and one
more. -/
example : ¬ ComputationallyIndistinguishable
    (generatorEnsemble (LFSR.wordGenerator (fun _ => figureTaps) (2 * · + 1)))
    (fun n => BitString.uniformList (2 * n + 1)) :=
  LFSR.not_computationallyIndistinguishable
    (LFSR.computableInPolyTime_wordGenerator (by fun_prop) (by fun_prop)) (fun n => by omega)

/-- The stretch hypothesis is needed: with `ℓ n = n` the register outputs its seed, which is
uniform. -/
example (taps : ℕ → List Bool) : ComputationallyIndistinguishable
    (generatorEnsemble (LFSR.wordGenerator taps fun n => n))
    (fun n => BitString.uniformList n) := by
  have h : LFSR.wordGenerator taps (fun n => n) = id :=
    funext fun seed => LFSR.output_length _ seed
  have hgen : generatorEnsemble (LFSR.wordGenerator taps fun n => n) =
      fun n => BitString.uniformList n := by
    funext n
    rw [generatorEnsemble, h, PMF.map_id]
  rw [hgen]
  exact .refl _

end CslibFrontierTests.Crypto.LFSR
