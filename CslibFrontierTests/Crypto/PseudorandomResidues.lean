/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.PseudorandomGenerator.ModReduction
import CslibFrontier.Crypto.Primitives.PRG.ModReduction
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PPT

/-!
# Checked tests for pseudorandom residues (Boneh–Shoup Example 3.3)

Exercises `modWord`, `modDistinguisher`, `ComputationallyIndistinguishable.map_modWord`,
`PseudorandomGenerator.indistinguishable_map_modWord`,
`advantage_generatorEnsemble_map_modWord_le`, `PRG.Generator.modNat` and
`PRG.Generator.advantage_modNat_le`, including hypothesis necessity probes and constant-modulus
instances (`m = 3` and general constant `c ≠ 0`).
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.PseudorandomResidues

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

/-- Two fair bits reduced modulo `3` give the residue `0` with probability `1 / 2`. -/
theorem toReal_uniformList_two_map_modWord_three_zero :
    (((BitString.uniformList 2).map (modWord 3)) (encNat 0)).toReal = 1 / 2 := by
  rw [uniformList_map_modWord, ProbComp.eval_sampleModNat, PMF.map_comp,
    PMF.toReal_uniformOfFintype_map_apply]
  simp only [Function.comp_apply, EmbeddingLike.apply_eq_iff_eq]
  have hset : (Finset.univ.filter fun a : Fin (2 ^ 2) => a.val % 3 = 0) = {0, 3} := by decide
  rw [hset]
  simp [Finset.dens]
  norm_num

/-- A uniform residue modulo `3` is `0` with probability `1 / 3`. -/
theorem toReal_uniform_residue_three_zero :
    (((PMF.uniformOfFintype (Fin 3)).map fun i => encNat i.val) (encNat 0)).toReal = 1 / 3 := by
  rw [PMF.toReal_uniformOfFintype_map_apply]
  simp only [EmbeddingLike.apply_eq_iff_eq]
  have hset : (Finset.univ.filter fun a : Fin 3 => a.val = 0) = {0} := by decide
  rw [hset]
  simp [Finset.dens]

/-- The test "is the word empty?" accepts a sample of `D` with the probability that `D` gives to
the residue `0`, whose binary form is the empty word. -/
theorem distinguishingGame_isEmpty_true (D : PMF (List Bool)) :
    (distinguishingGame D fun word => (pure word.isEmpty : ProbComp Bool)) true =
      D (encNat 0) := by
  rw [distinguishingGame_eq_bind]
  simp only [ProbComp.eval_pure, PMF.monad_bind_eq_bind]
  change (D.map List.isEmpty) true = _
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
    ← PMF.toOuterMeasure_apply_singleton D]
  have hzero : encNat 0 = [] := Nat.zero_bits
  congr 1
  ext word
  simp [hzero]

/-- That test is one PPT program. -/
theorem isPPT_isEmpty : IsPPT encBool
    (fun (_ : ℕ) (word : List Bool) => (pure word.isEmpty : ProbComp Bool)) := by ppt

/-- Probe for `hneg` in Example 3.3. With two bits and modulus `3` at every parameter,
`m / 2 ^ L = 3 / 4` is not negligible. The words are uniform, so the other hypotheses hold, and the
conclusion fails: the test "is the residue `0`?" is PPT and has advantage `1 / 2 - 1 / 3`. -/
theorem not_computationallyIndistinguishable_two_bits_mod_three :
    ¬ ComputationallyIndistinguishable
      (fun _ : ℕ => (BitString.uniformList 2).map (modWord 3))
      (fun _ : ℕ => (PMF.uniformOfFintype (Fin 3)).map fun i => encNat i.val) := by
  intro h
  refine not_negligible_const (c := 1 / 6) (by norm_num)
    (negligible_of_le (h _ isPPT_isEmpty) fun n => ?_)
  rw [← NNReal.coe_le_coe, Game.coe_advantage]
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, distinguishingGame_isEmpty_true,
    toReal_uniformList_two_map_modWord_three_zero, toReal_uniform_residue_three_zero]
  norm_num

/-- Probe for `hX` in Example 3.3. The constant ensemble at the empty word is not indistinguishable
from uniform words; with modulus `3` and `n` output bits the other hypotheses hold, and the
conclusion fails: the residue is always `0`. -/
theorem not_computationallyIndistinguishable_pure_mod_three :
    ¬ ComputationallyIndistinguishable
      (fun _ : ℕ => (PMF.pure ([] : List Bool)).map (modWord 3))
      (fun _ : ℕ => (PMF.uniformOfFintype (Fin 3)).map fun i => encNat i.val) := by
  intro h
  refine not_negligible_const (c := 1 / 6) (by norm_num)
    (negligible_of_le (h _ isPPT_isEmpty) fun n => ?_)
  have hpure : ((PMF.pure ([] : List Bool)).map (modWord 3)) (encNat 0) = 1 := by
    rw [PMF.pure_map]
    exact PMF.pure_apply_self _
  rw [← NNReal.coe_le_coe, Game.coe_advantage]
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, distinguishingGame_isEmpty_true,
    hpure, toReal_uniform_residue_three_zero]
  norm_num

/-- In that instance the other hypotheses of `ComputationallyIndistinguishable.map_modWord` hold:
only `hneg` is missing. -/
example : ComputationallyIndistinguishable (fun _ : ℕ => BitString.uniformList 2)
    (fun _ : ℕ => BitString.uniformList 2) ∧
    ComputableInPolyTime (fun _ : ℕ => 3) encUnary encNat :=
  ⟨.refl _, by fun_prop⟩

/-- In the `hX` probe above, the modulus and negligibility hypotheses hold: only `hX` is
missing. -/
example : ComputableInPolyTime (fun _ : ℕ => 3) encUnary encNat ∧
    Negligible fun n : ℕ => (3 : ℝ≥0) / 2 ^ n :=
  ⟨by fun_prop, by negligible⟩

/-- All three hypotheses of `ComputationallyIndistinguishable.map_modWord` hold together, with no
assumption: `n` fair bits and the modulus `3`. -/
example : ComputationallyIndistinguishable
    (fun n => (BitString.uniformList n).map (modWord 3))
    (fun _ => (PMF.uniformOfFintype (Fin 3)).map fun i => encNat i.val) :=
  (ComputationallyIndistinguishable.refl _).map_modWord (m := fun _ => 3) (by fun_prop)
    (by negligible)

/-- Example 3.3 for any pseudorandom generator and a constant modulus `c` (`NeZero c`), the book's
constant-`m` case: the stretch of the generator supplies the negligible error. -/
theorem indistinguishable_map_modWord_const {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (h : PseudorandomGenerator generator length) (c : ℕ) [NeZero c] :
    ComputationallyIndistinguishable
      (fun n => (generatorEnsemble generator n).map (modWord c))
      (fun _ => (PMF.uniformOfFintype (Fin c)).map fun i => encNat i.val) :=
  h.indistinguishable_map_modWord (m := fun _ => c) (by fun_prop) (by
    have hle : ∀ n, (c : ℝ≥0) / 2 ^ length n ≤ (c : ℝ≥0) / 2 ^ n := fun n => by
      gcongr
      · exact one_le_two
      · exact (h.stretch n).le
    negligible using hle)

/-- Example 3.3 for any pseudorandom generator and the modulus `3`. -/
theorem indistinguishable_map_modWord_three {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (h : PseudorandomGenerator generator length) :
    ComputationallyIndistinguishable
      (fun n => (generatorEnsemble generator n).map (modWord 3))
      (fun _ => (PMF.uniformOfFintype (Fin 3)).map fun i => encNat i.val) :=
  indistinguishable_map_modWord_const h 3

/-- The book's `G'(s) := G(s) mod m` is itself a word function, and the first ensemble above is
its output on a uniform seed. -/
example {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (h : PseudorandomGenerator generator length) :
    ComputationallyIndistinguishable
      (generatorEnsemble fun seed => modWord 3 (generator seed))
      (fun _ => (PMF.uniformOfFintype (Fin 3)).map fun i => encNat i.val) := by
  have hE : (generatorEnsemble fun seed => modWord 3 (generator seed)) =
      fun n => (generatorEnsemble generator n).map (modWord 3) :=
    funext fun n => generatorEnsemble_postprocess generator (fun _ => modWord 3) n
  rw [hE]
  exact indistinguishable_map_modWord_three h

/-- A modulus that grows with the parameter: `m n = n + 1` is computable from the unary parameter,
and `(n + 1) / 2 ^ length n` is negligible for every generator, by its stretch. -/
example {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (h : PseudorandomGenerator generator length) :
    ComputationallyIndistinguishable
      (fun n => (generatorEnsemble generator n).map (modWord (n + 1)))
      (fun n => (PMF.uniformOfFintype (Fin (n + 1))).map fun i => encNat i.val) :=
  h.indistinguishable_map_modWord (m := fun n => n + 1)
    (ComputableInPolyTime.unary_to_binary.comp ComputableInPolyTime.unary_succ) (by
    have hle : ∀ n, ((n + 1 : ℕ) : ℝ≥0) / 2 ^ length n ≤ ((n + 1 : ℕ) : ℝ≥0) / 2 ^ n := fun n => by
      gcongr
      · exact one_le_two
      · exact (h.stretch n).le
    negligible using hle)

/-- The book's inequality at one parameter, for a generator that is not assumed secure: the
identity map on words, eight output bits, modulus `3`. -/
example (adversary : Distinguisher) (n : ℕ) :
    Game.advantage
        (distinguishingGame ((generatorEnsemble id n).map (modWord 3)) (adversary n))
        (distinguishingGame ((PMF.uniformOfFintype (Fin 3)).map fun i => encNat i.val)
          (adversary n)) ≤
      Game.advantage (ProbComp.eval (prgRealGame id (modDistinguisher (fun _ => 3) adversary) n))
        (ProbComp.eval (prgIdealGame (fun _ => 8) (modDistinguisher (fun _ => 3) adversary) n)) +
        3 / 2 ^ 8 := by
  simpa using advantage_generatorEnsemble_map_modWord_le id (fun _ => 8) (fun _ => 3) adversary n

/-- The finite-type form with the book's `N = 2 ^ L`. -/
example {Seed : Type} [Fintype Seed] [Nonempty Seed] (L m : ℕ) [NeZero m]
    (G : PRG.Generator Seed (Fin (2 ^ L))) (A : PRG.Adversary (ZMod m)) :
    (G.modNat m).advantage A ≤ G.advantage (fun y => A (y.val : ZMod m)) + m / 2 ^ L := by
  simpa using G.advantage_modNat_le m A

/-- The finite-type form for numbers below `256` reduced modulo `3`, from one-bit seeds. -/
example (G : PRG.Generator Bool (Fin 256)) (A : PRG.Adversary (ZMod 3)) :
    (G.modNat 3).advantage A ≤ G.advantage (fun y => A (y.val : ZMod 3)) + 3 / 256 := by
  simpa using G.advantage_modNat_le 3 A

/-- `modNat` computes: `200 mod 3 = 2`. -/
example : (PRG.Generator.mk fun _ : Unit => (200 : Fin 256)).modNat 3 () = (2 : ZMod 3) := by
  decide

/-- The constant generator at `0`, reduced modulo `3`, against the test "is the residue `0`?":
the advantage is `1 - 1 / 3`. -/
theorem advantage_modNat_const_zero :
    ((PRG.Generator.mk fun _ : Unit => (0 : Fin 256)).modNat 3).advantage
      (fun y => PMF.pure (decide (y = 0))) = 2 / 3 := by
  have hreal : ((PRG.Generator.mk fun _ : Unit => (0 : Fin 256)).modNat 3).realExperiment
      (fun y => PMF.pure (decide (y = 0))) = PMF.pure true := by
    simp only [PRG.Generator.realExperiment, PRG.Generator.outputDist]
    rw [show (⇑((PRG.Generator.mk fun _ : Unit => (0 : Fin 256)).modNat 3)) =
      Function.const Unit (0 : ZMod 3) from by funext s; simp, PMF.map_const, PMF.pure_bind]
    simp
  have hideal : ((PRG.Generator.idealExperiment (Output := ZMod 3)
      fun y => PMF.pure (decide (y = 0))) true).toReal = 1 / 3 := by
    simp only [PRG.Generator.idealExperiment]
    change (((PMF.uniformOfFintype (ZMod 3)).map fun y => decide (y = 0)) true).toReal = 1 / 3
    rw [PMF.toReal_uniformOfFintype_map_apply]
    have hset : (Finset.univ.filter fun a : ZMod 3 => decide (a = 0) = true) = {0} := by decide
    rw [hset]
    simp [Finset.dens]
  unfold PRG.Generator.advantage
  rw [hreal, hideal]
  simp
  norm_num

end CslibFrontierTests.Crypto.PseudorandomResidues
