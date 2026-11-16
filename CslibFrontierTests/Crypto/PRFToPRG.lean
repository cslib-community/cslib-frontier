/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Crypto.Computational.PseudorandomFunction.ToPRG
import CslibFrontier.Crypto.Primitives.PRF.ToPRG

/-!
# Tests for PRF-to-PRG constructions

Concrete evaluation, length expansion, query budget, advantage identity, non-distinct query and
output-length counterexamples, and word-level security instantiation under module encapsulation.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.PRFToPRG

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

/-! ### Finite construction and Theorem 4.8 -/

private def xor1 : Bool → Bool → Bool := fun k d => k != d

private def twoBools : Fin 2 ↪ Bool := ⟨fun i => i.val == 0, by decide⟩

private def eqTest : (Fin 2 → Bool) → ProbComp Bool := fun y => pure (y 0 == y 1)

example : PRF.toPRG xor1 twoBools true 0 = false := by decide
example : PRF.toPRG xor1 twoBools true 1 = true := by decide

example : (PRF.toPRG xor1 twoBools).IsExpanding :=
  PRF.isExpanding_toPRG xor1 twoBools (by decide)

example : (PRF.prgReduction twoBools eqTest).IsQueryBounded 2 :=
  PRF.isQueryBounded_prgReduction twoBools eqTest

private theorem real_xor1_eqTest :
    (PRF.toPRG xor1 twoBools).realExperiment (fun y => ProbComp.eval (eqTest y)) =
      PMF.pure false := by
  refine PMF.ext fun b => ?_
  simp only [PRG.Generator.realExperiment, PRG.Generator.outputDist, PMF.bind_map, eqTest,
    ProbComp.eval_pure, PMF.bind_apply, PMF.uniformOfFintype_apply, Fintype.card_bool,
    Nat.cast_ofNat]
  rw [tsum_fintype, Fintype.sum_bool]
  cases b
  · suffices (2 : ENNReal)⁻¹ + 2⁻¹ = 1 by
      simpa [PRF.toPRG, xor1, twoBools] using this
    rw [← two_mul]
    exact ENNReal.mul_inv_cancel (a := (2 : ENNReal)) (by simp) (by simp)
  · simp [PRF.toPRG, xor1, twoBools]

private theorem ideal_eqTest :
    PRG.Generator.idealExperiment (fun y : Fin 2 → Bool => ProbComp.eval (eqTest y)) true =
      (1 / 2 : ENNReal) := by
  simp only [PRG.Generator.idealExperiment, eqTest, ProbComp.eval_pure, PMF.bind_apply,
    PMF.uniformOfFintype_apply, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
    Nat.reducePow, Nat.cast_ofNat]
  rw [tsum_fintype]
  have hu :
      (Finset.univ : Finset (Fin 2 → Bool)) =
        {![false, false], ![false, true], ![true, false], ![true, true]} := by decide
  rw [hu]
  simp only [PMF.pure_apply]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← two_mul]
  calc
    (2 : ENNReal) * (4 : ENNReal)⁻¹ = 2 * ((2 : ENNReal) * 2)⁻¹ := by norm_num
    _ = 2 * (2⁻¹ * 2⁻¹) := by rw [ENNReal.mul_inv (.inl (by simp)) (.inl (by simp))]
    _ = (2 * 2⁻¹) * 2⁻¹ := by rw [mul_assoc]
    _ = 2⁻¹ := by rw [ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

-- Avoid `decide` on `PMF`; compute `|(0 : ℝ) - 1/2| = 1/2` cleanly.
example :
    (PRF.toPRG xor1 twoBools).advantage (fun y => ProbComp.eval (eqTest y)) = 1 / 2 ∧
      (PRF.advantage xor1 (PRF.prgReduction twoBools eqTest) : ℝ) = 1 / 2 := by
  have hreal :
      (PRF.toPRG xor1 twoBools).realExperiment (fun y => ProbComp.eval (eqTest y)) true = 0 := by
    rw [real_xor1_eqTest]
    simp
  have hadv :
      (PRF.toPRG xor1 twoBools).advantage (fun y => ProbComp.eval (eqTest y)) = 1 / 2 := by
    rw [PRG.Generator.advantage_eq_game]
    simp only [Game.advantage, Game.succProbability, hreal, ideal_eqTest,
      ENNReal.toNNReal_zero, ENNReal.toNNReal_div, ENNReal.toNNReal_one, ENNReal.toNNReal_ofNat]
    norm_num
  exact ⟨hadv, by rw [← PRF.advantage_toPRG_eq xor1 twoBools eqTest, hadv]⟩

/-! ### Necessity of distinct evaluation points -/

private def idealBoolPRF : BitString 2 → Bool → Bool := fun k d => k (if d then 1 else 0)

private def dupBools : Fin 2 → Bool := fun _ => false

private def badDupPRG : PRG.Generator (BitString 2) (Fin 2 → Bool) where
  toFun k i := idealBoolPRF k (dupBools i)

-- `idealBoolPRF` matches a uniform random function on `Bool`, so `PRF.toPRG idealBoolPRF twoBools`
-- has zero PRG advantage on `eqTest`; reusing `false` at both coordinates gives advantage `1/2`.
example :
    (PRF.toPRG idealBoolPRF twoBools).advantage (fun y => ProbComp.eval (eqTest y)) = 0 ∧
      badDupPRG.advantage (fun y => ProbComp.eval (eqTest y)) = 1 / 2 := by
  have hgoodReal :
      (PRF.toPRG idealBoolPRF twoBools).realExperiment (fun y => ProbComp.eval (eqTest y)) =
        PRG.Generator.idealExperiment (fun y => ProbComp.eval (eqTest y)) := by
    let equiv : BitString 2 ≃ (Fin 2 → Bool) :=
      { toFun := PRF.toPRG idealBoolPRF twoBools
        invFun := fun y i => y (if i = 0 then 1 else 0)
        left_inv := fun k => funext fun i => by fin_cases i <;> rfl
        right_inv := fun y => funext fun i => by fin_cases i <;> rfl }
    simp only [PRG.Generator.realExperiment, PRG.Generator.outputDist,
      PRG.Generator.idealExperiment]
    have hmap :
        (PMF.uniformOfFintype (BitString 2)).map (PRF.toPRG idealBoolPRF twoBools) =
          PMF.uniformOfFintype (Fin 2 → Bool) :=
      PMF.uniformOfFintype_map_equiv equiv
    rw [hmap]
  have hgood :
      (PRF.toPRG idealBoolPRF twoBools).advantage (fun y => ProbComp.eval (eqTest y)) = 0 := by
    rw [PRG.Generator.advantage_eq_game, hgoodReal]
    simp
  have hbadReal :
      badDupPRG.realExperiment (fun y => ProbComp.eval (eqTest y)) = PMF.pure true := by
    refine PMF.ext fun b => ?_
    simp only [PRG.Generator.realExperiment, PRG.Generator.outputDist, PMF.bind_map, eqTest,
      ProbComp.eval_pure, PMF.bind_apply, PMF.uniformOfFintype_apply, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_bool, Nat.reducePow, Nat.cast_ofNat]
    rw [tsum_fintype]
    have hu :
        (Finset.univ : Finset (BitString 2)) =
          {![false, false], ![false, true], ![true, false], ![true, true]} := by decide
    rw [hu]
    cases b
    · simp [badDupPRG, idealBoolPRF, dupBools]
    · suffices (4 : ENNReal) * 4⁻¹ = 1 by
        simpa [badDupPRG, idealBoolPRF, dupBools] using this
      exact ENNReal.mul_inv_cancel (a := (4 : ENNReal)) (by simp) (by simp)
  have hbad :
      badDupPRG.advantage (fun y => ProbComp.eval (eqTest y)) = 1 / 2 := by
    rw [PRG.Generator.advantage_eq_game, hbadReal]
    simp [Game.advantage, Game.succProbability, ideal_eqTest, ENNReal.toNNReal_ofNat,
      NNReal.dist_eq]
    norm_num
  exact ⟨hgood, hbad⟩

/-! ### Word-level construction and efficiency -/

private def twoWordPts : ∀ n : ℕ, Fin 2 ↪ BitString (n + 1) := fun n =>
  ⟨fun i => if i = 0 then (fun _ => false) else fun k => decide (k.val = 0), by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · have h0 : false = true := congrFun hij 0
      contradiction
    · have h0 : true = false := congrFun hij 0
      contradiction
    · rfl⟩

private theorem listOfFn_twoWordPts (n : ℕ) :
    (List.ofFn fun i : Fin 2 => List.ofFn (twoWordPts n i)) =
      [List.replicate (n + 1) false, true :: List.replicate n false] := by
  have hpair (g : Fin 2 → List Bool) : List.ofFn g = [g 0, g 1] := by simp [List.ofFn_succ]
  have hz : twoWordPts n 0 = fun _ => false := rfl
  have ho : twoWordPts n 1 = fun k : Fin (n + 1) => decide (k.val = 0) := rfl
  have h0 : List.ofFn (twoWordPts n 0) = List.replicate (n + 1) false := by
    rw [hz]
    refine List.ext_getElem (by simp) fun i hi₁ hi₂ => ?_
    simp only [List.getElem_ofFn, List.getElem_replicate]
  have h1 : List.ofFn (twoWordPts n 1) = true :: List.replicate n false := by
    rw [ho]
    apply List.ext_getElem
    · simp
    · intro i hi₁ hi₂
      cases i with
      | zero => simp
      | succ j => simp
  rw [hpair, h0, h1]

private theorem hx_twoWordPts :
    ComputableInPolyTime
      (fun n => List.ofFn fun i : Fin 2 => List.ofFn (twoWordPts n i))
      encUnary (encList encBits) := by
  have heq :
      (fun n => List.ofFn fun i : Fin 2 => List.ofFn (twoWordPts n i)) =
        fun n => [List.replicate (n + 1) false, true :: List.replicate n false] :=
    funext listOfFn_twoWordPts
  rw [heq]
  have hsucc : ComputableInPolyTime (fun n : ℕ => n + 1) encUnary encUnary := by fun_prop
  have h0 : ComputableInPolyTime (fun n => List.replicate (n + 1) false) encUnary encBits :=
    (ComputableInPolyTime.bitsReplicate false).comp hsucc
  have h1 : ComputableInPolyTime (fun n => true :: List.replicate n false) encUnary encBits :=
    (ComputableInPolyTime.const [true]).bitsAppend (ComputableInPolyTime.bitsReplicate false)
  exact ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.cons' h0.tidy
      (ComputableTidilyInPolyTime.cons' h1.tidy (.const [])))

-- Concrete evaluation of `prgFromPRF` with XOR masking.
private def xorWordFamily (key query : List Bool) : List Bool := List.zipWith xor key query

example :
    prgFromPRF xorWordFamily (fun _ => 2) (fun n => n + 1) twoWordPts [true, false] =
      [true, false, false, false] := by
  decide

-- Exact polynomial-time and oracle-PPT certificates on the word-level reduction.
example :
    ComputableInPolyTime
      (prgFromPRF (fun k _ => k) (fun _ => 2) (fun n => n + 1) twoWordPts) encBits encBits :=
  computableInPolyTime_prgFromPRF (ComputableInPolyTime.fst encBits encBits) hx_twoWordPts

example :
    IsOraclePPT encBool
      (prgFromPRFReduction (fun _ => 2) (fun n => n + 1) (fun n => n + 1) twoWordPts
        (fun _ _ => pure false)) := by
  have hzero :
      IsPPTOn (encPair encUnary encBits) encBool
        (fun p : ℕ × List Bool => (fun (_ : ℕ) (_ : List Bool) => pure false) p.1 p.2) :=
    (ComputableInPolyTime.const false :
      ComputableInPolyTime (fun _ : ℕ × List Bool => false)
        (encPair encUnary encBits) encBool).isPPTOn
  exact isOraclePPT_prgFromPRFReduction hx_twoWordPts (by fun_prop) hzero

-- Instantiating `PseudorandomFunctionOver.toPRG` yields a `PseudorandomGenerator` of
-- output length `2 * (n + 1)`.
example (family : List Bool → List Bool → List Bool)
    (hfamily : PseudorandomFunctionOver (fun n => n + 1) (fun n => n + 1) family) :
    PseudorandomGenerator (prgFromPRF family (fun _ => 2) (fun n => n + 1) twoWordPts)
      (fun n => 2 * (n + 1)) :=
  hfamily.toPRG twoWordPts hx_twoWordPts fun n => by omega

-- One all-`false` point of `n` bits.
private def zeroPt : ∀ n : ℕ, Fin 1 ↪ BitString n := fun _ =>
  ⟨fun _ _ => false, fun _ _ _ => Subsingleton.elim _ _⟩

private theorem hx_zeroPt :
    ComputableInPolyTime (fun n => List.ofFn fun i : Fin 1 => List.ofFn (zeroPt n i))
      encUnary (encList encBits) := by
  have heq : (fun n => List.ofFn fun i : Fin 1 => List.ofFn (zeroPt n i)) =
      fun n => [List.replicate n false] := by
    funext n
    have h : List.ofFn (zeroPt n 0) = List.replicate n false := List.ofFn_const n false
    simp [List.ofFn_succ, h]
  rw [heq]
  have h0 : ComputableInPolyTime (fun n => List.replicate n false) encUnary encBits :=
    ComputableInPolyTime.bitsReplicate false
  exact ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.cons' h0.tidy (.const []))

-- A length-preserving `PseudorandomFunction` lacks stretch at `n = 0`, yet is covered by
-- `indistinguishable_prgFromPRF`.
example (family : List Bool → List Bool → List Bool) (hfamily : PseudorandomFunction family) :
    ComputationallyIndistinguishable
      (generatorEnsemble (prgFromPRF family (fun _ => 1) id zeroPt))
      (fun n => BitString.uniformList (1 * id n)) :=
  indistinguishable_prgFromPRF hfamily zeroPt hx_zeroPt (by fun_prop)

-- `hlength` is needed in `eval_prgRealGame_prgFromPRF` and `advantage_prgFromPRF_eq`.
private def pt0 : ∀ _ : ℕ, Fin 1 ↪ BitString 0 := fun _ =>
  ⟨fun _ i => i.elim0, fun _ _ _ => Subsingleton.elim _ _⟩

private def isEmptyTest : Distinguisher := fun _ w => pure w.isEmpty

-- A family that answers with the empty word where one bit is declared: the generator outputs the
-- empty word, the reduction pads the reply to `[false]`.
example :
    ProbComp.eval (prgRealGame (prgFromPRF (fun _ _ => []) (fun _ => 1) (fun _ => 0) pt0)
        isEmptyTest 0) true = 1 ∧
      ProbComp.eval (prfRealGame (fun _ => 0) (fun _ _ => [])
        (prgFromPRFReduction (fun _ => 1) (fun _ => 0) (fun _ => 1) pt0 isEmptyTest) 0)
        true = 0 := by
  constructor
  · simp [prgRealGame, prgFromPRF, isEmptyTest, List.ofFn_succ]
  · have hrun (key : List Bool) :
        (prgFromPRFReduction (fun _ => 1) (fun _ => 0) (fun _ => 1) pt0 isEmptyTest 0 []).run
          (fun request => pure (prfOracle (fun _ _ => []) 0 key request.2)) = pure false := by
      simp [prgFromPRFReduction, PRF.prgReduction, ProbOracleComp.run_simulate,
        ProbOracleComp.run_map, ProbOracleComp.run_query, PRF.run_queryPoints, prfOracle,
        isEmptyTest, List.ofFn_succ]
    simp [prfRealGame, hrun]

end CslibFrontierTests.Crypto.PRFToPRG
