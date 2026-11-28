/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction.Cascade.ChildChallenge
public import CslibFrontier.Crypto.Computational.PseudorandomFunction.Cascade.ChildReduction
import CslibFrontier.Crypto.Computational.PseudorandomFunction.Cascade.ChildReductionLaw
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Probability.BitString.List

/-!
# Sampled game law for the cascade child challenge

The wrapper draws the challenge index with fair bits and the local keys as consecutive fixed-width
rows. These draws give a uniform index and independent uniform keys. An unused index gives the
same rejecting output for every external challenge law.

## Main definitions

* `Cslib.Crypto.cascadeKeyedChildFunctionLaw`: the function distribution induced by a uniform key.

## Main results

* `Cslib.Crypto.bind_evalWith_cascadeChildChallengeProgram_eq_game`: the sampled wrapper has
  the output distribution of the finite-table challenge game, including its padding indices.
* `Cslib.Crypto.evalWith_cascadeChildChallengeWithIndex`: the fixed-index wrapper has the
  corresponding finite-table law.

## References

* [BonehShoup2023], v0.6, Section 4.6.1 (printed pp. 152–154) and Section 6.4.2
  (printed pp. 229–230), for the adjacent-hybrid argument.
-/

public section

namespace Cslib.Crypto

open Probability

/-- The child-function distribution induced by a uniform `n`-bit key at input width `width`.
The fixed-width representation reads the first `n` result bits, padding short results with zero. -/
@[expose]
noncomputable def cascadeKeyedChildFunctionLaw (family : List Bool → List Bool → List Bool)
    (width n : ℕ) : PMF (BitString width → BitString n) :=
  (PMF.uniformOfFintype (BitString n)).map fun key block =>
    BitString.ofList n (family (List.ofFn key) (List.ofFn block))

/-- The key-sampling wrapper at a specified index has the same law as the finite child table
with the supplied function in that row. -/
theorem evalWith_cascadeChildChallengeWithIndex {count width n : ℕ}
    (family : List Bool → List Bool → List Bool)
    (hlength : ∀ key block, key.length = n → block.length = width →
      (family key block).length = n)
    (selected : Fin count) (challenge : BitString width → BitString n)
    (program : WordOracleComp ℕ Bool) :
    OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle
        (fun req : Unit × List Bool => PMF.pure (randomFunctionOracle width challenge req.2)))
      (cascadeChildChallengeWithIndex family width n count selected.val program) =
      cascadeChildChallengeAt (cascadeKeyedChildFunctionLaw family width n)
        (PMF.uniformOfFintype (BitString width → BitString n)) selected challenge program := by
  let keyLaw := PMF.uniformOfFintype (BitString n)
  let idealLaw := PMF.uniformOfFintype (BitString width → BitString n)
  let choose (i : Fin count) (key : BitString n) (ideal : BitString width → BitString n) :=
    if i < selected then ideal
    else if i = selected then challenge
    else fun block => BitString.ofList n (family (List.ofFn key) (List.ofFn block))
  let law : Fin count → PMF (BitString width → BitString n) :=
    Function.update (fun i => if i < selected then idealLaw
      else cascadeKeyedChildFunctionLaw family width n) selected (PMF.pure challenge)
  have hrow (i : Fin count) : keyLaw.bind (fun key => idealLaw.map (choose i key)) = law i := by
    rcases lt_trichotomy i selected with hlt | rfl | hgt
    · simp [choose, law, hlt.ne, hlt, PMF.map, Function.comp_def]
    · simp [choose, law, PMF.map, Function.comp_def]
    · simp [choose, law, hgt.not_gt, hgt.ne', cascadeKeyedChildFunctionLaw, keyLaw, PMF.map,
        Function.comp_def]
  have htable : PMF.pi law =
      (PMF.uniformOfFintype (Fin count → BitString n)).bind fun keys =>
        (PMF.uniformOfFintype (Fin count → BitString width → BitString n)).map fun ideal i =>
          choose i (keys i) (ideal i) := by
    calc
      PMF.pi law = PMF.pi (fun i => keyLaw.bind fun key => idealLaw.map (choose i key)) :=
        congrArg PMF.pi (funext fun i => (hrow i).symm)
      _ = (PMF.pi fun _ : Fin count => keyLaw).bind (fun keys =>
          PMF.pi (fun i => idealLaw.map (choose i (keys i)))) := PMF.pi_bind _ _
      _ = _ := by simp only [PMF.pi_map, keyLaw, idealLaw, PMF.pi_uniformOfFintype]
  simp only [cascadeChildChallengeWithIndex, OracleComp.evalWith_bind,
    ProbOracleComp.evalWith_sumHandler_unifOracle_sample, BitString.eval_sampleList,
    evalWith_cascadeChildChallengeAtProgram_eq_eager family hlength]
  unfold cascadeChildChallengeAt
  change _ = (PMF.pi law).bind _
  rw [htable, PMF.bind_bind, ← BitString.uniformList_map_listRow_equiv (.refl (Fin count)) n,
    PMF.bind_map]
  congr 1 with word : 1
  rw [← PMF.uniformOfFintype_map_equiv (Equiv.curry (Fin count) (BitString width) (BitString n))]
  simp only [Function.comp_def, Equiv.refl_apply, PMF.bind_map, PMF.map_comp]
  congr 1 with ideal : 1
  congr 3
  funext channel block
  simp [choose, Function.curry, BitString.ofFn_ofList (BitString.length_listRow _ _ _), ite_apply]

/-- Under any external function distribution, the wrapper realizes the sampled finite-table
game with a range of size `2 ^ indexBits`. For the keyed family, keys have width `n`, inputs
have width `width`, and replies have width `n`. No external query is needed on a padding index. -/
theorem bind_evalWith_cascadeChildChallengeProgram_eq_game {width n : ℕ}
    (family : List Bool → List Bool → List Bool)
    (hlength : ∀ key block, key.length = n → block.length = width →
      (family key block).length = n)
    (count indexBits : ℕ) (source : PMF (BitString width → BitString n))
    (program : WordOracleComp ℕ Bool) :
    (source.bind fun challenge =>
      OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle
        (fun req : Unit × List Bool => PMF.pure (randomFunctionOracle width challenge req.2)))
        (cascadeChildChallengeProgram family width n count indexBits program)) =
      cascadeChildChallengeGame count (2 ^ indexBits) (cascadeKeyedChildFunctionLaw family width n)
        (PMF.uniformOfFintype (BitString width → BitString n)) source program := by
  simp only [cascadeChildChallengeProgram, OracleComp.evalWith_bind,
    ProbOracleComp.evalWith_sumHandler_unifOracle_sample, ProbComp.eval_sampleBinaryNat,
    PMF.bind_map, Function.comp_def, cascadeChildChallengeGame]
  rw [PMF.bind_comm source]
  congr 1 with index : 1
  by_cases hi : index.val < count
  · simp only [ite_eq_left hi, dite_eq_left hi,
      evalWith_cascadeChildChallengeWithIndex family hlength (⟨index.val, hi⟩ : Fin count)]
  · simp only [ite_eq_right hi, dite_eq_right hi, OracleComp.evalWith_pure, PMF.bind_const]

end Cslib.Crypto
