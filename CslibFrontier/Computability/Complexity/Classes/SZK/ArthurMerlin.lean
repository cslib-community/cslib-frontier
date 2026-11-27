/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.SZK
public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin
import CslibFrontier.Computability.Complexity.Classes.IP.Guessing
import CslibFrontier.Computability.Complexity.Classes.IP.Repetition
import CslibFrontier.Computability.Complexity.Classes.IP.Games.Oracle
import CslibFrontier.Computability.Circuit.Boolean.EvaluationTime
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Languages.Probabilistic.QueryCount.Iterate
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.StatisticalDistance

/-!
# An Arthur–Merlin upper bound for Statistical Difference

The private-coin guessing protocol of [Sahai and Vadhan, §3.3][SahaiVadhan2003] samples one
of two circuits and asks the prover to identify it. Its optimal acceptance probability is
`(1 + δ) / 2` for statistical distance `δ`. After polarization, two sequential rounds
suffice. The constant-query private-to-public coin simulation then gives an AM protocol
for every language reducing to Statistical Difference.

The source proves interactive statistical zero knowledge. Here the class on the left uses
the reduction-to-Statistical-Difference characterization of `SZK` in
`CslibFrontier.Computability.Complexity.Classes.SZK`. The interactive characterization
and the complementary protocol are tracked in [#3205](https://github.com/cslib-community/cslib-frontier/issues/3205).
-/

namespace Cslib.Complexity

open Cslib Cslib.Probability Circuits Circuits.Boolean Turing.MultiTapeTM
open scoped Cslib.Probability.PMF

namespace SDInstance

private def circuit (x : SDInstance) (b : Bool) : Circuit signature x.inputs x.outputs :=
  if b then x.right else x.left

private noncomputable def message (x : SDInstance) (b : Bool) : ProbComp (List Bool) :=
  evalCircuitOutputs (x.circuit b).code <$> BitString.sampleList x.inputs

private theorem eval_message (x : SDInstance) (b : Bool) :
    ProbComp.eval (x.message b) = ((x.circuit b).outputDist interpretation).map List.ofFn := by
  rw [message, ProbComp.eval_map, BitString.eval_sampleList, BitString.uniformList,
    Circuit.outputDist, PMF.map_comp, PMF.map_comp]
  congr 1 with r : 1
  exact evalCircuitOutputs_code _ r

private theorem isPPTOn_message :
    IsPPTOn (encPair encSDInstance encBool) encBits (fun p => message p.1 p.2) := by
  have hproj : ComputableInPolyTime
      (fun x : SDInstance => ((x.inputs, x.outputs), (x.left.code, x.right.code)))
      encSDInstance (encPair (encPair encUnary encUnary) (encPair encCode encCode)) :=
    .of_eq fun x => (encSDInstance_apply x).symm
  have h := hproj.comp (ComputableInPolyTime.fst encSDInstance encBool)
  have hc : ComputableInPolyTime (fun p : SDInstance × Bool => (p.1.circuit p.2).code)
      (encPair encSDInstance encBool) encCode := by
    have heq (p : SDInstance × Bool) : (p.1.circuit p.2).code =
        (if p.2 then p.1.right.code else p.1.left.code) := by cases p.2 <;> rfl
    simp only [heq]
    have hr := h.snd'.snd'
    have hl := h.snd'.fst'
    fun_prop
  apply IsPPTOn.of_seeded (f := fun p => evalCircuitOutputs
    (p.1.1.circuit p.1.2).code p.2) h.fst'.fst'
  exact computableInPolyTime_evalCircuitOutputs
    (hc.comp (ComputableInPolyTime.fst _ encBits)) (ComputableInPolyTime.snd _ encBits)

private noncomputable def round (x : SDInstance) := guessingRound x.message

private theorem round_probability (x : SDInstance) (P : Prover Unit) :
    (acceptProb x.round P).toReal = (∑ y : BitString x.outputs,
      ((x.left.outputDist interpretation y).toReal *
        (P.guessProb P.init (List.ofFn y) false).toReal +
       (x.right.outputDist interpretation y).toReal *
        (P.guessProb P.init (List.ofFn y) true).toReal)) / 2 := by
  rw [round, acceptProb_guessingRound]
  simp only [eval_message, Probability.PMF.tsum_map_mul, tsum_fintype, circuit,
    Bool.false_eq_true, ↓reduceIte, ← Finset.sum_add_distrib, ENNReal.toReal_div,
    ENNReal.toReal_ofNat]
  congr 1
  have hfin (y : BitString x.outputs) (b : Bool) : P.guessProb P.init (List.ofFn y) b ≠ ⊤ :=
    PMF.apply_ne_top _ _
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro y _
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (hfin y false))
      (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (hfin y true)),
      ENNReal.toReal_mul, ENNReal.toReal_mul]
  · intro y _
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (hfin y false),
      ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (hfin y true)⟩

private theorem round_probability_le (x : SDInstance) (P : Prover Unit) :
    (acceptProb x.round P).toReal ≤ (1 + x.distance) / 2 := by
  rw [round_probability, distance, ← Probability.PMF.sum_max_toReal]
  gcongr with y
  let q := fun b => P.guessProb P.init (List.ofFn y) b
  have hn (b : Bool) : q b ≠ ⊤ := PMF.apply_ne_top _ _
  have h := ENNReal.toReal_mono (by simp : (1 : ENNReal) ≠ ⊤)
    (P.guessProb_add_le_one P.init (List.ofFn y))
  change (q false + q true).toReal ≤ _ at h
  rw [ENNReal.toReal_add (hn _) (hn _), ENNReal.toReal_one] at h
  calc
    _ ≤ max _ _ * (q false).toReal + max _ _ * (q true).toReal :=
      add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) ENNReal.toReal_nonneg)
        (mul_le_mul_of_nonneg_right (le_max_right _ _) ENNReal.toReal_nonneg)
    _ ≤ _ := by rw [← mul_add]; exact mul_le_of_le_one_right (by positivity) h

private noncomputable def best (x : SDInstance) : Prover Unit where
  State := Unit
  init := ()
  respond req s :=
    let y := BitString.ofList x.outputs req.2
    pure ([decide ((x.left.outputDist interpretation y).toReal <
      (x.right.outputDist interpretation y).toReal)], s)

private theorem round_probability_best (x : SDInstance) :
    (acceptProb x.round x.best).toReal = (1 + x.distance) / 2 := by
  rw [round_probability, distance, ← Probability.PMF.sum_max_toReal]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : (x.left.outputDist interpretation y).toReal <
    (x.right.outputDist interpretation y).toReal
  · simp [Prover.guessProb, best, BitString.ofList_ofFn, h, max_eq_right h.le, StateT.run]
  · simp [Prover.guessProb, best, BitString.ofList_ofFn, h,
      max_eq_left (le_of_not_gt h), StateT.run]

private theorem round_queryBound (x : SDInstance) : x.round.IsQueryBounded 1 := by
  unfold round guessingRound ProbOracleComp.IsQueryBounded
  refine (OracleComp.IsCostBounded.bind (ProbOracleComp.IsQueryBounded.sample _) fun b =>
    OracleComp.IsCostBounded.bind (ProbOracleComp.IsQueryBounded.sample _) fun m => ?_).mono
      (show 0 + (0 + 1) ≤ 1 by decide)
  rw [bind_pure_comp, OracleComp.isCostBounded_map_iff, OracleComp.isCostBounded_map_iff]
  exact ProbOracleComp.IsQueryBounded.query _

private theorem two_rounds_queryBound (x : SDInstance) :
    (sequentialRepeat 2 x.round).IsQueryBounded 2 := by
  rw [sequentialRepeat_eq_iterate]
  refine OracleComp.IsCostBounded.iterate (c := 1) (fun b => ?_) 2 true
  cases b
  · exact .pure _ _
  · exact x.round_queryBound

end SDInstance

public section

variable {α : Type} {enc : α ↪ List Bool}

/-- Languages reducing to Statistical Difference admit public-coin Arthur–Merlin protocols.
The reduction uses the complete-problem definition of `SZK`, the private-coin protocol of
[Sahai and Vadhan, §3.3][SahaiVadhan2003], and Goldwasser–Sipser public-coin simulation. -/
theorem SZK_subset_AM : SZK enc ⊆ AM enc := by
  intro A hA
  obtain ⟨f, hf, hyes, hno⟩ :=
    (mem_PromiseSZK_iff_polyTimeReducible (hi := 15 / 16) (lo := 1 / 16)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mp hA
  rw [← IPQueryBounded_eq_AM enc (q := 2) (by decide)]
  refine ⟨fun a => sequentialRepeat 2 (f a).round,
    ((isOraclePPTOn_sequentialRepeat (isOraclePPTOn_guessingRound SDInstance.isPPTOn_message)
      2).preprocess hf), fun a => (f a).two_rounds_queryBound, ?_⟩
  constructor
  · intro a ha
    have hd := mem_yes_statisticalDifference.mp (hyes ha)
    refine ⟨(f a).best, le_trans ?_ (le_acceptProb_sequentialRepeat (c := 15 / 16)
      (f a).best (fun s => ?_) 2)⟩
    · simp (discharger := norm_num) only [← ENNReal.coe_ofNat, ← ENNReal.coe_div,
        ← ENNReal.coe_pow, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, NNReal.coe_pow,
        NNReal.coe_div, NNReal.coe_ofNat]
      norm_num
    · cases s
      apply (ENNReal.toReal_le_toReal (ENNReal.div_ne_top (by simp) (by norm_num))
        (show acceptProb (f a).round (f a).best ≠ ⊤ from PMF.apply_ne_top _ _)).mp
      rw [SDInstance.round_probability_best]
      norm_num
      linarith
  · intro a ha P
    have hd := (mem_no_statisticalDifference (by norm_num : (1 / 16 : ℝ) < 15 / 16)).mp (hno ha)
    refine (acceptProb_sequentialRepeat_le (ε := 17 / 32) (fun Q => ?_) 2 P).trans ?_
    · apply (ENNReal.toReal_le_toReal (PMF.apply_ne_top _ _)
        (ENNReal.div_ne_top (by simp) (by norm_num))).mp
      refine ((f a).round_probability_le Q).trans ?_
      norm_num
      linarith
    · simp (discharger := norm_num) only [← ENNReal.coe_ofNat, ← ENNReal.coe_one,
        ← ENNReal.coe_div, ← ENNReal.coe_pow, ENNReal.coe_le_coe, ← NNReal.coe_le_coe,
        NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_one]
      norm_num

end

end Cslib.Complexity
