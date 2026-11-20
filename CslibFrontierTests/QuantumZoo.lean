/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Complexity.Classes.BQP.Search
import CslibFrontier.Computability.Complexity.Classes.FBPP
import CslibFrontier.Computability.Complexity.Classes.BQP.SBQP
import CslibFrontier.Computability.Complexity.Classes.BQP.ZQP
import CslibFrontier.Computability.Complexity.Classes.QMA.QCMA
import CslibFrontier.Computability.Complexity.Classes.QNC
import CslibFrontierTests.BQPTensorContraction

/-! The first-bit language has exact acceptance without any gates. The same circuit witnesses
small-gap decision and classical-witness verification, and its empty layering has constant depth.
-/

namespace CslibFrontierTests.QuantumZoo

open Cslib Cslib.Complexity Cslib.Quantum Turing.MultiTapeTM
  CslibFrontierTests.BQPTensorContraction

example : FirstBit ∈ QCMA encBits :=
  BQP_subset_QCMA (BQTIME_subset_BQP _ (firstBit_mem_BQTIME fun _ => 0))

example : FirstBit ∈ SBQP encBits := by
  refine ⟨readFirst, 0, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · rw [encBits_apply, acceptProb_readFirst]
    rw [ite_eq_left (show x.headD false = true from hx)]
    norm_num
  · rw [encBits_apply, acceptProb_readFirst]
    rw [ite_eq_right (show x.headD false ≠ true from hx)]
    norm_num

private def readFirstLayered : LayeredCircuitFamily where
  width n := n + 1
  layers _ := []
  width_bound := ⟨Polynomial.X + 1, by simp⟩
  input_le_width := by omega
  width_pos := by omega
  arity_pos := by simp
  disjoint_wires := by simp

example : FirstBit ∈ QNC0 encBits := by
  refine ⟨readFirstLayered, ⟨0, by
    intro n layer hLayer
    exact (List.not_mem_nil hLayer).elim⟩,
    ⟨0, by simp [readFirstLayered]⟩, fun x => ?_⟩
  have hprob : readFirstLayered.acceptProb (encBits x) = readFirst.acceptProb x := by
    rw [encBits_apply]
    simp [LayeredCircuitFamily.acceptProb, readFirstLayered, UniformCircuitFamily.acceptProb,
      readFirst, Quantum.acceptProb, Circuit.ofCodes_nil]
  rw [hprob, acceptProb_readFirst]
  exact ⟨fun hx => ite_eq_left (show x.headD false = true from hx),
    fun hx => ite_eq_right (show x.headD false ≠ true from hx)⟩

private def readFlaggedAnswer : UniformAlgebraicCircuitFamily where
  gateCount := 0
  arity := Fin.elim0
  gate i := i.elim0
  algebraic i := i.elim0
  width n := n + 2
  instructions _ := []
  computableInPolyTime_width := by fun_prop
  computableInPolyTime_instructions := ComputableInPolyTime.const _
  input_le_width := by omega
  output_le_width := by omega
  label_lt := by simp
  wires_length := by simp
  wires_nodup := by simp
  wires_lt := by simp

example : readFlaggedAnswer.answerProb [false, true] false = 1 := by
  change measureProb (Circuit.run [] (inputState 4 [false, true]))
    (patternAt 4 [(0, false), (1, true)]) = 1
  rw [Circuit.run, Circuit.eval_nil, measureProb_ket,
    ite_eq_left (by decide)]

example : readFlaggedAnswer.answerProb [true, false] true = 0 := by
  change measureProb (Circuit.run [] (inputState 4 [true, false]))
    (patternAt 4 [(0, true), (1, true)]) = 0
  rw [Circuit.run, Circuit.eval_nil, measureProb_ket,
    ite_eq_right (by decide)]

/-- The relation admits multiple outputs, and always returning the empty word succeeds. -/
example : (fun (_ : List Bool) w => w = [] ∨ w = [true]) ∈ FBPP encBits encBits := by
  refine ⟨fun _ => ⟨[], Or.inl rfl⟩, fun _ => pure [],
    (ComputableInPolyTime.const ([] : List Bool)).isPPTOn, ?_⟩
  intro ε hε
  refine ⟨0, fun a _ => ?_⟩
  simp [ProbComp.eval_pure, PMF.toOuterMeasure_pure_apply]
  linarith

/-- A decoder returning the empty word finds one of the valid outputs on every measurement. -/
example : (fun (_ : List Bool) w => w = [] ∨ w = [true]) ∈ FBQP encBits := by
  refine ⟨fun _ => ⟨[], Or.inl rfl⟩, readFirst, fun _ => some [],
    ComputableInPolyTime.const _, ?_⟩
  intro ε hε
  refine ⟨0, fun a _ => ?_⟩
  simp only [quantumSearchSuccess, eq_self, true_or, Set.ofPred_true,
    PMF.toOuterMeasure_apply, Set.indicator_univ, PMF.tsum_coe, ENNReal.toReal_one]
  linarith

end CslibFrontierTests.QuantumZoo
