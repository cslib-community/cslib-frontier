/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Boolean.ACC0.UniversalSimulation
import CslibFrontier.Computability.Circuit.Boolean.SymAnd.ACC0.WitnessVerifier
import CslibFrontier.Computability.Complexity.Classes.Hierarchy.FineNondeterministicExponentialTime

/-!
# Tests for fine `NTIME` hierarchy, Lemma 5.1 universal simulation, and `ACC⁰` witness verifier

Concrete and non-vacuous checks for:
* `CslibFrontier.Computability.Complexity.Classes.Hierarchy.FineNondeterministicExponentialTime`;
* `CslibFrontier.Computability.Circuit.Boolean.ACC0.UniversalSimulation`;
* `CslibFrontier.Computability.Circuit.Boolean.SymAnd.ACC0.WitnessVerifier`.

Covers model boundaries including:
* valid satisfying `ACC⁰` witness circuit (`decodeExtWitness = some`, verifier UNSAT);
* valid non-satisfying `ACC⁰` witness circuit (verifier SAT);
* malformed/empty certificate bit string (`decodeExtWitness = none`, verifier SAT);
* depth-exceeding semantically satisfying `ACC⁰` witness circuit (`depth > d`,
  `decodeExtWitness = none`, verifier SAT);
* non-vacuous instantiation of `smallACC0WitnessLanguage_mem_NTIME_of_acc0SAT` and
  `exists_hard_acc0Witness_of_quasilinear_reduction`, and a satisfying instance of
  `CheckedACC0Decoders` for `checkedACC0WitnessLanguage_mem_NTIME_of_acc0SAT`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Computability.Circuit.Boolean.SymAnd.ACC0.WitnessVerifier

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.SymAnd
  Cslib.Complexity Turing.MultiTapeTM

/-! ### 1. Fine nondeterministic exponential time hierarchy -/

example : FineExpLazyDiagonal.certLen 1 4 = 2 := by decide
example : FineExpLazyDiagonal.horizon 2 3 = 32 := by decide

example : ∃ k : ℕ, NTIME encBits (fun n => 2 ^ n / (n + 1) ^ k) ⊂
    NTIME encBits fun n => 2 ^ n :=
  exists_NTIME_two_pow_div_pow_ssubset

example : NTIME encBits (fun n => ⌊(2 : ℝ) ^ ((n : ℝ) - (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ))⌋₊) ⊂
    NTIME encBits fun n => 2 ^ n :=
  NTIME_two_pow_sub_rpow_ssubset (by norm_num) (by norm_num)

/-! ### 2. Lemma 5.1 universal simulation -/

/-- Two-input De Morgan XOR circuit. -/
def xorCircuit : Circuit Boolean.signature 2 1 :=
  (Formula.xor (.input 0) (.input 1)).toCircuit

theorem xorCircuit_eval_tf : xorCircuit.eval Boolean.interpretation ![true, false] 0 = true := by
  simp [xorCircuit, Formula.eval_toCircuit, Formula.eval_xor]

theorem xorCircuit_eval_tt : xorCircuit.eval Boolean.interpretation ![true, true] 0 = false := by
  simp [xorCircuit, Formula.eval_toCircuit, Formula.eval_xor]

/-- `circuitEvalLanguage` accepts `evalPrefix xorCircuit ++ [true, false]` and rejects
`evalPrefix xorCircuit ++ [true, true]`. -/
theorem circuitEvalLanguage_xor_boundaries :
    evalPrefix xorCircuit ++ [true, false] ∈ circuitEvalLanguage ∧
    evalPrefix xorCircuit ++ [true, true] ∉ circuitEvalLanguage := by
  constructor
  · have h := (mem_circuitEvalLanguage_evalPrefix xorCircuit ![true, false]).2 xorCircuit_eval_tf
    simpa [List.ofFn_succ, List.ofFn_zero] using h
  · intro h
    have h1 : evalPrefix xorCircuit ++ List.ofFn (![true, true] : BitString 2) ∈
        circuitEvalLanguage := by
      simpa [List.ofFn_succ, List.ofFn_zero] using h
    have h2 := (mem_circuitEvalLanguage_evalPrefix xorCircuit ![true, true]).1 h1
    rw [xorCircuit_eval_tt] at h2
    exact Bool.false_ne_true h2

example : circuitEvalLanguage ∈ P encBits :=
  circuitEvalLanguage_mem_P

/-! ### 3. `ACC⁰` witness verifier and model boundaries -/

/-- Concrete depth-1 `ACC⁰[2]` succinct 3-CNF decoder (`q = 1, r = 1`): every clause is
`(var ![false] = true) ∨ (var ![false] = true) ∨ (var ![false] = true)`. -/
def testDecoder : Circuit Unbounded.extSignature 1 (3 * (1 + 1)) :=
  let p1 : Program Unbounded.extSignature 1 1 :=
    Program.gate Program.empty ⟨.ac (.or 0), Fin.elim0⟩
  let p2 : Program Unbounded.extSignature 1 2 :=
    Program.gate p1 ⟨.ac (.and 0), Fin.elim0⟩
  ⟨p2, fun i => if i.val % 2 = 0 then Wire.gate 0 else Wire.gate 1⟩

/-- Valid depth-1 satisfying witness circuit computing constant `true`. -/
def testWitnessTrue : Circuit Unbounded.extSignature 1 1 :=
  Circuit.oneGate (σ := Unbounded.extSignature) (.ac (.and 0)) Fin.elim0

/-- Valid depth-1 non-satisfying witness circuit computing constant `false`. -/
def testWitnessFalse : Circuit Unbounded.extSignature 1 1 :=
  Circuit.oneGate (σ := Unbounded.extSignature) (.ac (.or 0)) Fin.elim0

/-- Valid depth-2 satisfying witness circuit computing `¬false = true`, exceeding depth cap `1`. -/
def testWitnessDeep : Circuit Unbounded.extSignature 1 1 :=
  let p1 : Program Unbounded.extSignature 1 1 :=
    Program.gate Program.empty ⟨.ac (.or 0), Fin.elim0⟩
  let p2 : Program Unbounded.extSignature 1 2 :=
    Program.gate p1 ⟨.ac .not, fun _ => Wire.gate 0⟩
  ⟨p2, fun _ => Wire.gate ⟨1, by decide⟩⟩

theorem depth_testDecoder : testDecoder.depth ≤ 1 := by
  have h : testDecoder.depthWith 1 ≤ 1 := by
    rw [Circuit.depthWith_le_iff]
    intro j
    dsimp only [testDecoder]
    split_ifs with hmod
    · change (Program.gate
          (Program.gate (Program.empty : Program Unbounded.extSignature 1 0)
            ⟨Unbounded.ExtOp.ac (.or 0), Fin.elim0⟩)
          ⟨Unbounded.ExtOp.ac (.and 0), Fin.elim0⟩).depthsWith 1 (Fin.castSucc (Fin.last 0)) ≤ 1
      rw [Program.depthsWith_gate_castSucc, Program.depthsWith_gate_last]
      rfl
    · change (Program.gate
          (Program.gate (Program.empty : Program Unbounded.extSignature 1 0)
            ⟨Unbounded.ExtOp.ac (.or 0), Fin.elim0⟩)
          ⟨Unbounded.ExtOp.ac (.and 0), Fin.elim0⟩).depthsWith 1 (Fin.last 1) ≤ 1
      rw [Program.depthsWith_gate_last]
      rfl
  simpa only [Circuit.depthWith_one] using h

theorem depth_testWitnessTrue : testWitnessTrue.depth ≤ 1 := by
  simp [testWitnessTrue, Circuit.depth_oneGate]

theorem depth_testWitnessDeep : 1 < testWitnessDeep.depth := by
  have h : testWitnessDeep.depthWith 1 = 2 := by
    change (Fin.foldl 1 (fun acc j => max acc _) 0) = 2
    rw [Fin.foldl_succ, Fin.foldl_zero, Nat.zero_max]
    change (Program.gate
      (Program.gate (Program.empty : Program Unbounded.extSignature 1 0)
        ⟨Unbounded.ExtOp.ac (.or 0), Fin.elim0⟩)
      ⟨Unbounded.ExtOp.ac .not, fun _ => Wire.gate 0⟩).depthsWith 1 (Fin.last 1) = 2
    rw [Program.depthsWith_gate_last]
    rfl
  rw [Circuit.depthWith_one] at h
  omega

private theorem eval_testDecoder_sign (x : BitString 1) (j : Fin 3) :
    testDecoder.eval (Unbounded.extInterpretation (modGate 2)) x
      (SuccinctVerifier.signWire 1 j) = true := by
  fin_cases j
  all_goals
    change (Program.gate
      (Program.gate (Program.empty : Program Unbounded.extSignature 1 0)
        ⟨Unbounded.ExtOp.ac (.or 0), Fin.elim0⟩)
      ⟨Unbounded.ExtOp.ac (.and 0), Fin.elim0⟩).trace
      (Unbounded.extInterpretation (modGate 2)) x (Wire.gate (Fin.last 1)) = true
    rw [Program.trace_gate_last]
    rfl

/-- Boundary 1: valid satisfying depth-1 witness passes verification (`badClauseExt` and
`certificateCircuitExt` are both unsatisfiable). -/
theorem valid_satisfying_witness_passes :
    let w := frame (Circuit.encCode Unbounded.encExtOp testWitnessTrue.code)
    decodeExtWitness 1 1 w = some testWitnessTrue ∧
    ⟨1, badClauseExt testDecoder testWitnessTrue⟩ ∉
      SignatureCircuitSAT (Unbounded.extInterpretation (modGate 2)) ∧
    ⟨1, certificateCircuitExt testDecoder 1 w⟩ ∉
      SignatureCircuitSAT (Unbounded.extInterpretation (modGate 2)) := by
  have hdec : decodeExtWitness 1 1
      (frame (Circuit.encCode Unbounded.encExtOp testWitnessTrue.code)) =
      some testWitnessTrue := by
    simpa only [List.append_nil] using
      decodeExtWitness_frame_append testWitnessTrue depth_testWitnessTrue []
  have hsat : (toCNFExt 2 testDecoder).eval
      (fun y => testWitnessTrue.eval (Unbounded.extInterpretation (modGate 2)) y 0) = true := by
    rw [eval_toCNFExt_eq_true_iff]
    intro x
    rw [Cslib.Logic.PL.Clause.eval_eq_true_iff]
    refine ⟨_, List.mem_ofFn.mpr ⟨0, rfl⟩, ?_⟩
    rw [eval_testDecoder_sign x 0]
    simp only [testWitnessTrue, Circuit.eval_oneGate]
    exact decide_eq_true fun j => j.elim0
  refine ⟨hdec, (not_mem_SignatureCircuitSAT_badClauseExt_iff 2 testDecoder testWitnessTrue).2 hsat,
    (not_mem_SignatureCircuitSAT_certificateCircuitExt_iff 2 testDecoder 1 _).2
      ⟨testWitnessTrue, hdec, hsat⟩⟩

/-- Boundary 2: valid non-satisfying witness fails verification (`badClauseExt` is satisfiable). -/
theorem valid_nonsatisfying_witness_fails :
    ⟨1, badClauseExt testDecoder testWitnessFalse⟩ ∈
      SignatureCircuitSAT (Unbounded.extInterpretation (modGate 2)) := by
  by_contra h
  have hsat := (not_mem_SignatureCircuitSAT_badClauseExt_iff 2 testDecoder testWitnessFalse).1 h
  rw [eval_toCNFExt_eq_true_iff] at hsat
  have hcl := hsat (fun _ => false)
  rw [Cslib.Logic.PL.Clause.eval_eq_true_iff] at hcl
  obtain ⟨l, hl, hev⟩ := hcl
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hl
  rw [eval_testDecoder_sign _ j] at hev
  simp [testWitnessFalse, Circuit.eval_oneGate, Unbounded.extInterpretation,
    Unbounded.interpretation] at hev

/-- Boundary 3: malformed/empty certificate is rejected (`decodeExtWitness = none`,
`certificateCircuitExt` is satisfiable). -/
theorem malformed_certificate_rejected :
    decodeExtWitness 1 1 [] = none ∧
    ⟨1, certificateCircuitExt testDecoder 1 []⟩ ∈
      SignatureCircuitSAT (Unbounded.extInterpretation (modGate 2)) := by
  refine ⟨decodeExtWitness_nil 1 1, ?_⟩
  by_contra h
  obtain ⟨W, hdec, _⟩ :=
    (not_mem_SignatureCircuitSAT_certificateCircuitExt_iff 2 testDecoder 1 []).1 h
  rw [decodeExtWitness_nil] at hdec
  cases hdec

/-- Boundary 4: a depth-2 witness circuit is rejected at depth cap `1` even though it computes
a satisfying assignment (`decodeExtWitness = none`, `certificateCircuitExt` is satisfiable). -/
theorem depth_exceeding_witness_rejected :
    let w := frame (Circuit.encCode Unbounded.encExtOp testWitnessDeep.code)
    decodeExtWitness 1 1 w = none ∧
    ⟨1, certificateCircuitExt testDecoder 1 w⟩ ∈
      SignatureCircuitSAT (Unbounded.extInterpretation (modGate 2)) := by
  have hdec : decodeExtWitness 1 1
      (frame (Circuit.encCode Unbounded.encExtOp testWitnessDeep.code)) = none := by
    simpa only [List.append_nil] using
      decodeExtWitness_eq_none_of_depth_gt testWitnessDeep depth_testWitnessDeep []
  refine ⟨hdec, ?_⟩
  by_contra h
  obtain ⟨W, hdec', _⟩ :=
    (not_mem_SignatureCircuitSAT_certificateCircuitExt_iff 2 testDecoder 1 _).1 h
  rw [hdec] at hdec'
  cases hdec'

/-- Non-vacuous instantiation of `smallACC0WitnessLanguage_mem_NTIME_of_acc0SAT` on the concrete
depth-1 `ACC⁰[2]` decoder family `fun _ => testDecoder`. -/
theorem nonvacuous_smallACC0WitnessLanguage_mem_NTIME :
    ∃ (r_w : ℕ) (δ c₀ : ℝ), 0 < r_w ∧ 0 < δ ∧ δ < 1 ∧ 0 < c₀ ∧
      smallACC0WitnessLanguage 2 1 (fun _ : List Bool => testDecoder)
        (fun x => 2 ^ Nat.nthRoot r_w x.length) ∈
        NTIME encBits fun n => ⌊(2 : ℝ) ^ ((n : ℝ) - c₀ * (n : ℝ) ^ δ)⌋₊ := by
  obtain ⟨r_w, δ, c₀, hrw, hδ, hδ1, hc₀, hsim⟩ :=
    smallACC0WitnessLanguage_mem_NTIME_of_acc0SAT 1 1 (m := 2) (by decide)
  exact ⟨r_w, δ, c₀, hrw, hδ, hδ1, hc₀,
    hsim (fun _ => testDecoder) 1 (ComputableInPolyTime.const 1) (ComputableInPolyTime.const 1)
      (ComputableInPolyTime.const testDecoder.code) (fun _ => depth_testDecoder)
      (fun x => by omega)⟩

/-- A satisfying instance of `CheckedACC0Decoders`: a certificate of length `1`, the constant
`false` check circuit and the decoder `testDecoder`. -/
def testCheckedDecoders :
    CheckedACC0Decoders 1 1 (fun _ => 1) (fun _ => 1) fun _ => 3 * (1 + 1) where
  certLength _ := 1
  slack := 1
  check _ := Unbounded.constCircuit Unbounded.toExt false
  decoder _ := testDecoder
  certLength_polyTime := ComputableInPolyTime.const 1
  certLength_le x := by simp
  check_polyTime := ComputableInPolyTime.const _
  decoder_polyTime := ComputableInPolyTime.const _
  depth_check_le _ := Unbounded.depth_constCircuit_le false
  depth_decoder_le _ := depth_testDecoder

/-- Non-vacuous instantiation of `checkedACC0WitnessLanguage_mem_NTIME_of_acc0SAT` on
`testCheckedDecoders`. -/
theorem nonvacuous_checkedACC0WitnessLanguage_mem_NTIME :
    ∃ (r_w : ℕ) (δ c₀ : ℝ), 0 < r_w ∧ 0 < δ ∧ δ < 1 ∧ 0 < c₀ ∧
      checkedACC0WitnessLanguage 2 1 (q₁ := fun _ => 1) (q := fun _ => 1) (r := fun _ => 1)
        testCheckedDecoders.check testCheckedDecoders.decoder testCheckedDecoders.certLength
        (fun x => 2 ^ Nat.nthRoot r_w x.length) ∈
        NTIME encBits fun n => ⌊(2 : ℝ) ^ ((n : ℝ) - c₀ * (n : ℝ) ^ δ)⌋₊ := by
  obtain ⟨r_w, δ, c₀, hrw, hδ, hδ1, hc₀, hsim⟩ :=
    checkedACC0WitnessLanguage_mem_NTIME_of_acc0SAT 1 1 1 (m := 2) (by decide)
  exact ⟨r_w, δ, c₀, hrw, hδ, hδ1, hc₀,
    hsim (r := fun _ => 1) testCheckedDecoders 1 (ComputableInPolyTime.const 1)
      (ComputableInPolyTime.const 1) (ComputableInPolyTime.const 1) (fun x => by omega)
      (fun x => by omega)⟩

/-- Non-vacuous instantiation of `exists_hard_acc0Witness_of_quasilinear_reduction`. -/
example :
    ∃ (r_w : ℕ) (H : Set (List Bool)), 0 < r_w ∧ H ∈ NTIME encBits (fun n => 2 ^ n) ∧
      ∀ {q r : List Bool → ℕ}
        (D : (x : List Bool) → Circuit Unbounded.extSignature (q x) (3 * (r x + 1)))
        (c : ℕ),
        ComputableInPolyTime q encBits encUnary →
        ComputableInPolyTime r encBits encUnary →
        ComputableInPolyTime (fun x => (D x).code) encBits (Circuit.encCode Unbounded.encExtOp) →
        (∀ x, (D x).depth ≤ 1) →
        (∀ x, q x ≤ x.length + c * Nat.log 2 (x.length + 2) + c) →
        (∀ x, x ∈ H ↔ (toCNFExt 2 (D x)).Satisfiable) →
        ∀ N₀ : ℕ, ∃ x ∈ H, N₀ ≤ x.length ∧ ¬ ∃ W : Circuit Unbounded.extSignature (r x) 1,
          W.depth ≤ 1 ∧
          (Circuit.encCode Unbounded.encExtOp W.code).length ≤ 2 ^ Nat.nthRoot r_w x.length ∧
          (toCNFExt 2 (D x)).eval
            (fun y => W.eval (Unbounded.extInterpretation (modGate 2)) y 0) = true :=
  exists_hard_acc0Witness_of_quasilinear_reduction 1 1 (m := 2) (by decide)

end CslibFrontierTests.Computability.Circuit.Boolean.SymAnd.ACC0.WitnessVerifier
