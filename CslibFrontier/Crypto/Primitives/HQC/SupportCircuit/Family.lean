/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ParallelCode
public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Generator
public import CslibFrontier.Computability.Circuit.Quantum.Output
public import CslibFrontier.Computability.Circuit.Quantum.Reversible.Sampling.Prefix
public import CslibFrontier.Crypto.Game.AttackResources
public import CslibFrontier.Crypto.Primitives.HQC.SupportCircuit.PolyTime
public import CslibFrontier.Crypto.Primitives.HQC.SupportCircuit.Resolve.PolyTime
public import CslibFrontier.Crypto.Primitives.HQC.SupportCircuit.Sampler
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Foundations.Data.List.UnaryCode

/-!
# A growing-width client of the HQC support sampler

This module gives one concrete asymptotic schedule for the existing finite sampler.  At security
parameter `s`, two independent `(s + 1)`-bit words sample a support of weight two in a universe of
size three.  The schedule deliberately retains the ordinary non-dyadic finite law and its exact
collision correction; its discrepancy from the ideal fixed-weight law is negligible as `s`
grows.

The fixed `(n, count) = (3, 2)` schedule is a deliberately small checked client of the generic
sampler construction.  It is not a published HQC parameter schedule and does not compose the
three support vectors used by HQC encryption.

The Boolean circuit is generated natively from component codes.  The uniform quantum family then
clears the known unary security-parameter input, runs the reversible sampler, and moves its output
block to the measured prefix.  Generator time, workspace, static program bits, generated
description bits, and online circuit resources remain separate.  In particular, this module does
not charge offline generation as attack execution, instantiate the actual HQC reduction schedule,
or make an HQC security or QROM claim.

## Main definitions

* `Cslib.Crypto.HQC.growingSupportCircuit`: the concrete Boolean sampler at a supplied word width.
* `Cslib.Crypto.HQC.growingSupportSamplerFamily`: its growing-width uniform quantum family.

## Main results

* `Cslib.Crypto.HQC.samplerDist_growingSupportCircuit`: the exact finite `sampleSupport2` law.
* `Cslib.Crypto.HQC.negligible_growingSupportSamplerError`: negligible non-dyadic discrepancy.

The circuit-generation and family-composition results are original infrastructure.  The finite
sampler law and its density bound are reused unchanged from `SupportCircuit.Sampler` and
`SupportProbability`.
-/

public section

namespace Cslib.Crypto.HQC

open Circuits Circuits.Boolean BitString Probability
open Quantum Quantum.GateCode Quantum.Reversible
open Turing.MultiTapeTM ComputableInPolyTime

/-- The two fixed multiply-high candidates, each reading its own `width`-bit source word. -/
private def growingSupportCandidates (width : ℕ) : Circuit signature (2 * width) (2 * 2) :=
  ((candidateCircuit width 2 3 0).parallel (candidateCircuit width 2 3 1)).comp
    (Circuit.wiring signature (Fin.cast (Nat.two_mul width).symm))

/-- Raw native code for `growingSupportCandidates`, including its input-block wiring. -/
private def growingSupportCandidatesCode (width : ℕ) :
    List (Op × List ℕ) × List ℕ :=
  compCode (2 * width)
    (parallelCode width width (candidateCircuit width 2 3 0).code
      (candidateCircuit width 2 3 1).code)
    ([], List.range (2 * width))

/-- The native two-candidate code agrees with every gate and output wire of the typed circuit. -/
private theorem growingSupportCandidatesCode_eq_code (width : ℕ) :
    growingSupportCandidatesCode width = (growingSupportCandidates width).code := by
  rw [growingSupportCandidatesCode, growingSupportCandidates]
  rw [show ([], List.range (2 * width)) =
      (Circuit.wiring signature (Fin.cast (Nat.two_mul width).symm)).code by
    symm
    simpa [Nat.two_mul] using Circuit.code_wiring_eq_map
      (σ := signature) (f := Fin.cast (Nat.two_mul width).symm) (g := id) (fun _ => rfl)]
  rw [parallelCode_code, compCode_code]

/-- The complete two-candidate circuit has a native polynomial-time generator in the unary word
width. -/
@[fun_prop] private theorem computableInPolyTime_growingSupportCandidates :
    ComputableInPolyTime (fun width => (growingSupportCandidates width).code)
      encUnary encCode := by
  have hparallel := computableInPolyTime_parallelCode id' id'
    (computableInPolyTime_candidateCircuit id' (const 2) (const 3) (const 0))
    (computableInPolyTime_candidateCircuit id' (const 2) (const 3) (const 1))
  have hinput : ComputableInPolyTime
      (fun width => ([], List.range (2 * width))) encUnary encCode := by
    have htwice : ComputableInPolyTime (fun width : ℕ => 2 * width) encUnary encUnary :=
      unary_mul' (const 2) id'
    have hwires := unary_to_binary.map.comp (range.comp htwice)
    exact (const (encOut := encList encGate) []).prod
      (by simpa only [Function.comp_def, List.map_id_fun', id_eq] using hwires)
  have h := computableInPolyTime_compCode (binary_mul' (const 2) unary_to_binary)
    hparallel hinput
  change ComputableInPolyTime growingSupportCandidatesCode encUnary encCode at h
  have heq : (fun width => (growingSupportCandidates width).code) =
      growingSupportCandidatesCode := by
    funext width
    exact (growingSupportCandidatesCode_eq_code width).symm
  rw [heq]
  exact h

/-- The natively generated pair has exactly the semantics of the existing two-element candidate
family. -/
private theorem eval_growingSupportCandidates (width : ℕ) (x : BitString (2 * width)) :
    (growingSupportCandidates width).eval interpretation x =
      (supportCandidateCircuit width 2 3 2).eval interpretation x := by
  funext i
  obtain ⟨⟨j, k⟩, rfl⟩ := finProdFinEquiv.surjective i
  change _ = (Circuit.parallelFamily fun j : Fin 2 =>
    candidateCircuit width 2 3 j.val).eval interpretation x (finProdFinEquiv (j, k))
  rw [Circuit.eval_parallelFamily_apply]
  simp only [growingSupportCandidates, Circuit.eval_comp, Circuit.eval_wiring,
    Circuit.eval_parallel]
  have hleft :
      ((x ∘ Fin.cast (Nat.two_mul width).symm) ∘ Fin.castAdd width) = block x (0 : Fin 2) := by
    funext q
    apply congrArg x
    apply Fin.ext
    simp [finProdFinEquiv]
  have hright :
      ((x ∘ Fin.cast (Nat.two_mul width).symm) ∘ Fin.natAdd width) = block x (1 : Fin 2) := by
    funext q
    apply congrArg x
    apply Fin.ext
    simp [finProdFinEquiv]
  rw [hleft, hright]
  fin_cases j
  · change Fin.append _ _ (finProdFinEquiv ((0 : Fin 2), k)) =
      (candidateCircuit width 2 3 0).eval interpretation (block x 0) k
    rw [show finProdFinEquiv ((0 : Fin 2), k) = Fin.castAdd 2 k by
      apply Fin.ext
      simp [finProdFinEquiv], Fin.append_left]
  · change Fin.append _ _ (finProdFinEquiv ((1 : Fin 2), k)) =
      (candidateCircuit width 2 3 1).eval interpretation (block x 1) k
    rw [show finProdFinEquiv ((1 : Fin 2), k) = Fin.natAdd 2 k by
      apply Fin.ext
      simp [finProdFinEquiv], Fin.append_right]

/-- The concrete Boolean sampler: two multiply-high candidates, exact descending collision
correction, and a three-bit support indicator. -/
def growingSupportCircuit (width : ℕ) : Circuit signature (2 * width) 3 :=
  (supportIndicatorCircuit 2 3 2).comp
    ((supportScanCircuit 2 0 2).comp (growingSupportCandidates width))

/-- The concrete circuit evaluates exactly like the existing generic sampler at parameters
`bits = 2`, `n = 3`, and `count = 2`. -/
theorem eval_growingSupportCircuit (width : ℕ) (x : BitString (2 * width)) :
    (growingSupportCircuit width).eval interpretation x =
      (supportSamplerCircuit width 2 3 2).eval interpretation x := by
  simp only [growingSupportCircuit, supportSamplerCircuit, Circuit.eval_comp]
  rw [eval_growingSupportCandidates]

/-- The whole concrete Boolean sampler has a native polynomial-time code generator. -/
@[fun_prop] theorem computableInPolyTime_growingSupportCircuit :
    ComputableInPolyTime (fun width => (growingSupportCircuit width).code)
      encUnary encCode := by
  have hinput := binary_mul' (const 2) unary_to_binary
  have hscan : ComputableInPolyTime
      (fun _ : ℕ => (supportScanCircuit 2 0 2).code) encUnary encCode := const _
  have hindicator : ComputableInPolyTime
      (fun _ : ℕ => (supportIndicatorCircuit 2 3 2).code) encUnary encCode := const _
  have hinner := computableInPolyTime_compCode hinput hscan
    computableInPolyTime_growingSupportCandidates
  have h := computableInPolyTime_compCode hinput hindicator hinner
  simpa only [growingSupportCircuit, compCode_code] using h

private theorem samplerDist_growingSupportCircuit_eq (width : ℕ) :
    samplerDist (growingSupportCircuit width) =
      samplerDist (supportSamplerCircuit width 2 3 2) := by
  rw [samplerDist_eq_outputDist, samplerDist_eq_outputDist]
  have heval : (growingSupportCircuit width).eval interpretation =
      (supportSamplerCircuit width 2 3 2).eval interpretation := by
    funext x
    exact eval_growingSupportCircuit width x
  unfold Circuit.outputDist
  rw [heval]

/-- Measuring the reversible concrete sampler retains the exact finite `sampleSupport2` law,
including its non-dyadic bias and collision correction. -/
theorem samplerDist_growingSupportCircuit (width : ℕ) :
    samplerDist (growingSupportCircuit width) =
      (ProbComp.eval (sampleSupport2 width 3 2)).map (indicatorVector 3) := by
  rw [samplerDist_growingSupportCircuit_eq]
  exact samplerDist_supportSamplerCircuit (by decide) (by decide)

/-- The exact finite discrepancy of the growing schedule from the ideal weight-two support law. -/
theorem growingSupportSampler_closeTo_ideal (s : ℕ) :
    CloseTo (samplerDist (growingSupportCircuit (s + 1)))
      ((PMF.uniformOfFinset ((Finset.range 3).powersetCard 2)
        (Finset.powersetCard_nonempty.mpr (by decide))).map (indicatorVector 3))
      (ENNReal.ofReal (1 - (supportLowerDensity (s + 1) 3 0 2).toReal)) := by
  rw [samplerDist_growingSupportCircuit_eq]
  exact supportSamplerDist_closeTo_ideal (by decide) (by decide)

/-- The growing word width makes the exact non-dyadic sampling discrepancy negligible. -/
theorem negligible_growingSupportSamplerError :
    Negligible (fun s => Real.toNNReal
      (1 - (supportLowerDensity (s + 1) 3 0 2).toReal)) := by
  apply negligible_one_sub_supportLowerDensity
    (width := fun s => s + 1) (n := fun _ => 3) (count := fun _ => 2)
  · intro s
    omega
  · exact .const 3
  · exact .const 2
  · intro s
    omega

/-- Flipping the framed unary security parameter clears the initialized basis word for empty
auxiliary input.  No deterministic input bit is used as a fair sampler seed. -/
private theorem classicalRun_clearGrowingSupportInput {s width : ℕ}
    (hwidth : 2 * s + 1 ≤ width) :
    classicalRun (flipCodes (List.range (2 * s)))
      (inputState width (encPair encUnary encBits (s, []))) = inputState width [] := by
  apply funext_readBit
  intro c
  rw [readBit_classicalRun_flipCodes List.nodup_range
    (by intro j hj; have := List.mem_range.mp hj; omega)]
  rw [readBit_inputState (by simp [encUnary_apply]; omega),
    readBit_inputState (by simp)]
  simp only [encPair_apply, encUnary_apply, encBits_apply, List.append_nil,
    frame_replicate_true]
  by_cases hc : c ≤ 2 * s
  · rw [List.getD_replicate_true_append_false_of_le [] hc]
    simp only [List.mem_range, List.getD_nil]
    by_cases hlt : c < 2 * s <;> simp [hlt]
  · have hc' : 2 * s + 1 ≤ c := by omega
    have hlen : (List.replicate (2 * s) true ++ [false]).length ≤ c := by
      simp only [List.length_append, List.length_replicate, List.length_singleton]
      omega
    rw [List.getD_eq_default _ _ hlen]
    have hnot : ¬c < 2 * s := by omega
    simp [List.mem_range, hnot]

/-- Active width of the reversible growing sampler before allowance for an auxiliary input. -/
@[expose] def growingSupportSamplerWidth (s : ℕ) : ℕ :=
  samplerWidth (2 * (s + 1)) (growingSupportCircuit (s + 1)).code

/-- Complete oracle-free gate code at security parameter `s`: clear the known framed unary
input, run the reversible sampler, then move its three-bit output block to the measured prefix. -/
@[expose] def growingSupportSamplerGateCodes (s : ℕ) : List GateCode :=
  flipCodes (List.range (2 * s)) ++
    samplerCodes (2 * (s + 1)) (growingSupportCircuit (s + 1)).code ++
    prefixSwapCodes
      (samplerOutputStart (2 * (s + 1)) (growingSupportCircuit (s + 1)).code) 3

private theorem computableInPolyTime_growingSupportSeed :
    ComputableInPolyTime (fun s : ℕ => 2 * (s + 1)) encUnary encUnary := by
  fun_prop

private theorem computableInPolyTime_growingSupportCircuitCode :
    ComputableInPolyTime (fun s => (growingSupportCircuit (s + 1)).code)
      encUnary encCode := by
  exact computableInPolyTime_growingSupportCircuit.comp (by fun_prop)

/-- The complete family gate list is generated in polynomial time from the unary security
parameter. -/
@[fun_prop] theorem computableInPolyTime_growingSupportSamplerGateCodes :
    ComputableInPolyTime growingSupportSamplerGateCodes encUnary (encList encGateCode) := by
  have hseed := computableInPolyTime_growingSupportSeed
  have hcode := computableInPolyTime_growingSupportCircuitCode
  have hsampler := computableInPolyTime_samplerCodes hseed hcode
  have hsource : ComputableInPolyTime
      (fun s => samplerOutputStart (2 * (s + 1))
        (growingSupportCircuit (s + 1)).code) encUnary encUnary :=
    computableInPolyTime_samplerOutputStart hseed hcode
  have hprefix := computableInPolyTime_prefixSwapCodes hsource (const 3)
  unfold growingSupportSamplerGateCodes flipCodes
  fun_prop

private theorem run_growingSupportSamplerGateCodes (s : ℕ) :
    let C := growingSupportCircuit (s + 1)
    let seed := 2 * (s + 1)
    let width := samplerWidth seed C.code
    Circuit.run (Circuit.ofCodes width (growingSupportSamplerGateCodes s))
        (inputState width (encPair encUnary encBits (s, []))) =
      Circuit.eval (Circuit.ofCodes width
          (prefixSwapCodes (samplerOutputStart seed C.code) 3))
        (Circuit.run (Circuit.ofCodes width (samplerCodes seed C.code))
          (inputState width [])) := by
  dsimp only
  have hclear : IsClassical
      (samplerWidth (2 * (s + 1)) (growingSupportCircuit (s + 1)).code)
      (flipCodes (List.range (2 * s))) :=
    isClassical_flipCodes (by
      intro j hj
      have hj' := List.mem_range.mp hj
      unfold samplerWidth samplerOutputStart samplerZero
      omega)
  rw [Circuit.run, growingSupportSamplerGateCodes, Circuit.ofCodes_append,
    Circuit.ofCodes_append, Quantum.Circuit.eval_append, Quantum.Circuit.eval_append,
    Circuit.eval_ofCodes_ket hclear,
    classicalRun_clearGrowingSupportInput (by
      unfold samplerWidth samplerOutputStart samplerZero
      omega)]
  rw [Quantum.Circuit.run]

/-- Starting from the actual framed empty input, the complete raw gate list has exactly the
existing reversible sampler law at width `s + 1`.  The prefix adapter and input clearing add no
approximation. -/
theorem measureOut_growingSupportSamplerGateCodes (s : ℕ) :
    let C := growingSupportCircuit (s + 1)
    let seed := 2 * (s + 1)
    let width := samplerWidth seed C.code
    let Q := Circuit.ofCodes width (growingSupportSamplerGateCodes s)
    measureOut (Circuit.run Q (inputState width (encPair encUnary encBits (s, []))))
        (Circuit.norm_run Q _) (blockReadout 0 3) = samplerDist C := by
  dsimp only
  let C := growingSupportCircuit (s + 1)
  let seed := 2 * (s + 1)
  let width := samplerWidth seed C.code
  let source := samplerOutputStart seed C.code
  let ψ : Qubits width := Circuit.run
    (Circuit.ofCodes width (samplerCodes seed C.code)) (inputState width [])
  have hψ : ‖ψ‖ = 1 := by
    dsimp only [ψ]
    exact Circuit.norm_run _ _
  have hrun :
      Circuit.run (Circuit.ofCodes width (growingSupportSamplerGateCodes s))
          (inputState width (encPair encUnary encBits (s, []))) =
        Circuit.eval (Circuit.ofCodes width (prefixSwapCodes source 3)) ψ := by
    simpa only [C, seed, width, source, ψ] using run_growingSupportSamplerGateCodes s
  calc
    measureOut
        (Circuit.run (Circuit.ofCodes width (growingSupportSamplerGateCodes s))
          (inputState width (encPair encUnary encBits (s, []))))
        (Circuit.norm_run _ _) (blockReadout 0 3) =
      measureOut (Circuit.eval (Circuit.ofCodes width (prefixSwapCodes source 3)) ψ)
        (by rw [Circuit.norm_eval, hψ]) (blockReadout 0 3) := by
          congr 1
    _ = measureOut ψ hψ (blockReadout source 3) :=
      measureOut_eval_prefixSwapCodes (by
        dsimp only [source, seed]
        unfold samplerOutputStart samplerZero
        omega) (by
        dsimp only [source, width]
        unfold samplerWidth
        simp only [C, Circuit.code, List.length_ofFn]
        omega) ψ hψ
    _ = samplerDist C := by
      have hout : blockReadout source 3 = samplerReadout C := by
        funext X j
        rw [blockReadout, samplerReadout]
      rw [hout]
      simp only [ψ, width, seed, samplerDist]

/-- The exact finite description generated for a security parameter and auxiliary-input length.
The extra `ℓ` qubits only ensure that every declared classical input fits. -/
@[expose] def growingSupportSamplerDescription (s ℓ : ℕ) : OracleCircuitDescription where
  width := growingSupportSamplerWidth s + ℓ
  queryWidth := 0
  responseWidth := 0
  quantumInputWidth := 0
  outputWidth := 3
  instructions := (growingSupportSamplerGateCodes s).map fun g =>
    OracleGateCode.gate (false, g)

private theorem computableInPolyTime_growingSupportSamplerDescription :
    ComputableInPolyTime
      (fun input : OracleInputSize => growingSupportSamplerDescription
        input.securityParameter input.classicalInputLength)
      encOracleInputSize encOracleCircuitDescription := by
  have hs : ComputableInPolyTime
      (fun input : OracleInputSize => input.securityParameter) encOracleInputSize encUnary := by
    fun_prop
  have hℓ : ComputableInPolyTime
      (fun input : OracleInputSize => input.classicalInputLength) encOracleInputSize encUnary := by
    fun_prop
  have hseed := computableInPolyTime_growingSupportSeed
  have hcode := computableInPolyTime_growingSupportCircuitCode
  have hwidth : ComputableInPolyTime growingSupportSamplerWidth encUnary encUnary :=
    computableInPolyTime_samplerWidth hseed hcode
  have hphase : ComputableInPolyTime (fun g : GateCode => (false, g))
      encGateCode encPhaseGateCode := (const false).prod id'
  have horacle := OracleGateCode.computableInPolyTime_gate hphase
  have hinstructions := horacle.map.comp
    (computableInPolyTime_growingSupportSamplerGateCodes.comp hs)
  unfold growingSupportSamplerDescription
  fun_prop

private theorem wellFormed_growingSupportSamplerDescription (s ℓ : ℕ) :
    (growingSupportSamplerDescription s ℓ).WellFormed ⟨s, ℓ⟩ := by
  let code := (growingSupportCircuit (s + 1)).code
  let seed := 2 * (s + 1)
  let source := samplerOutputStart seed code
  let width := samplerWidth seed code
  have hinput : 2 * s + 1 + ℓ ≤ width + ℓ := by
    dsimp only [width, seed]
    unfold samplerWidth samplerOutputStart samplerZero
    omega
  have hsource : 3 ≤ source := by
    dsimp only [source, seed]
    unfold samplerOutputStart samplerZero
    omega
  have hfit : source + 3 ≤ width := by
    have hlen : code.2.length = 3 := by
      simp only [code, growingSupportCircuit, Circuit.code, List.length_ofFn]
    change source + 3 ≤ source + code.2.length
    rw [hlen]
  have hclear : IsClassical width (flipCodes (List.range (2 * s))) :=
    isClassical_flipCodes (by
      intro j hj
      have hj' := List.mem_range.mp hj
      dsimp only [width, seed]
      unfold samplerWidth samplerOutputStart samplerZero
      omega)
  have hsampler : ∀ g ∈ samplerCodes seed code, g.WellFormed width := by
    simpa only [width] using wellFormed_samplerCodes seed code
  have hprefix : IsClassical width (prefixSwapCodes source 3) :=
    isClassical_prefixSwapCodes hsource hfit
  refine ⟨hinput, by simp [growingSupportSamplerDescription], ?_, ?_⟩
  · change 3 ≤ width + ℓ
    omega
  intro instruction hinstruction
  simp only [growingSupportSamplerDescription, List.mem_map] at hinstruction
  obtain ⟨g, hg, rfl⟩ := hinstruction
  change OracleGateCode.WellFormed 0 0 (width + ℓ) (.gate (false, g))
  simp only [OracleGateCode.WellFormed, PhaseGateCode.WellFormed]
  have hgwidth : g.WellFormed width := by
    simp only [growingSupportSamplerGateCodes, List.mem_append] at hg
    rcases hg with (hg | hg) | hg
    · exact (hclear g hg).2
    · exact hsampler g hg
    · exact (hprefix g hg).2
  simpa using hgwidth.shift (o := 0) (by omega : 0 + width ≤ width + ℓ)

/-- A native uniform oracle-circuit family for the growing support sampler.  It is oracle-free and
its certified output law below is for empty auxiliary input. -/
def growingSupportSamplerFamily : UniformOracleCircuitFamily where
  description := growingSupportSamplerDescription
  computableInPolyTime_description := computableInPolyTime_growingSupportSamplerDescription
  wellFormed := wellFormed_growingSupportSamplerDescription

private theorem output_growingSupportSamplerFamily_eq_measureOut (s : ℕ) :
    growingSupportSamplerFamily.output s [] (fun _ _ => false)
        (ket (fun _ => false)) (norm_ket _) =
      (measureOut
        (Circuit.run
          (Circuit.ofCodes (growingSupportSamplerWidth s) (growingSupportSamplerGateCodes s))
          (inputState (growingSupportSamplerWidth s) (encPair encUnary encBits (s, []))))
        (Circuit.norm_run _ _) (blockReadout 0 3)).map List.ofFn := by
  let H : (Fin (growingSupportSamplerFamily.description s 0).queryWidth → Bool) →
      Fin (growingSupportSamplerFamily.description s 0).responseWidth → Bool :=
    fun _ _ => false
  let z : Fin (growingSupportSamplerFamily.description s 0).quantumInputWidth → Bool :=
    fun _ => false
  let ψ : Qubits (growingSupportSamplerFamily.description s 0).width :=
    Circuit.eval
      (OracleCircuit.toCircuit (growingSupportSamplerFamily.description s 0).width H
        (growingSupportSamplerFamily.description s 0).instructions)
      (ket (inputState (growingSupportSamplerFamily.description s 0).width
        (encPair encUnary encBits (s, ([] : List Bool)) ++ List.ofFn z)))
  have hψ : ‖ψ‖ = 1 := by
    dsimp only [ψ]
    rw [Circuit.norm_eval, norm_ket]
  calc
    growingSupportSamplerFamily.output s [] (fun _ _ => false)
        (ket (fun _ => false)) (norm_ket _) =
      measureOut ψ hψ (fun y => List.ofFn fun i =>
        y (Fin.castLEEmb (growingSupportSamplerFamily.wellFormed s 0).output_le i)) := by
      convert
        (UniformOracleCircuitFamily.output_ket growingSupportSamplerFamily s
          ([] : List Bool) H z) using 1
    _ = measureOut ψ hψ (fun y => List.ofFn
          (blockReadout 0 (growingSupportSamplerFamily.description s 0).outputWidth y)) := by
      congr 1
      exact listOfFn_castLEEmb_eq_blockReadout
        (growingSupportSamplerFamily.wellFormed s 0).output_le
    _ = (measureOut ψ hψ
        (blockReadout 0 (growingSupportSamplerFamily.description s 0).outputWidth)).map
          List.ofFn :=
      (measureOut_map ψ hψ _ List.ofFn).symm
    _ = _ := by
      simp only [H, z, ψ, growingSupportSamplerFamily, growingSupportSamplerDescription,
        List.ofFn_zero, List.append_nil, Nat.add_zero]
      simp only [OracleCircuit.toCircuit_map_gateCode, Quantum.Circuit.run]
      congr 1

/-- On empty auxiliary input, the actual uniform family returns exactly the finite
`sampleSupport2 (s + 1) 3 2` indicator law.  The oracle type is empty, so no oracle behavior enters
the statement. -/
theorem output_growingSupportSamplerFamily (s : ℕ) :
    growingSupportSamplerFamily.output s [] (fun _ _ => false)
        (ket (fun _ => false)) (norm_ket _) =
      ((ProbComp.eval (sampleSupport2 (s + 1) 3 2)).map
        (indicatorVector 3)).map List.ofFn := by
  rw [output_growingSupportSamplerFamily_eq_measureOut,
    growingSupportSamplerWidth, measureOut_growingSupportSamplerGateCodes,
    samplerDist_growingSupportCircuit]

/-- Exact online-circuit and finite-description resources of the generated artifact.  These
coordinates do not include generator time, workspace, or static generator code. -/
@[expose] def growingSupportSamplerCircuitResources (s ℓ : ℕ) : OracleCircuit.Resources :=
  let description := growingSupportSamplerDescription s ℓ
  ⟨description.width, description.instructions.gateCount,
    description.instructions.queryCount, (encOracleCircuitDescription description).length⟩

/-- The generated finite artifact fits its exact four online/description coordinates. -/
theorem within_growingSupportSamplerCircuitResources (s ℓ : ℕ) :
    OracleCircuit.Within (growingSupportSamplerDescription s ℓ).instructions
      (growingSupportSamplerDescription s ℓ).width
      (encOracleCircuitDescription (growingSupportSamplerDescription s ℓ)).length
      (growingSupportSamplerCircuitResources s ℓ) := by
  simp [growingSupportSamplerCircuitResources, OracleCircuit.Within]

/-- The generated family is oracle-free: every instruction is an elementary gate. -/
@[simp] theorem queryCount_growingSupportSamplerDescription (s ℓ : ℕ) :
    (growingSupportSamplerDescription s ℓ).instructions.queryCount = 0 := by
  simp [growingSupportSamplerDescription, OracleCircuit.queryCount,
    OracleGateCode.isQuery]

/-- One retained generator occurrence and one retained generated-description occurrence.  The
latter is the same description charged by the circuit resource's `descriptionBits` coordinate;
it is not a second stored artifact. -/
@[expose] def growingSupportSamplerInstalledArtifacts
    (certificate : growingSupportSamplerFamily.GeneratorCertificate) (s : ℕ) :
    List Crypto.Game.InstalledArtifact :=
  [{ kind := .generator, bits := (certificate.resources ⟨s, 0⟩).codeBits },
    { kind := .generatedProgram, bits := (certificate.resources ⟨s, 0⟩).outputBits }]

/-- The occurrence inventory charges the exact static universal-machine description once. -/
theorem installedBits_growingSupportSamplerGenerator
    (certificate : growingSupportSamplerFamily.GeneratorCertificate) (s : ℕ) :
    Crypto.Game.InstalledArtifact.installedBits
      (growingSupportSamplerInstalledArtifacts certificate s) .generator =
        (Turing.MultiTapeTM.Universal.eDesc certificate.code).length := by
  simp [growingSupportSamplerInstalledArtifacts,
    Crypto.Game.InstalledArtifact.installedBits,
    UniformOracleCircuitFamily.GeneratorCertificate.resources]

/-- The occurrence inventory charges the exact generated description once. -/
theorem installedBits_growingSupportSamplerGeneratedProgram
    (certificate : growingSupportSamplerFamily.GeneratorCertificate) (s : ℕ) :
    Crypto.Game.InstalledArtifact.installedBits
      (growingSupportSamplerInstalledArtifacts certificate s) .generatedProgram =
        (encOracleCircuitDescription (growingSupportSamplerDescription s 0)).length := by
  simp [growingSupportSamplerInstalledArtifacts,
    Crypto.Game.InstalledArtifact.installedBits,
    UniformOracleCircuitFamily.GeneratorCertificate.resources,
    growingSupportSamplerFamily]

/-- The actual uniform family has a deterministic generator certificate whose static code,
offline time, offline workspace, and exact generated output size are polynomial on this schedule.
The existential certificate exposes exact finite resource values, but does not choose inspectable
construction-specific constants. -/
theorem exists_growingSupportSamplerGenerator :
    ∃ certificate : growingSupportSamplerFamily.GeneratorCertificate,
      UniformOracleCircuitFamily.GeneratorResources.IsPolynomial
        (fun s => certificate.resources ⟨s, 0⟩) := by
  obtain ⟨certificate⟩ := growingSupportSamplerFamily.exists_generatorCertificate
  refine ⟨certificate, certificate.resources_isPolynomial ?_⟩
  simpa only [encOracleInputSize_apply, encOracleInputSizeFields, length_encPair,
    encUnary_apply, List.length_replicate, Nat.add_zero] using
      (((PolynomiallyBounded.const 2).mul .id).add (.const 1))

end Cslib.Crypto.HQC
