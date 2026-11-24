/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.CSP.VariableElimination
public import CslibFrontier.Algorithms.WordRAM.VariableElimination.Instance
public import CslibFrontier.Computability.WordRAM.Function
import CslibFrontier.Algorithms.WordRAM.VariableElimination.Run

/-!
# Bucket (variable) elimination on the Word-RAM

This module implements bucket (variable) elimination (`Cslib.Algorithms.Lean.CSP.eliminateOrder`)
over materialized radix-indexed factor tables (`FactorTable ℕ ℕ`) on the exact-basis Word-RAM
(`Cslib.WordRAM.Basis.exact`). `Basis.exact` supplies unit-cost multiplication, division, and
remainder for mixed-radix indexing and exact `ℕ` weight products while certifying non-underflowing
subtraction and non-zero divisors in the machine semantics.

Every operation of the algorithm is genuinely executed and charged on word-addressed memory:
- parsing serialized factor records into 4-word descriptors (`initFactors`),
- scanning and filtering active variable lists (`memScan`, `filterNe`),
- partitioning live factors into the active variable's bucket and unaffected factors
  (`partitionLive`),
- flattening, deduplicating, and filtering bucket scopes to form `bucketOutScope`
  (`buildOutScope`),
- decoding output table indices, looking up variable assignments across factor scopes, computing
  radix offsets, multiplying bucket factor entries, summing over all `d` domain values, and
  materializing the new `d ^ |outScope|` factor table (`evalScopeIdx`, `evalBucketProd`,
  `sumDomainValues`, `buildOutEntries`), and
- multiplying the final scalar accumulator across remaining zero-arity factor tables
  (`finalResultProd`).

Using the amortized bucket-count invariant `Cslib.Algorithms.Lean.CSP.sum_bucketFactors_le`, the
total Word-RAM instruction count along an arbitrary elimination order `order` is bounded
exponentially only in the actual intermediate joint bucket width
`W = maxJointScopeLen domain order initState`, with at most `|factors| + |order|` total factor
evaluations across the entire run.

The implementation and proof are organized into focused submodules under
`CslibFrontier.Algorithms.WordRAM.VariableElimination`:

* `VariableElimination.Instance`: public `encodeFactor`, `ElimInstance`, bounds, and `ofCSP`.
* `VariableElimination.Memory`: append-only memory predicates, `memScan`, and `writeDesc`.
* `VariableElimination.CopyFilter`: block copy (`copyWords`) and inequality filter (`filterNe`).
* `VariableElimination.Radix`: integer power (`powProg`) and radix assignment `lookupAssign`.
* `VariableElimination.Horner`: multiplicative `capFactor`/`stateCap` bounds and `evalScopeIdx`.
* `VariableElimination.BucketProd`: bucket-product evaluator `evalBucketProd`.
* `VariableElimination.SumDomain`: domain summation `sumDomainValues`.
* `VariableElimination.BuildEntries`: output entry table materializer `buildOutEntries`.
* `VariableElimination.Partition`: live factor-descriptor partitioning `partitionLive`.
* `VariableElimination.FlattenScope`: `dedupStepPure`, `sumScopeLen`, and `flattenScopes`.
* `VariableElimination.OutScope`: output scope deduplication `buildOutScope`.
* `VariableElimination.FinalProd`: final scalar-table product `finalResultProd`.
* `VariableElimination.InitFactors`: input factor parser `initFactors`.
* `VariableElimination.ElimVar`: single-step bucket elimination `elimVarProg`.
* `VariableElimination.ElimLoop`: sequential elimination loop `elimOrderLoop`.
* `VariableElimination.Run`: end-to-end `runProg` specification and realization.

## Main definitions

* `Cslib.Algorithms.WordRAM.VariableElimination.encodeFactor`: word-list serialization of a
  `FactorTable ℕ ℕ`.
* `Cslib.Algorithms.WordRAM.VariableElimination.ElimInstance`: input bundle (`domain`, `declared`,
  `order`, `factors`) with `ElimInstance.encode`, `ElimInstance.wordBound`,
  `ElimInstance.stepBound`, `ElimInstance.result`, and `ElimInstance.ofCSP`.

## Main results

* `Cslib.Algorithms.WordRAM.VariableElimination.exists_program_variableElimination`: one fixed
  exact-basis Word-RAM program computes `ElimInstance.result` in `O(stepBound + 1)` instructions
  for every word size `w` satisfying `Fits w inst.wordBound` and `InputFits w inst.encode`.
* `Cslib.Algorithms.WordRAM.VariableElimination.uniformComputableInTime_variableElimination`:
  `UniformComputableInTime .exact` certificate for `ElimInstance.result`.
* `Cslib.Algorithms.WordRAM.VariableElimination.exists_program_csp_partitionFunctionOn`: Word-RAM
  computation of `CSP.partitionFunctionOn` via `FactorTable.ofCSP`.
-/

public section

namespace Cslib.Algorithms.WordRAM.VariableElimination

open Cslib.Logic.PL Cslib.Logic.PL.CSP
open Cslib.Algorithms.Lean.CSP
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-- One fixed exact-basis Word-RAM program computes bucket (variable) elimination
`ElimInstance.result` in `≤ C * (inst.stepBound + 1) + 1` instructions for every word width `w`
satisfying `Fits w inst.wordBound` and `InputFits w inst.encode`. -/
theorem exists_program_variableElimination :
    ∃ r C : ℕ, ∃ prog : Program .exact r,
      prog.ComputesInTime
        (fun _ inst => inst.encode)
        (fun inst _ => C * (inst.stepBound + 1) + 1)
        (fun inst w => Fits w inst.wordBound)
        ElimInstance.result := by
  obtain ⟨r, C, pc, prog, _, _, hexec⟩ :=
    runProg_realizes.exists_standard_init_program_state_from_words (0 : Fin 1)
  refine ⟨r, C, prog, fun inst w hw hin => ?_⟩
  have hf_len : Fits w (inst.encode.length + 1) :=
    hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega)
  obtain ⟨hval, hres, hcost⟩ := runProg_spec inst hin hw
  obtain ⟨y, n, hruns, hhalt, _, _, hn_le⟩ :=
    hexec w () inst.encode (fun i => Fin.elim0 i) (Nat.zero_le _) hf_len hin
      ⟨inst, rfl, hin, hw⟩ hval
  rw [clientResult_width, hres] at hhalt
  refine ⟨n + 1, ⟨⟨pc, y⟩, n, hruns, hhalt, rfl⟩, ?_⟩
  have hwork : (fun (_ : Unit) (_ : Memory.State) => (0 : ℕ)) () (Memory.State.init inst.encode) =
      0 := rfl
  have hmul : C * (memoryCost (runProg ()) (Memory.State.init inst.encode) + 0 + 1) + 1 ≤
      C * (inst.stepBound + 1) + 1 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left C (by omega)) 1
  exact hn_le.trans hmul

/-- Uniform exact-basis Word-RAM computability certificate for `ElimInstance.result`. -/
theorem uniformComputableInTime_variableElimination :
    ∃ C : ℕ,
      UniformComputableInTime .exact
        ElimInstance.result
        (fun _ inst => inst.encode)
        (fun inst _ => C * (inst.stepBound + 1) + 1)
        (fun inst w => Fits w inst.wordBound) := by
  obtain ⟨r, C, prog, hcomp⟩ := exists_program_variableElimination
  refine ⟨C, r, prog, hcomp, fun inst => ?_⟩
  obtain ⟨w, hw_le, hin⟩ := InputFits.exists_width inst.encode inst.wordBound
  exact ⟨w, (fits_self inst.wordBound).mono hw_le, hin⟩

/-- One fixed exact-basis Word-RAM program computes the weighted CSP partition function
`F.partitionFunctionOn wt declared.toFinset` by variable elimination along any supplied order
`order` covering `declared` (whenever `F.vars.toFinset ⊆ declared.toFinset`), within
`C * ((ElimInstance.ofCSP d e wt F declared order).stepBound + 1) + 1` instructions. -/
theorem exists_program_csp_partitionFunctionOn :
    ∃ r C : ℕ, ∃ prog : Program .exact r,
      ∀ {Rel D : Type*} [Fintype D] [Inhabited D]
        (d : ℕ) (e : D ≃ Fin d) (wt : Rel → List D → ℕ) (F : CSP Rel ℕ)
        (declared order : List ℕ),
        F.vars.toFinset ⊆ declared.toFinset →
        declared.toFinset ⊆ order.toFinset →
        ∀ w : ℕ,
          let inst := ElimInstance.ofCSP d e wt F declared order
          Fits w inst.wordBound →
          InputFits w inst.encode →
          ∃ n,
            Executes w prog (.init inst.encode) (F.partitionFunctionOn wt declared.toFinset) n ∧
            n ≤ C * (inst.stepBound + 1) + 1 := by
  obtain ⟨r, C, prog, hcomp⟩ := exists_program_variableElimination
  refine ⟨r, C, prog, fun d e wt F declared order hvars hcover w hw hin => ?_⟩
  rw [← ElimInstance.result_ofCSP d e wt hvars hcover]
  exact hcomp (ElimInstance.ofCSP d e wt F declared order) w hw hin

end Cslib.Algorithms.WordRAM.VariableElimination
