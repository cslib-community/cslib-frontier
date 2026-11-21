/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Reachability.MinIsolation.Generator.Scale
import CslibFrontier.Algorithms.Reachability.MinIsolation.Generator.SeedWeight
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunPropFinite

/-! Checked ordinary-import seed read, masking, and final scaling. -/

set_option linter.privateModule false

namespace CslibFrontierTests.HozaSeedDigits

open Cslib.Reachability.Hoza Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace

private def code (enabled : Bool) (j : ℕ) : Bool :=
  enabled && !(decide (j = 1))

private theorem code_inSpace :
    ComputableInSpace (fun p : Bool × ℕ => code p.1 p.2) (encPair encBool encNat) encBool
      (fun p => (encPair encBool encNat p).length) :=
  budget_boolAnd (fst encBool encNat)
    (budget_boolNot (budget_natEq (snd encBool encNat) (budget_const 1 (.refl _))))

/-- The middle seed bit is masked out by the code callback. -/
example : ((SeedDigits.machine code true).run [true, true, true] 4).accumulator = 37 := by
  rw [show 4 = [true, true, true].length + 1 from rfl, SeedDigits.run_at_end]
  rfl

/-- A raw word in seed index order produces the accumulator of the finite seed function. -/
example {n : ℕ} (seed : Fin n → Bool) :
    ((SeedDigits.machine code true).run (List.ofFn seed) (n + 1)).accumulator =
      accumulateWeightDigits (fun j => code true j.val && seed j) := by
  simpa only [List.length_ofFn, SeedDigits.maskedPrefix_ofFn] using
    congrArg SeedDigits.State.accumulator (SeedDigits.run_at_end code true (List.ofFn seed))

/-- An ordinary-import caller composes the native read-only digit scan and final scaling. -/
example :
    ComputableInSpace
      (fun seed => scaleAccumulatedWeight 12 (SeedDigits.maskedPrefix (code true) seed seed.length))
      encBits encNat List.length := by
  have hscan := SeedDigits.maskedSeed_inSpace encBool code true code_inSpace
  have hpack := budget_prod (budget_const (encB := encNat) 12 (.refl _)) hscan
  exact (budget_comp_linear scaleAccumulatedWeight_inSpace hpack).of_enc_eq fun _ => rfl

open Cslib.Code.JustesenFamily in
/-- The actual raw-word run, followed by guarded scaling, gives the isolation weight. -/
example {w n : ℕ} (seed : Fin (codeLength w n) → Bool) (z : Fin (n + 1) × Fin w)
    (code : ℕ → Bool)
    (hcode : ∀ j : Fin (codeLength w n), code j.val = indexedCodewordMod z.2 j) :
    (if z.1.val = 0 then 0 else
      scaleAccumulatedWeight z.1.val
        (((SeedDigits.machine (fun (_ : Unit) => code) ()).run (List.ofFn seed)
          ((List.ofFn seed).length + 1)).accumulator)) =
      generatedWeight seed z := by
  rw [SeedDigits.run_at_end, ← generatedWeightScan_eq]
  exact SeedDigits.scaledMaskedPrefix_eq_generatedWeightScan seed z code hcode

open Cslib.Code.JustesenFamily in
/-- The concrete pass returns the weight at layer one and meets its bound on that same run. -/
example (seed : Fin (codeLength 1 1) → Bool) :
    let z : Fin (1 + 1) × Fin 1 := (1, 0)
    let ctx : SeedWeight.Context := ⟨fieldContext 1 1, 1, 0⟩
    let raw := List.ofFn seed
    let M := SeedWeight.machine ctx
    let enc := SeedDigits.encState SeedWeight.Context SeedWeight.encContext
    M.output raw (raw.length + 1) = encNat (generatedWeight seed z) ∧
      (∀ t, (enc (M.run raw t)).length ≤
        2 * (SeedWeight.encContext ctx).length + 8 * raw.length + 4) ∧
      ComputableInSpace (SeedWeight.weight ctx) encBits encNat List.length :=
  ⟨(SeedWeight.generatedWeight_output seed (1, 0)).2.2, SeedWeight.length_run_le _ _,
    SeedWeight.weight_inSpace _⟩

open Cslib.Code.JustesenFamily in
/-- A uniform dimension budget bounds the live states and the actual emitted word. -/
example :
    ∃ C : ℕ, ∀ {w n : ℕ} (seed : Fin (codeLength w n) → Bool) (z : Fin (n + 1) × Fin w),
      let ctx : SeedWeight.Context := ⟨fieldContext w n, z.1.val, z.2.val⟩
      let raw := List.ofFn seed
      let M := SeedWeight.machine ctx
      let enc := SeedDigits.encState SeedWeight.Context SeedWeight.encContext
      let budget := (encPair encNat encNat (w, n)).length + 1
      (∀ t, (enc (M.run raw t)).length ≤ C * budget) ∧
        (M.output raw (raw.length + 1)).length ≤ C * budget := by
  obtain ⟨C, hC⟩ := SeedWeight.generatedWeight_run_length_le_encodedDimensions
  refine ⟨C, fun seed z => ?_⟩
  obtain ⟨hstate, hweight⟩ := hC seed z
  refine ⟨hstate, ?_⟩
  rw [(SeedWeight.generatedWeight_output seed z).2.2]
  exact hweight

open Cslib.Code.JustesenFamily SeedWeight.Runtime in
/-- The loaded executor returns the generator's weight from the original framed seed input. -/
example {w n : ℕ} (seed : Fin (codeLength w n) → Bool) (z : Fin (n + 1) × Fin w) :
    let x := canonicalInput seed z
    let last := executor.runFrom (encInput x) (load x) (x.seed.length + 1)
    ComputableInSpace load encInput encRuntimeState
      (fun x => (SeedWeight.encContext x.context).length) ∧
      executor.halted last = true ∧ executor.finish last = encNat (generatedWeight seed z) := by
  intro x last
  obtain ⟨hhalt, hfinish⟩ := executor_finish x
  refine ⟨load_inSpace, hhalt, hfinish.trans ?_⟩
  exact congrArg encNat (SeedWeight.weight_eq_generatedWeight seed z)

open Turing Cslib.Code.JustesenFamily SeedWeight.Runtime in
/-- An ordinary-import caller obtains the native dimension budget at a nonzero layer. -/
example :
    ∃ (time : Input → ℕ) (C k : ℕ) (State : Type) (_ : Finite State)
        (tm : MultiTapeTM k Bool State),
      ∀ seed : Fin (codeLength 1 1) → Bool,
        let z : Fin 2 × Fin 1 := (1, 0)
        let x := canonicalInput seed z
        let budget := C * ((encPair encNat encNat (1, 1)).length + 1)
        tm.ComputesInTimeAndSpace (encInput x) (encNat (generatedWeight seed z)) (time x) budget ∧
          (encNat (generatedWeight seed z)).length ≤ budget := by
  obtain ⟨time, C, k, State, hfinite, tm, h⟩ := generatedWeight_computesInTimeAndSpace
  exact ⟨time, C, k, State, hfinite, tm, fun seed => h (w := 1) (n := 1) seed (1, 0)⟩

end CslibFrontierTests.HozaSeedDigits
