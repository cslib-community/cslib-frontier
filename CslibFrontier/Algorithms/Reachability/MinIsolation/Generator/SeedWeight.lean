/-
Copyright (c) 2026 Christian Reitwiessner, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.MinIsolation.Generator.SeedDigits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Justesen
import CslibFrontier.Algorithms.Reachability.MinIsolation.Generator.Scale
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.JustesenBit

/-!
# A native weight pass on a read-only Justesen seed

Read the raw seed in index order, mask each bit using the prepared Justesen field context
and the vertex column, and apply the layer scaling to the base-six sum. The implementation
shares the seed-digit loop and replaces only its final output. The query state bound
charges the prepared field context and seed length separately. With a fixed prepared
context, the entire raw-seed computation has a native linear-workspace certificate.
-/

public section

namespace Cslib.Reachability.Hoza.SeedWeight

open Cslib.Code.JustesenFamily
open Turing Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace

/-- The field data and vertex coordinates retained during a single weight query. -/
structure Context where
  /-- Prepared Justesen field for the graph dimensions. -/
  field : FieldContext
  /-- Layer of the weighted vertex. -/
  layer : ℕ
  /-- Column used as the binary Justesen label. -/
  column : ℕ

/-- Framed field context and binary layer, followed by the binary column. -/
enc_structure encContext : Context where
  field : encFieldContext, layer : encNat, column : encNat

private def codeBit (ctx : Context) (index : ℕ) : Bool :=
  ctx.field.indexedBit ctx.column index

private def finishWeight (s : SeedDigits.State Context) : ℕ :=
  if s.context.layer = 0 then 0 else scaleAccumulatedWeight s.context.layer s.accumulator

/-- Scan one raw seed and return the binary Justesen weight of the given vertex. -/
def machine (ctx : Context) : QueryMachine (SeedDigits.State Context) :=
  { SeedDigits.machine codeBit ctx with finish := fun s => encNat (finishWeight s) }

private theorem codeBit_inSpace :
    ComputableInSpace (fun p : Context × ℕ => codeBit p.1 p.2) (encPair encContext encNat)
      encBool (fun p => (encPair encContext encNat p).length) := by
  have hctx := fst encContext encNat
  exact budget_comp_linear fieldContext_indexedBit_inSpace
    (budget_prod (budget_prod (encContext_field_budget hctx)
      (encContext_column_budget hctx)) (snd encContext encNat))

private theorem finishWeight_inSpace :
    let e := SeedDigits.encState Context encContext
    ComputableInSpace finishWeight e encNat (fun s => (e s).length) := by
  let e := SeedDigits.encState Context encContext
  have hid := budget_id (enc := e) (.refl _)
  have hctx := SeedDigits.encState_context_budget Context encContext hid
  have hlayer := encContext_layer_budget hctx
  have hacc := SeedDigits.encState_accumulator_budget Context encContext hid
  have hzero := budget_const (encB := encNat) 0 (.refl fun s => (e s).length)
  have hscaled := budget_comp_linear scaleAccumulatedWeight_inSpace (budget_prod hlayer hacc)
  exact (budget_ite (budget_natEq hlayer hzero) hzero hscaled).of_enc_eq fun s => by
    by_cases h : s.context.layer = 0 <;> simp [finishWeight, h]

/-- The actual Justesen query pass has native components linear in their encoded arguments. -/
theorem parts_inSpace (ctx : Context) :
    let M := machine ctx
    let e := SeedDigits.encState Context encContext
    let eR := QueryMachine.encStateRead e
    ComputableInSpace M.query e encNat (fun s => (e s).length) ∧
    ComputableInSpace M.next eR e (fun p => (eR p).length) ∧
    ComputableInSpace M.emit eR encBits (fun p => (eR p).length) ∧
    ComputableInSpace M.halted e encBool (fun s => (e s).length) ∧
    ComputableInSpace M.finish e encBits (fun s => (e s).length) := by
  obtain ⟨hq, hn, he, hh, _⟩ := SeedDigits.parts_inSpace encContext codeBit ctx codeBit_inSpace
  exact ⟨hq, hn, he, hh, finishWeight_inSpace.of_enc_eq fun _ => (encBits_apply _).symm⟩

/-- The weight of a raw seed at the vertex specified by the prepared context. -/
def weight (ctx : Context) (seed : List Bool) : ℕ :=
  finishWeight ⟨ctx, seed.length, SeedDigits.maskedPrefix (codeBit ctx) seed seed.length, true⟩

/-- With a fixed prepared field and vertex context, the entire raw-seed pass uses native
workspace linear in the seed length, including its binary output. -/
theorem weight_inSpace (ctx : Context) :
    ComputableInSpace (weight ctx) encBits encNat List.length :=
  SeedDigits.scanWithFinish_inSpace encContext codeBit ctx finishWeight
    codeBit_inSpace finishWeight_inSpace

/-- Every clock charges only the retained context and the length of the read-only seed. -/
theorem length_run_le (ctx : Context) (seed : List Bool) (t : ℕ) :
    (SeedDigits.encState Context encContext ((machine ctx).run seed t)).length ≤
      2 * (encContext ctx).length + 8 * seed.length + 4 :=
  SeedDigits.length_run_le encContext codeBit ctx seed t

/-- A raw seed in index order gives the existing generated weight at the prepared vertex. -/
theorem weight_eq_generatedWeight {w n : ℕ} (seed : Fin (codeLength w n) → Bool)
    (z : Fin (n + 1) × Fin w) :
    weight ⟨fieldContext w n, z.1.val, z.2.val⟩ (List.ofFn seed) = generatedWeight seed z := by
  rw [← generatedWeightScan_eq]
  exact SeedDigits.scaledMaskedPrefix_eq_generatedWeightScan seed z _
    (fieldContext_indexedBit_eq z.2)

/-- For the seed in increasing index order, the pass first halts at the first absent bit
and returns the existing generated weight, including the zero weight at layer zero. -/
theorem generatedWeight_output {w n : ℕ} (seed : Fin (codeLength w n) → Bool)
    (z : Fin (n + 1) × Fin w) :
    let raw := List.ofFn seed
    let M := machine ⟨fieldContext w n, z.1.val, z.2.val⟩
    (∀ t < raw.length + 1, M.halted (M.run raw t) = false) ∧
      M.halted (M.run raw (raw.length + 1)) = true ∧
      M.output raw (raw.length + 1) = encNat (generatedWeight seed z) := by
  rw [← weight_eq_generatedWeight seed z]
  exact SeedDigits.run_withFinish codeBit _ (List.ofFn seed) finishWeight

end Cslib.Reachability.Hoza.SeedWeight
