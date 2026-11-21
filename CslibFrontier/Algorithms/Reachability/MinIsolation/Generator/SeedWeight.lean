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
shares the seed-digit loop and replaces only its final output. It certifies the query
components and every live state with the prepared field context and seed length charged
separately.
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

/-- The real Justesen query pass has native components linear in their encoded arguments. -/
theorem parts_inSpace (ctx : Context) :
    let M := machine ctx
    let e := SeedDigits.encState Context encContext
    let eR := QueryMachine.encStateRead e
    ComputableInSpace M.query e encNat (fun s => (e s).length) ∧
    ComputableInSpace M.next eR e (fun p => (eR p).length) ∧
    ComputableInSpace M.emit eR encBits (fun p => (eR p).length) ∧
    ComputableInSpace M.halted e encBool (fun s => (e s).length) ∧
    ComputableInSpace M.finish e encBits (fun s => (e s).length) := by
  have hrequest := fst encContext encNat
  have hbit := budget_comp_linear fieldContext_indexedBit_inSpace
    (budget_prod (budget_prod (encContext_field_budget hrequest)
      (encContext_column_budget hrequest)) (snd encContext encNat))
  obtain ⟨hq, hn, he, hh, _⟩ := SeedDigits.parts_inSpace encContext codeBit ctx hbit
  let e := SeedDigits.encState Context encContext
  have hid := budget_id (enc := e) (.refl _)
  have hctx := SeedDigits.encState_context_budget Context encContext hid
  have hlayer := encContext_layer_budget hctx
  have hacc := SeedDigits.encState_accumulator_budget Context encContext hid
  have hzero := budget_const (encB := encNat) 0 (.refl fun s => (e s).length)
  have hscaled := budget_comp_linear scaleAccumulatedWeight_inSpace (budget_prod hlayer hacc)
  have hvalue := budget_ite (budget_natEq hlayer hzero) hzero hscaled
  exact ⟨hq, hn, he, hh, hvalue.of_enc_eq fun s => by
    by_cases h : s.context.layer = 0 <;> simp [machine, finishWeight, h, encBits_apply]⟩

/-- Every clock charges only the retained context and the length of the read-only seed. -/
theorem length_run_le (ctx : Context) (seed : List Bool) (t : ℕ) :
    (SeedDigits.encState Context encContext ((machine ctx).run seed t)).length ≤
      2 * (encContext ctx).length + 8 * seed.length + 4 :=
  SeedDigits.length_run_le encContext codeBit ctx seed t

/-- For the seed in increasing index order, the pass first halts at the first absent bit
and returns the existing generated weight, including the zero weight at layer zero. -/
theorem generatedWeight_output {w n : ℕ} (seed : Fin (codeLength w n) → Bool)
    (z : Fin (n + 1) × Fin w) :
    let raw := List.ofFn seed
    let M := machine ⟨fieldContext w n, z.1.val, z.2.val⟩
    (∀ t < raw.length + 1, M.halted (M.run raw t) = false) ∧
      M.halted (M.run raw (raw.length + 1)) = true ∧
      M.output raw (raw.length + 1) = encNat (generatedWeight seed z) := by
  intro raw M
  let ctx : Context := ⟨fieldContext w n, z.1.val, z.2.val⟩
  have hlive (t : ℕ) (ht : t < raw.length + 1) :
      M.halted (M.run raw t) = false := by
    change (SeedDigits.machine codeBit ctx).halted
      ((SeedDigits.machine codeBit ctx).run raw t) = false
    rw [SeedDigits.run_prefix _ _ _ _ (by omega)]
    rfl
  have hend : M.run raw (raw.length + 1) =
      ⟨ctx, raw.length, SeedDigits.maskedPrefix (codeBit ctx) raw raw.length, true⟩ :=
    SeedDigits.run_at_end codeBit ctx raw
  refine ⟨hlive, ?_, ?_⟩
  · rw [hend]
    rfl
  · rw [M.output_eq_of_not_halted raw hlive, hend]
    have h := SeedDigits.scaledMaskedPrefix_eq_generatedWeightScan seed z (codeBit ctx)
      (fieldContext_indexedBit_eq z.2)
    rw [generatedWeightScan_eq] at h
    change ((List.range (raw.length + 1)).map (fun _ => ([] : List Bool))).flatten ++
      encNat (finishWeight ⟨ctx, raw.length, SeedDigits.maskedPrefix (codeBit ctx) raw raw.length,
        true⟩) = encNat (generatedWeight seed z)
    simpa [finishWeight, ctx, raw] using congrArg encNat h

end Cslib.Reachability.Hoza.SeedWeight
