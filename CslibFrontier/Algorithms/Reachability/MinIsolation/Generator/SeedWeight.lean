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

/-- For canonical seeds and vertices, a single bound in the encoded binary dimensions
covers every state of the read-only pass and the binary weight it returns. -/
theorem generatedWeight_run_length_le_encodedDimensions :
    ∃ C : ℕ, ∀ {w n : ℕ} (seed : Fin (codeLength w n) → Bool) (z : Fin (n + 1) × Fin w),
      let ctx : Context := ⟨fieldContext w n, z.1.val, z.2.val⟩
      let raw := List.ofFn seed
      let M := machine ctx
      let e := SeedDigits.encState Context encContext
      let budget := (encPair encNat encNat (w, n)).length + 1
      (∀ t, (e (M.run raw t)).length ≤ C * budget) ∧
        (encNat (generatedWeight seed z)).length ≤ C * budget := by
  obtain ⟨A, hA⟩ := length_fieldContext_le_encodedDimensions
  have hseed : (fun p : ℕ × ℕ => codeLength p.1 p.2) ≼
      fun p => (encPair encNat encNat p).length := ⟨_, codeLength_le_encodedDimensions⟩
  obtain ⟨S, hS⟩ := hseed
  obtain ⟨D, hD⟩ := finishWeight_inSpace.length_le
  let K := 4 * A + 8 * S + 12
  refine ⟨max K (D * (K + 1)), fun {w n} seed z => ?_⟩
  intro ctx raw M e budget
  have hw : (encNat z.2.val).length ≤ (encNat w).length :=
    length_encNat_mono z.2.isLt.le
  have hn : (encNat z.1.val).length ≤ (encNat n).length :=
    length_encNat_mono (Nat.le_of_lt_succ z.1.isLt)
  have hctx : (encContext ctx).length ≤ 2 * (A * budget) + 4 * budget := by
    have hf := hA (w, n)
    dsimp only at hf
    change (encFieldContext (fieldContext w n)).length ≤ A * budget at hf
    dsimp only [ctx]
    simp only [encContext_apply, encContextFields, length_encPair]
    have hbudget : budget = 2 * (encNat w).length + 1 + (encNat n).length + 1 := by
      simp only [budget, length_encPair]
    omega
  have hraw : raw.length ≤ S * budget := by
    simpa only [raw, List.length_ofFn] using hS (w, n)
  have hstates (t : ℕ) : (e (M.run raw t)).length ≤ K * budget := by
    have hrun := length_run_le ctx raw t
    have hb : 1 ≤ budget := Nat.le_add_left _ _
    change (e (M.run raw t)).length ≤ _ at hrun
    dsimp only [K]
    simp only [Nat.add_mul, Nat.mul_assoc]
    omega
  refine ⟨fun t => (hstates t).trans (Nat.mul_le_mul_right budget (le_max_left _ _)), ?_⟩
  let last := M.run raw (raw.length + 1)
  have hfinish : finishWeight last = generatedWeight seed z := by
    have hend : last =
        ⟨ctx, raw.length, SeedDigits.maskedPrefix (codeBit ctx) raw raw.length, true⟩ :=
      SeedDigits.run_at_end codeBit ctx raw
    rw [hend]
    exact weight_eq_generatedWeight seed z
  have hlast : (e last).length + 1 ≤ (K + 1) * budget := by
    have hb : 1 ≤ budget := Nat.le_add_left _ _
    rw [Nat.add_mul K 1, Nat.one_mul]
    exact Nat.add_le_add (hstates _) hb
  calc
    _ = (encNat (finishWeight last)).length := by rw [hfinish]
    _ ≤ D * ((e last).length + 1) := hD last
    _ ≤ D * ((K + 1) * budget) := Nat.mul_le_mul_left _ hlast
    _ ≤ _ := by
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ (le_max_right _ _)

end Cslib.Reachability.Hoza.SeedWeight
