/-
Copyright (c) 2026 Christian Reitwiessner, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.MinIsolation.Generator.SeedDigits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Justesen
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.Offset
import CslibFrontier.Algorithms.Reachability.MinIsolation.Generator.Scale
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FramePrefix
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.JustesenBit
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# A native weight pass on a read-only Justesen seed

Read the raw seed in index order, mask each bit using the prepared Justesen field context
and the vertex column, and apply the layer scaling to the base-six sum. The implementation
shares the seed-digit loop and replaces only its final output. The query state bound
charges the prepared field context and seed length separately. With a fixed prepared
context, the entire raw-seed computation has a native linear-workspace certificate.

The runtime entry loads a prepared context from the framed input prefix. Its offset executor
agrees with the direct weight pass on the unchanged seed suffix. One native machine loads
the header and executes this pass, using workspace linear in the encoded request and
returning the binary weight. Preparing the field context from graph dimensions remains
separate.
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

namespace Runtime

open QueryMachine (Located encLocated encLocated_mk_budget)

private abbrev ScanState := SeedDigits.State Context

private abbrev encScanState := SeedDigits.encState Context encContext

/-- A framed binary offset and the complete encoded weight-pass state. -/
abbrev encRuntimeState :=
  encLocated (SeedDigits.State Context) (SeedDigits.encState Context encContext)

/-- A prepared weight context and its read-only seed word. -/
structure Input where
  /-- Field information and vertex coordinates for this weight. -/
  context : Context
  /-- Seed bits in query order. -/
  seed : List Bool

/-- Framed weight context followed by the raw seed without an extra frame. -/
enc_structure encInput : Input where
  context : encContext, seed : encBits

/-- Start the weight pass at the first seed cell, with the context in its initial registers. -/
def load (x : Input) : Located (SeedDigits.State Context) :=
  ⟨(frame (encContext x.context)).length, ⟨x.context, 0, 0, false⟩⟩

private abbrev headerBudget (x : Input) : ℕ := (encContext x.context).length

private theorem context_inSpace :
    ComputableInSpace Input.context encInput encContext headerBudget :=
  ComputableInSpace.framedPrefix Input.context encInput encContext Input.seed
    (fun x => by simp [encInput_apply, encInputFields])

private theorem initialRegisters_inSpace :
    ComputableInSpace (fun x : Input => (load x).inner) encInput encScanState headerBudget := by
  have hzero : ComputableInSpace (fun _ : Input => 0) encInput encNat headerBudget :=
    (constZero (encIn := encInput) (encB := encNat) 0).weaken
      (.of_le fun _ => Nat.zero_le _)
  have hflag : ComputableInSpace (fun _ : Input => false) encInput encBool headerBudget :=
    (constZero (encIn := encInput) (encB := encBool) false).weaken
      (.of_le fun _ => Nat.zero_le _)
  exact SeedDigits.encState_mk_budget Context encContext context_inSpace hzero hzero hflag

/-- Native initialization charges the prepared header's length, independently of seed length. -/
theorem load_inSpace :
    ComputableInSpace load encInput encRuntimeState (fun x => (encContext x.context).length) :=
  encLocated_mk_budget ScanState encScanState context_inSpace.frameLength initialRegisters_inSpace

/-- Dropping the initialized offset leaves exactly the original seed bits. -/
theorem drop_seed (x : Input) : (encInput x).drop (load x).offset = x.seed := by
  simp [load, encInput_apply, encInputFields, encPair_apply, encBits_apply]

private def dummy : Context := ⟨⟨0, 0, []⟩, 0, 0⟩

/-- The offset weight executor. Use the loaded state as the entry to its run. -/
def executor : QueryMachine (Located (SeedDigits.State Context)) :=
  (machine dummy).withOffset

/-- The runtime executor from the loaded state matches the direct seed pass at every clock. -/
theorem executor_runFrom (x : Input) (t : ℕ) :
    executor.runFrom (encInput x) (load x) t =
      ⟨(load x).offset, (machine x.context).run x.seed t⟩ := by
  change (machine dummy).withOffset.runFrom (encInput x)
    ⟨(load x).offset, (machine x.context).init⟩ t = _
  rw [QueryMachine.withOffset_runFrom, drop_seed]
  rfl

/-- All native components charge space linear in the encoded located state or state and reply. -/
theorem executor_parts_inSpace :
    let e := encRuntimeState
    let eR := QueryMachine.encStateRead e
    ComputableInSpace executor.query e encNat (fun s => (e s).length) ∧
    ComputableInSpace executor.next eR e (fun p => (eR p).length) ∧
    ComputableInSpace executor.emit eR encBits (fun p => (eR p).length) ∧
    ComputableInSpace executor.halted e encBool (fun s => (e s).length) ∧
    ComputableInSpace executor.finish e encBits (fun s => (e s).length) := by
  obtain ⟨hq, hn, he, hh, hf⟩ := parts_inSpace dummy
  exact ⟨QueryMachine.withOffset_query_inSpace _ _ hq,
    QueryMachine.withOffset_next_inSpace _ _ hn, QueryMachine.withOffset_emit_inSpace _ _ he,
    QueryMachine.withOffset_halted_inSpace _ _ hh, QueryMachine.withOffset_finish_inSpace _ _ hf⟩


/-- The loaded executor halts at the end of the seed with the native pass's scaled weight. -/
theorem executor_finish (x : Input) :
    let last := executor.runFrom (encInput x) (load x) (x.seed.length + 1)
    executor.halted last = true ∧ executor.finish last = encNat (weight x.context x.seed) := by
  dsimp only
  rw [executor_runFrom]
  have hend : (machine x.context).run x.seed (x.seed.length + 1) =
      ⟨x.context, x.seed.length, SeedDigits.maskedPrefix (codeBit x.context) x.seed
        x.seed.length, true⟩ := SeedDigits.run_at_end codeBit x.context x.seed
  rw [hend]
  exact ⟨rfl, rfl⟩

/-- One native machine loads the framed context and runs the weight pass on the original word.
The binary result and workspace are both linear in the encoded prepared request. -/
theorem weight_inSpace :
    ComputableInSpace (fun x : Input => SeedWeight.weight x.context x.seed)
      encInput encNat (fun x => (encInput x).length + 1) := by
  let budget (x : Input) := (encInput x).length + 1
  let time (x : Input) := x.seed.length + 1
  have hlength (x : Input) :
      budget x = 2 * (encContext x.context).length + 1 + x.seed.length + 1 := by
    simp only [budget, encInput_apply, encInputFields, length_encPair, encBits_apply]
  have hload : ComputableInSpace load encInput encRuntimeState budget :=
    load_inSpace.mono_le fun x => by rw [hlength]; omega
  have hlog (x : Input) : Nat.log2 (encInput x).length + 1 ≤ budget x :=
    Nat.add_le_add_right (Nat.log2_le_self _) _
  have hstate (x : Input) (t : ℕ) :
      (encRuntimeState (executor.runFrom (encInput x) (load x) t)).length ≤ 8 * budget x := by
    rw [executor_runFrom, QueryMachine.length_encLocated, hlength]
    dsimp only [QueryMachine.Located.offset, QueryMachine.Located.inner]
    have hoff : (encNat (load x).offset).length ≤ 2 * (encContext x.context).length + 2 := by
      refine (length_encNat_le_log2 le_rfl).trans ?_
      simpa only [load, length_frame, Nat.add_assoc] using
        Nat.add_le_add_right (Nat.log2_le_self (load x).offset) 1
    have h := length_run_le x.context x.seed t
    omega
  have hlive (x : Input) (t : ℕ) (ht : t < time x) :
      executor.halted (executor.runFrom (encInput x) (load x) t) = false := by
    rw [executor_runFrom]
    exact (SeedDigits.run_withFinish codeBit x.context x.seed finishWeight).1 t ht
  have hout (x : Input) :
      encNat (SeedWeight.weight x.context x.seed) =
        executor.outputFrom (encInput x) (load x) (time x) :=
    (executor_finish x).2.symm.trans
      (executor.outputFrom_eq_finish_of_emit_nil (encInput x) (fun _ => rfl) (load x)
        (time x)).symm
  obtain ⟨hq, hn, he, hh, hf⟩ := executor_parts_inSpace
  obtain ⟨runtime, C, hrun⟩ := executor.computableInSpaceFrom
    (enc := encInput) (encS := encRuntimeState) (encOut := encNat)
    hq hn he hh hf time budget hload (fun x => (executor_finish x).1) hlive hout hlog
    ⟨8, fun x t _ => hstate x t⟩
  obtain ⟨D, hD⟩ := hf.length_le
  refine ⟨runtime, max C (D * 8), hrun.mono (fun _ => le_rfl) ?_, ?_⟩
  · intro x
    exact Nat.mul_le_mul (Nat.le_max_left _ _) (Nat.le_succ _)
  · intro x
    let last := executor.runFrom (encInput x) (load x) (time x)
    have h := hD last
    change (encBits (executor.finish last)).length ≤ D * ((encRuntimeState last).length + 1) at h
    have hfinish : executor.finish last = encNat (SeedWeight.weight x.context x.seed) :=
      (executor_finish x).2
    rw [encBits_apply, hfinish] at h
    change _ ≤ max C (D * 8) * (budget x + 1)
    calc
      _ ≤ D * ((encRuntimeState last).length + 1) := h
      _ ≤ D * (8 * (budget x + 1)) := Nat.mul_le_mul_left D (by
        have hs := hstate x (time x)
        change (encRuntimeState last).length ≤ _ at hs
        omega)
      _ = (D * 8) * (budget x + 1) := (Nat.mul_assoc _ _ _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_max_right _ _)

end Runtime

end Cslib.Reachability.Hoza.SeedWeight
