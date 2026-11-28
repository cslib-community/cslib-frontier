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
returning the binary weight. For canonical seeds and vertices, the compiled machine's workspace
and output length are linear in the encoded binary dimensions. The input still contains the
prepared field context.
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
  have hzero := budget_const (encIn := e) (Bs := fun s => (e s).length) (encB := encNat) 0
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
  obtain ⟨S, hS⟩ : (fun p : ℕ × ℕ => codeLength p.1 p.2) ≼
      fun p => (encPair encNat encNat p).length := ⟨_, codeLength_le_encodedDimensions⟩
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
  have hfinish : finishWeight last = generatedWeight seed z :=
    (congrArg finishWeight (SeedDigits.run_at_end codeBit ctx raw)).trans
      (weight_eq_generatedWeight seed z)
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

private theorem length_encInput (x : Input) :
    (encInput x).length = 2 * (encContext x.context).length + 1 + x.seed.length := by
  simp only [encInput_apply, encInputFields, length_encPair, encBits_apply]

private def enter (loc : Located Context) : Located ScanState :=
  ⟨loc.offset, ⟨loc.inner, 0, 0, false⟩⟩

private def locate (x : Input) : Located Context :=
  ⟨(frame (encContext x.context)).length, x.context⟩

/-- Start the weight pass at the first seed cell, with the context in its initial registers. -/
def load (x : Input) : Located (SeedDigits.State Context) :=
  enter (locate x)

private abbrev headerBudget (x : Input) : ℕ := (encContext x.context).length

private theorem locate_inSpace :
    ComputableInSpace locate encInput (encLocated Context encContext) headerBudget := by
  have hctx := ComputableInSpace.framedPrefix Input.context encInput encContext Input.seed
    (fun x => by simp [encInput_apply, encInputFields])
  exact encLocated_mk_budget Context encContext hctx.frameLength hctx

private theorem enter_budget {α : Type} {enc : α ↪ List Bool}
    {loc : α → Located Context} {budget : α → ℕ}
    (h : ComputableInSpace loc enc (encLocated Context encContext) budget) :
    ComputableInSpace (fun x => enter (loc x)) enc encRuntimeState budget := by
  have hzero : ComputableInSpace (fun _ : α => 0) enc encNat budget :=
    budget_const 0
  have hflag : ComputableInSpace (fun _ : α => false) enc encBool budget :=
    budget_const false
  exact encLocated_mk_budget ScanState encScanState
    (QueryMachine.encLocated_offset_budget Context encContext h)
    (SeedDigits.encState_mk_budget Context encContext
      (QueryMachine.encLocated_inner_budget Context encContext h) hzero hzero hflag)

/-- Native initialization charges the prepared header's length, independently of seed length. -/
theorem load_inSpace :
    ComputableInSpace load encInput encRuntimeState (fun x => (encContext x.context).length) :=
  enter_budget locate_inSpace

private theorem drop_locate (x : Input) : (encInput x).drop (locate x).offset = x.seed := by
  simp [locate, encInput_apply, encInputFields, encPair_apply, encBits_apply]

/-- Dropping the initialized offset leaves exactly the original seed bits. -/
theorem drop_seed (x : Input) : (encInput x).drop (load x).offset = x.seed := by
  simp [load, enter, locate, encInput_apply, encInputFields, encPair_apply, encBits_apply]

private def dummy : Context := ⟨⟨0, 0, []⟩, 0, 0⟩

/-- The offset weight executor. Use the loaded state as the entry to its run. -/
def executor : QueryMachine (Located (SeedDigits.State Context)) :=
  (machine dummy).withOffset

private theorem executor_runFrom_enter (word : List Bool) (loc : Located Context)
    {seed : List Bool} (hseed : word.drop loc.offset = seed) (t : ℕ) :
    executor.runFrom word (enter loc) t =
      ⟨loc.offset, (machine loc.inner).run seed t⟩ := by
  change (machine dummy).withOffset.runFrom word
    ⟨loc.offset, (machine loc.inner).init⟩ t = _
  rw [QueryMachine.withOffset_runFrom, hseed]
  rfl

/-- The runtime executor from the loaded state matches the direct seed pass at every clock. -/
theorem executor_runFrom (x : Input) (t : ℕ) :
    executor.runFrom (encInput x) (load x) t =
      ⟨(load x).offset, (machine x.context).run x.seed t⟩ := by
  have h := executor_runFrom_enter (encInput x) (locate x) (drop_locate x) t
  dsimp only [enter, locate] at h; dsimp only [load, enter, locate]; exact h

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


private theorem executor_finish_enter (word : List Bool) (loc : Located Context)
    {seed : List Bool} (hseed : word.drop loc.offset = seed) :
    let last := executor.runFrom word (enter loc) (seed.length + 1)
    executor.halted last = true ∧ executor.finish last = encNat (weight loc.inner seed) := by
  dsimp only
  rw [executor_runFrom_enter word loc hseed]
  erw [SeedDigits.run_at_end codeBit loc.inner seed]
  exact ⟨rfl, rfl⟩

/-- The loaded executor halts at the end of the seed with the native pass's scaled weight. -/
theorem executor_finish (x : Input) :
    let last := executor.runFrom (encInput x) (load x) (x.seed.length + 1)
    executor.halted last = true ∧ executor.finish last = encNat (weight x.context x.seed) := by
  unfold load; exact executor_finish_enter (encInput x) (locate x) (drop_locate x)

/-- Compile the weight pass with a native context-and-offset initializer. The seed suffix is
read from the original input. Workspace and binary output length are linear in the input
encoding when the initializer fits that budget. -/
theorem weight_inSpace_of_locate {α : Type} {enc : α ↪ List Bool}
    {loc : α → Located Context} {seed : α → List Bool}
    (hload : ComputableInSpace loc enc (encLocated Context encContext) (fun x => (enc x).length))
    (hseed : ∀ x, (enc x).drop (loc x).offset = seed x) :
    ComputableInSpace (fun x => SeedWeight.weight (loc x).inner (seed x))
      enc encNat (fun x => (enc x).length + 1) := by
  let budget (x : α) := (enc x).length + 1
  let time (x : α) := (seed x).length + 1
  let state (x : α) (t : ℕ) := executor.runFrom (enc x) (enter (loc x)) t
  have hentry : ComputableInSpace (fun x => enter (loc x)) enc encRuntimeState budget :=
    enter_budget (hload.mono_le fun _ => Nat.le_succ _)
  have hlog (x : α) : Nat.log2 (enc x).length + 1 ≤ budget x :=
    Nat.add_le_add_right (Nat.log2_le_self _) _
  obtain ⟨C, hC⟩ := hload.length_le
  let K := 2 * C + 13
  have hstate (x : α) (t : ℕ) : (encRuntimeState (state x t)).length ≤ K * budget x := by
    have hloc := hC x
    change (encLocated Context encContext (loc x)).length ≤ C * budget x at hloc
    rw [QueryMachine.length_encLocated] at hloc
    have hraw : (seed x).length ≤ (enc x).length := by
      rw [← hseed x, List.length_drop]
      exact Nat.sub_le _ _
    have hrun := length_run_le (loc x).inner (seed x) t
    dsimp only [state]
    rw [executor_runFrom_enter (enc x) (loc x) (hseed x), QueryMachine.length_encLocated]
    dsimp only [Located.offset, Located.inner, K, encScanState]
    rw [Nat.add_mul, Nat.mul_assoc]
    dsimp only [budget] at hloc ⊢
    omega
  have hend (x : α) :
      executor.halted (state x (time x)) = true ∧
        executor.finish (state x (time x)) = encNat (SeedWeight.weight (loc x).inner (seed x)) :=
    executor_finish_enter (enc x) (loc x) (hseed x)
  have hlive (x : α) (t : ℕ) (ht : t < time x) :
      executor.halted (state x t) = false := by
    dsimp only [state]
    rw [executor_runFrom_enter (enc x) (loc x) (hseed x)]
    exact (SeedDigits.run_withFinish codeBit (loc x).inner (seed x) finishWeight).1 t ht
  have hout (x : α) :
      encNat (SeedWeight.weight (loc x).inner (seed x)) =
        executor.outputFrom (enc x) (enter (loc x)) (time x) :=
    (hend x).2.symm.trans
      (executor.outputFrom_eq_finish_of_emit_nil (enc x) (fun _ => rfl) (enter (loc x))
        (time x)).symm
  obtain ⟨hq, hn, he, hh, hf⟩ := executor_parts_inSpace
  obtain ⟨runtime, A, hrun⟩ := executor.computableInSpaceFrom
    (enc := enc) (encS := encRuntimeState) (encOut := encNat)
    hq hn he hh hf time budget hentry (fun x => (hend x).1) hlive hout hlog
    ⟨K, fun x t _ => hstate x t⟩
  obtain ⟨D, hD⟩ := hf.length_le
  refine ⟨runtime, max A (D * (K + 1)), hrun.mono (fun _ => le_rfl) ?_, ?_⟩
  · intro x
    exact Nat.mul_le_mul (Nat.le_max_left _ _) (Nat.le_succ (budget x))
  · intro x
    let last := state x (time x)
    have h := hD last
    change (encBits (executor.finish last)).length ≤ D * ((encRuntimeState last).length + 1) at h
    rw [encBits_apply, (hend x).2] at h
    change _ ≤ max A (D * (K + 1)) * (budget x + 1)
    calc
      _ ≤ D * ((encRuntimeState last).length + 1) := h
      _ ≤ D * ((K + 1) * (budget x + 1)) := Nat.mul_le_mul_left D (by
        have hs := hstate x (time x)
        change (encRuntimeState last).length ≤ _ at hs
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one]
        omega)
      _ = (D * (K + 1)) * (budget x + 1) := (Nat.mul_assoc _ _ _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_max_right _ _)

/-- One native machine loads the framed context and runs the weight pass on the original word.
The binary result and workspace are both linear in the encoded prepared request. -/
theorem weight_inSpace :
    ComputableInSpace (fun x : Input => SeedWeight.weight x.context x.seed)
      encInput encNat (fun x => (encInput x).length + 1) :=
  weight_inSpace_of_locate (loc := locate) (seed := Input.seed)
    (locate_inSpace.mono_le fun x => by rw [headerBudget, length_encInput]; omega)
    drop_locate

/-- The prepared request for a canonical seed in increasing index order and a valid vertex. -/
@[expose] def canonicalInput {w n : ℕ} (seed : Fin (codeLength w n) → Bool)
    (z : Fin (n + 1) × Fin w) : Input :=
  ⟨⟨fieldContext w n, z.1.val, z.2.val⟩, List.ofFn seed⟩

private theorem length_canonicalInput_le_encodedDimensions :
    ∃ C : ℕ, ∀ {w n : ℕ} (seed : Fin (codeLength w n) → Bool) (z : Fin (n + 1) × Fin w),
      (encInput (canonicalInput seed z)).length + 2 ≤
        C * ((encPair encNat encNat (w, n)).length + 1) := by
  obtain ⟨A, hA⟩ := generatedWeight_run_length_le_encodedDimensions
  obtain ⟨S, hS⟩ : (fun p : ℕ × ℕ => codeLength p.1 p.2) ≼
      fun p => (encPair encNat encNat p).length := ⟨_, codeLength_le_encodedDimensions⟩
  refine ⟨2 * A + S + 3, fun {w n} seed z => ?_⟩
  let x := canonicalInput seed z
  let dim := (encPair encNat encNat (w, n)).length + 1
  let start : SeedDigits.State Context := ⟨x.context, 0, 0, false⟩
  have hstate : (encScanState start).length ≤ A * dim := (hA seed z).1 0
  have hctx : (encContext x.context).length ≤ A * dim :=
    (SeedDigits.encState_context_length_le Context encContext start).trans hstate
  have hraw : x.seed.length ≤ S * dim := by
    simpa only [x, canonicalInput, List.length_ofFn, dim] using hS (w, n)
  have hpos : 1 ≤ dim := Nat.le_add_left _ _
  change (encInput x).length + 2 ≤ (2 * A + S + 3) * dim
  rw [length_encInput]
  simp only [Nat.add_mul, Nat.mul_assoc]
  omega

/-- One native machine computes the generated weight on each prepared canonical request.
Both workspace and binary output length are linear in the encoded graph dimensions.
The runtime bound is existential and indexed by the prepared request. -/
theorem generatedWeight_computesInTimeAndSpace :
    ∃ (time : Input → ℕ) (C k : ℕ) (State : Type) (_ : Finite State)
        (tm : MultiTapeTM k Bool State),
      ∀ {w n : ℕ} (seed : Fin (codeLength w n) → Bool) (z : Fin (n + 1) × Fin w),
        let x := canonicalInput seed z
        let budget := C * ((encPair encNat encNat (w, n)).length + 1)
        tm.ComputesInTimeAndSpace (encInput x) (encNat (generatedWeight seed z)) (time x) budget ∧
          (encNat (generatedWeight seed z)).length ≤ budget := by
  obtain ⟨time, A, hrun, hlength⟩ := weight_inSpace
  obtain ⟨k, State, hfinite, tm, hrun⟩ := hrun
  obtain ⟨C, hC⟩ := length_canonicalInput_le_encodedDimensions
  refine ⟨time, A * C, k, State, hfinite, tm, ?_⟩
  intro w n seed z x budget
  have hword : encNat (SeedWeight.weight x.context x.seed) = encNat (generatedWeight seed z) :=
    congrArg encNat (weight_eq_generatedWeight seed z)
  have hbound : A * ((encInput x).length + 2) ≤ budget := by
    dsimp only [budget]
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left A (hC seed z)
  obtain ⟨houtput, htime, hspace⟩ := hrun x
  exact ⟨⟨Eq.ndrec (motive := tm.Computes (encInput x)) houtput hword, htime, hspace.mono hbound⟩,
    (congrArg List.length hword).symm.trans_le ((hlength x).trans hbound)⟩

end Runtime

end Cslib.Reachability.Hoza.SeedWeight
