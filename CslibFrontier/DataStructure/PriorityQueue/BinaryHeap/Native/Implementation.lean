/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.BinaryHeap.Native.Base
public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.Decode
import CslibFrontier.Tactic.WramOmega

/-!
# Raw native execution of the memory heap

The single global heap program is certified through its existing operation realizations and
Backend. Arguments must already match the raw calling convention; argument delivery is not
executed for free. Zero staging, dispatch and the lookup key copy are actual charged code.

The representation and initialization are inherited from `subroutineBase`. Typed extraction
uses the exact erased original source result, not an unchecked natural-handle observation.

## Main results

* `subroutineImpl`: the existing raw heap `StateTransitionImpl`, including actual method execution.
* `subroutineImpl_exec_memoryState`: every matching actual raw execution leaves the original
  memory program's complete state.

Complete allocated clients and native Dijkstra have their separate contracts; no old exact
clock or register count is inherited.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.BinaryHeap.Native

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.PriorityQueue.WordRAM
open Cslib.DataStructure.PriorityQueue.BinaryHeap (space)

/-- Canonical observation of the heap's actual fixed output bank. It is the same structural
parser used by the native DynamicProgram, with no operation-dependent register selection. -/
@[expose] noncomputable def nativeObservation {n K : ℕ} (o : IndexedMinPQ.Op n)
    (regs : Fin Program.registers → ℕ) : Option ((indexedMinPQSpec n K).Result o) :=
  ((PQCode.nativeResultType n o).decode (regs ∘ Program.code.nativeResultBank) 0).map
    (cast (PQCode.nativeResultType_eq n K o).symm)

/-- Typed canonical parsing succeeds exactly when the fixed bank contains the presented result. -/
theorem nativeObservation_eq_some_iff {n K : ℕ} (o : IndexedMinPQ.Op n)
    (regs : Fin Program.registers → ℕ) (a : (indexedMinPQSpec n K).Result o) :
    nativeObservation o regs = some a ↔
      (PQCode.nativeResultType n o).decode (regs ∘ Program.code.nativeResultBank) 0 =
        some (cast (PQCode.nativeResultType_eq n K o) a) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
    simpa only [cast_cast, cast_eq] using hb
  · simp only [nativeObservation, h, Option.map_some, cast_cast, cast_eq]

private theorem decode_body {w n K : ℕ} (L : Memory.Layout n) (e : Memory.State)
    (o : IndexedMinPQ.Op n) (y z : Data Program.registers)
    (hout : ∀ j, y.regs (Backend.tmp Program.family (.inl ((backend n K L).tag o))
        (Fin.castAdd ((certificates ((backend n K L).tag o)).realizes.scratchSize + 1) j)) =
      (certificates ((backend n K L).tag o)).output
        ((Memory.spec w).clientResult e
          ((certificates ((backend n K L).tag o)).prog ((backend n K L).arg o))) j)
    (hflag : z.regs Program.code.outFlag = y.regs Program.code.outFlag)
    (hvalue : z.regs Program.code.outV = y.regs Program.code.outV)
    (hkey : z.regs Program.code.outK =
      (match o with | .getKey _ => y.regs Program.code.outV | _ => y.regs Program.code.outK)) :
    Program.code.decode (K_max := K) o z.regs =
      some ((Memory.spec w).clientResult e (Memory.ops L o)) ∧
    nativeObservation (K := K) o z.regs =
      some ((Memory.spec w).clientResult e (Memory.ops L o)) := by
  cases o with
  | isEmpty =>
    have hz : z.regs Program.code.outFlag =
        ((Memory.spec w).clientResult e (Memory.isEmpty L)).toNat :=
      hflag.trans
        (Program.code_outFlag.symm ▸ Program.output_bank 0 (0 : Fin 2) 0 rfl ▸ hout (0 : Fin 2))
    refine ⟨PQCode.decode_isEmpty _ _ (by simpa only [Memory.ops] using hz),
      (nativeObservation_eq_some_iff _ _ _).mpr (cast_eq _ _ ▸ ?_)⟩
    cases hb : (Memory.spec w).clientResult e (Memory.isEmpty L) <;>
      simp [PQCode.nativeResultType, ResultType.decode, Function.comp_apply,
        PQCode.nativeResultBank, hz, hb, Memory.ops]
  | getKey v =>
    have hj (j : Fin 2) (a : Fin 4) (he : j.val = a.val) : y.regs (Program.bank a) =
        optionWords ((Memory.spec w).clientResult e (Memory.getKey L v)) j :=
      Program.output_bank 1 j a he ▸ hout j
    cases ha : (Memory.spec w).clientResult e (Memory.getKey L v) with
    | none =>
      have hf : z.regs Program.code.outFlag = 0 := hflag.trans (by
        simpa only [Program.code_outFlag, ha, optionWords_none, Matrix.cons_val_zero] using
          hj 0 0 rfl)
      refine ⟨by simpa only [Memory.ops, ha] using PQCode.decode_getKey_none _ _ v hf,
        (nativeObservation_eq_some_iff _ _ _).mpr (cast_eq _ _ ▸ ?_)⟩
      simp [PQCode.nativeResultType, ResultType.decode, Function.comp_apply,
        PQCode.nativeResultBank, hf, Memory.ops, ha]
    | some k =>
      rw [ha] at hj
      have hf : z.regs Program.code.outFlag = 1 :=
        hflag.trans (Program.code_outFlag.symm ▸ hj 0 0 rfl)
      have h1' : y.regs Program.code.outV = k := Program.code_outV.symm ▸ hj 1 1 rfl
      refine ⟨by simpa only [Memory.ops, ha] using
          PQCode.decode_getKey_some Program.code z.regs v (by simp [hf]) (hkey.trans h1'),
        (nativeObservation_eq_some_iff _ _ _).mpr (cast_eq _ _ ▸ ?_)⟩
      simp [PQCode.nativeResultType, ResultType.decode, Function.comp_apply,
        PQCode.nativeResultBank, hf, hvalue.trans h1', Memory.ops, ha]
  | insert v k | decreaseKey v k =>
    constructor <;> exact congrArg some (Subsingleton.elim _ _)
  | extractMin =>
    have hj (j : Fin 3) (a : Fin 4) (he : j.val = a.val) : y.regs (Program.bank a) =
        WordEncoding.encode (α := Option (ℕ × ℕ))
          ((Memory.spec w).clientResult e
            ((Memory.extractMin L).map (Option.map fun a => (a.1.val, a.2)))) j :=
      Program.output_bank 4 j a he ▸ hout j
    simp only [extractMin_result w ⟨n, L⟩ e] at hj
    cases ha : (Memory.spec w).clientResult e (Memory.extractMin L) with
    | none =>
      rw [ha] at hj
      have hf : z.regs Program.code.outFlag = 0 :=
        hflag.trans (Program.code_outFlag.symm ▸ hj 0 0 rfl)
      refine ⟨by simpa only [Memory.ops, ha] using PQCode.decode_extractMin_none _ _ hf,
        (nativeObservation_eq_some_iff _ _ _).mpr (cast_eq _ _ ▸ ?_)⟩
      simp [PQCode.nativeResultType, ResultType.decode, Function.comp_apply,
        PQCode.nativeResultBank, hf, Memory.ops, ha]
    | some a =>
      rcases a with ⟨v, k⟩
      rw [ha] at hj
      have hf : z.regs Program.code.outFlag = 1 :=
        hflag.trans (Program.code_outFlag.symm ▸ hj 0 0 rfl)
      have hv : z.regs Program.code.outV = v.val :=
        hvalue.trans (Program.code_outV.symm ▸ hj 1 1 rfl)
      have hk : z.regs Program.code.outK = k :=
        hkey.trans (Program.code_outK.symm ▸ hj 2 2 rfl)
      refine ⟨by simpa only [Memory.ops, ha] using
          PQCode.decode_extractMin_some Program.code z.regs v (by simp [hf]) hv hk,
        (nativeObservation_eq_some_iff _ _ _).mpr (cast_eq _ _ ▸ ?_)⟩
      simp [PQCode.nativeResultType, ResultType.decode, ResultType.words, Function.comp_apply,
        PQCode.nativeResultBank, hf, hv, v.isLt, hk, Memory.ops, ha]

private theorem raw_exec
    {w n K base : ℕ} (hn : Fits w n) (hK : Fits w K)
    {s : (indexedMinPQSpec n K).State} {x : Data Program.registers} (o : IndexedMinPQ.Op n)
    (hr : Representation.Rep base hn hK s x) (hv : IndexedMinPQ.valid K s o)
    (ha : Program.code.argMatch o x.regs) :
    ∃ z s' a steps, Exec w Program.code.code x z steps ∧
      (indexedMinPQSpec n K).step s o s' a ∧ Program.code.decode (K_max := K) o z.regs = some a ∧
      Representation.Rep base hn hK s' z ∧
      Modifies (Block.mk base (space n)).footprint x.mem z.mem ∧
      steps ≤ Backend.factor Program.family * (memoryBound o + 1) + 8 ∧
      memoryState (Backend.frontier Program.family) z = (Memory.spec w).clientState
        (memoryState (Backend.frontier Program.family) x)
        (Memory.ops (Memory.compactLayout n base) o) ∧
      nativeObservation (K := K) o z.regs = some a := by
  let L := Memory.compactLayout n base
  let hL := Memory.valid_compactLayout (base := base) hn hK
  let S : Backend (indexedMinPQSpec n K) Program.family :=
    (backend n K L).extend Program.initialization
  have hI : S.Implements (Memory.refinement hL) := (implements L hL).extend Program.initialization
  let x₀ := x.set (Program.bank 3) 0
  obtain ⟨hbx₀, hm₀, hl₀⟩ := Program.stage_zero x hr.bounded
  have hr₀ : Representation.Rep base hn hK s x₀ := hr.congr
    (fun _ _ => rfl) (le_of_eq (congrArg Memory.State.frontier hm₀).symm) hl₀ hbx₀
  obtain ⟨hi, habs, _⟩ := (Backend.rep_iff hI s x₀).mp hr₀.1
  let e := memoryState (Backend.frontier Program.family) x₀
  have hv₀ : (indexedMinPQSpec n K).valid ((Memory.refinement hL).abs e) o := habs.symm ▸ hv
  have hrun := hI.run o e
  have hvalid := ((Memory.spec w).demonicValid_iff_validHistory_runClient _ _).mp
    ((Memory.refinement hL).valid o hi hv₀)
  have hhist : (Memory.spec w).clientHistory e ((Memory.refinement hL).methods o) =
      (Memory.spec w).clientHistory e ((Program.family (S.tag o)).prog (S.arg o)) :=
    congrArg (fun t => t.2.2) hrun
  obtain ⟨_, hsafe⟩ := hI.entry o (wellFormed_memoryState hbx₀) hi hv₀
  have hlive : x₀.regs ∘ Backend.src Program.family (S.tag o) =
      (Program.family (S.tag o)).input (S.arg o) :=
    (Program.stage_zero_input ((backend n K L).tag o) x).trans
      (Program.method_arguments L x o hr.2 ha)
  obtain ⟨y, N, he, _, hstate, hout, hby, hframe⟩ :=
    Backend.exists_exec_live Program.family (S.tag o) (S.arg o) hbx₀ hlive hsafe
      (hhist ▸ hvalid)
  let a := S.answer o ((Memory.spec w).clientResult e
    ((Program.family (S.tag o)).prog (S.arg o)))
  have hbe : S.exec w x₀ o a y N := (Backend.exec_iff S w x₀ y o a N).mpr
    ⟨by simpa only [Backend.prepare,
      Backend.install_eq_self Program.family (S.tag o) (S.arg o) x₀ hlive] using he, _, rfl, hout⟩
  have hN : N ≤ Backend.factor Program.family * (memoryBound o + 1) :=
    bound_extend Program.initialization L hL hr₀.1 hv hbe
  obtain ⟨s', hstep, hrepY⟩ := (Backend.implementation hI).correct hr₀.1 hv hbe
  have hlY : ∀ i : Fin 4,
      y.regs (Program.argument (i.castAdd 2)) = layoutWords ⟨n, L⟩ i := fun i =>
    calc
      y.regs (Program.argument (i.castAdd 2)) = x₀.regs (Program.argument (i.castAdd 2)) :=
        hframe _ (by rw [Program.argument_source]; exact Backend.src_ne_frontier _ _ _)
          (fun j => by rw [Program.argument_source]; exact (Backend.src_ne_tmp _ _ _ _ _).symm)
      _ = layoutWords ⟨n, L⟩ i := hr₀.2 i
  have hmodY := Backend.modifies (M := Memory.framed hL) hI hr₀.1 hv hbe
  obtain ⟨z, ⟨steps, hsteps, hez⟩, hbz, hmz, hfz, hlz, hflag, hvalue, hkey⟩ :=
    Program.wrap_body L x o ha (N := N) ⟨N, le_rfl, he⟩ hby
  have hzstate : memoryState (Backend.frontier Program.family) z =
      memoryState (Backend.frontier Program.family) y :=
    Memory.State.ext hmz (Program.code_frontier ▸ hfz)
  have hrZ : Representation.Rep base hn hK s' z := Representation.Rep.congr ⟨hrepY, hlY⟩
    (fun c _ => congrFun hmz c) (le_of_eq (congrArg Memory.State.frontier hzstate).symm) hlz hbz
  obtain ⟨hdecode, hnative⟩ :=
    decode_body L e o y z hout hflag hvalue (by cases o <;> exact hkey)
  have hanswer : (Memory.spec w).clientResult e (Memory.ops L o) = a := congrArg Prod.fst hrun
  refine ⟨z, s', a, steps, hez, hstep, hdecode.trans (congrArg some hanswer), hrZ,
    fun c hc => (congrFun hmz c).trans (hmodY c (by
      simpa only [Memory.Framed.region_eq_footprint (Memory.framed hL) rfl,
        Memory.framed_footprint, Memory.compactLayout_footprint n base] using hc)),
    by omega,
    (hzstate.trans (hstate.trans (congrArg (fun ⟨_, st, _⟩ => st) hrun).symm)).trans
      (congrArg (fun e => (Memory.spec w).clientState e (Memory.ops L o)) hm₀),
    hnative.trans (congrArg some hanswer)⟩

private noncomputable def implementationImpl {w n K base : ℕ}
    (hS : Fits w (base + space n)) (hK : Fits w K) :
    Cslib.DataStructure.WordRAM.StateTransitionImpl Program.code.toSubroutineCode
      (indexedMinPQSpec n K) w base ![n] (IndexedMinPQ.empty n) where
  toSubroutineBase := subroutineBase hS hK
  step_exec {s x} o hr hv ha := by
    have hn : Fits w n := hS.of_le (by unfold space; omega)
    have hrep : Representation.Rep base hn hK s x :=
      (subroutineBase_rep_iff hS hK s x).mp hr
    rw [subroutineBase_argMatch] at ha
    obtain ⟨y, s', a, N, he, hstep, hd, hr', hm, hb, _, _⟩ := raw_exec hn hK o hrep hv ha
    refine ⟨y, s', a, N, he, hstep, ?_, (subroutineBase_rep_iff hS hK s' y).mpr hr', ?_, ?_⟩
    · rwa [subroutineBase_decode]
    · rwa [subroutineBase_space]
    · simpa only [subroutineBase_potential, subroutineBase_charge, Nat.add_zero] using hb

/-- The single global raw heap program implements the indexed priority queue under the original
end-fit and key-fit assumptions. Argument matching is an explicit calling-convention premise;
the charged method code includes zero staging, dispatch and the lookup result copy. -/
noncomputable def subroutineImpl {w n K base : ℕ}
    (hS : Fits w (base + space n)) (hK : Fits w K) :
    Cslib.DataStructure.WordRAM.StateTransitionImpl Program.code.toSubroutineCode
      (indexedMinPQSpec n K) w base ![n] (IndexedMinPQ.empty n) := implementationImpl hS hK

private theorem subroutineImpl_toBase_aux {w n K base : ℕ}
    (hS : Fits w (base + space n)) (hK : Fits w K) :
    (subroutineImpl hS hK).toSubroutineBase = subroutineBase hS hK := rfl

/-- Raw initialization, representation, charge and argument metadata are inherited unchanged. -/
theorem subroutineImpl_toBase {w n K base : ℕ}
    (hS : Fits w (base + space n)) (hK : Fits w K) :
    (subroutineImpl hS hK).toSubroutineBase = subroutineBase hS hK :=
  subroutineImpl_toBase_aux hS hK

/-- An arbitrary actual raw execution leaves the complete state of the original source method,
not merely a state with the same typed answer. Determinism transfers the certified execution's
literal memory/frontier equality to the supplied execution. -/
theorem subroutineImpl_exec_memoryState {w n K base : ℕ}
    (hS : Fits w (base + space n)) (hK : Fits w K)
    {s : (indexedMinPQSpec n K).State} {x y : Data Program.registers} {N : ℕ}
    (o : IndexedMinPQ.Op n) (hr : (subroutineImpl hS hK).rep s x)
    (hv : IndexedMinPQ.valid K s o) (ha : (subroutineImpl hS hK).argMatch o x.regs)
    (he : Exec w Program.code.code x y N) :
    memoryState (Backend.frontier Program.family) y = (Memory.spec w).clientState
      (memoryState (Backend.frontier Program.family) x)
      (Memory.ops (Memory.compactLayout n base) o) := by
  rw [subroutineImpl_toBase, subroutineBase_argMatch] at ha
  obtain ⟨_, _, _, _, hez, _, _, _, _, _, hstate, _⟩ := raw_exec (hS.of_le (by wram_omega)) hK o
    ((subroutineBase_rep_iff hS hK s x).mp (subroutineImpl_toBase hS hK ▸ hr)) hv ha
  rwa [(he.unique hez).1]

/-- Every actual admissible body run already produces canonical fixed-bank observations.
The lookup payload remains in the first payload slot even after the legacy key copy. -/
theorem subroutineImpl_exec_nativeObservation {w n K base : ℕ}
    (hS : Fits w (base + space n)) (hK : Fits w K)
    {s : (indexedMinPQSpec n K).State} {x y : Data Program.registers} {N : ℕ}
    (o : IndexedMinPQ.Op n) (hr : (subroutineImpl hS hK).rep s x)
    (hv : IndexedMinPQ.valid K s o) (ha : (subroutineImpl hS hK).argMatch o x.regs)
    (he : Exec w Program.code.code x y N) :
    nativeObservation (K := K) o y.regs = Program.code.decode (K_max := K) o y.regs := by
  rw [subroutineImpl_toBase, subroutineBase_argMatch] at ha
  obtain ⟨_, _, _, _, hez, _, hd, _, _, _, _, hnative⟩ := raw_exec (hS.of_le (by wram_omega)) hK o
    ((subroutineBase_rep_iff hS hK s x).mp (subroutineImpl_toBase hS hK ▸ hr)) hv ha
  exact (he.unique hez).1 ▸ hnative.trans hd.symm

end Cslib.DataStructure.PriorityQueue.BinaryHeap.Native
