/-
Copyright (c) 2026 Sam McGuire, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BiTape
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.RunsBetween

/-!
# Emitting a work-tape word

A one-state native machine copies the suffix of a work-tape word to the append-only output.
It preserves the word, stops at its first following blank, and charges one transition per
emitted symbol plus one terminating transition. The input head does not move.
-/

public section

namespace Turing.MultiTapeTM

open Cslib.Turing

variable {Symbol : Type*}

/-- `BiTape.mk₁ xs` represents `tapeOfList xs` with head at `0`. -/
theorem represents_tapeOfList (xs : List Symbol) :
    (BiTape.mk₁ xs).Represents (tapeOfList xs) 0 := by
  intro position
  cases position <;> simp [BiTape.read_mk₁, tapeOfList]

/-- Phase 3 machine: walks right along work tape `0`, emitting each symbol to the output tape, and
halts on the first blank cell. -/
@[expose] def emitWork (Symbol : Type*) : MultiTapeTM 1 Symbol Unit :=
  ofTr () fun _ _ work =>
    match work 0 with
    | some a => ⟨0, fun _ => (none, 1), some a, some ()⟩
    | none => ⟨0, fun _ => (none, 0), none, none⟩

namespace EmitWork

variable {input : List Symbol} {inpos : Fin (input.length + 2)}

lemma runFrom_walk {y : List Symbol} {contents : ℤ → Option Symbol} {head : ℤ}
    (hrep : (BiTape.mk₁ y).Represents contents head) (out : List Symbol)
    (n : ℕ) (hn : n ≤ y.length) :
    (emitWork Symbol).runFrom ⟨some (), inpos, fun _ => contents, fun _ => head, out⟩ n =
      ⟨some (), inpos, fun _ => contents, fun _ => head + n, out ++ y.take n⟩ := by
  induction n with
  | zero => simp [runFrom]
  | succ n ih =>
    have hlt : n < y.length := by omega
    have hsym : contents (head + n) = some (y[n]'hlt) := by
      have hread := (hrep n).symm
      rw [BiTape.read_mk₁] at hread
      simpa [List.getElem?_eq_getElem hlt] using hread
    rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by omega), step_of_state rfl]
    simp only [emitWork, tr_ofTr, Cfg.workTapeSymbols, hsym]
    refine Cfg.ext rfl (by simp [Action.apply, moveInputPos_zero]) rfl ?_ ?_
    · funext _
      simp only [Action.apply_workTapePos, SignType.coe_one, Nat.cast_add, Nat.cast_one]
      omega
    · rw [List.take_add_one, List.getElem?_eq_getElem hlt]
      simp [Action.apply]

end EmitWork

open EmitWork in
/-- The emitter leaves all work cells in place and stops immediately after the emitted word. -/
theorem runFrom_emitWork_eq {input y : List Symbol} (mcfg : Cfg 1 Symbol Unit input)
    (hstate : mcfg.state = some ())
    (hrep : (BiTape.mk₁ y).Represents (mcfg.workTapes 0) (mcfg.workTapePos 0)) :
    (emitWork Symbol).runFrom mcfg (y.length + 1) =
      ⟨none, mcfg.inputPos, fun _ => mcfg.workTapes 0, fun _ => mcfg.workTapePos 0 + y.length,
        mcfg.output ++ y⟩ := by
  have hmcfg : mcfg = ⟨some (), mcfg.inputPos, fun _ => mcfg.workTapes 0,
      fun _ => mcfg.workTapePos 0, mcfg.output⟩ := by
    refine Cfg.ext hstate rfl ?_ ?_ rfl <;> funext i <;> rw [Fin.fin_one_eq_zero i]
  have hwalk := runFrom_walk (inpos := mcfg.inputPos) hrep mcfg.output y.length le_rfl
  have hblank : mcfg.workTapes 0 (mcfg.workTapePos 0 + y.length) = none := by
    have hread := (hrep y.length).symm
    rw [BiTape.read_mk₁] at hread
    simpa using hread
  have htotal : (emitWork Symbol).runFrom
      ⟨some (), mcfg.inputPos, fun _ => mcfg.workTapes 0, fun _ => mcfg.workTapePos 0, mcfg.output⟩
      (y.length + 1) =
    ⟨none, mcfg.inputPos, fun _ => mcfg.workTapes 0, fun _ => mcfg.workTapePos 0 + y.length,
      mcfg.output ++ y⟩ := by
    rw [runFrom, Function.iterate_succ_apply', ← runFrom, hwalk, step_of_state rfl]
    simp only [emitWork, tr_ofTr, Cfg.workTapeSymbols, hblank]
    refine Cfg.ext rfl (by simp [Action.apply, moveInputPos_zero]) rfl ?_ ?_
    · funext _
      simp [Action.apply]
    · simp [Action.apply]
  rw [← hmcfg] at htotal
  exact htotal

theorem runFrom_emitWork {input y : List Symbol} (mcfg : Cfg 1 Symbol Unit input)
    (hstate : mcfg.state = some ())
    (hrep : (BiTape.mk₁ y).Represents (mcfg.workTapes 0) (mcfg.workTapePos 0)) :
    ((emitWork Symbol).runFrom mcfg (y.length + 1)).state = none ∧
      ((emitWork Symbol).runFrom mcfg (y.length + 1)).output = mcfg.output ++ y := by
  rw [runFrom_emitWork_eq mcfg hstate hrep]
  exact ⟨rfl, rfl⟩

/-- Emit a complete work word while preserving its cells; its head ends on the following blank.
The previous output is preserved as a prefix. -/
theorem runsBetween_emitWork {input : List Symbol} (word out : List Symbol) :
    RunsBetween (emitWork Symbol) (tapesCfg input (fun _ => word) 0 0 out)
      (tapesCfg input (fun _ => word) 0 (fun _ => word.length) (out ++ word))
      (word.length + 1) (word.length + 2) := by
  let c := (tapesCfg input (fun _ : Fin 1 => word) 0 0 out).withState (some ())
  have hrep : (BiTape.mk₁ word).Represents (c.workTapes 0) (c.workTapePos 0) := by
    simpa [c, tapesCfg, Cfg.withState] using represents_tapeOfList word
  have hr := runFrom_emitWork_eq c rfl hrep
  rw [← Nat.one_mul (word.length + 2)]
  apply RunsBetween.of_runFrom
  simpa [c, tapesCfg, Cfg.withState] using hr

end Turing.MultiTapeTM
