/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Complexity.Classes.CatalyticSpace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Bool
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # A checked catalytic run that changes and restores its borrowed bit -/

set_option linter.privateModule false

namespace CslibFrontierTests.CatalyticSpace

open Cslib.Catalytic Cslib.Complexity Turing Turing.MultiTapeTM

private def put (bit : Bool) (emit state : Option Bool) : Turing.Action 1 Bool (Option Bool) :=
  ⟨0, fun _ => (some (some bit), 0), emit, state.map some⟩

private def flipRestore : MultiTapeTM 1 Bool (Option Bool) :=
  MultiTapeTM.ofTr none fun state input work =>
    match state with
    | none =>
      let bit := (work 0).getD false
      put (!bit) none (some bit)
    | some bit => put bit (some (input.getD false)) none

private def cfg (inputBit cell : Bool) (state : Option (Option Bool)) (out : List Bool) :
    Cfg 1 Bool (Option Bool) [inputBit] :=
  wordsCfg [inputBit] state (fun _ => [cell]) out

private theorem put_apply (inputBit old new : Bool) (state : Option (Option Bool))
    (emit next : Option Bool) (out : List Bool) :
    (put new emit next).apply (cfg inputBit old state out) =
      cfg inputBit new (next.map some) (out ++ emit.toList) := by
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · simp [cfg, Turing.Action.apply, put]
  · funext i
    change Function.update (tapeOfList [old]) 0 (some new) = tapeOfList [new]
    have h (b : Bool) : tapeOfList [b] =
        Function.update (fun _ => none) 0 (some b) := by
      simpa using tapeOfList_append_single ([] : List Bool) b
    simp [h]
  · funext i
    rfl

private theorem step_flip (a b : Bool) :
    flipRestore.step (cfg a b (some none) []) = cfg a (!b) (some (some b)) [] := by
  rw [step_of_state (rfl : (cfg a b (some none) []).state = some none), flipRestore, tr_ofTr]
  change (put (!(Option.getD (tapeOfList [b] 0) false)) none
    (some (Option.getD (tapeOfList [b] 0) false))).apply (cfg a b (some none) []) = _
  simpa [tapeOfList_zero] using put_apply a b (!b) (some none) none (some b) []

private theorem step_restore (a b : Bool) :
    flipRestore.step (cfg a (!b) (some (some b)) []) = cfg a b none [a] := by
  rw [step_of_state (rfl : (cfg a (!b) (some (some b)) []).state = some (some b)),
    flipRestore, tr_ofTr]
  change (put b (some ((cfg a (!b) (some (some b)) []).inputSymbol.getD false))
    none).apply (cfg a (!b) (some (some b)) []) = _
  have h : (cfg a (!b) (some (some b)) []).inputSymbol = some a :=
    inputSymbolInner 0 rfl (by simp)
  simpa [h] using put_apply a (!b) b (some (some b)) (some a) none []

private noncomputable def path (a b : Bool) : flipRestore.RunPath [a] where
  length := 2
  toFun := ![cfg a b (some none) [], cfg a (!b) (some (some b)) [], cfg a b none [a]]
  step i := by
    apply (MultiTapeTM.step_iff (tm := flipRestore)).mpr
    fin_cases i
    · exact step_flip a b
    · exact step_restore a b

private theorem path_valid (a b : Bool) : ValidRun (path a b) [b] 0 a := by
  refine ⟨?_, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · refine Cfg.ext rfl rfl ?_ rfl rfl
    funext i
    have hi : i = Fin.last 0 := Fin.ext (by omega)
    subst i
    rfl
  · simp [freeSpaceUsed]
  · rintro c ⟨i, rfl⟩
    change Fin 3 at i
    fin_cases i <;> change -1 ≤ (0 : ℤ) ∧ 0 ≤ (1 : ℤ) <;> norm_num
  · rintro c ⟨i, rfl⟩ j
    change Fin 3 at i
    fin_cases i <;>
      simp [path, cfg, Option.isSome_iff_ne_none, tapeOfList_eq_none_iff, not_or, not_lt,
        not_le]

/-- The output reads the input bit and is independent of the catalyst's initial bit. -/
example : {b : Bool | b = true} ∈ CL encBool := by
  refine ⟨0, 0, ?_⟩
  refine ⟨fun _ => by simp, 0, Option Bool, inferInstance, flipRestore, fun a catalyst h => ?_⟩
  have hlen : catalyst.length = 1 := by simpa using h
  obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hlen
  exact ⟨path a b, a, by simpa using path_valid a b, Iff.rfl⟩

end CslibFrontierTests.CatalyticSpace
