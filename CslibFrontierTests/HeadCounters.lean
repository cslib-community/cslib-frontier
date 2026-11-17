/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.HeadCounters

/-! Checked clients of the fixed-marker counter simulation: decrement, zero-test, and halting.
The countdown runs from a represented counter configuration, not from a length-encoded input.
-/

set_option linter.privateModule false

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.HeadCounter

private def countdown (_ : Unit) (_ : Option Bool) (zero : Fin 1 → Bool) : Instruction 1 Unit :=
  if zero 0 then ⟨0, fun _ => -1, some true, none⟩
  else ⟨0, fun _ => -1, none, some ()⟩

private theorem countdown_step_succ (input : List Bool) (n : ℕ) :
    (machine () countdown).step
      (cfg (some ()) (1 : Fin (input.length + 2)) (fun _ => n + 1) []) =
      cfg (some ()) 1 (fun _ => n) [] := by
  rw [step_cfg]
  simp [countdown, Nat.cast_add, SignType.cast]

private theorem countdown_step_zero (input : List Bool) :
    (machine () countdown).step
      (cfg (some ()) (1 : Fin (input.length + 2)) (fun _ => 0) []) =
      cfg none 1 (fun _ => 0) [true] := by
  rw [step_cfg]
  simp [countdown, SignType.cast]

-- Every natural counter value counts down and halts; the same one marker suffices throughout.
private theorem countdown_run (input : List Bool) (n : ℕ) :
    (machine () countdown).runFrom
      (cfg (some ()) (1 : Fin (input.length + 2)) (fun _ => n) []) (n + 1) =
      cfg none 1 (fun _ => 0) [true] := by
  induction n with
  | zero => exact countdown_step_zero input
  | succ n ih =>
    rw [show n + 1 + 1 = 1 + (n + 1) by omega, runFrom_add, runFrom_one,
      countdown_step_succ, ih]

example (input : List Bool) (n : ℕ) :
    let c := (machine () countdown).runFrom
      (cfg (some ()) (1 : Fin (input.length + 2)) (fun _ => n) []) (n + 1)
    c.Halted ∧ c.output = [true] ∧ ∀ i, c.workTapePos i = 0 := by
  dsimp only
  rw [countdown_run]
  simp [cfg]

-- The invariant applies to initialized executions and all times, not only to represented starts.
example (input : List Bool) (t : ℕ) (i : Fin 1) (z : ℤ) (hz : z ≠ 0) :
    ((machine () countdown).runFrom ((machine () countdown).initCfg input) t).workTapes i z =
      none := by
  by_contra h
  exact hz (run_support () countdown input t i z h)
