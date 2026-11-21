/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WhileCond.Partial

/-! # Checked terminal and divergent runs of a native loop -/

set_option linter.privateModule false

namespace CslibFrontierTests.NativeWhilePartial

open Turing Turing.MultiTapeTM

/-- In one step, move the input head right, emit a symbol and halt. -/
private def emit : MultiTapeTM 0 Bool Unit :=
  ofTr () fun _ _ _ =>
    ⟨.pos, Fin.elim0, some true, none⟩

/-- The boundaries after zero and after one round on a singleton input. -/
private def checkpoints : ℕ → Cfg 0 Bool Unit [true]
  | 0 => wordsCfgAt [true] 1 none Fin.elim0 []
  | _ + 1 => wordsCfgAt [true] 2 none Fin.elim0 [true]

private def hasInput (b : Option Bool) (_ : Fin 0 → Option Bool) : Bool := b.isSome

example : ∃ t,
    (whileCond hasInput emit).runFrom ((checkpoints 0).withState (some (.inr ()))) t =
      (checkpoints 1).withState none := by
  have hbody (i : ℕ)
      (h : hasInput (checkpoints i).inputSymbol (checkpoints i).workTapeSymbols = true) :
      ∃ t, emit.runFrom ((checkpoints i).withState (some emit.q₀)) t =
        (checkpoints (i + 1)).withState none := by
    cases i with
    | zero =>
      refine ⟨1, ?_⟩
      rw [runFrom_one, step_of_state rfl]
      simp only [emit, tr_ofTr]
      refine Cfg.ext rfl ?_ (funext fun i => nomatch i) (funext fun i => nomatch i) rfl
      change moveInputPos (1 : Fin 3) .pos = 2
      exact Fin.ext (by decide)
    | succ _ => contradiction
  have hpre (i : ℕ) (hi : i < 1) :
      hasInput (checkpoints i).inputSymbol (checkpoints i).workTapeSymbols = true := by
    have : i = 0 := by omega
    subst i
    rfl
  exact ((whileCond_halted_run_iff (c := hasInput) (tm := emit) checkpoints hbody
    ((checkpoints 1).withState none)).mpr ⟨1, hpre, rfl, rfl⟩).2

/-- For an always-true test, even a body that halts immediately does not make the loop halt. -/
example (cfg : ℕ → Cfg 0 Bool Unit [true])
    (hbody : ∀ i, ∃ t, emit.runFrom ((cfg i).withState (some emit.q₀)) t =
      (cfg (i + 1)).withState none) (t : ℕ) :
    ¬ ((whileCond (fun _ _ => true) emit).runFrom
      ((cfg 0).withState (some (.inr ()))) t).Halted := by
  intro h
  obtain ⟨_, _, impossible, _⟩ :=
    (whileCond_halted_run_iff (c := fun _ _ => true) (tm := emit) cfg (fun i _ => hbody i) _).mp
      ⟨h, t, rfl⟩
  exact Bool.noConfusion impossible

end CslibFrontierTests.NativeWhilePartial
