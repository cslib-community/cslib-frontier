/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Reachability.DoubleCounting.Scan.NondeterministicChoice

/-! # Native destination choices

Use the ordinary imports to compile a destination choice at dimension three and check both
its canonical successful occurrence trace and its out-of-range branch.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.DoubleCountingNondeterministicChoice

open Turing MultiTapeTM NondeterministicQueryMachine
open Turing.DoubleCounting.NondeterministicChoice Cslib.DoubleCounting.Scan.Binary

private def budget (input : List Bool) : ℕ := Nat.log2 input.length + 3

/-- At a destination boundary, one canonical vertex choice is realized by one native
occurrence list. Its verdict is acceptance on the original input, and the native space bound
applies to the machine on the same input. -/
example (input : List Bool) (v : Fin 3) :
    ∃ R : Routines (machine 0) (fun _ : List Bool => (machine 3).init) encBits budget,
      R.machine.RunsInSpace input (R.k * (2 * (R.c * budget input) + 1)) ∧
        (∃! indices, ∃ final,
          Native.replayChoices R.I R.P R.F R.C (R.machine.initCfg input) indices =
            some (true :: vertex v, final) ∧ final.Halted ∧ final.output = [true]) := by
  obtain ⟨R⟩ := Turing.DoubleCounting.NondeterministicChoice.exists_routines encBits (fun _ => 3)
    budget (fun _ => Nat.add_le_add_left (by decide : 1 ≤ 3) _)
    (fun input => Nat.le_add_left 3 (Nat.log2 input.length))
    ((ComputableInSpace.constZero (machine 3).init).mono_le fun _ => Nat.zero_le _)
  exact ⟨R, R.runsInSpace input,
    (native_firstHalting_accept_iff R input _).mpr (Or.inr ⟨v, rfl⟩)⟩

/-- The unused two-bit rank three rejects after its full width and meets the same bound. -/
example (input : List Bool) :
    let choices := [true, true, true]
    let s := (machine 3).run input choices
    (machine 3).halted s = true ∧ (machine 3).accept s = false ∧
      (encState s).length ≤ 27 :=
  ⟨haltsWithin 3 input _ rfl, rfl, length_run_le 3 input _⟩

end CslibFrontierTests.DoubleCountingNondeterministicChoice
