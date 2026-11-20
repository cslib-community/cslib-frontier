/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import CslibFrontier.Computability.Complexity.Classes.NPMV.Machine
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

open Cslib.Complexity
open Turing.MultiTapeTM

private def outputRel (b : Bool) (word : List Bool) : Prop :=
  b = true ∧ word.length ≤ 1

private theorem outputRel_mem_NPMV : outputRel ∈ NPMV encBool := by
  refine ⟨⟨1, fun _ _ h => by simpa using h.2⟩, P_subset_NP (mem_P.mpr ?_)⟩
  refine ⟨fun x => x.1 && decide (x.2.length ≤ 1), ?_, fun x => ?_⟩
  · apply ComputableInPolyTime.bool_and' (ComputableInPolyTime.fst encBool encBits)
    apply ComputableInPolyTime.unary_le'
    · exact (ComputableInPolyTime.encoding_length encBits).comp
        (ComputableInPolyTime.snd encBool encBits)
    · exact .const 1
  · simp [outputRel]

/-- A compiled transducer can return two different outputs, including the empty word,
and has no successful output on another input. -/
public theorem npmVMachine_outputs :
    ∃ (k : ℕ) (State : Type) (_ : Finite State)
      (M : Turing.MultiTapeNTM k Bool State) (clock : Polynomial ℕ),
      (∀ b, M.RunsInTime (encBool b) (clock.eval 1)) ∧
      M.Produces [true] [] ∧ M.Produces [true] [false] ∧
      ∀ w, ¬M.Produces [false] w := by
  obtain ⟨k, State, hfinite, M, clock, hM⟩ :=
    mem_NPMV_iff_computesRelationInPolyTime.mp outputRel_mem_NPMV
  exact ⟨k, State, hfinite, M, clock, fun b => (hM b).1,
    ((hM true).2 []).mp (by simp [outputRel]),
    ((hM true).2 [false]).mp (by simp [outputRel]),
    fun w hw => by simpa [outputRel] using ((hM false).2 w).mpr hw⟩
