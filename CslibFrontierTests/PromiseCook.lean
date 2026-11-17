/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Init
import CslibFrontier.Computability.Complexity.Classes.Promise.Oracle
import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure

/-! A promise with unrestricted answers on malformed words, and a typed one-query Cook client. -/

set_option linter.privateModule false

namespace CslibFrontierTests.PromiseCook

open Cslib.Complexity Turing.MultiTapeTM

private def bitPromise : PromiseProblem (List Bool) where
  yes := {[true]}
  no := {[false]}
  disjoint := by simp

private theorem bitPromise_mem : bitPromise ∈ PromiseP encBits := by
  refine mem_PromiseP_iff.2 ⟨fun w => w.headD false, Decoder.bool.computableInPolyTime, ?_⟩
  constructor
  · intro w hw
    have hw' : w = [true] := hw
    subst w
    rfl
  · intro w hw
    have hw' : w = [false] := hw
    subst w
    rfl

-- Two legal completions disagree on the empty word, which violates the promise.
example : bitPromise.SolvedBy (fun w => w.headD false) ∧
    bitPromise.SolvedBy (fun w => w.isEmpty || w.headD false) ∧
    ([] : List Bool).headD false ≠ (([] : List Bool).isEmpty || [].headD false) := by
  simp [PromiseProblem.SolvedBy, bitPromise]

-- The reduction negates its typed Boolean input and queries the resulting valid singleton.
-- Its correctness holds for every completion, not merely the canonical completion.
private theorem negation_reduction :
    PromiseProblem.PolyTimeTuringReducible encBool encBits
      (PromiseProblem.ofSet {false}) bitPromise := by
  classical
  apply PolyTimeOracleProgram.of_query (req := fun b : Bool => encBool (!b))
  · exact (show ComputableInPolyTime (fun b : Bool => !b) encBool encBool by
      fun_prop).encoding_comp
  · intro A hA
    constructor
    · intro b hb
      have hb' : b = false := hb
      subst b
      exact hA.1 [true] rfl
    · intro b hb
      have hb' : b = true := by simpa using hb
      subst b
      exact hA.2 [false] rfl

-- The closure theorem turns this oracle algorithm into an ordinary polynomial-time solver.
example : {false} ∈ P encBool :=
  ofSet_mem_PromiseP.1 (negation_reduction.mem_PromiseP Decoder.bits bitPromise_mem)

-- The shared elimination argument also applies to a non-word oracle encoding.
open Classical in
example : ∃ A ∈ P encBits,
    (PromiseProblem.ofSet ({false} : Set Bool)).SolvedBy (fun b => decide (encBool b ∈ A)) := by
  classical
  exact exists_mem_P_solvedBy_of_mem_PromiseP Decoder.bool
    (negation_reduction.mem_PromiseP Decoder.bits bitPromise_mem)

end CslibFrontierTests.PromiseCook
