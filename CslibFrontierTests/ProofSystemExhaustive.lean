/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.ProofSystem.Exhaustive
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime

/-! Exhaustive proof systems: an unconditional one for `UNSAT`, and a small one for the pairs of
Booleans whose first component is `true`, where a padded framed member proves itself and a framed
non-member proves the default member. -/

set_option linter.privateModule false

namespace CslibFrontierTests.ProofSystemExhaustive

open Cslib.Complexity Turing.MultiTapeTM

/-- `UNSAT` has a proof system, without any assumption on `NP` and `coNP`. -/
example : Nonempty (ProofSystem encCNF UNSAT) :=
  ProofSystem.nonempty_of_mem_coNP cnfDecoder UNSAT_mem_coNP ⟨[[]], fun ⟨_, h⟩ => by simp at h⟩

/-- The pairs of Booleans whose first component is `true`. -/
abbrev FirstTrue : Set (Bool × Bool) := {q | q.1 = true}

/-- The complement of `FirstTrue` has the verifier that reads the first component and needs no
certificate. -/
theorem isVerifier_compl_firstTrue :
    IsVerifier (encPair encBool encBool) 0 (fun x : (Bool × Bool) × List Bool => !x.1.1)
      FirstTrueᶜ := by
  intro q
  simp [FirstTrue]

theorem polyTime_firstTrue_verifier :
    ComputableInPolyTime (fun x : (Bool × Bool) × List Bool => !x.1.1)
      (encPair (encPair encBool encBool) encBits) encBool := by
  fun_prop

/-- The exhaustive proof system of `FirstTrue`, with default member `(true, true)`. -/
noncomputable abbrev firstTrueSystem : ProofSystem (encPair encBool encBool) FirstTrue :=
  ProofSystem.exhaustive (.pair .bool .bool) polyTime_firstTrue_verifier isVerifier_compl_firstTrue
    (a₀ := (true, true)) rfl

/-- Acceptance: the framed member `(true, false)` with `2 ^ 0` padding bits proves itself. -/
example : firstTrueSystem (frame (encPair encBool encBool (true, false)) ++ [false]) =
    (true, false) := by
  simpa using ProofSystem.exhaustive_frame_append_replicate (.pair .bool .bool)
    polyTime_firstTrue_verifier isVerifier_compl_firstTrue (a₀ := (true, true)) rfl
    (a := (true, false)) rfl

/-- Fallback: the framed non-member `(false, false)` proves the default member `(true, true)`. -/
example : firstTrueSystem (frame (encPair encBool encBool (false, false)) ++ [false]) =
    (true, true) :=
  ProofSystem.exhaustive_eq_of_notMem _ _ _ _ (by
    rw [ProofSystem.verifierInstance, unframe_frame_append, Decoder.decode_enc]
    decide)

end CslibFrontierTests.ProofSystemExhaustive
