/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Complexity.Classes.MIPStar.Defs
import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.RE

/-! # The class `MIP*` and recursively enumerable sets

Checked clients of the native definitions behind `MIP* = RE`: the games of the constant verifiers
have entangled values `1` and `0`, the trivial problems are in `MIP*`, and a recursively enumerable
language is recursively enumerable in Mathlib's sense.
-/

namespace CslibFrontierTests.MIPStar

open Cslib.Complexity Turing.MultiTapeTM

/-- The game of the verifier accepting everything, on any instance, has entangled value `1`. -/
example (z : List Bool) : ((GameVerifier.const true).game encBits z).quantumValue = 1 :=
  GameVerifier.quantumValue_game_eq_one_of_forall _ _ fun _ _ => rfl

/-- The game of the verifier rejecting everything has entangled value `0`. -/
example (z : List Bool) : ((GameVerifier.const false).game encBits z).quantumValue = 0 :=
  GameVerifier.quantumValue_game_eq_zero_of_forall _ _ fun _ _ => rfl

example : (∅ : Set (List Bool)) ∈ MIPStar encBits := empty_mem_MIPStar encBits

example : (Set.univ : Set (List Bool)) ∈ MIPStar encBits := univ_mem_MIPStar encBits

/-- The verifier's game on an instance draws its seed and answers of the stated length. -/
example (V : GameVerifier (List Bool)) (z : List Bool) :
    V.bound encBits z = V.length.eval z.length := by
  simp [GameVerifier.bound]

example {L : Set (List Bool)} (hL : IsRE L encBits) : REPred (· ∈ L) := hL.rePred_bits

end CslibFrontierTests.MIPStar
