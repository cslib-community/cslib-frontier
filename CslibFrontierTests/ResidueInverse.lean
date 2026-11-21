/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.ResidueInverse

open Cslib.Circuits.Frontier.FastContraction.ResidueInverse Cslib.BitString

-- At scale zero the trinomial has degree six. The first universal index asks the operand,
-- while index six must check the locally computed inverse instead.
private def unitWord : List Bool := [true, false, false, false, false, false]

example : route ⟨0, 0, true, unitWord ++ lowBits 3 0⟩ = .inr (0, true) := by decide
example : route ⟨0, 0, true, unitWord ++ lowBits 3 4⟩ = .inr (4, false) := by decide
example : route ⟨0, 0, true, unitWord ++ lowBits 3 6⟩ = .inl true := by decide
example : route ⟨0, 0, false, unitWord ++ lowBits 3 7⟩ = .inl false := by decide

open Cslib.Circuits.Frontier.FastContraction Turing.MultiTapeATM.QuantifiedWord

-- The same choices and machine must refute an incorrect claim on the genuine unit.
example : ¬plays (fun choices => answer unitWord (route ⟨0, 0, false, choices⟩)) []
    (flags (modulus 0).length) := by
  rw [plays_flags 0 0 false unitWord (by decide)]
  decide
