/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Circuit.Frontier.Compiler.OpenBitNetwork
import CslibFrontier.Computability.Circuit.InnerSize
import CslibFrontier.Computability.Circuit.Pi
import Mathlib.Data.ZMod.Basic

/-!
# Compiling repeated and unread inputs

A binary AND reads the first input twice and ignores the second. Over the field with two
elements, setting the first bit to true gives contraction one for either value of the second bit.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Computability.Circuit.Frontier.OpenCircuitNetwork

open Cslib.Circuits Cslib.Circuits.Frontier

private def circuit : Circuit (fullSignature 2 Bool) 2 1 :=
  Circuit.oneGate (.fn fun b => b 0 && b 1) (fun _ => 0)

example :
    ∃ (V E : Type) (_ : Fintype V) (_ : Fintype E) (_ : DecidableEq E)
      (N : OpenBitNetwork (ZMod 2) (Fin 2) V E), N.Trivalent ∧ N.volume ≤ 17 ∧
        ∀ x, N.contraction x = if x 0 then 1 else 0 := by
  obtain ⟨V, E, iV, iE, dE, N, ht, hv, hc⟩ :=
    Compiler.exists_trivalent_openBitNetwork circuit fullInterpretation (ZMod 2)
      circuit.fanInAtMost_fullSignature
  refine ⟨V, E, iV, iE, dE, N, ht, hv, fun x => ?_⟩
  rw [hc]
  change (if x 0 && x 0 then (1 : ZMod 2) else 0) = _
  rw [Bool.and_self]

end CslibFrontierTests.Computability.Circuit.Frontier.OpenCircuitNetwork
