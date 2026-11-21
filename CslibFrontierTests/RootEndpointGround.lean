/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootEndpointGround
import Mathlib.Tactic.FinCases

open Turing MultiTapeTM MultiTapeATM

private def queries : Fin 3 → RootEndpointCheck.Input := ![
  ((0, 10), ⟨List.replicate 8 false, 1, 0⟩),
  ((0, 11), ⟨List.replicate 8 false, 1, 0⟩),
  ((0, 0), ⟨[true, true], 1, 0⟩)]

-- Both the positive and negative ground branches use the same physical dispatcher and root
-- machine; even a malformed schedule cannot witness the default pair.
example : ∃ (u : ℕ) (G : Type) (_ : Finite G) (ground : MultiTapeATM (u + 2) Bool G) (C d : ℕ),
    ∀ {S : Type} (node : MultiTapeATM ((u + 2) + 1) Bool S) (mark : S → Bool)
      (input : List Bool) (i : Fin 3),
      let a := queries i
      let atm := TailCallGround.machine (Fin.natAdd (u + 2) 0) node
        (ground.extendTapes (Fin.castAddEmb 1)) mark
      let z := RootEndpointGround.groundConfig u S G input a
      let time := C * (a.2.raw.length + RootEndpointCheck.shortSize a ^ d + 1) + 1
      atm.HaltsWithin time z ∧ (atm.AcceptsWithin time z ↔ i = 0) := by
  obtain ⟨u, G, hG, ground, C, d, h⟩ := RootEndpointGround.exists_ground 1
  refine ⟨u, G, hG, ground, C, d, ?_⟩
  intro S node mark input i
  obtain ⟨hh, ha⟩ := h _ _ node mark (queries i) _
    (RootEndpointGround.ready_groundConfig u S G input (queries i))
  exact ⟨hh, ha.trans (by fin_cases i <;> decide)⟩
