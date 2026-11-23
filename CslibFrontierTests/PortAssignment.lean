/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.PortAssignment

namespace Turing.MultiTapeATM.PortAssignment.Tests

open MultiTapeTM MultiTapeTM.PortAssignment QuantifiedWord
open Cslib.Circuits.Frontier

-- The restriction preserves order and repeats, without requiring a sorted port list.
example : plays (fun xs => check (⟨⟨[2, 0, 2], [false, true, false]⟩, [true]⟩, xs) = true)
    [] (flags ⟨[2, 0, 2], [false, true, false]⟩) :=
  (plays_check _).mpr rfl

-- A short global word supplies false at missing positions.
example : plays (fun xs => check (⟨⟨[0, 2], [true, false]⟩, [true]⟩, xs) = true)
    [] (flags ⟨[0, 2], [true, false]⟩) :=
  (plays_check _).mpr rfl

example : ¬ plays (fun xs => check (⟨⟨[0, 2], [true, true]⟩, [true]⟩, xs) = true)
    [] (flags ⟨[0, 2], [true, true]⟩) := by
  rw [plays_check]
  decide

-- No universal bits are needed for an empty list; its terminal still enforces length.
example : plays (fun xs => check (⟨⟨[], []⟩, [true, false]⟩, xs) = true)
    [] (flags ⟨[], []⟩) := (plays_check _).mpr rfl

example : ¬ plays (fun xs => check (⟨⟨[], [false]⟩, []⟩, xs) = true)
    [] (flags ⟨[], [false]⟩) := by
  rw [plays_check]
  decide

-- Padded challenge 3 accepts a structurally valid two-port request and rejects a short candidate.
example : check (⟨⟨[0, 2], [true, false]⟩, [true]⟩, [true, true]) = true := by decide
example : check (⟨⟨[0, 2], [true]⟩, [true]⟩, [true, true]) = false := by decide

-- An enormous binary address still has the default-bit semantics of the sharp native accessor.
example : plays (fun xs => check (⟨⟨[2 ^ 100], [false]⟩, [true]⟩, xs) = true)
    [] (flags ⟨[2 ^ 100], [false]⟩) := by
  rw [plays_check]
  decide

/- The same finite machine accepts the exact restriction of every runtime word to every
runtime port list and rejects all candidates with a different length. -/
example :
    ∃ (U : ℕ) (src : Fin U) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM U Bool Q) (C D : ℕ),
      ∀ (host word : List Bool) (ports : List ℕ),
        let accepts := fun bits =>
          let a : Input := ⟨⟨ports, bits⟩, word⟩
          atm.AcceptsWithin (C * (word.length + shortSize a ^ D + 1))
            (SharedWordFork.start src atm host (encInput a) 0)
        accepts (DescribedNetwork.wordBits word ports) ∧
          ∀ bits, bits.length ≠ ports.length → ¬ accepts bits := by
  obtain ⟨U, src, Q, hQ, atm, C, D, h⟩ := exists_evaluator
  refine ⟨U, src, Q, hQ, atm, C, D, ?_⟩
  intro host word ports accepts
  refine ⟨(h host ⟨⟨ports, DescribedNetwork.wordBits word ports⟩, word⟩).2.mpr rfl, ?_⟩
  intro bits hlen hacc
  have heq := (h host ⟨⟨ports, bits⟩, word⟩).2.mp hacc
  apply hlen
  simpa [DescribedNetwork.wordBits] using congrArg List.length heq

end Turing.MultiTapeATM.PortAssignment.Tests
