/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.PauliBraidingGame
import CslibFrontier.Computability.PCP.TwoProverGame.CHSH

/-! # Checked rounds of the Pauli braiding verifier

These clients instantiate the verifier with CHSH. The consistency rounds use an odd
pair whose X string is lexicographically larger than its Z string.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.PauliBraidingGame

open Cslib Cslib.PCP Cslib.BitString

private def xString : Fin 2 → Bool := fun _ => true
private def zString : Fin 2 → Bool := fun i => decide (i = 0)
private def dummy : Fin 2 → Bool := fun _ => false

private def odd : ↥(oddPairs (Fin 2)) := ⟨(xString, zString), mem_oddPairs.mpr (by decide)⟩

private noncomputable def game :=
  pauliBraidingGame 2 TwoProverGame.chsh id (fun _ => id)

/-- The linearity branch uses the same questions and verdict as the standalone game. -/
example (r : SymmetricLinearitySeed 2) (a b : Bool × Bool) :
    let q := (symmetricLinearityGame 2).query r
    game.query (.linearity true r) = (.basis true q.1, .basis true q.2) ∧
      (game.accepts (.linearity true r) (.inl a) (.inl b) ↔
        (symmetricLinearityGame 2).accepts r a b) :=
  ⟨rfl, Iff.rfl⟩

/-- The CHSH subgame carries the same oriented pair to both players and swaps the questions
and the answers together. -/
example (x y a b : Bool) :
    game.query (.anticommutation true odd x y) =
        (.anticommutation true y odd, .anticommutation false x odd) ∧
      (game.accepts (.anticommutation true odd x y) (.inr b) (.inr a) ↔
        TwoProverGame.chsh.accepts x y a b) :=
  ⟨rfl, Iff.rfl⟩

/-- A shared CHSH question token still produces two distinct questions. The special
round sends precisely the second logical player's anticommutation question. -/
example :
    let q := game.query (.anticommutation false odd true true)
    q.1 ≠ q.2 ∧ (game.query (.special false true odd true)).2 = q.2 := by
  refine ⟨?_, rfl⟩
  intro h
  cases h

/-- The matching special question compares the Z bit in the first sorted coordinate.
An unmatched question accepts a well-typed answer automatically. -/
example :
    game.accepts (.special true true odd true) (.inr true) (.inl (true, false)) ∧
      ¬ game.accepts (.special true true odd true) (.inr true) (.inl (false, true)) ∧
      game.accepts (.special true true odd false) (.inr true) (.inl (false, true)) ∧
      ¬ game.accepts (.special true true odd false) (.inl (true, false)) (.inl (false, true)) := by
  change (true = true → true = true) ∧ ¬ (true = true → false = true) ∧
    (false = true → false = true) ∧ ¬ False
  decide

/-- The Z string is shared in the same-basis round. It is the first coordinate for the
odd pair and the second coordinate for the independently padded question. -/
example :
    game.query (.sameBasis false true odd dummy) =
        (.basis true (zString, xString), .basis true (dummy, zString)) ∧
      game.accepts (.sameBasis false true odd dummy) (.inl (true, false)) (.inl (false, true)) ∧
      ¬ game.accepts (.sameBasis false true odd dummy) (.inl (true, false)) (.inl (true, false)) :=
  ⟨rfl, rfl, Bool.noConfusion⟩

end CslibFrontierTests.PauliBraidingGame
