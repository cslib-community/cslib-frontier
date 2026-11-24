/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Circuit.Boolean.Tableau.LocalValueGame

/-!
# Tests: claims relative to the input in the circuit-value game on the tableau

The encoding `Cslib.Circuits.Boolean.Tableau.ValueGame.encLocal x` does not store the bits of the
input of a claim about `x`, only its length: claims about two different inputs of a thousand bits
have the same encoding relative to their inputs. A claim about another input takes the other tag
bit, so the encoding stays injective across inputs. With claims encoded relative to `x`, the game
on the claim that the output wire is true still decides the run of the machine
(`Cslib.Circuits.Boolean.Tableau.ValueGame.wins_position_outWire_iff`), and its reachable positions
have length logarithmic in the input length and the step count
(`Cslib.Circuits.Boolean.Tableau.ValueGame.exists_length_le_of_reach_encLocal`).
-/

set_option linter.privateModule false

namespace CslibFrontierTests.TableauLocalValueGame

open Cslib Cslib.Circuits.Boolean.Tableau Cslib.Circuits.Boolean.Tableau.ValueGame
open Turing Turing.MultiTapeATM.WordGame

/-- The bits of the input are not stored: claims about two inputs of the same length have the same
encoding relative to their inputs. -/
example : encLocal (List.replicate 1000 true) ⟨List.replicate 1000 true, 4, 7, true⟩ =
    encLocal (List.replicate 1000 false) ⟨List.replicate 1000 false, 4, 7, true⟩ := by
  simp only [encLocal_self, List.length_replicate]

/-- A claim about another input is tagged `true`, a claim about `x` is tagged `false`. -/
example : (encLocal [true] ⟨[false], 0, 0, true⟩).head? = some true ∧
    (encLocal [true] ⟨[true], 0, 0, true⟩).head? = some false := by
  rw [encLocal_of_ne (by decide), encLocal_self]
  exact ⟨rfl, rfl⟩

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State] (tm : MultiTapeTM k Bool State)

/-- With claims encoded relative to the input, the game on the output claim decides the run. -/
example {x : List Bool} {T : ℕ} (hn : x.length < 2 * T) :
    Wins (update tm (encLocal x))
        (position tm (encLocal x) ⟨x, T, outWire k State x.length T, true⟩) ↔
      OutView.ofList (tm.runFrom (tm.initCfg x) T).output = .one true :=
  wins_position_outWire_iff (encLocal x) hn

/-- Positions reachable from the output claim have length `O(log x.length + log T)`. -/
example : ∃ c, ∀ (x : List Bool) (T : ℕ) (w : List Bool),
    Reach (update tm (encLocal x))
      (position tm (encLocal x) ⟨x, T, outWire k State x.length T, true⟩) w →
    w.length ≤ 4 * Nat.size x.length + 6 * Nat.size T + c := by
  obtain ⟨c, hc⟩ := exists_length_le_of_reach_encLocal (tm := tm)
  exact ⟨c, fun x T w h => hc x T _ true w (outWire_lt _ _) h⟩

end CslibFrontierTests.TableauLocalValueGame
