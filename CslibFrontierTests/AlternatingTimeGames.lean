/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

import CslibFrontier.Computability.Complexity.Classes.Alternation.GuessVerify
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp

/-!
# Tests: games within linear time are in `ATIME`

`Cslib.Complexity.mem_ATIME_of_alternation` applied to a game of two moves whose number of moves
and verifier are constants: with a verifier that always answers `true` the existential player
wins, giving `Set.univ ∈ ATIME (n + 1)`, and with one that always answers `false` it loses,
giving `∅ ∈ ATIME (n + 1)`. The hypotheses, including the bound `n + L a + TL a ≤ C * t n + C`
that pays for copying the instance, hold together at the linear bound `t n = n + 1`.
-/

-- Ordinary module client test: private declarations only.
set_option linter.privateModule false

namespace CslibFrontierTests.AlternatingTimeGames

open Cslib.Complexity Turing Turing.MultiTapeTM

/-- The constant game bounds: the instance, the two moves and the time to write their number. -/
private theorem le_of_const (a : List Bool) :
    (encBits a).length + 2 + (encBits a).length ≤ 3 * ((encBits a).length + 1) + 3 := by
  omega

/-- The verifier bound: the framed moves followed by the instance. -/
private theorem le_of_pair (a z : List Bool) (hz : z.length = 2) :
    (encPair encBits encBits (a, z)).length ≤ 3 * ((encBits a).length + 1) + 3 := by
  rw [length_encPair]
  simp only [encBits_apply, hz]
  omega

/-- A game of two moves that the existential player always wins is in `ATIME (n + 1)`. -/
example : (Set.univ : Set (List Bool)) ∈ ATIME encBits fun n => n + 1 :=
  mem_ATIME_of_alternation (L := fun _ => 2) (V := fun _ => true) (C := 3)
    (ComputableInO.const 2) (ComputableInO.const true)
    (fun _ => iff_of_true (Set.mem_univ _) (alternation_const.mpr rfl))
    le_of_const fun a z hz => le_of_pair a z hz

/-- A game of two moves that the existential player always loses is in `ATIME (n + 1)`. -/
example : (∅ : Set (List Bool)) ∈ ATIME encBits fun n => n + 1 :=
  mem_ATIME_of_alternation (L := fun _ => 2) (V := fun _ => false) (C := 3)
    (ComputableInO.const 2) (ComputableInO.const false)
    (fun a => iff_of_false (Set.notMem_empty a) fun h => Bool.false_ne_true
      (alternation_const.mp h))
    le_of_const fun a z hz => le_of_pair a z hz

end CslibFrontierTests.AlternatingTimeGames
