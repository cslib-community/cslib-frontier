/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Tactic.Space

/-!
# Indexed lists keep their input certificates and the caller's workspace budget

`space` reads and replaces an entry of a list of binary naturals when the list, the index and the
replacement value each have a certificate at the goal's budget. The negative control is the
replacement goal with the index certificate removed, and matches the part of the error that names
the obligation `space` could not meet.
-/

namespace CslibFrontierTests.SpaceIndexedLists

open Turing.MultiTapeTM

variable {α : Type} {encIn : α ↪ List Bool} {S : α → ℕ}
  {l : α → List ℕ} {i j v : α → ℕ}

example (hl : ComputableInSpace l encIn (encList encNat) S)
    (hi : ComputableInSpace i encIn encNat S) :
    ComputableInSpace (fun x => (l x).getD (i x) 0) encIn encNat S := by
  space

example (hl : ComputableInSpace l encIn (encList encNat) S)
    (hi : ComputableInSpace i encIn encNat S)
    (hv : ComputableInSpace v encIn encNat S) :
    ComputableInSpace (fun x => (l x).set (i x) (v x)) encIn (encList encNat) S := by
  space

-- The replacement value can itself be read from the original list.
example (hl : ComputableInSpace l encIn (encList encNat) S)
    (hi : ComputableInSpace i encIn encNat S)
    (hj : ComputableInSpace j encIn encNat S) :
    ComputableInSpace (fun x => (l x).set (i x) ((l x).getD (j x) 0))
      encIn (encList encNat) S := by
  space

-- A runtime index needs a certificate; it is not arbitrary nonuniform advice.
/--
No theorems found for `i` in order to prove `ComputableInSpace (fun a => i a) encIn encNat S`
-/
#guard_msgs (whitespace := lax, substring := true) in
example (hl : ComputableInSpace l encIn (encList encNat) S)
    (hv : ComputableInSpace v encIn encNat S) :
    ComputableInSpace (fun x => (l x).set (i x) (v x)) encIn (encList encNat) S := by
  space

end CslibFrontierTests.SpaceIndexedLists
