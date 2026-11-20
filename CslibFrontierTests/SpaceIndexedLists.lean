/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Tactic.Space

/-! # Indexed lists keep their input certificates and the caller's workspace budget -/

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

-- Runtime indices need a certificate; they are not arbitrary nonuniform advice.
example (hl : ComputableInSpace l encIn (encList encNat) S)
    (hv : ComputableInSpace v encIn encNat S) (i : α → ℕ) : True := by
  fail_if_success
    have : ComputableInSpace (fun x => (l x).set (i x) (v x))
        encIn (encList encNat) S := by space
  trivial

-- A certified index cannot stand in for a missing replacement-value certificate.
example (hl : ComputableInSpace l encIn (encList encNat) S)
    (hi : ComputableInSpace i encIn encNat S) (v : α → ℕ) : True := by
  fail_if_success
    have : ComputableInSpace (fun x => (l x).set (i x) (v x))
        encIn (encList encNat) S := by space
  trivial

-- The original certificates do not justify a different, unrelated budget.
example (hl : ComputableInSpace l encIn (encList encNat) S)
    (hi : ComputableInSpace i encIn encNat S) (T : α → ℕ) : True := by
  fail_if_success
    have : ComputableInSpace (fun x => (l x).getD (i x) 0) encIn encNat T := by space
  trivial

end CslibFrontierTests.SpaceIndexedLists
