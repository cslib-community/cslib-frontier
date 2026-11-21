/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveLeafATM

open Turing MultiTapeTM MultiTapeATM Cslib.CountingLeaf

-- These six raw fields serialize to 22 bits. Writing the carry and rewinding the two-bit path
-- takes five steps, serializing takes 49, and either sign's one-step continuation finishes at 55.
example {S : Type} (run : Bool → MultiTapeATM 2 Bool S) (carry claim : Bool) (host : List Bool) :
    let q := CarrySaveLeaf.query [true, false] [false] [true, true] [false, true] [true] carry
    let leaf := (WorkTapePredicate.config host (encRawInput q)).withState
      (some (run claim).toPTM.initial)
    let atm := CarrySaveLeafATM.machine (k := 0) (run claim) carry
    let start := (CarrySaveLeaf.initial 0 host q.context q.count q.width [true] q.bit q.path
      [] 3 false).withState (some atm.toPTM.initial)
    (run claim).HaltsWithin 1 leaf → atm.HaltsWithin 55 start ∧
      (atm.AcceptsWithin 55 start ↔ (run claim).AcceptsWithin 1 leaf) := by
  intro q leaf atm start hh
  have h := CarrySaveLeafATM.spec (k := 0) (run claim) host [true, false] [false] [true, true]
    [true] [true] [false, true] [] 3 false carry 1 hh
  have hl : (encRawInput q).length = 22 := by rw [length_encRawInput]; rfl
  change _ ∧ (_ ↔ _) at h
  have he : [false, true].length + 3 + (2 * (encRawInput q).length + 5) + 1 = 55 := by
    rw [hl]
    decide
  rw [he] at h
  simpa only [start, leaf, atm, q, CarrySaveLeaf.query] using h
