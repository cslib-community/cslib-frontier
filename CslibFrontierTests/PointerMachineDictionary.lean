/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: local-only (regression tests)

import CslibFrontier.DataStructure.AVLTree.PointerMachine.Dictionary
import CslibFrontier.Computability.WordRAM.PointerMachine.Defs

/-! Mutable dictionary reads and writes exercise absent keys, replacement, zero values,
rotations, and framing of another stored key and a client register. -/

set_option linter.privateModule false

open Cslib.PointerMachine Cslib.DataStructure
open SearchTree.PointerMachine
open AVLTree.PointerMachine
open AVLTree.PointerMachine.Dictionary

private abbrev model := Cslib.WordRAM.PointerMachine.model 8

private def empty (query value : ℕ) : State model (layout 2 3) :=
  { State.empty with data := fun i => if i = 0 then query else if i = 3 then value else 77 }

-- The full correctness theorem has an instance for every address and value, including zero.
example (query value : ℕ) : ∃ t tree time,
    Executes (write (M := model) (.constant 0) .maxSucc .lt .heavy .le) (empty query value) t time ∧
      time ≤ 52 ∧ WriteResult id (empty query value) t tree .nil (fun _ => 0) := by
  exact write_correct (M := model) (.constant 0) .maxSucc .lt .heavy .le id
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (empty query value) .nil .nil (fun _ => 0)
    trivial trivial AVLTree.valid_nil AddressesDistinct.nil (Stores.empty (M := model) 0) rfl rfl

private def label (address key height value : ℕ) : Label model 2 :=
  ⟨address, fun f => if f = 0 then key else if f = 1 then height else value⟩

private def initial (query value : ℕ) : State model (layout 2 3) where
  pc := 0
  ptr i := if i = 1 then some 0 else none
  data i := if i = 0 then query else if i = 3 then value else 77
  heap := [record (some 1) none none (label 0 20 2 200),
    record none none (some 0) (label 1 10 1 100)]

private def written (query value : ℕ) : State model (layout 2 3) :=
  let code := write (M := model) (.constant 0) .maxSucc .lt .heavy .le
  (fun s => (step code s).getD s)^[346] (initial query value)

private def readBack (s : State model (layout 2 3)) (query : ℕ) : ℕ :=
  let code := read (M := model) (.constant 0) .lt
  let start := { s.setData 0 query with pc := 0 }
  ((fun t => (step code t).getD t)^[40] start).data 3

-- Inserting 5 rotates the root but retains the other values and the client scalar register.
example : (written 5 50).ptr 1 = some 1 ∧ (written 5 50).heap.length = 3 ∧
    (written 5 50).data 4 = 77 := by decide +kernel
example : readBack (written 5 50) 5 = 50 ∧ readBack (written 5 50) 20 = 200 ∧
    readBack (written 5 50) 10 = 100 := by decide +kernel

-- Replacement and stored zero need no allocation; a missing key reads zero too.
example : (written 20 9).heap.length = 2 ∧ readBack (written 20 9) 20 = 9 ∧
    readBack (written 20 9) 10 = 100 := by decide +kernel
example : (written 10 0).heap.length = 2 ∧ readBack (written 10 0) 10 = 0 ∧
    readBack (written 10 0) 30 = 0 := by decide +kernel
