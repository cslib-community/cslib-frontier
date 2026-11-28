/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: local-only (regression tests)

import CslibFrontier.DataStructure.AVLTree.WordRAM
import Mathlib.Tactic.FinCases

/-! A complete compiled AVL insertion from empty input, with a distinct payload field.
The theorem supplies an actual standard word-RAM run and its represented insertion result. -/

set_option linter.privateModule false
open Cslib.PointerMachine Cslib.DataStructure SearchTree.PointerMachine
open Cslib.PointerMachine.WordRAM
open Cslib.PointerMachine.WordRAM.Natural (model scalars)

private abbrev L := layout 2 2
private def initial : State model L :=
  { State.empty with data := fun i => if i = 0 then 5 else if i = 3 then 17 else 0 }
private def source (_ : Fin 3) : Fin 4 := 3
private def sampleCode : List (Instr model L) :=
  AVLTree.PointerMachine.insert .zero .maxSucc .lt .heavy .le 1 source

-- All semantic, validity, source-register and width hypotheses are discharged concretely.
example : ∃ (t : State model L) (tree : BinaryTree (Label model 2))
    (z : Cslib.WordRAM.Data (regCount L)) (k : ℕ),
    AVLTree.PointerMachine.InsertResult id 1 source initial t .nil tree .nil ∧
    k + 1 ≤ 990 ∧
    Cslib.WordRAM.Runs 8 ((scalars L).compile sampleCode)
        ⟨0, encodeState (scalars L).encode initial⟩
      ⟨(scalars L).blockSize sampleCode * t.pc, z⟩ k ∧ Repr (scalars L).encode t z ∧
    Cslib.WordRAM.step 8 ((scalars L).compile sampleCode)
      ⟨(scalars L).blockSize sampleCode * t.pc, z⟩ = .halt 0 := by
  have initialBound : initial.DataValid (· ≤ 17) := by
    constructor
    · intro i
      fin_cases i <;> decide
    · simp [initial, State.empty]
  have certificate := AVLTree.WordRAM.insert_correct
    (extra := 2) (regs := 1) (w := 8) (b := 17) 1 (by decide) source
    (by intro f _ _; simp [source]) initial .nil .nil
    State.empty_valid initialBound trivial AddressesDistinct.nil trivial
    AVLTree.valid_nil rfl rfl rfl (by decide) (by decide)
  obtain ⟨t, tree, z, k, result, cost, execution, representation, halt⟩ := certificate
  exact ⟨t, tree, z, k, result, cost, execution, representation, halt⟩
