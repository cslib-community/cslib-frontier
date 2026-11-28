/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.PointerMachine.Scalar
public import CslibFrontier.DataStructure.AVLTree.PointerMachine.Dictionary

/-! # Word-RAM states represented by pointer-machine dictionaries

The logical AVL tree witnesses the shape and height of the concrete heap dictionary. Its
cardinality counts stored addresses, including entries whose value has subsequently become zero.
Program counters are separate from this data representation.
-/

public section
namespace Cslib.WordRAM.PointerMachine
open Cslib.DataStructure

/-- The register bank and linked AVL dictionary implement one RAM data state. -/
structure Represents {w r : ℕ} (x : Data r)
    (s : Cslib.PointerMachine.State (model w) (layout r))
    (tree : BinaryTree (SearchTree.PointerMachine.Label (model w) 2))
    (avl : AVLTree ℕ) : Prop where
  /-- Source registers occupy the client bank. -/
  registers : ∀ i, s.data (register i) = x.regs i
  /-- The heap contains the linked tree, with null parent at its root. -/
  heap : SearchTree.PointerMachine.Represents s.heap none tree
  /-- Keys and cached heights agree with the logical AVL tree. -/
  matched : AVLTree.PointerMachine.Matches id 1 tree avl
  /-- The dictionary is ordered, balanced, and has correct cached heights. -/
  valid : avl.Valid
  /-- Different tree positions occupy different heap records. -/
  distinct : SearchTree.PointerMachine.AddressesDistinct tree
  /-- Payload fields implement the total RAM memory, with zero outside the tree. -/
  memory : AVLTree.PointerMachine.Dictionary.Stores (M := model w) 0 tree x.mem
  /-- Pointer register one holds the dictionary root. -/
  root : s.ptr 1 = SearchTree.PointerMachine.root tree

/-- Changing the program counter preserves the data representation. -/
theorem Represents.with_pc {w r : ℕ} {x : Data r}
    {s : Cslib.PointerMachine.State (model w) (layout r)}
    {tree : BinaryTree (SearchTree.PointerMachine.Label (model w) 2)} {avl : AVLTree ℕ}
    (h : Represents x s tree avl) (pc : ℕ) : Represents x { s with pc := pc } tree avl :=
  ⟨h.registers, h.heap, h.matched, h.valid, h.distinct, h.memory, h.root⟩

end Cslib.WordRAM.PointerMachine
