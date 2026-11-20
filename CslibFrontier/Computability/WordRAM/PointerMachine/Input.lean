/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.PointerMachine.Defs
public import CslibFrontier.Computability.WordRAM.PointerMachine.Representation
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Encoding
import Mathlib.Data.List.GetD

/-! # Finite AVL keys for the word-RAM input convention

The source input occupies address zero (the length) and addresses one through the input length.
This construction supplies a valid AVL tree containing precisely that finite interval.
-/

public section
namespace Cslib.WordRAM.PointerMachine
open Cslib.DataStructure

/-- A valid AVL key tree for the first `n` addresses, built by the existing insertion algorithm. -/
@[expose] def inputKeys : ℕ → AVLTree ℕ
  | 0 => .nil
  | n + 1 => AVLTree.insert n (inputKeys n)

/-- The canonical input key tree has correct heights, ordering and balance. -/
theorem inputKeys_valid (n : ℕ) : (inputKeys n).Valid := by
  induction n with
  | zero => exact AVLTree.valid_nil
  | succ n ih => exact AVLTree.valid_insert ih n

/-- Exactly the first `n` addresses occur in the canonical input key tree. -/
@[simp] theorem elements_inputKeys (n : ℕ) : (inputKeys n).elements = Finset.range n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [inputKeys, AVLTree.elements_insert, ih, Finset.range_add_one]

/-- The source's initial memory is zero outside its length cell and input cells. -/
theorem init_memory_support (input : List ℕ) {r a : ℕ}
    (nonzero : (Data.init input : Data r).mem a ≠ 0) :
    a ∈ (inputKeys (input.length + 1)).elements := by
  rw [elements_inputKeys, Finset.mem_range]
  cases a with
  | zero => omega
  | succ a =>
    rw [Data.init_mem_succ] at nonzero
    by_contra h
    have bound : input.length ≤ a := by omega
    exact nonzero (List.getD_eq_default input 0 bound)

/-- Store each AVL node's key, cached height, and memory value in fields zero, one, and two. -/
@[expose] def payloadTree (memory : ℕ → ℕ) : AVLTree ℕ → BinaryTree (Fin 3 → ℕ)
  | .nil => .nil
  | .node key height l r => .node
      (fun f => if f = 0 then key else if f = 1 then height else memory key)
      (payloadTree memory l) (payloadTree memory r)

private theorem payloadTree_matches (w : ℕ) (memory : ℕ → ℕ) (avl : AVLTree ℕ)
    (base : ℕ) : AVLTree.PointerMachine.Matches id 1
      (SearchTree.PointerMachine.labelTree (M := model w) base (payloadTree memory avl)) avl := by
  induction avl generalizing base with
  | nil => trivial
  | node key height l r il ir => exact ⟨rfl, rfl, il _, ir _⟩

private theorem payloadTree_values (w : ℕ) (memory : ℕ → ℕ) (avl : AVLTree ℕ)
    (base : ℕ) (p : PosNum) (label : SearchTree.PointerMachine.Label (model w) 2)
    (found : (SearchTree.PointerMachine.labelTree base (payloadTree memory avl)).get p =
      some label) : label.data 2 = memory (label.data 0) := by
  induction avl generalizing base p with
  | nil => cases p <;> cases found
  | node key height l r il ir =>
    cases p with
    | one => cases Option.some.inj found; rfl
    | bit0 p => exact il _ p found
    | bit1 p => exact ir _ p found

private theorem payloadTree_numNodes (memory : ℕ → ℕ) (avl : AVLTree ℕ) :
    (payloadTree memory avl).numNodes = avl.numNodes := by
  induction avl with
  | nil => rfl
  | node key height l r il ir => simp [payloadTree, il, ir]; omega

/-- Canonical initial dictionary: preorder-labelled input cells, including the length cell. -/
@[expose] def inputTree (w : ℕ) (input : List ℕ) :
    BinaryTree (SearchTree.PointerMachine.Label (model w) 2) :=
  SearchTree.PointerMachine.labelTree 0
    (payloadTree (Data.init (r := 0) input).mem (inputKeys (input.length + 1)))

/-- Encode a word-RAM input as a linked AVL heap, with zeroed scalar registers and the root
in pointer register one. As with `WordRAM.Data.init`, input encoding is outside execution cost. -/
@[expose] def inputState (w r : ℕ) (input : List ℕ) :
    Cslib.PointerMachine.State (model w) (layout r) where
  pc := 0
  ptr := fun i => if i = 1 then SearchTree.PointerMachine.root (inputTree w input) else none
  data := fun _ => 0
  heap := SearchTree.PointerMachine.encodeHeap
    (payloadTree (Data.init (r := 0) input).mem (inputKeys (input.length + 1))) 0 none

/-- The explicitly encoded input satisfies the complete compiler representation invariant. -/
theorem inputState_represents (w r : ℕ) (input : List ℕ) :
    Represents (Data.init input) (inputState w r input) (inputTree w input)
      (inputKeys (input.length + 1)) := by
  have matched := payloadTree_matches w (Data.init (r := 0) input).mem
    (inputKeys (input.length + 1)) 0
  refine ⟨fun _ => rfl, ?_, matched, inputKeys_valid _,
    SearchTree.PointerMachine.addressesDistinct_labelTree _ _, ⟨?_, ?_⟩, ?_⟩
  · simpa [inputState, inputTree] using
      (SearchTree.PointerMachine.represents_encodeHeap (M := model w) (regs := r + 2)
        (payloadTree (Data.init (r := 0) input).mem (inputKeys (input.length + 1))) [] [] none)
  · exact payloadTree_values w (Data.init (r := 0) input).mem (inputKeys (input.length + 1)) 0
  · intro key nonzero
    change key ∈ SearchTree.elements (SearchTree.PointerMachine.keys
      (SearchTree.PointerMachine.labelTree (M := model w) 0
        (payloadTree (Data.init (r := 0) input).mem (inputKeys (input.length + 1)))))
    rw [matched.keys]
    exact init_memory_support input nonzero
  · simp [inputState]

/-- The input heap has one node per input cell, plus its length cell. -/
@[simp] theorem inputState_heap_length (w r : ℕ) (input : List ℕ) :
    (inputState w r input).heap.length = input.length + 1 := by
  simp only [inputState, SearchTree.PointerMachine.length_encodeHeap]
  rw [payloadTree_numNodes]
  rw [← AVLTree.card_elements (inputKeys_valid _).ordered, elements_inputKeys, Finset.card_range]

/-- Every pointer in the encoded input names an allocated node. -/
theorem inputState_valid (w r : ℕ) (input : List ℕ) : (inputState w r input).Valid := by
  constructor
  · intro i a eq
    simp only [inputState] at eq
    split at eq
    · exact by
        have rep := (inputState_represents w r input).heap
        cases h : inputTree w input with
        | nil => simp [h, SearchTree.PointerMachine.root] at eq
        | node label l rr =>
          simp only [h, SearchTree.PointerMachine.root, Option.some.injEq] at eq
          subst a
          rw [h] at rep
          exact (List.getElem?_eq_some_iff.mp rep.1).1
    · cases eq
  · exact SearchTree.PointerMachine.encodeHeap_links _ 0 none
      (by simp [inputState])
      (by intro a h; cases h)

end Cslib.WordRAM.PointerMachine
