/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.AVLTree.PointerMachine.Insert
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Search
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Lookup

/-!
# Memory represented by a linked AVL dictionary

A node stores its key in field zero, height in field one, and memory value in field two.
The tree may retain keys with the default value. Keys absent from the tree have that default;
this represents a total RAM memory without allocating a node for every possible address.
-/

public section
namespace Cslib.DataStructure.AVLTree.PointerMachine.Dictionary
open Cslib.PointerMachine SearchTree.PointerMachine
variable {M : Model} [LinearOrder M.Value]

/-- Field-two payloads represent a total memory; absent keys have the specified default. -/
structure Stores (zero : M.Value) (tree : BinaryTree (Label M 2))
    (memory : M.Value → M.Value) : Prop where
  /-- Every represented node contains its key's memory value. -/
  value : ∀ p label, tree.get p = some label → label.data 2 = memory (label.data 0)
  /-- All nondefault cells are represented; default cells may also have nodes. -/
  support : ∀ key, memory key ≠ zero → key ∈ SearchTree.elements (keys tree)

/-- The empty tree represents the everywhere-default memory. -/
theorem Stores.empty (zero : M.Value) : Stores zero (.nil : BinaryTree (Label M 2))
    (fun _ => zero) := by
  constructor
  · intro p label h
    cases p <;> cases h
  · intro key h
    exact (h rfl).elim

/-- An unsuccessful ordered search reads the default memory value. -/
theorem Stores.absent {zero : M.Value} {tree : BinaryTree (Label M 2)}
    {memory : M.Value → M.Value} (h : Stores zero tree memory)
    (ordered : SearchTree.Ordered (keys tree)) {key : M.Value}
    (missing : SearchTree.contains key (keys tree) = false) : memory key = zero := by
  by_contra ne
  have present := (SearchTree.contains_eq_true ordered key).mpr (h.support key ne)
  simp [missing] at present

omit [LinearOrder M.Value] in
/-- A payload store retains the key and height match with the same mathematical AVL tree. -/
theorem matches_updatePayload {encode : ℕ → M.Value} {tree : BinaryTree (Label M 2)}
    {avl : AVLTree M.Value} (h : Matches encode 1 tree avl) (a : ℕ) (value : M.Value) :
    Matches encode 1 (updateData tree a 2 value) avl := by
  induction tree generalizing avl with
  | nil => cases avl <;> exact h
  | node label l r il ir =>
    cases avl with
    | nil => cases h
    | node key height left right =>
      obtain ⟨hk, hh, hl, hr⟩ := h
      change _ ∧ _ ∧ Matches encode 1 (updateData l a 2 value) left ∧
        Matches encode 1 (updateData r a 2 value) right
      refine ⟨?_, ?_, il hl, ir hr⟩ <;>
        by_cases eq : label.address = a <;> simp [eq, hk, hh]

omit [LinearOrder M.Value] in
private theorem get_updatePayload (tree : BinaryTree (Label M 2)) (a : ℕ)
    (value : M.Value) (p : PosNum) :
    (updateData tree a 2 value).get p = (tree.get p).map (fun label =>
      { label with data := if label.address = a then Function.update label.data 2 value
        else label.data }) := by
  induction tree generalizing p with
  | nil => cases p <;> rfl
  | node label l r il ir =>
    cases p with
    | one => rfl
    | bit0 p => exact il p
    | bit1 p => exact ir p

/-- Inserting a key preserves the represented memory values at every other key,
including when rotations move the new node above old nodes. -/
theorem payload_except_insert {regs : ℕ} {encode : ℕ → M.Value}
    {s t : State M (layout 2 (regs + 2))} {before after : BinaryTree (Label M 2)}
    {original : AVLTree M.Value} {memory : M.Value → M.Value}
    (rep : Represents s.heap none before) (stored : Stores (encode 0) before memory)
    (result : InsertResult encode 1 (fun _ => 3) s t before after original) :
    ∀ q u, after.get q = some u → u.data 0 ≠ s.data 0 → u.data 2 = memory (u.data 0) := by
  intro q u get notQuery
  obtain ⟨node, lookup, fields⟩ := result.rep.get get
  have mem : u.address ∈ addresses after := (mem_addresses_iff ..).mpr ⟨q, u, get, rfl⟩
  rcases Finset.mem_insert.mp (result.footprint.2 mem) with fresh | old
  · have grows : s.heap.length < t.heap.length := by
      simpa only [fresh] using (List.getElem?_eq_some_iff.mp lookup).1
    have payload := result.freshPayload grows 0 (by decide)
    rw [← fresh, lookup] at payload
    have key : u.data 0 = s.data 0 := by simpa [fields] using payload
    exact (notQuery key).elim
  · obtain ⟨p, label, found, address⟩ := (mem_addresses_iff ..).mp old
    obtain ⟨oldNode, oldLookup, oldFields⟩ := rep.get found
    have bound := rep.address_lt old
    have key := result.payload u.address 0 bound (by decide)
    have payload := result.payload u.address 2 bound (by decide)
    rw [lookup, ← address, oldLookup] at key payload
    have eqKey : u.data 0 = label.data 0 := by simpa [fields, oldFields] using key
    have eqValue : u.data 2 = label.data 2 := by simpa [fields, oldFields] using payload
    rw [eqValue, stored.value p label found, eqKey]

/-- Writing a located key establishes its new memory value; values at every other key
are inherited. This also covers a newly inserted node whose old payload was arbitrary. -/
theorem stores_updatePayload (zero : M.Value) (tree : BinaryTree (Label M 2))
    (memory : M.Value → M.Value) (query value : M.Value) (p : PosNum) (label : Label M 2)
    (ordered : SearchTree.Ordered (keys tree)) (distinct : AddressesDistinct tree)
    (found : tree.get p = some label)
    (key : label.data 0 = query)
    (other : ∀ q u, tree.get q = some u → u.data 0 ≠ query → u.data 2 = memory (u.data 0))
    (support : ∀ k, memory k ≠ zero → k ∈ SearchTree.elements (keys tree)) :
    Stores zero (updateData tree label.address 2 value) (Function.update memory query value) := by
  constructor
  · intro q u get
    rw [get_updatePayload] at get
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp get
    by_cases eq : v.data 0 = query
    · have positions := get_key_injective ordered hv found (eq.trans key.symm)
      subst q
      have labels : v = label := Option.some.inj (hv.symm.trans found)
      subst v
      simp [eq]
    · have ne : v.address ≠ label.address := by
        intro address
        have positions := distinct q p v label hv found address
        subst q
        have labels : v = label := Option.some.inj (hv.symm.trans found)
        exact eq (labels ▸ key)
      simp [ne, eq, other q v hv eq]
  · intro k hk
    rw [keys_updateData _ _ _ _ (by decide)]
    by_cases eq : k = query
    · subst k
      exact key ▸ key_mem_of_get found
    · apply support
      simpa [Function.update_of_ne eq] using hk

/-- After inserting the query key, writing a value at its node updates the represented memory
at that key and leaves every other cell unchanged. -/
theorem stores_insert_updatePayload {regs : ℕ} {encode : ℕ → M.Value}
    {s t : State M (layout 2 (regs + 2))} {before after : BinaryTree (Label M 2)}
    {original : AVLTree M.Value} {memory : M.Value → M.Value}
    (rep : Represents s.heap none before) (matched : Matches encode 1 before original)
    (valid : original.Valid) (stored : Stores (encode 0) before memory)
    (result : InsertResult encode 1 (fun _ => 3) s t before after original)
    (p : PosNum) (label : Label M 2) (found : after.get p = some label)
    (key : label.data 0 = s.data 0) (value : M.Value) :
    Stores (encode 0) (updateData after label.address 2 value)
      (Function.update memory (s.data 0) value) := by
  refine stores_updatePayload (encode 0) after memory (s.data 0) value p label
    (result.matched.keys.symm ▸ (valid_insert valid (s.data 0)).ordered) result.distinct
    found key (payload_except_insert rep stored result) ?_
  intro k hk
  have old := stored.support k hk
  rw [matched.keys] at old
  rw [result.matched.keys]
  change k ∈ (AVLTree.insert (s.data 0) original).elements
  rw [elements_insert]
  exact Finset.mem_insert_of_mem old

end Cslib.DataStructure.AVLTree.PointerMachine.Dictionary
