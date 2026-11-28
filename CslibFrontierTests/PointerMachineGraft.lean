/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: local-only (regression tests)

import CslibFrontier.DataStructure.SearchTree.PointerMachine.Graft

/-! Fresh-leaf attachment under two ancestors, including the root and exact address footprint. -/

set_option linter.privateModule false

open Cslib.PointerMachine Cslib.DataStructure SearchTree.PointerMachine

private abbrev model : Model where
  Value := ℕ
  undefined := 0
  Op := Empty
  Test := Empty
  evalOp op := nomatch op
  evalTest test := nomatch test

private def label (a : ℕ) : Label model 0 := ⟨a, fun _ => 10 + a⟩

private def context : List (Frame model 0) :=
  [.right .nil (label 1), .left (label 0) .nil]

private def heap : List (Record model (layout 0 0)) :=
  [record (some 1) none none (label 0), record none none (some 0) (label 1)]

private def expected : List (Record model (layout 0 0)) :=
  [record (some 1) none none (label 0), record none (some 2) (some 0) (label 1),
    record none none (some 1) (label 2)]

example : Represents expected none (plug context (.node (label 2) .nil .nil)) ∧
    AddressesDistinct (plug context (.node (label 2) .nil .nil)) ∧
    addresses (plug context (.node (label 2) .nil .nil)) = {0, 1, 2} ∧
    root (plug context (.node (label 2) .nil .nil)) = some 0 := by
  obtain ⟨rep, distinct, _, root⟩ := graftLeaf heap context (label 2) 1
    (by simp [heap, context, plug, Represents, root, label])
    (by simp [context, plug, AddressesDistinct.node_iff, addresses,
      BinaryTree.map, SearchTree.elements, label]) rfl rfl
  refine ⟨?_, distinct, ?_, root⟩
  · convert rep using 1
    simp [expected, heap, context, contextParent, record, label, Function.update,
      funext_iff, Fin.forall_fin_succ]
  · simp [context, plug, addresses, BinaryTree.map, SearchTree.elements, label]

-- The same theorem handles an empty tree, with no parent record to update.
example : Represents ([record none none none (label 0)] : List (Record model (layout 0 0)))
    none (.node (label 0) .nil .nil) ∧ AddressesDistinct (.node (label 0) .nil .nil) := by
  obtain ⟨rep, distinct, _, _⟩ := graftLeaf ([] : List (Record model (layout 0 0))) []
    (label 0) 0 trivial AddressesDistinct.nil rfl trivial
  exact ⟨rep, distinct⟩
