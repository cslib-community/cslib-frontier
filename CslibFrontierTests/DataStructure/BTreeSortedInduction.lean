/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (regression tests)

import CslibFrontier.DataStructure.BTree.Basic

set_option linter.privateModule false

open Cslib.DataStructure Cslib.DataStructure.BTree

private def leastKey? {α β : Type} : BTree α β → Option α
  | .leaf => none
  | .node first [] => leastKey? first
  | .node first ((k, _, _) :: _) => (leastKey? first).or (some k)

example {α β : Type} [LinearOrder α] {tr : BTree α β} (h : tr.toList.IsSortedAssoc) :
    leastKey? tr = (tr.toList.head?).map Prod.fst := by
  induction h using induction_isSortedAssoc with
  | leaf => rfl
  | node_nil _ _ ih => simpa [leastKey?] using ih
  | node_cons first k _ _ _ _ _ _ _ ih₁ _ =>
    rw [toList_node_cons, leastKey?, ih₁]; cases first.toList <;> rfl
