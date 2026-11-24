/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.AVLTree.Basic

/-!
# AVL operations relative to a side

Rotations and rebalancing come in mirror-image pairs. The definitions here name a child by its
side instead, so that a statement about "the child on side `right`" covers both: `nodeSide`,
`mkNodeAt`, `rotateAt` and `balanceAt` are `AVLTree.node`, `mkNode`, the rotation that promotes
that child, and `balance`, with the distinguished child placed on the selected side.

## Main results

* `rotateAt_nodeSide`: a rotation, as two `mkNodeAt`.
* `balanceAt_heavy`: `balance` at a node whose child on a side is too tall is a single or a
  double rotation of that child.
* `insert_nodeSide`: insertion on a side, as an insertion into the child and a `balanceAt`.
-/

public section

namespace Cslib.DataStructure.AVLTree

variable {α : Type*}

/-- A node with its distinguished child on the selected side. -/
@[expose] def nodeSide (right : Bool) (a : α) (h : ℕ) (child sibling : AVLTree α) : AVLTree α :=
  if right then .node a h sibling child else .node a h child sibling

/-- `mkNode` with the distinguished child on the selected side. -/
@[expose] def mkNodeAt (right : Bool) (a : α) (child sibling : AVLTree α) : AVLTree α :=
  if right then mkNode a sibling child else mkNode a child sibling

/-- The rotation that promotes the child on the selected side. -/
@[expose] def rotateAt (right : Bool) (a : α) (child sibling : AVLTree α) : AVLTree α :=
  if right then rotateLeft a sibling child else rotateRight a child sibling

/-- `balance` with the distinguished child on the selected side. -/
@[expose] def balanceAt (right : Bool) (a : α) (child sibling : AVLTree α) : AVLTree α :=
  if right then balance a sibling child else balance a child sibling

/-- Promoting a child, whose own children are `outer` on the same side and `inner` on the other,
puts `outer` on that side and the old root, with `inner` and the sibling, on the other. -/
theorem rotateAt_nodeSide (right : Bool) (a k : α) (h : ℕ) (outer inner sibling : AVLTree α) :
    rotateAt right a (nodeSide right k h outer inner) sibling =
      mkNodeAt right k outer (mkNodeAt right a inner sibling) := by
  cases right <;> rfl

/-- `mkNodeAt` is a node with the height of `mkNode`. -/
theorem mkNodeAt_eq_nodeSide (right : Bool) (a : α) (child sibling : AVLTree α) :
    mkNodeAt right a child sibling =
      nodeSide right a (1 + max child.cachedHeight sibling.cachedHeight) child sibling := by
  cases right
  · rfl
  · simp [mkNodeAt, nodeSide, mkNode, Nat.max_comm]

/-- Exchanging the side and the two subtrees gives the same node. -/
theorem nodeSide_not (right : Bool) (a : α) (h : ℕ) (child sibling : AVLTree α) :
    nodeSide (!right) a h sibling child = nodeSide right a h child sibling := by
  cases right <;> rfl

/-- The children of a height-consistent node are height-consistent. -/
theorem HeightConsistent.of_nodeSide {right : Bool} {a : α} {h : ℕ} {child sibling : AVLTree α}
    (hc : (nodeSide right a h child sibling).HeightConsistent) :
    child.HeightConsistent ∧ sibling.HeightConsistent := by
  cases right
  · exact ⟨hc.2.1, hc.2.2⟩
  · exact ⟨hc.2.2, hc.2.1⟩

/-- `mkNodeAt` preserves height consistency. -/
theorem heightConsistent_mkNodeAt (right : Bool) {a : α} {child sibling : AVLTree α}
    (hc : child.HeightConsistent) (hs : sibling.HeightConsistent) :
    (mkNodeAt right a child sibling).HeightConsistent := by
  cases right
  · exact heightConsistent_mkNode hc hs
  · exact heightConsistent_mkNode hs hc

/-- At a node whose child on a side is at least two taller than its sibling, `balance` promotes
that child, after first promoting its inner child when that one is the taller. -/
theorem balanceAt_heavy (right : Bool) (a k : α) (h : ℕ) (outer inner sibling : AVLTree α)
    (heavy : sibling.cachedHeight + 1 < h) :
    balanceAt right a (nodeSide right k h outer inner) sibling =
      if inner.cachedHeight ≤ outer.cachedHeight then
        rotateAt right a (nodeSide right k h outer inner) sibling
      else rotateAt right a (rotateAt (!right) k inner outer) sibling := by
  cases right
  · simp [balanceAt, nodeSide, rotateAt, balance, heavy]
  · have light : ¬h + 1 < sibling.cachedHeight := by omega
    simp [balanceAt, nodeSide, rotateAt, balance, heavy, light]

/-- At a node whose children differ in height by at most one, `balance` only recomputes the
height. -/
theorem balanceAt_balanced (right : Bool) (a : α) (child sibling : AVLTree α)
    (hc : ¬sibling.cachedHeight + 1 < child.cachedHeight)
    (hs : ¬child.cachedHeight + 1 < sibling.cachedHeight) :
    balanceAt right a child sibling = mkNodeAt right a child sibling := by
  cases right <;> simp [balanceAt, mkNodeAt, balance, hc, hs]

/-- Inserting on the side of the distinguished child inserts into that child and rebalances. -/
theorem insert_nodeSide [LinearOrder α] (right : Bool) (a : α) (h : ℕ)
    (child sibling : AVLTree α) (x : α) (side : if right then a < x else x < a) :
    insert x (nodeSide right a h child sibling) = balanceAt right a (insert x child) sibling := by
  cases right
  · have less : x < a := by simpa using side
    simp [nodeSide, insert, balanceAt, less]
  · have greater : a < x := by simpa using side
    simp [nodeSide, insert, balanceAt, greater, not_lt_of_gt greater]

end Cslib.DataStructure.AVLTree
