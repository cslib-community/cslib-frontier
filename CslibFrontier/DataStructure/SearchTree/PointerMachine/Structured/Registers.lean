/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.SymbolicExec
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Representation

/-!
# Names for the registers and fields of linked search trees

The structured programs on linked search trees name the registers and fields of
`SearchTree.PointerMachine.layout` instead of numbering them. The names are abbreviations of the
numbers and `simp` unfolds them, so statements about a program may use either. `open Register`
brings them into scope.

Scratch registers have a name for each role they play: pointer register two is `pivot` in a
rotation, `par` when it holds a parent and `kid` when it holds a child. A program should use
the name of the role.
-/

public section

namespace Cslib.DataStructure.SearchTree.PointerMachine.Register

variable {extra regs : ℕ}

/-- Pointer register zero: the cursor, and the result of a search or rotation. -/
@[simp, pm_simps] abbrev cur : Fin 7 := 0
/-- Pointer register one: the root of the tree. -/
@[simp, pm_simps] abbrev top : Fin 7 := 1
/-- Pointer register two: scratch; the promoted node of a rotation. -/
@[simp, pm_simps] abbrev pivot : Fin 7 := 2
/-- Pointer register two, holding a parent: of the cursor during a search, or of a new leaf. -/
@[simp, pm_simps] abbrev par : Fin 7 := 2
/-- Pointer register two, holding a child whose cached height is read. -/
@[simp, pm_simps] abbrev kid : Fin 7 := 2
/-- Pointer register three: scratch; the external parent in a rotation. -/
@[simp, pm_simps] abbrev up : Fin 7 := 3
/-- Pointer register three, holding the child that is too tall. -/
@[simp, pm_simps] abbrev tall : Fin 7 := 3
/-- Pointer register three, holding a child link of a parent, for comparison. -/
@[simp, pm_simps] abbrev link : Fin 7 := 3
/-- Pointer register four: scratch; the middle subtree of a rotation. -/
@[simp, pm_simps] abbrev mid : Fin 7 := 4
/-- Pointer register five: null, or where a search stops. -/
@[simp, pm_simps] abbrev stop : Fin 7 := 5
/-- Pointer register five, holding null. -/
@[simp, pm_simps] abbrev nul : Fin 7 := 5
/-- Pointer register six: the former root of a subtree that is being rebuilt. -/
@[simp, pm_simps] abbrev old : Fin 7 := 6
/-- Data register zero: the key searched for. -/
@[simp, pm_simps] abbrev query : Fin (regs + 2) := 0
/-- Data register one, holding the key of the node at the cursor. -/
@[simp, pm_simps] abbrev here : Fin (regs + 2) := 1
/-- Data register one, holding the cached height of a left child, or a new height. -/
@[simp, pm_simps] abbrev lh : Fin (regs + 3) := 1
/-- Data register two, holding the cached height of a right child. -/
@[simp, pm_simps] abbrev rh : Fin (regs + 3) := 2
/-- Data register two, holding the key of the parent of a new leaf. -/
@[simp, pm_simps] abbrev parentKey : Fin (regs + 3) := 2
/-- Pointer field zero: the left child. -/
@[simp, pm_simps] abbrev left : Fin 3 := 0
/-- Pointer field one: the right child. -/
@[simp, pm_simps] abbrev right : Fin 3 := 1
/-- Pointer field two: the parent. -/
@[simp, pm_simps] abbrev parent : Fin 3 := 2
/-- Data field zero: the key. -/
@[simp, pm_simps] abbrev key : Fin (extra + 1) := 0

end Cslib.DataStructure.SearchTree.PointerMachine.Register
