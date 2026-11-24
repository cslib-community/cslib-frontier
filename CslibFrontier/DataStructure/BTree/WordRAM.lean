/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BTree.WordRAM.Insert
public import CslibFrontier.DataStructure.BTree.WordRAM.Lookup
public import CslibFrontier.DataStructure.BTree.WordRAM.Rep

/-!
# Array-Allocated Word-RAM B-Tree (`O(t log_t n)` Lookup and Insertion)

Re-export facade for the concrete in-memory Word-RAM implementation of classic minimum-degree-`t`
B-trees (`t ≥ 2`) over `Cslib.WordRAM.Basis.standard` (`20` registers), backed by the flat arena
representation of `CslibFrontier.DataStructure.BTree.WordRAM.Arena` and following [CLRS2009],
Section 18.2:

* **Representation & Initialization (`WordRAM.Rep`):** caller-visible registers `Reg.rBase..rFound`,
  coupling invariant `Rep`, allocated-node counter `allocCount`, and `O(1)` initializer `initCode`
  (`initCode_spec`).
* **Lookup (`WordRAM.Lookup`):** walks a single root-to-leaf path without modifying memory,
  returning `(found, val)` matching `BTree.lookup k tr` in at most `(16 * t + 21) * tr.height + 16`
  (`O(t log_t n)`) Word-RAM instructions (`lookupCode`, `lookupProgram`, `lookupCode_spec`,
  `lookupCode_log_spec`, `lookupProgram_spec`).
* **Proactive top-down insertion (`WordRAM.Insert`):** splits a full `(2 * t - 1)`-key root and
  descends through non-full nodes, proactively splitting any full child before descending, realizing
  `Cslib.SortedAssoc.insert k v tr.toList` in `O(t log_t n)` Word-RAM instructions while preserving
  `BTree.IsWF t` and outside memory (`insertCode`, `insertProgram`, `insertCode_spec`,
  `insertCode_log_spec`, `insertProgram_spec`).

## Main definitions

* `Cslib.DataStructure.BTree.WordRAM.Reg.rBase`,
  `Cslib.DataStructure.BTree.WordRAM.Reg.rDeg`,
  `Cslib.DataStructure.BTree.WordRAM.Reg.rKey`,
  `Cslib.DataStructure.BTree.WordRAM.Reg.rVal`,
  `Cslib.DataStructure.BTree.WordRAM.Reg.rFound`: caller-visible Word-RAM interface registers.
* `Cslib.DataStructure.BTree.WordRAM.Rep` and `Cslib.DataStructure.BTree.WordRAM.allocCount`:
  coupling invariant and allocated-node count (`x.mem (base + 1)`) for a `20`-register Word-RAM
  state `x : Data 20` representing a well-formed `BTree ℕ ℕ` in
  `[base, base + arenaWords t capNodes)`.
* `Cslib.DataStructure.BTree.WordRAM.initCode`: `O(1)` empty-arena initializer over
  `Basis.standard`.
* `Cslib.DataStructure.BTree.WordRAM.lookupCode`,
  `Cslib.DataStructure.BTree.WordRAM.lookupProgram`: `O(t log_t n)` B-tree lookup code and
  compiled flat program over `Basis.standard`.
* `Cslib.DataStructure.BTree.WordRAM.insertCode`,
  `Cslib.DataStructure.BTree.WordRAM.insertProgram`: `O(t log_t n)` proactive top-down B-tree
  insertion code and compiled flat program over `Basis.standard`.

## Main results

* `Cslib.DataStructure.BTree.WordRAM.Rep.isWF`,
  `Cslib.DataStructure.BTree.WordRAM.Rep.height_le_log`,
  `Cslib.DataStructure.BTree.WordRAM.Rep.setKey`, and
  `Cslib.DataStructure.BTree.WordRAM.Rep.setKeyVal`: well-formedness, logarithmic height bound,
  and argument-register framing for `Rep`.
* `Cslib.DataStructure.BTree.WordRAM.initCode_spec`: `O(1)` Word-RAM initialization of `.leaf`.
* `Cslib.DataStructure.BTree.WordRAM.lookupCode_spec`,
  `Cslib.DataStructure.BTree.WordRAM.lookupCode_log_spec`, and
  `Cslib.DataStructure.BTree.WordRAM.lookupProgram_spec`: `O(t * tr.height)` and `O(t log_t n)`
  Word-RAM instruction bounds for `lookupCode` and halting flat `lookupProgram`.
* `Cslib.DataStructure.BTree.WordRAM.insertCode_spec`,
  `Cslib.DataStructure.BTree.WordRAM.insertCode_log_spec`, and
  `Cslib.DataStructure.BTree.WordRAM.insertProgram_spec`: `O(t * (tr.height + 1))` and
  `O(t log_t n)` Word-RAM instruction bounds, `Rep` preservation, `SortedAssoc.insert` correctness,
  node-allocation bound, and memory framing for `insertCode` and halting flat `insertProgram`.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 18.2][CLRS2009]
-/
