/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBTreeProg.Pre
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBTreeProg.Lookup
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBTreeProg.Delete
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBTreeProg.Update
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBTreeProg.Insert

/-!
# Certified `Memory.Prog` Implementation of the SWAR Top-Down B+-Tree Query-Mapper

This module re-exports the bounded-depth SWAR top-down split-only B+-tree preconditions and
parameter-free `Memory.Prog` subroutines across focused parallel submodules under
`SuccinctWhpBTreeProg`:

* `SuccinctWhpBTreeProg.Pre`: shared `BTreeQueryGenPre` and `BTreeModGenPre` preconditions.
* `SuccinctWhpBTreeProg.Lookup`, `Delete`, `Update`: read-only lookup, lazy leaf deletion, and
  in-place value update (`btreeLookupGenProg`, `btreeDeleteGenProg`, `btreeUpdateGenProg`).
* `SuccinctWhpBTreeProg.Insert`: top-down proactive-split insertion (`btreeInsertGenProg`).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.BTreeQueryGenPre`, `BTreeModGenPre`:
  shared preconditions for read/delete and update/insert B+-tree operations.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.btreeLookupGenProg`,
  `btreeDeleteGenProg`, `btreeUpdateGenProg`, `btreeInsertGenProg`:
  parameter-free `Memory.Prog` implementations of all four SWAR B+-tree operations.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_btreeLookupGen`,
  `realizes_btreeDeleteGen`, `realizes_btreeUpdateGen`, `realizes_btreeInsertGen`:
  parameter-free `Realizes .exact` certificates.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.btreeLookupGenProg_spec`,
  `btreeDeleteGenProg_spec`, `btreeUpdateGenProg_spec`, `btreeInsertGenProg_spec`:
  exact refinement, `O(1)` `memoryCost` bounds, `ValidProg`, and slice/segment frame laws.
-/
