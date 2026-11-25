/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBufferTrieProg.Rt
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBufferTrieProg.Frame
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBufferTrieProg.EverPresent
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBufferTrieProg.Lookup
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBufferTrieProg.Delete
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBufferTrieProg.Insert
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBufferTrieProg.CheckSlot
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBufferTrieProg.Clear

/-!
# Certified `Memory.Prog` Implementation of the Bounded-Depth Character Trie Buffer (`BufTrie`)

This module re-exports the constant-depth character trie buffer runtime parameters, frame laws,
and parameter-free `Memory.Prog` operations across focused parallel submodules under
`SuccinctWhpBufferTrieProg`:

* `SuccinctWhpBufferTrieProg.Rt`, `SuccinctWhpBufferTrieProg.Frame`: `BufRt`, `mkBufRt`,
  `BufEpFrame`, `BufReadGenPre`, and external-segment/opposite-buffer preservation laws.
* `SuccinctWhpBufferTrieProg.EverPresent`, `Lookup`, `Delete`: read-only/delete buffer-trie
  operations (`bufEverPresentGenProg`, `bufLookupGenProg`, `bufDeleteGenProg`).
* `SuccinctWhpBufferTrieProg.Insert`: path-allocating `bufInsertGenProg`.
* `SuccinctWhpBufferTrieProg.CheckSlot`, `Clear`: active log validation (`bufCheckSlotGenProg`)
  and deamortized incremental reset (`bufClearStepsGenProg`).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.BufRt`, `mkBufRt`, `BufEpFrame`: compact
  runtime parameter tuple and disjoint-segment frame invariant for buffer `ep ∈ {0, 1}`.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bufLookupGenProg`,
  `bufEverPresentGenProg`, `bufDeleteGenProg`, `bufInsertGenProg`, `bufCheckSlotGenProg`,
  `bufClearStepsGenProg`: parameter-free `Memory.Prog` buffer-trie operations.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_bufLookupGen`,
  `realizes_bufEverPresentGen`, `realizes_bufDeleteGen`, `realizes_bufInsertGen`,
  `realizes_bufCheckSlotGen`, `realizes_bufClearStepsGen`: parameter-free `Realizes .exact`
  certificates.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bufLookupGenProg_spec`,
  `bufEverPresentGenProg_spec`, `bufDeleteGenProg_spec`, `bufInsertGenProg_spec`,
  `bufCheckSlotGenProg_spec`, `bufClearStepsGenProg_spec`: exact refinement, `O_c(1)` `memoryCost`
  bounds, `ValidProg`, `BufTrieMemRep` preservation, and `BufEpFrame` frame laws.
-/
