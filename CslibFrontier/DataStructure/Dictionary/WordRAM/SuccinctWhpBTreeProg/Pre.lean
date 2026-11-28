/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpSwarProg

/-!
# Shared Preconditions for SWAR Top-Down B+-Tree `Memory.Prog` Operations

Defines the parameter-free input/state preconditions `BTreeQueryGenPre` (for read/delete queries)
and `BTreeModGenPre` (for key-value update and proactive-split insertion).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.BTreeQueryGenPre`: shared precondition for
  `btreeLookupGenProg` and `btreeDeleteGenProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.BTreeModGenPre`: shared precondition for
  `btreeUpdateGenProg` and `btreeInsertGenProg`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctWhp

/-- Shared precondition for `btreeLookupGenProg` and `btreeDeleteGenProg`
(`d = (((cp, base), sIdx), q)`). -/
@[expose] def BTreeQueryGenPre (w : ℕ) :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, base), sIdx), q), s =>
    ∃ c U V w₀ n_max insCount sl mapFn,
      WhpLargeEnv c U V w₀ n_max w base ∧
      cp = mkWhpCoreParams c U V w₀ n_max ∧
      sIdx < 3 * numBucketsWhp n_max ∧
      insCount ≤ 8 * (slabScale n_max) ^ 12 ∧
      BTreeSliceMemRep base c U V w₀ n_max sIdx sl s.mem ∧
      ValidWhpSlice n_max insCount sl mapFn ∧
      q < 2 ^ fpBitsWhp n_max

/-- Precondition for `btreeUpdateGenProg` and `btreeInsertGenProg`
(`d = ((((cp, base), sIdx), q), val)`). -/
@[expose] def BTreeModGenPre (w : ℕ) :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | ((((cp, base), sIdx), q), val), s =>
    ∃ c U V w₀ n_max insCount sl mapFn,
      WhpLargeEnv c U V w₀ n_max w base ∧
      cp = mkWhpCoreParams c U V w₀ n_max ∧
      sIdx < 3 * numBucketsWhp n_max ∧
      insCount ≤ 8 * (slabScale n_max) ^ 12 ∧
      BTreeSliceMemRep base c U V w₀ n_max sIdx sl s.mem ∧
      ValidWhpSlice n_max insCount sl mapFn ∧
      q < 2 ^ fpBitsWhp n_max ∧
      val < 2 ^ valLaneBitsWhp n_max

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
