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
# Compact `BufRt` Descriptor, `BufEpFrame` Invariant, and `BufReadGenPre`

Public runtime parameter descriptor `BufRt`, segment offset accessors, constructor `mkBufRt`,
disjoint-buffer frame invariant `BufEpFrame` (`refl`, `trans`), and shared read/delete
admissibility predicate `BufReadGenPre`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.BufRt`, `mkBufRt`, `BufEpFrame`,
  `BufReadGenPre`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.BufEpFrame.refl`, `BufEpFrame.trans`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Cslib.DataStructure
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

/-- Compact 14-word scalar runtime parameter tuple for an epoch buffer trie `ep ∈ {0, 1}`. -/
abbrev BufRt : Type :=
  ((ℕ × ℕ) × (ℕ × ℕ)) × (((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))))


/-- Word offset of the child-pointer array in `BufRt`. -/
@[expose] def brOffChild (rt : BufRt) : ℕ := rt.2.2.1.2
/-- Word offset of the per-node metadata array in `BufRt`. -/
@[expose] def brOffMeta (rt : BufRt) : ℕ := rt.2.2.2.1.1
/-- Word offset of the item-log array in `BufRt`. -/
@[expose] def brOffItems (rt : BufRt) : ℕ := rt.2.2.2.1.2
/-- Header offset of `nodeAlloc` in `BufRt`. -/
@[expose] def brHdrNA (rt : BufRt) : ℕ := rt.2.2.2.2.1
/-- Header offset of `itemAlloc` in `BufRt`. -/
@[expose] def brHdrIA (rt : BufRt) : ℕ := rt.2.2.2.2.2

/-- Pure constructor for `BufRt`. -/
@[expose] def mkBufRt (c U V w n_max base ep : ℕ) : BufRt :=
  (((base, w), (globalPtrBits n_max, bCharWhp n_max)),
   (((2 ^ bCharWhp n_max, 2 ^ bCharWhp n_max - 1), (cTabWhp c, qEpochWhp n_max)),
    ((maxTrieNodesWhp c n_max,
      if ep = 0 then offTrieChild0 c U V w n_max else offTrieChild1 c U V w n_max),
     ((if ep = 0 then offTrieMeta0 c U V w n_max else offTrieMeta1 c U V w n_max,
       if ep = 0 then offTrieItems0 c U V w n_max else offTrieItems1 c U V w n_max),
      (if ep = 0 then hdrBuf0NodeAlloc else hdrBuf1NodeAlloc,
       if ep = 0 then hdrBuf0ItemAlloc else hdrBuf1ItemAlloc)))))


/-- Compositional frame invariant for writes confined to buffer `ep ∈ {0, 1}` (preserving all
non-buffer words, the opposite buffer `1 - ep`, and `dirtyBuckets` in `offTrieItems0`). -/
@[expose] def BufEpFrame (base c U V w n_max ep : ℕ) (mem₁ mem₂ : ℕ → ℕ) : Prop :=
  let rt := mkBufRt c U V w n_max base ep
  (∀ a,
    a ≠ base + brHdrNA rt →
    a ≠ base + brHdrIA rt →
    (a < base + brOffChild rt ∨
      base + brOffChild rt +
        packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w ≤ a) →
    (a < base + brOffMeta rt ∨
      base + brOffMeta rt +
        packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w ≤ a) →
    (a < base + brOffItems rt ∨
      base + brOffItems rt +
        packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w ≤ a) →
    mem₂ a = mem₁ a) ∧
  (∀ idx, 3 * qEpochWhp n_max ≤ idx → idx < 6 * qEpochWhp n_max + 6 →
    readPacked (base + offTrieItems0 c U V w n_max) (globalPtrBits n_max) w mem₂ idx =
      readPacked (base + offTrieItems0 c U V w n_max) (globalPtrBits n_max) w mem₁ idx)

theorem BufEpFrame.refl {base c U V w n_max ep : ℕ} (mem : ℕ → ℕ) :
    BufEpFrame base c U V w n_max ep mem mem :=
  ⟨fun _ _ _ _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem BufEpFrame.trans {base c U V w n_max ep : ℕ} {m₁ m₂ m₃ : ℕ → ℕ}
    (h₁₂ : BufEpFrame base c U V w n_max ep m₁ m₂)
    (h₂₃ : BufEpFrame base c U V w n_max ep m₂ m₃) :
    BufEpFrame base c U V w n_max ep m₁ m₃ :=
  ⟨fun a h1 h2 h3 h4 h5 => (h₂₃.1 a h1 h2 h3 h4 h5).trans (h₁₂.1 a h1 h2 h3 h4 h5),
   fun idx h1 h2 => (h₂₃.2 idx h1 h2).trans (h₁₂.2 idx h1 h2)⟩


/-- Shared read/delete admissibility precondition on `(((cp, base), ep), rKey)`. -/
@[expose] def BufReadGenPre (w : ℕ) :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, base), ep), _), s =>
    ∃ c U V w₀ n_max tr mapFn,
      WhpLargeEnv c U V w₀ n_max w base ∧
      cp = mkWhpCoreParams c U V w₀ n_max ∧
      (ep = 0 ∨ ep = 1) ∧
      BufTrieMemRep base c U V w₀ n_max ep tr s.mem ∧
      ValidBufTrie (cTabWhp c) (bCharWhp n_max) tr mapFn

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
