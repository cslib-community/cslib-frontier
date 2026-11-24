/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Init
import CslibFrontier.DataStructure.BTree.WordRAM
meta import CslibFrontier.DataStructure.BTree.WordRAM
import Mathlib.Tactic.FinCases

/-!
# Word-RAM B-Tree Tests and Non-Vacuity Witnesses

Kernel-checked examples (without `native_decide`) exercising `Cslib.DataStructure.BTree.WordRAM`:

1. Relocated arena initialization (`initCode.eval`) at `base = 4, capNodes = 12, t = 2, w = 12` on
   dirty initial memory (`3 ↦ 777`, garbage `999` inside `[4, 150)`, `150 ↦ 888`) and empty-tree
   miss lookup.
2. Concrete `insertCode.eval` sequence of 12 updates exercising `initSingleCode`, out-of-order leaf
   shift-insertions, proactive root splitting (`splitRootCode`), proactive internal full-child
   splitting (`splitChildCode`), and overwrites of both internal/promoted keys and leaf keys,
   followed by `lookupCode.eval` verification on all 9 present keys, 5 absent boundary/gap keys,
   instruction step bounds, and preservation of sentinels `3 ↦ 777` and `150 ↦ 888`.
3. End-to-end non-vacuity theorem chaining `initCode_spec`, `insertCode_log_spec`,
   `insertProgram_spec`, `lookupProgram_spec`, `Rep.setKey`, `Rep.setKeyVal`, `Rep.isWF`, and
   width/randomness independence predicates.
-/

set_option linter.privateModule false
set_option linter.hashCommand false

namespace CslibFrontierTests.BTreeWordRAM

open Cslib.WordRAM Cslib.DataStructure
open Cslib.DataStructure.BTree.WordRAM Cslib.DataStructure.BTree.WordRAM.Reg

/-! ## 1. Dirty relocated arena (`base = 4, capNodes = 12, t = 2, w = 12`) -/

/-- Initial machine state with `rBase = 4`, `rDeg = 2`, sentinel `777` at address `3` (`< base`),
non-zero garbage `999` throughout `[4, 150)`, and sentinel `888` at `150 = 4 + arenaWords 2 12`. -/
def rawData : Data 20 where
  regs i := if i = rBase then 4 else if i = rDeg then 2 else 0
  mem a :=
    if a = 3 then 777
    else if a = 150 then 888
    else if 4 ≤ a ∧ a < 150 then 999
    else 0

theorem bounded_rawData : rawData.Bounded 12 := by
  refine ⟨fun i => ?_, fun a => ?_⟩
  · fin_cases i <;> decide
  · simp only [rawData]
    split_ifs <;> decide

private def runInsertStep (st : Option (Data 20)) (kv : ℕ × ℕ) : Option (Data 20) :=
  match st with
  | none => none
  | some x =>
    let x' := (x.set rKey kv.1).set rVal kv.2
    (insertCode.eval 12 200 x').map Prod.fst

private def runLookup (x : Data 20) (k : ℕ) : Option (ℕ × ℕ × ℕ) :=
  match lookupCode.eval 12 200 (x.set rKey k) with
  | none => none
  | some (y, steps) => some (y.regs rFound, y.regs rVal, steps)

/-! ## 2. Concrete `Code.eval` checks across root split, child split, and overwrites -/

/-- Twelve updates at `t = 2`:
- `(20, 200)` (`initSingleCode`)
- `(10, 100), (30, 300)` (leaf shift-insertions filling root to `2 * t - 1 = 3` keys)
- `(40, 400)` (proactive `splitRootCode`, raising height to `2`)
- `(50, 500)` (fills right leaf to `3` keys)
- `(60, 600)` (proactive internal `splitChildCode` on full right child)
- `(35, 350), (15, 150), (5, 50)` (further multi-branch insertions)
- `(20, 2222), (40, 4444), (15, 1555)` (overwrites on internal and leaf keys). -/
def updateSeq : List (ℕ × ℕ) :=
  [(20, 200), (10, 100), (30, 300), (40, 400), (50, 500), (60, 600),
   (35, 350), (15, 150), (5, 50), (20, 2222), (40, 4444), (15, 1555)]

def initState? : Option (Data 20 × ℕ) := initCode.eval 12 20 rawData

def finalState? : Option (Data 20) :=
  updateSeq.foldl runInsertStep (initState?.map Prod.fst)

-- Empty initialized arena: 5 instructions, sentinels preserved, lookup misses in 8 steps.
#guard initState?.map Prod.snd == some 5
#guard (initState?.bind fun p => some (p.1.mem 3, p.1.mem 150)) == some (777, 888)
#guard (initState?.bind fun p => runLookup p.1 20) == some (0, 0, 8)

-- After all 12 updates (root split + internal child split + leaf/internal overwrites):
-- every present key returns `(1, v)` within `(16 * 2 + 21) * 2 + 16 = 122` steps, every absent
-- key returns `(0, 0)`, and dirty sentinels `3 ↦ 777` and `150 ↦ 888` are untouched.
#guard (finalState?.map fun y => (y.mem 3, y.mem 150, y.regs rBase, y.regs rDeg)) ==
  some (777, 888, 4, 2)
#guard [5, 10, 15, 20, 30, 35, 40, 50, 60].map
    (fun k => finalState?.bind (fun y => (runLookup y k).map fun r => (r.1, r.2.1))) ==
  [some (1, 50), some (1, 100), some (1, 1555), some (1, 2222), some (1, 300),
   some (1, 350), some (1, 4444), some (1, 500), some (1, 600)]
#guard [0, 12, 25, 45, 99].map
    (fun k => finalState?.bind (fun y => (runLookup y k).map fun r => (r.1, r.2.1))) ==
  [some (0, 0), some (0, 0), some (0, 0), some (0, 0), some (0, 0)]
#guard (finalState?.bind fun y => (runLookup y 35).map fun r => decide (r.2.2 ≤ 122)) ==
  some true

/-! ## 3. Non-vacuity theorem chaining `Rep`, `ExecWithin`, `lookupProgram_spec`, and
`insertProgram_spec` -/

example :
    ¬lookupProgram.ReadsWidth ∧
      lookupProgram.IsRandFree ∧
      ¬insertProgram.ReadsWidth ∧
      insertProgram.IsRandFree ∧
      ∃ y₀ y₁ tr₁ y₂ tr₂ t₂ y_hit steps_hit y_miss steps_miss y₃ tr₃ steps_ins,
        ExecWithin 12 initCode rawData y₀ 5 ∧
        Rep 4 12 2 12 .leaf y₀ ∧
        allocCount 4 y₀ = 0 ∧
        Rep 4 12 2 12 tr₁ y₁ ∧
        BTree.IsWF 2 tr₁ ∧
        tr₁.toList = [(20, 200)] ∧
        Runs 12 insertProgram ⟨0, (y₁.set rKey 10).set rVal 100⟩ ⟨insertCode.size, y₂⟩ t₂ ∧
        step 12 insertProgram ⟨insertCode.size, y₂⟩ = .halt 4 ∧
        Rep 4 12 2 12 tr₂ y₂ ∧
        tr₂.toList = [(10, 100), (20, 200)] ∧
        y₂.mem 3 = 777 ∧
        y₂.mem 150 = 888 ∧
        Runs 12 lookupProgram ⟨0, y₂.set rKey 10⟩ ⟨lookupCode.size, y_hit⟩ steps_hit ∧
        step 12 lookupProgram ⟨lookupCode.size, y_hit⟩ = .halt 100 ∧
        steps_hit + 1 ≤ (16 * 2 + 21) * (Nat.log 2 ((tr₂.size + 1) / 2) + 1) + 17 ∧
        y_hit.regs rFound = 1 ∧
        y_hit.mem = y₂.mem ∧
        Runs 12 lookupProgram ⟨0, y₂.set rKey 99⟩ ⟨lookupCode.size, y_miss⟩ steps_miss ∧
        step 12 lookupProgram ⟨lookupCode.size, y_miss⟩ = .halt 0 ∧
        y_miss.regs rFound = 0 ∧
        Runs 12 insertProgram ⟨0, (y₂.set rKey 30).set rVal 300⟩ ⟨insertCode.size, y₃⟩ steps_ins ∧
        step 12 insertProgram ⟨insertCode.size, y₃⟩ = .halt 4 ∧
        Rep 4 12 2 12 tr₃ y₃ ∧
        tr₃.toList = [(10, 100), (20, 200), (30, 300)] ∧
        y₃.mem 3 = 777 ∧
        y₃.mem 150 = 888 := by
  have ht : (2 : ℕ) ≤ 2 := by decide
  have hfit : Fits 12 (4 + arenaWords 2 12) := by decide
  obtain ⟨y₀, hinit, hrep₀, hcnt₀, hmod₀⟩ :=
    initCode_spec (base := 4) (t := 2) ht bounded_rawData rfl rfl hfit
  have hf_k20 : Fits 12 20 := by decide
  have hf_v200 : Fits 12 200 := by decide
  obtain ⟨y₁, tr₁, _, hrep₁, htl₁, hcnt₁, hmod₁⟩ :=
    insertCode_log_spec (hrep₀.setKeyVal hf_k20 hf_v200) (k := 20) (v := 200) rfl rfl
      (by simp only [allocCount_set, hcnt₀]; decide)
  simp only [allocCount_set, Data.set_mem, hcnt₀] at hcnt₁ hmod₁
  have htl₁_eq : tr₁.toList = [(20, 200)] := by rw [htl₁]; rfl
  have hh₁_le : tr₁.height ≤ 1 := by
    have hlog := hrep₁.height_le_log
    have hsize : tr₁.size = 1 := by simp only [BTree.size, htl₁_eq]; rfl
    rw [hsize] at hlog
    have : Nat.log 2 ((1 + 1) / 2) = 0 := by decide
    omega
  have hcnt₁_le : allocCount 4 y₁ ≤ 2 := by
    have : (BTree.leaf : BTree ℕ ℕ).height = 0 := rfl
    omega
  have hf_k10 : Fits 12 10 := by decide
  have hf_v100 : Fits 12 100 := by decide
  obtain ⟨y₂, tr₂, t₂, hruns₂, hhalt₂, _, hrep₂, htl₂, hcnt₂, hmod₂⟩ :=
    insertProgram_spec (hrep₁.setKeyVal hf_k10 hf_v100) (k := 10) (v := 100) rfl rfl
      (by simp only [allocCount_set]; omega)
  simp only [allocCount_set, Data.set_mem] at hcnt₂ hmod₂
  have htl₂_eq : tr₂.toList = [(10, 100), (20, 200)] := by rw [htl₂, htl₁_eq]; rfl
  have h3_not : (3 : ℕ) ∉ (Block.mk 4 (arenaWords 2 12)).footprint := by
    simp only [Block.mem_footprint, Block.Owns, arenaWords, nodeStride]; omega
  have h150_not : (150 : ℕ) ∉ (Block.mk 4 (arenaWords 2 12)).footprint := by
    simp only [Block.mem_footprint, Block.Owns, arenaWords, nodeStride]; omega
  have hm3 : y₂.mem 3 = 777 :=
    (hmod₂ 3 h3_not).trans ((hmod₁ 3 h3_not).trans (hmod₀ 3 h3_not))
  have hm150 : y₂.mem 150 = 888 :=
    (hmod₂ 150 h150_not).trans ((hmod₁ 150 h150_not).trans (hmod₀ 150 h150_not))
  obtain ⟨y_hit, steps_hit, hruns_hit, hhalt_hit, hle_hit, _, hmem_hit, hfnd_hit, _⟩ :=
    lookupProgram_spec (hrep₂.setKey hf_k10) (k := 10) rfl
  have hlk10 : BTree.lookup 10 tr₂ = some 100 := by
    rw [BTree.lookup_eq hrep₂.isWF 10, htl₂_eq]; rfl
  rw [hlk10] at hhalt_hit hfnd_hit
  have hf_k99 : Fits 12 99 := by decide
  obtain ⟨y_miss, steps_miss, hruns_miss, hhalt_miss, _, _, _, hfnd_miss, _⟩ :=
    lookupProgram_spec (hrep₂.setKey hf_k99) (k := 99) rfl
  have hlk99 : BTree.lookup 99 tr₂ = none := by
    rw [BTree.lookup_eq hrep₂.isWF 99, htl₂_eq]; rfl
  rw [hlk99] at hhalt_miss hfnd_miss
  have hh₂_le : tr₂.height ≤ 1 := by
    have hlog := hrep₂.height_le_log
    have hsize : tr₂.size = 2 := by simp only [BTree.size, htl₂_eq]; rfl
    rw [hsize] at hlog
    have : Nat.log 2 ((2 + 1) / 2) = 0 := by decide
    omega
  have hcnt₂_le : allocCount 4 y₂ ≤ 5 := by omega
  have hf_k30 : Fits 12 30 := by decide
  have hf_v300 : Fits 12 300 := by decide
  obtain ⟨y₃, tr₃, steps_ins, hruns_ins, hhalt_ins, _, hrep₃, htl₃, _, hmod₃⟩ :=
    insertProgram_spec (hrep₂.setKeyVal hf_k30 hf_v300) (k := 30) (v := 300) rfl rfl
      (by simp only [allocCount_set]; omega)
  simp only [Data.set_mem] at hmod₃
  have htl₃_eq : tr₃.toList = [(10, 100), (20, 200), (30, 300)] := by
    rw [htl₃, htl₂_eq]; rfl
  exact ⟨not_readsWidth_lookupProgram, isRandFree_lookupProgram,
    not_readsWidth_insertProgram, isRandFree_insertProgram,
    y₀, y₁, tr₁, y₂, tr₂, t₂, y_hit, steps_hit, y_miss, steps_miss, y₃, tr₃, steps_ins,
    hinit, hrep₀, hcnt₀, hrep₁, hrep₁.isWF, htl₁_eq, hruns₂, hhalt₂, hrep₂, htl₂_eq, hm3, hm150,
    hruns_hit, hhalt_hit, hle_hit, hfnd_hit, hmem_hit,
    hruns_miss, hhalt_miss, hfnd_miss,
    hruns_ins, hhalt_ins, hrep₃, htl₃_eq,
    (hmod₃ 3 h3_not).trans hm3, (hmod₃ 150 h150_not).trans hm150⟩

end CslibFrontierTests.BTreeWordRAM
