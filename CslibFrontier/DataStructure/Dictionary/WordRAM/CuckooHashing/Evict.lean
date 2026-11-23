/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.WordRAM.Heap
public import CslibFrontier.Computability.WordRAM.Randomized.Expected
public import CslibFrontier.DataStructure.Dictionary.Spec
public import CslibFrontier.DataStructure.Dictionary.WordRAM.CuckooHashing.HashFamily
import CslibFrontier.Computability.WordRAM.Randomized.SymbolicExec
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.MemFrame
import CslibFrontier.Computability.WordRAM.SymbolicExec.StructFrame
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.WramOmega

/-!
# Word-RAM Cuckoo Hashing: Memory Layout, Lookup, and Bounded Eviction

This module defines the contiguous Word-RAM memory layout, representation invariants, allocation and
initialization programs, deterministic two-probe lookup (`probeKeyCode`, `queryCode`), and bounded
two-table cuckoo displacement loop (`evictLoopCode`) for Pagh and Rodler's cuckoo hashing dictionary
[PaghRodler2004] backed by the regime-switched hash family from
`CslibFrontier.DataStructure.Dictionary.WordRAM.CuckooHashing.HashFamily` [Thorup2013].

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.space`,
  `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.spaceFactor`: Word-RAM memory footprint in
  words and its linear scale factor in `n_max + 1`.
* `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.RepWithKeys`,
  `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.Rep`: insertion-order-indexed and
  existentially quantified Word-RAM representation invariants.
* `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.allocSpan`,
  `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.initSetup`: bump-allocation span and
  randomized header/hash initialization subroutines.
* `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.probeKeyCode`,
  `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.queryCode`,
  `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.queryStepsBound`: deterministic two-table
  slot probing, dictionary lookup subroutine, and `O_{c_exp}(1)` lookup step bound.
* `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.evictLoopCode`: bounded two-table cuckoo
  displacement loop.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.space_le`: the total Word-RAM footprint is
  at most `spaceFactor c_exp * (n_max + 1)` words for every capacity `n_max : ℕ`.
* `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.Rep.unique`,
  `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.Rep.supported`: state uniqueness and
  memory-footprint framing for `Rep`.
* `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.queryCode_execWithin`,
  `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.querySteps_le`: deterministic worst-case
  two-probe lookup specification preserving `RepWithKeys` and the in-memory seed, with step count at
  most `queryStepsBound c_exp` under `U ≤ max n_max 4 ^ c_exp`.
* `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.evictLoopCode_execWithin`: deterministic
  execution specification relating `evictLoopCode` to `pureEvict` and `evictRounds`.

## References

* [R. Pagh and F. F. Rodler, "Cuckoo hashing"][PaghRodler2004] (8 December 2003 author manuscript,
  Section 2, pp. 3–10).
* [M. Thorup, "Simple Tabulation, Fast Expanders, Double Tabulation, and High
  Independence"][Thorup2013] (FOCS 2013, pp. 90–99; `arXiv:1311.3121v2`, pp. 4–5, 11–13).
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing

open Cslib.DataStructure.Dictionary.CuckooHashing
open Cslib.WordRAM
open Cslib.Probability
open Cslib.Probability.PMF
open Cslib.DataStructure.HashFamily.WordRAM
open scoped ENNReal

/-! ### Section 1: Memory layout, slot encoding, and representation invariants -/

/-- Base address of the hash pair region `[base + 20, t1Base base c_exp n_max)`. -/
@[expose, wram_arith]
def hashBase (base : ℕ) : ℕ :=
  base + 20

/-- Base address of the first cuckoo sub-table `T₁` of size `tableSize n_max`. -/
@[expose, wram_arith]
def t1Base (base c_exp n_max : ℕ) : ℕ :=
  hashBase base + hashPairSpace c_exp n_max

/-- Base address of the second cuckoo sub-table `T₂` of size `tableSize n_max`. -/
@[expose, wram_arith]
def t2Base (base c_exp n_max : ℕ) : ℕ :=
  t1Base base c_exp n_max + tableSize n_max

/-- Base address of the insertion-order key array `insKeys[0 .. n_max - 1]`. -/
@[expose, wram_arith]
def keysBase (base c_exp n_max : ℕ) : ℕ :=
  t2Base base c_exp n_max + tableSize n_max

/-- Base address of the insertion-order value array `insVals[0 .. n_max - 1]`. -/
@[expose, wram_arith]
def valsBase (base c_exp n_max : ℕ) : ℕ :=
  keysBase base c_exp n_max + n_max

/-- Total contiguous Word-RAM memory footprint `[base, base + space c_exp n_max)` in words. -/
@[expose, wram_arith]
def space (c_exp n_max : ℕ) : ℕ :=
  20 + hashPairSpace c_exp n_max + 2 * tableSize n_max + 2 * n_max

theorem le_space (c_exp n_max : ℕ) :
    77 ≤ space c_exp n_max := by
  have h1 := le_hashPairSpace c_exp n_max
  have h2 := four_le_tableSize n_max
  dsimp only [space]
  omega

/-- Constant factor `20 + hashPairSpaceFactor c_exp + 514` bounding `space c_exp n_max` by
`O_{c_exp}(n_max + 1)` across all `n_max : ℕ`. -/
@[expose]
def spaceFactor (c_exp : ℕ) : ℕ :=
  20 + hashPairSpaceFactor c_exp + 514

/-- Total memory footprint `space c_exp n_max` is `O_{c_exp}(n_max + 1)`: at most
`spaceFactor c_exp * (n_max + 1)` words for every `n_max : ℕ`. -/
theorem space_le (c_exp n_max : ℕ) :
    space c_exp n_max ≤ spaceFactor c_exp * (n_max + 1) := by
  have hhp := hashPairSpace_le c_exp n_max
  have hts := tableSize_le_sixtyFour_mul_max n_max
  have hmax : max n_max 4 ≤ 4 * (n_max + 1) := by omega
  dsimp only [space, spaceFactor]
  nlinarith

/-- Encode an optional `SlotEntry U` as a single machine word: `0` for `none` and `e.idx + 1` for
`some e`. -/
@[expose]
def encodeSlot {U : ℕ} : Option (SlotEntry U) → ℕ
  | none => 0
  | some e => e.idx + 1

@[simp]
theorem encodeSlot_none {U : ℕ} : encodeSlot (none : Option (SlotEntry U)) = 0 := rfl

@[simp]
theorem encodeSlot_some {U : ℕ} (e : SlotEntry U) : encodeSlot (some e) = e.idx + 1 := rfl

/-- Memory representation of the two cuckoo sub-tables `T₁` (at `t1Addr`) and `T₂` (at `t2Addr`).
-/
@[expose]
def TableSlotsRep {U M : ℕ} (t1Addr t2Addr : ℕ) (tbl : PureTable U (2 ^ M))
    (mem : ℕ → ℕ) : Prop :=
  (∀ b : Fin (2 ^ M), mem (t1Addr + b.val) = encodeSlot (tbl.t1 b)) ∧
  (∀ b : Fin (2 ^ M), mem (t2Addr + b.val) = encodeSlot (tbl.t2 b))

/-- Static header constants stored at `base + 0 .. 4` and `base + 6 .. 10`. -/
@[expose]
def HeaderConstsRep (base c_exp n_max U : ℕ) (mem : ℕ → ℕ) : Prop :=
  mem base = n_max ∧
  mem (base + 1) = U ∧
  mem (base + 2) = tableBits n_max ∧
  mem (base + 3) = tableSize n_max ∧
  mem (base + 4) = maxEvictions n_max ∧
  mem (base + 6) = hashBase base ∧
  mem (base + 7) = t1Base base c_exp n_max ∧
  mem (base + 8) = t2Base base c_exp n_max ∧
  mem (base + 9) = keysBase base c_exp n_max ∧
  mem (base + 10) = valsBase base c_exp n_max

/-- Representation of the insertion-order arrays `insKeys` and `insVals` at `keysBase` and
`valsBase` realizing abstract dictionary state `s : Dictionary.State U`. -/
@[expose]
def KeysValsRep (base c_exp n_max U V : ℕ) (ks : List (Fin U)) (s : Dictionary.State U)
    (mem : ℕ → ℕ) : Prop :=
  ks.Nodup ∧
  ks.length ≤ n_max ∧
  mem (base + 5) = ks.length ∧
  (∀ u : Fin U, u ∈ ks ↔ u ∈ Dictionary.dom s) ∧
  (∀ (idx : ℕ) (h : idx < ks.length),
    mem (keysBase base c_exp n_max + idx) = (ks[idx]).val ∧
    s (ks[idx]) = some (mem (valsBase base c_exp n_max + idx))) ∧
  Dictionary.ValuesBounded V s

private theorem KeysValsRep.toFinset_eq_dom {base c_exp n_max U V : ℕ} {ks : List (Fin U)}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (h : KeysValsRep base c_exp n_max U V ks s mem) :
    ks.toFinset = Dictionary.dom s := by
  ext u
  rw [List.mem_toFinset]
  exact h.2.2.2.1 u

theorem KeysValsRep.card_dom_eq {base c_exp n_max U V : ℕ} {ks : List (Fin U)}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (h : KeysValsRep base c_exp n_max U V ks s mem) :
    (Dictionary.dom s).card = ks.length := by
  rw [← h.toFinset_eq_dom, List.card_toFinset, List.dedup_eq_self.mpr h.1]

private theorem KeysValsRep.unique {base c_exp n_max U V : ℕ} {ks₁ ks₂ : List (Fin U)}
    {s₁ s₂ : Dictionary.State U} {mem : ℕ → ℕ}
    (h₁ : KeysValsRep base c_exp n_max U V ks₁ s₁ mem)
    (h₂ : KeysValsRep base c_exp n_max U V ks₂ s₂ mem) :
    s₁ = s₂ := by
  funext u
  have hlen : ks₁.length = ks₂.length := h₁.2.2.1.symm.trans h₂.2.2.1
  have hks_eq : ks₁ = ks₂ := by
    apply List.ext_getElem hlen
    intro idx hlt1 hlt2
    apply Fin.ext
    rw [← (h₁.2.2.2.2.1 idx hlt1).1, ← (h₂.2.2.2.2.1 idx hlt2).1]
  subst hks_eq
  by_cases hu : u ∈ ks₁
  · obtain ⟨idx, hlt, rfl⟩ := List.mem_iff_getElem.mp hu
    rw [(h₁.2.2.2.2.1 idx hlt).2, (h₂.2.2.2.2.1 idx hlt).2]
  · have hu1 : u ∉ Dictionary.dom s₁ := fun h => hu ((h₁.2.2.2.1 u).mpr h)
    have hu2 : u ∉ Dictionary.dom s₂ := fun h => hu ((h₂.2.2.2.1 u).mpr h)
    rw [Dictionary.notMem_dom_iff] at hu1 hu2
    rw [hu1, hu2]

/-- Insertion-order-indexed representation invariant `RepWithKeys w base c_exp n_max U V ks s x`
for cuckoo hashing: stores the static header, the hash pair `θ_mem = extractSeed ... x.mem`, the
insertion-order key-value arrays `ks` for `s`, and a valid table placement `tbl` obtained by
replaying `ks` under `θ_mem`. -/
@[expose]
def RepWithKeys (w base c_exp n_max U V : ℕ) (ks : List (Fin U))
    (s : Dictionary.State U) (x : Data 19) : Prop :=
  let M := tableBits n_max
  let θ_mem := extractSeed (hashBase base) c_exp n_max U M x.mem
  x.Bounded w ∧
  x.regs 0 = base ∧
  HeaderConstsRep base c_exp n_max U x.mem ∧
  HashPairRep (hashBase base) c_exp n_max U M θ_mem x.mem ∧
  KeysValsRep base c_exp n_max U V ks s x.mem ∧
  ∃ tbl : PureTable U (2 ^ M),
    pureReplay (evalHash1 θ_mem) (evalHash2 θ_mem)
      (maxEvictions n_max) ks = some tbl ∧
    TableSlotsRep (t1Base base c_exp n_max) (t2Base base c_exp n_max) tbl x.mem

/-- Representation invariant `Rep w base c_exp n_max U V s x` for cuckoo hashing. -/
@[expose]
def Rep (w base c_exp n_max U V : ℕ) (s : Dictionary.State U) (x : Data 19) : Prop :=
  ∃ ks : List (Fin U), RepWithKeys w base c_exp n_max U V ks s x

theorem RepWithKeys.toRep {w base c_exp n_max U V : ℕ} {ks : List (Fin U)}
    {s : Dictionary.State U} {x : Data 19}
    (hrep : RepWithKeys w base c_exp n_max U V ks s x) :
    Rep w base c_exp n_max U V s x :=
  ⟨ks, hrep⟩

theorem RepWithKeys.extractSeed_mem_survivingSeeds {w base c_exp n_max U V : ℕ}
    {ks : List (Fin U)} {s : Dictionary.State U} {x : Data 19}
    (hrep : RepWithKeys w base c_exp n_max U V ks s x) :
    extractSeed (hashBase base) c_exp n_max U (tableBits n_max) x.mem ∈
      survivingSeeds (Θ := Seed c_exp n_max U (tableBits n_max))
        evalHash1 evalHash2 (maxEvictions n_max) ks := by
  obtain ⟨-, -, -, -, -, tbl, hreplay, -⟩ := hrep
  rw [mem_survivingSeeds, hreplay]
  rfl

theorem Rep.bounded {w base c_exp n_max U V : ℕ} {s : Dictionary.State U} {x : Data 19}
    (h : Rep w base c_exp n_max U V s x) : x.Bounded w := by
  obtain ⟨_, hbdd, _⟩ := h
  exact hbdd

/-- A machine state `x` represents at most one abstract dictionary state `s`. -/
theorem Rep.unique {w base c_exp n_max U V : ℕ}
    {s₁ s₂ : Dictionary.State U} {x : Data 19}
    (h₁ : Rep w base c_exp n_max U V s₁ x) (h₂ : Rep w base c_exp n_max U V s₂ x) :
    s₁ = s₂ := by
  obtain ⟨ks₁, -, -, -, -, hkv₁, -, -, -⟩ := h₁
  obtain ⟨ks₂, -, -, -, -, hkv₂, -, -, -⟩ := h₂
  exact hkv₁.unique hkv₂

private theorem extractSeed_congr_of_block_footprint {base c_exp n_max U : ℕ} {mem mem' : ℕ → ℕ}
    (hmem : ∀ a ∈ (Block.mk base (space c_exp n_max)).footprint, mem' a = mem a) :
    extractSeed (hashBase base) c_exp n_max U (tableBits n_max) mem' =
      extractSeed (hashBase base) c_exp n_max U (tableBits n_max) mem :=
  extractSeed_congr_of_footprint fun a ha1 ha2 =>
    hmem a (by simp only [Block.mem_footprint, Block.Owns, hashBase, space] at *; omega)

theorem RepWithKeys.supported {w base c_exp n_max U V : ℕ} {ks : List (Fin U)}
    {s : Dictionary.State U} {x x' : Data 19}
    (hreg0 : x'.regs 0 = x.regs 0)
    (hmem : ∀ a ∈ (Block.mk base (space c_exp n_max)).footprint, x'.mem a = x.mem a)
    (hbdd : x'.Bounded w)
    (hrep : RepWithKeys w base c_exp n_max U V ks s x) :
    RepWithKeys w base c_exp n_max U V ks s x' := by
  obtain ⟨_, h0, hhdr, hhash, hkv, tbl, hreplay, hslots⟩ := hrep
  have hθ_eq : extractSeed (hashBase base) c_exp n_max U (tableBits n_max) x'.mem =
      extractSeed (hashBase base) c_exp n_max U (tableBits n_max) x.mem :=
    extractSeed_congr_of_block_footprint hmem
  have hle_sp := le_space c_exp n_max
  have hlen_le : ks.length ≤ n_max := hkv.2.1
  have hts : tableSize n_max = 2 ^ tableBits n_max := rfl
  exact ⟨hbdd, by regs_frame, by struct_frame hhdr,
    hθ_eq ▸ hhash.congr_of_footprint (by mem_frame),
    by struct_frame hkv, tbl, hθ_eq ▸ hreplay, by struct_frame hslots⟩

/-- `Rep` depends only on `reg 0` and the owned memory block `[base, base + space c_exp n_max)`. -/
theorem Rep.supported {w base c_exp n_max U V : ℕ}
    {s : Dictionary.State U} {x x' : Data 19}
    (hreg0 : x'.regs 0 = x.regs 0)
    (hmem : ∀ a ∈ (Block.mk base (space c_exp n_max)).footprint, x'.mem a = x.mem a)
    (hbdd : x'.Bounded w)
    (hrep : Rep w base c_exp n_max U V s x) :
    Rep w base c_exp n_max U V s x' := by
  obtain ⟨ks, hrep_ks⟩ := hrep
  exact ⟨ks, hrep_ks.supported hreg0 hmem hbdd⟩

/-! ### Section 2: `allocSpan` and `initSetup` programs and specifications -/

/-- Subprogram loading `(1, M, 2 ^ M, MaxLoop, hashPairSpace, space)` into registers
`(6, 8, 9, 10, 11, 13)` while preserving `reg 0 .. 4` and all memory. -/
private def computeScaleCode (c_exp n_max : ℕ) : Code .exact 19 :=
  .seq (.op (.const 6 1))
  (.seq (.op (.const 8 (tableBits n_max)))
  (.seq (.op (.const 9 (tableSize n_max)))
  (.seq (.op (.const 10 (maxEvictions n_max)))
  (.seq (.op (.const 11 (hashPairSpace c_exp n_max)))
        (.op (.const 13 (space c_exp n_max)))))))

private theorem computeScaleCode_execWithin {w c_exp n_max : ℕ} {x : Data 19}
    (hfit_sp : Fits w (space c_exp n_max))
    (hfit_ev : Fits w (maxEvictions n_max)) :
    ∃ y : Data 19,
      ExecWithin w (computeScaleCode c_exp n_max) x y 6 ∧
      y.mem = x.mem ∧
      (∀ r : Fin 19, r.val ≤ 4 → y.regs r = x.regs r) ∧
      y.regs 6 = 1 ∧
      y.regs 8 = tableBits n_max ∧
      y.regs 9 = tableSize n_max ∧
      y.regs 10 = maxEvictions n_max ∧
      y.regs 11 = hashPairSpace c_exp n_max ∧
      y.regs 13 = space c_exp n_max := by
  have hM_lt : tableBits n_max < tableSize n_max := Nat.lt_two_pow_self
  have hsp : space c_exp n_max =
      20 + hashPairSpace c_exp n_max + 2 * tableSize n_max + 2 * n_max := rfl
  unfold computeScaleCode
  wram_exec
  exact ⟨rfl, fun r hr => by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
    by wram_simp, by wram_simp⟩

/-- `allocSpan` program: sets `reg 0 = base` and advances `reg 1` (`frontierReg`) to
`base + space c_exp n_max`. -/
def allocSpan (c_exp n_max : ℕ) : Code .exact 19 :=
  .seq (.op (.copy 0 1))
  (.seq (computeScaleCode c_exp n_max)
        (.op (.exactBin .add 1 0 13)))

/-- Exact step bound for `allocSpan`. -/
@[expose]
def spanSteps : ℕ :=
  8

theorem allocSpan_execWithin {w base c_exp n_max U : ℕ} {x : Data 19}
    (hfr : x.regs 1 = base) (h3 : x.regs 3 = n_max) (h4 : x.regs 4 = U)
    (hfit_end : Fits w (base + space c_exp n_max))
    (hfit_ev : Fits w (maxEvictions n_max)) :
    ∃ x₁ : Data 19,
      ExecWithin w (allocSpan c_exp n_max) x x₁ spanSteps ∧
      x₁.mem = x.mem ∧
      x₁.regs 0 = base ∧
      x₁.regs 1 = base + space c_exp n_max ∧
      x₁.regs 3 = n_max ∧
      x₁.regs 4 = U := by
  have hfit_sp : Fits w (space c_exp n_max) := by fits
  unfold allocSpan spanSteps
  refine WP.exists_execWithin (WP.seq ?_)
  wram_exec [hfr]
  wram_call (computeScaleCode_execWithin (c_exp := c_exp) (n_max := n_max) hfit_sp hfit_ev)
    with d ⟨hd_mem, hd_low, -, -, -, -, -, hd_13⟩
  have hd_0 : d.regs 0 = base := by regs_frame
  wram_exec [hd_0, hd_13]
  exact ⟨hd_mem, by regs_frame, by wram_simp, by regs_frame, by regs_frame⟩

/-- Subprogram storing the static header constants `base + 0 .. 10`, saving `reg 1` (`frontierReg`)
at `base + 19`, and setting `(reg 0, reg 1, reg 2, reg 3) = (hashBase base, n_max, U, M)`. -/
private def writeHeaderAndAdvanceCode : Code .exact 19 :=
  .seq (.op (.store 0 3))
  (.seq (.op (.exactBin .add 12 0 6))
  (.seq (.op (.store 12 4))
  (.seq (.op (.exactBin .add 12 12 6))
  (.seq (.op (.store 12 8))
  (.seq (.op (.exactBin .add 12 12 6))
  (.seq (.op (.store 12 9))
  (.seq (.op (.exactBin .add 12 12 6))
  (.seq (.op (.store 12 10))
  (.seq (.op (.exactBin .add 12 12 6))
  (.seq (.op (.const 14 0))
  (.seq (.op (.store 12 14))
  (.seq (.op (.exactBin .add 12 12 6))
  (.seq (.op (.const 15 20))
  (.seq (.op (.exactBin .add 16 0 15))
  (.seq (.op (.store 12 16))
  (.seq (.op (.exactBin .add 12 12 6))
  (.seq (.op (.exactBin .add 17 16 11))
  (.seq (.op (.store 12 17))
  (.seq (.op (.exactBin .add 12 12 6))
  (.seq (.op (.exactBin .add 17 17 9))
  (.seq (.op (.store 12 17))
  (.seq (.op (.exactBin .add 12 12 6))
  (.seq (.op (.exactBin .add 17 17 9))
  (.seq (.op (.store 12 17))
  (.seq (.op (.exactBin .add 12 12 6))
  (.seq (.op (.exactBin .add 17 17 3))
  (.seq (.op (.store 12 17))
  (.seq (.op (.const 15 19))
  (.seq (.op (.exactBin .add 12 0 15))
  (.seq (.op (.store 12 1))
  (.seq (.op (.copy 0 16))
  (.seq (.op (.copy 1 3))
  (.seq (.op (.copy 2 4))
        (.op (.copy 3 8)))))))))))))))))))))))))))))))))))

private theorem writeHeaderAndAdvanceCode_exec {w base c_exp n_max U : ℕ} {x : Data 19}
    (h0 : x.regs 0 = base) (h1 : x.regs 1 = base + space c_exp n_max)
    (h3 : x.regs 3 = n_max) (h4 : x.regs 4 = U)
    (h6 : x.regs 6 = 1) (h8 : x.regs 8 = tableBits n_max)
    (h9 : x.regs 9 = tableSize n_max) (h10 : x.regs 10 = maxEvictions n_max)
    (h11 : x.regs 11 = hashPairSpace c_exp n_max)
    (hfit_end : Fits w (base + space c_exp n_max)) :
    ∃ y : Data 19,
      Exec w writeHeaderAndAdvanceCode x y 35 ∧
      y.regs 0 = hashBase base ∧
      y.regs 1 = n_max ∧
      y.regs 2 = U ∧
      y.regs 3 = tableBits n_max ∧
      HeaderConstsRep base c_exp n_max U y.mem ∧
      y.mem (base + 5) = 0 ∧
      y.mem (base + 19) = base + space c_exp n_max ∧
      (∀ a, (a < base ∨ base + 20 ≤ a) → y.mem a = x.mem a) := by
  have hle_sp := le_space c_exp n_max
  unfold writeHeaderAndAdvanceCode
  wram_exec [h0, h1, h3, h4, h6, h8, h9, h10, h11]
  refine ⟨by wram_simp [hashBase], by wram_simp, by wram_simp, by wram_simp, ?_, by wram_simp,
    by wram_simp, fun a ha => by mem_frame⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wram_simp <;> rfl

private def restoreAfterHashInitData (base c_exp n_max : ℕ) (d : Data 19) : Data 19 :=
  ((((d.set 15 20).set 0 base).set 15 19).set 1 (base + 19)).set 1 (base + space c_exp n_max)

private def restoreAfterHashInitCode : Code .exact 19 :=
  .seq (.op (.const 15 20))
  (.seq (.op (.exactBin .sub 0 0 15))
  (.seq (.op (.const 15 19))
  (.seq (.op (.exactBin .add 1 0 15))
        (.op (.load 1 1)))))

private theorem restoreAfterHashInitCode_exec {w base c_exp n_max : ℕ} {d : Data 19}
    (h0 : d.regs 0 = hashBase base)
    (hm19 : d.mem (base + 19) = base + space c_exp n_max)
    (hfit_end : Fits w (base + space c_exp n_max)) :
    Exec w restoreAfterHashInitCode d (restoreAfterHashInitData base c_exp n_max d) 5 := by
  have hle_sp := le_space c_exp n_max
  unfold restoreAfterHashInitCode restoreAfterHashInitData
  wram_exec [h0, hm19, hashBase, Nat.add_sub_cancel]

@[simp]
private theorem restoreAfterHashInitData_mem (base c_exp n_max : ℕ) (d : Data 19) :
    (restoreAfterHashInitData base c_exp n_max d).mem = d.mem := rfl

@[simp]
private theorem restoreAfterHashInitData_regs_zero (base c_exp n_max : ℕ) (d : Data 19) :
    (restoreAfterHashInitData base c_exp n_max d).regs 0 = base := by
  simp +decide [restoreAfterHashInitData]

@[simp]
private theorem restoreAfterHashInitData_regs_one (base c_exp n_max : ℕ) (d : Data 19) :
    (restoreAfterHashInitData base c_exp n_max d).regs 1 = base + space c_exp n_max := by
  simp +decide [restoreAfterHashInitData]

private def initSetupDetPrefix (c_exp n_max : ℕ) : Code .exact 19 :=
  .seq (computeScaleCode c_exp n_max)
  (.seq writeHeaderAndAdvanceCode
        (initTableHashPairCode c_exp n_max))

/-- Complete `initSetup` program for cuckoo hashing: populates the header, initializes the static
hash tables, samples the initial cuckoo hash pair `(h₁, h₂)`, and restores `base` and
`frontierReg`. -/
def initSetup (c_exp n_max : ℕ) : Code .exact 19 :=
  .seq (initSetupDetPrefix c_exp n_max)
  (.seq (resampleHashPairCode c_exp n_max (tableBits n_max))
        restoreAfterHashInitCode)

/-- Exact step bound for `initSetup`. -/
@[expose]
def setupSteps (c_exp n_max U : ℕ) : ℕ :=
  6 + 35 + initTableHashPairSteps c_exp n_max U (tableBits n_max) +
    resampleHashPairSteps c_exp n_max + 5

/-- Distributional execution specification for `resampleHashPairCode`. -/
private theorem resampleHashPairCode_execCodeDist {w hashBase c_exp n_max U M : ℕ} {x : Data 19}
    (htab : HashPairTableRep hashBase c_exp n_max U M x.mem)
    (h0 : x.regs 0 = hashBase)
    (hfit_end : Fits w (hashBase + hashPairSpace c_exp n_max))
    (hfit_q : Fits w (2 ^ Probability.trinomialDeg U M)) :
    let μ_res := (Prod.fst <$> resampleHashPairComp hashBase c_exp n_max U M x).eval
    ExecCodeDist w (resampleHashPairCode c_exp n_max M) x μ_res
      (resampleHashPairSteps c_exp n_max) ∧
    μ_res.map (fun y => extractSeed hashBase c_exp n_max U M y.mem) =
      seedLaw c_exp n_max U M ∧
    ∀ y ∈ μ_res.support,
      y.regs 0 = hashBase ∧
      HashPairRep hashBase c_exp n_max U M (extractSeed hashBase c_exp n_max U M y.mem) y.mem ∧
      (∀ a, (a < hashBase ∨ hashBase + hashPairSpace c_exp n_max ≤ a) → y.mem a = x.mem a) := by
  intro μ_res
  have hres := resampleHashPairCode_execRand (w := w) htab h0 hfit_end hfit_q
  refine ⟨?_, ?_, ?_⟩
  · refine (ExecCodeDist.of_execRand hres).mono ?_
    refine (ProbComp.expect_mono_on_support fun z hz => ?_).trans (ProbComp.expect_const _ _).le
    obtain ⟨ht, -, -, -⟩ := mem_support_resampleHashPairComp htab h0 hz
    exact_mod_cast ht
  · dsimp only [μ_res]
    rw [ProbComp.eval_map, PMF.map_comp]
    exact map_extractSeed_eval_resampleHashPairComp htab h0
  · intro y hy
    dsimp only [μ_res] at hy
    rw [ProbComp.eval_map, PMF.mem_support_map_iff] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [ProbComp.support_eval] at hz
    obtain ⟨-, hz_0, hz_hash, hz_frame⟩ := mem_support_resampleHashPairComp htab h0 hz
    exact ⟨hz_0, hz_hash, hz_frame⟩

/-- Couples a state distribution `μ : PMF (Data 19)` with its extracted in-memory seed. -/
noncomputable def coupleExtractedSeed (base c_exp n_max U : ℕ) (μ : PMF (Data 19)) :
    PMF (Seed c_exp n_max U (tableBits n_max) × Data 19) :=
  μ.map fun y => (extractSeed (hashBase base) c_exp n_max U (tableBits n_max) y.mem, y)

@[simp]
theorem map_snd_coupleExtractedSeed (base c_exp n_max U : ℕ) (μ : PMF (Data 19)) :
    (coupleExtractedSeed base c_exp n_max U μ).map Prod.snd = μ := by
  dsimp only [coupleExtractedSeed]
  rw [PMF.map_comp]
  exact PMF.map_id _

@[simp]
theorem map_fst_coupleExtractedSeed (base c_exp n_max U : ℕ) (μ : PMF (Data 19)) :
    (coupleExtractedSeed base c_exp n_max U μ).map Prod.fst =
      μ.map (fun y => extractSeed (hashBase base) c_exp n_max U (tableBits n_max) y.mem) := by
  dsimp only [coupleExtractedSeed]
  rw [PMF.map_comp]
  rfl

theorem mem_support_coupleExtractedSeed {base c_exp n_max U : ℕ} {μ : PMF (Data 19)}
    {p : Seed c_exp n_max U (tableBits n_max) × Data 19}
    (hp : p ∈ (coupleExtractedSeed base c_exp n_max U μ).support) :
    p.1 = extractSeed (hashBase base) c_exp n_max U (tableBits n_max) p.2.mem ∧
    p.2 ∈ μ.support := by
  dsimp only [coupleExtractedSeed] at hp
  rw [PMF.mem_support_map_iff] at hp
  obtain ⟨y, hy, rfl⟩ := hp
  exact ⟨rfl, hy⟩

/-- Coupled distributional specification for `initSetup`, directly returning the seed-coupled
initial distribution `ν₀`. -/
theorem initSetup_spec {w base c_exp n_max U V : ℕ} {x₁ : Data 19}
    (hx₁ : x₁.Bounded w)
    (hb : x₁.regs 0 = base)
    (hfr : x₁.regs 1 = base + space c_exp n_max)
    (h3 : x₁.regs 3 = n_max) (h4 : x₁.regs 4 = U)
    (hz : ∀ a ∈ (Block.mk base (space c_exp n_max)).footprint, x₁.mem a = 0)
    (hfit_ev : Fits w (maxEvictions n_max))
    (hfit_U : Fits w (max U 2 + 1))
    (hfit_q : Fits w (2 ^ Probability.trinomialDeg U (tableBits n_max))) :
    ∃ ν₀ : PMF (Seed c_exp n_max U (tableBits n_max) × Data 19),
      ExecCodeDist w (initSetup c_exp n_max) x₁ (ν₀.map Prod.snd) (setupSteps c_exp n_max U) ∧
      ν₀.map Prod.fst = seedLaw c_exp n_max U (tableBits n_max) ∧
      ∀ p ∈ ν₀.support,
        p.1 = extractSeed (hashBase base) c_exp n_max U (tableBits n_max) p.2.mem ∧
        p.2.regs 1 = base + space c_exp n_max ∧
        RepWithKeys w base c_exp n_max U V [] (Dictionary.empty U) p.2 ∧
        Modifies (Block.mk base (space c_exp n_max)).footprint x₁.mem p.2.mem := by
  have hfit_end : Fits w (base + space c_exp n_max) := by
    rw [← hfr]; exact hx₁.1 1
  have hfit_sp : Fits w (space c_exp n_max) := by fits
  have hle_sp := le_space c_exp n_max
  have hle_hp := le_hashPairSpace c_exp n_max
  have hts : tableSize n_max = 2 ^ tableBits n_max := rfl
  have h4le := four_mul_max_le_tableSize n_max
  have hfit_n : Fits w (max n_max 2) := hfit_sp.of_le (by wram_omega)
  have hfit_hp : Fits w (hashBase base + hashPairSpace c_exp n_max) := by wram_omega
  obtain ⟨d1, ⟨t_sc, ht_sc, he_sc⟩, hd1_mem, hd1_low, hd1_6, hd1_8, hd1_9, hd1_10,
      hd1_11, -⟩ :=
    computeScaleCode_execWithin (w := w) (c_exp := c_exp) (n_max := n_max) (x := x₁)
      hfit_sp hfit_ev
  obtain ⟨d2, he_wh, hd2_0, hd2_1, hd2_2, hd2_3, hd2_hdr, hd2_m5, hd2_m19, hd2_frame⟩ :=
    writeHeaderAndAdvanceCode_exec (w := w) (base := base) (c_exp := c_exp) (n_max := n_max)
      (U := U) (x := d1) (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame)
      hd1_6 hd1_8 hd1_9 hd1_10 hd1_11 hfit_end
  obtain ⟨d3, ⟨t_it, ht_it, he_it⟩, hd3_tab, hd3_0, hd3_frame⟩ :=
    initTableHashPairCode_execWithin (w := w) (hashBase := hashBase base) (c_exp := c_exp)
      (n_max := n_max) (U := U) (M := tableBits n_max) (x := d2)
      hd2_0 hd2_1 hd2_2 hd2_3 hfit_hp hfit_n hfit_U hfit_q
  have he_pref : Exec w (initSetupDetPrefix c_exp n_max) x₁ d3 (t_sc + (35 + t_it)) :=
    he_sc.seq (he_wh.seq he_it)
  obtain ⟨hres_dist, hres_law, hres_supp⟩ :=
    resampleHashPairCode_execCodeDist (w := w) hd3_tab hd3_0 hfit_hp hfit_q
  let μ_res : PMF (Data 19) :=
    (Prod.fst <$> resampleHashPairComp (hashBase base) c_exp n_max U (tableBits n_max) d3).eval
  have hout : ∀ z ∈ μ_res.support, ∀ a,
      (a < hashBase base ∨ hashBase base + hashPairSpace c_exp n_max ≤ a) →
      z.mem a = d2.mem a :=
    fun z hz a ha => ((hres_supp z hz).2.2 a ha).trans (hd3_frame a ha)
  have hrestore : ∀ z ∈ μ_res.support,
      ExecCodeDist w restoreAfterHashInitCode z
        (PMF.pure (restoreAfterHashInitData base c_exp n_max z)) 5 := fun z hz =>
    ExecCodeDist.of_exec (restoreAfterHashInitCode_exec (hres_supp z hz).1
      (by have := hout z hz; mem_frame) hfit_end)
  let μ_init : PMF (Data 19) := μ_res.map (restoreAfterHashInitData base c_exp n_max)
  have hfull_dist :
      ExecCodeDist w (initSetup c_exp n_max) x₁ μ_init (setupSteps c_exp n_max U) :=
    ((ExecCodeDist.of_exec he_pref).seq_pure
      ((hres_dist.seq_const hrestore (fun _ _ => le_rfl)).congr_dist rfl le_rfl)).mono
      (by exact_mod_cast (by dsimp only [setupSteps]; omega : t_sc + (35 + t_it) +
        (resampleHashPairSteps c_exp n_max + 5) ≤ setupSteps c_exp n_max U))
  refine ⟨coupleExtractedSeed base c_exp n_max U μ_init, ?_, ?_, fun p hp => ?_⟩
  · simpa only [map_snd_coupleExtractedSeed] using hfull_dist
  · rw [map_fst_coupleExtractedSeed]
    dsimp only [μ_init]
    rw [PMF.map_comp]
    exact hres_law
  · obtain ⟨hp1, hy⟩ := mem_support_coupleExtractedSeed hp
    rcases p with ⟨θ₀, y⟩
    have hy_bdd : y.Bounded w := hfull_dist.bounded hx₁ y hy
    dsimp only [μ_init] at hy
    rw [PMF.mem_support_map_iff] at hy
    obtain ⟨z₀, hz₀, rfl⟩ := hy
    have hz₀_out := hout z₀ hz₀
    have hrmem : (restoreAfterHashInitData base c_exp n_max z₀).mem = z₀.mem := rfl
    exact ⟨hp1, restoreAfterHashInitData_regs_one base c_exp n_max z₀,
      ⟨hy_bdd, restoreAfterHashInitData_regs_zero base c_exp n_max z₀,
        by struct_frame hd2_hdr, (hres_supp z₀ hz₀).2.1,
        ⟨List.nodup_nil, Nat.zero_le _, by mem_frame,
          fun u => by simp [Dictionary.dom_empty], fun _ h => by simp at h,
          Dictionary.valuesBounded_empty U V⟩,
        PureTable.empty U (2 ^ tableBits n_max), rfl,
        by mem_frame, by mem_frame⟩,
      by mem_frame⟩

/-! ### Section 3: Base-shifted hash wrappers, `probeKeyCode`, and `queryCode` -/

/-- Encode `Option ℕ` as a single machine word (`0` for `none` and `v + 1` for `some v`). -/
@[expose]
def encodeOptionNat : Option ℕ → ℕ
  | none => 0
  | some v => v + 1

/-- Decode a single machine word into `Option ℕ` (`0` as `none` and `v + 1` as `some v`). -/
@[expose]
def decodeOptionNat : ℕ → Option ℕ
  | 0 => none
  | v + 1 => some v

@[simp]
theorem decodeOptionNat_encodeOptionNat (o : Option ℕ) :
    decodeOptionNat (encodeOptionNat o) = o := by
  cases o <;> rfl

private def shiftToHashBaseCode : Code .exact 19 :=
  .seq (.op (.const 15 20))
       (.op (.exactBin .add 0 0 15))

private def unshiftFromHashBaseCode : Code .exact 19 :=
  .seq (.op (.const 15 20))
       (.op (.exactBin .sub 0 0 15))

/-- Evaluates `h₁(u)` (`second = false`) or `h₂(u)` (`second = true`) with `reg 0 = base` and
`reg 1 = u.val`, placing the bucket index in `reg 2` and restoring `reg 0 = base` without modifying
memory. -/
private def evalHashAtBaseCode (second : Bool) (c_exp n_max : ℕ) : Code .exact 19 :=
  .seq shiftToHashBaseCode
  (.seq (cond second (evalHash2Code c_exp n_max) (evalHash1Code c_exp n_max))
        unshiftFromHashBaseCode)

/-- Resamples `(h₁, h₂)` with `reg 0 = base` and restores `reg 0 = base`. -/
def resampleAtBaseCode (c_exp n_max : ℕ) : Code .exact 19 :=
  .seq shiftToHashBaseCode
  (.seq (resampleHashPairCode c_exp n_max (tableBits n_max))
        unshiftFromHashBaseCode)

private def evalHashAtBaseSteps (c_exp n_max U : ℕ) : ℕ :=
  evalHashSteps c_exp n_max U (tableBits n_max) + 4

/-- Step bound for `resampleAtBaseCode`. -/
@[expose]
def resampleAtBaseSteps (c_exp n_max : ℕ) : ℕ :=
  resampleHashPairSteps c_exp n_max + 4

private theorem evalHashAtBaseCode_execWithin (second : Bool) {w base c_exp n_max U : ℕ}
    {θ : Seed c_exp n_max U (tableBits n_max)} {u : Fin U} {x : Data 19}
    (hrep : HashPairRep (hashBase base) c_exp n_max U (tableBits n_max) θ x.mem)
    (h0 : x.regs 0 = base)
    (h1 : x.regs 1 = u.val)
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space c_exp n_max)) :
    ∃ y : Data 19,
      ExecWithin w (evalHashAtBaseCode second c_exp n_max) x y
        (evalHashAtBaseSteps c_exp n_max U) ∧
      y.regs 0 = base ∧
      y.regs 2 = (cond second (evalHash2 θ u) (evalHash1 θ u)).val ∧
      y.mem = x.mem := by
  have hle_sp := le_space c_exp n_max
  have hfit_hp : Fits w (hashBase base + hashPairSpace c_exp n_max) := by wram_omega
  set s1 := (x.set 15 20).set 0 (hashBase base)
  have hs1_eval : ∃ s2 : Data 19,
      ExecWithin w (cond second (evalHash2Code c_exp n_max) (evalHash1Code c_exp n_max))
        s1 s2 (evalHashSteps c_exp n_max U (tableBits n_max)) ∧
      s2.regs 0 = hashBase base ∧
      s2.regs 2 = (cond second (evalHash2 θ u) (evalHash1 θ u)).val ∧
      s2.mem = x.mem := by
    cases second
    · obtain ⟨s2, he, h0', -, h2', -, hm⟩ :=
        evalHash1Code_execWithin (x := s1) u hrep (by wram_simp [s1]) (by wram_simp [s1, h1])
          hw hfit_hp
      exact ⟨s2, he, h0', h2', hm⟩
    · obtain ⟨s2, he, h0', -, h2', -, hm⟩ :=
        evalHash2Code_execWithin (x := s1) u hrep (by wram_simp [s1]) (by wram_simp [s1, h1])
          hw hfit_hp
      exact ⟨s2, he, h0', h2', hm⟩
  unfold evalHashAtBaseCode evalHashAtBaseSteps shiftToHashBaseCode unshiftFromHashBaseCode
  wram_exec [h0, show base + 20 = hashBase base from rfl]
  wram_call hs1_eval with s2 ⟨hs2_0, hs2_2, hs2_mem⟩
  wram_exec [hs2_0, hashBase, Nat.add_sub_cancel]
  exact ⟨by wram_simp, by wram_simp [hs2_2], hs2_mem⟩

/-- Distributional execution specification for `resampleAtBaseCode`. -/
theorem resampleAtBaseCode_execCodeDist {w base c_exp n_max U : ℕ} {x : Data 19}
    (htab : HashPairTableRep (hashBase base) c_exp n_max U (tableBits n_max) x.mem)
    (h0 : x.regs 0 = base)
    (hfit_end : Fits w (base + space c_exp n_max))
    (hfit_q : Fits w (2 ^ Probability.trinomialDeg U (tableBits n_max))) :
    ∃ μ_res : PMF (Data 19),
      ExecCodeDist w (resampleAtBaseCode c_exp n_max) x μ_res (resampleAtBaseSteps c_exp n_max) ∧
      μ_res.map (fun y => extractSeed (hashBase base) c_exp n_max U (tableBits n_max) y.mem) =
        seedLaw c_exp n_max U (tableBits n_max) ∧
      ∀ y ∈ μ_res.support,
        y.regs 0 = base ∧
        HashPairRep (hashBase base) c_exp n_max U (tableBits n_max)
          (extractSeed (hashBase base) c_exp n_max U (tableBits n_max) y.mem) y.mem ∧
        (∀ a, (a < hashBase base ∨
          hashBase base + hashPairSpace c_exp n_max ≤ a) → y.mem a = x.mem a) := by
  have hle_sp := le_space c_exp n_max
  have hfit_hp : Fits w (hashBase base + hashPairSpace c_exp n_max) :=
    hfit_end.of_le (by dsimp only [hashBase, space]; omega)
  set s1 := (x.set 15 20).set 0 (hashBase base)
  obtain ⟨hres_dist, hres_law, hres_supp⟩ :=
    resampleHashPairCode_execCodeDist (w := w) (x := s1) htab (by wram_simp [s1]) hfit_hp hfit_q
  let unshiftFn : Data 19 → Data 19 := fun d => (d.set 15 20).set 0 base
  let μ_res : PMF (Data 19) :=
    (Prod.fst <$>
      resampleHashPairComp (hashBase base) c_exp n_max U (tableBits n_max) s1).eval.map unshiftFn
  refine ⟨μ_res, ?_, ?_, ?_⟩
  · unfold resampleAtBaseCode shiftToHashBaseCode unshiftFromHashBaseCode resampleAtBaseSteps
    wram_rand_exec [h0, show base + 20 = hashBase base from rfl]
    wram_rand_call hres_dist with z hz
    · wram_rand_exec [(hres_supp z hz).1, hashBase, Nat.add_sub_cancel]
    · exact ⟨by simp only [μ_res, unshiftFn, ← PMF.bind_pure_comp, Function.comp_def],
        by norm_cast; omega⟩
  · dsimp only [μ_res]
    rw [PMF.map_comp]
    exact hres_law
  · intro y hy
    dsimp only [μ_res] at hy
    rw [PMF.mem_support_map_iff] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨-, hz_hash, hz_frame⟩ := hres_supp z hz
    exact ⟨by wram_simp [unshiftFn], hz_hash, hz_frame⟩

/-- Helper subprogram that loads `mem[base + off]` into `reg dst` using `reg 15` as scratch. -/
@[expose]
def loadHeaderCode (dst : Fin 19) (off : ℕ) : Code .exact 19 :=
  .seq (.op (.const 15 off))
  (.seq (.op (.exactBin .add dst 0 15))
        (.op (.load dst dst)))

theorem loadHeaderCode_exec {w base off : ℕ} (dst : Fin 19) {x : Data 19}
    (h0 : x.regs 0 = base)
    (hfit_off : Fits w off)
    (hfit_addr : Fits w (base + off)) :
    Exec w (loadHeaderCode dst off) x
      (((x.set 15 off).set dst (base + off)).set dst (x.mem (base + off))) 3 := by
  unfold loadHeaderCode
  wram_exec [h0]

/-- Helper subprogram that stores `reg src` into `mem[base + off]` using `reg 15, 16` as scratch. -/
@[expose]
def storeHeaderCode (off : ℕ) (src : Fin 19) : Code .exact 19 :=
  .seq (.op (.const 15 off))
  (.seq (.op (.exactBin .add 16 0 15))
        (.op (.store 16 src)))

theorem storeHeaderCode_exec {w base off : ℕ} (src : Fin 19) {x : Data 19}
    (h0 : x.regs 0 = base)
    (hne15 : src ≠ 15) (hne16 : src ≠ 16)
    (hfit_off : Fits w off)
    (hfit_addr : Fits w (base + off)) :
    Exec w (storeHeaderCode off src) x
      (((x.set 15 off).set 16 (base + off)).write (base + off) (x.regs src)) 3 := by
  unfold storeHeaderCode
  wram_exec [h0]

/-- Helper subprogram that stores constant `val` into `mem[base + off]` using `reg 15, 16, 18` as
scratch. -/
@[expose]
def storeHeaderConstCode (off val : ℕ) : Code .exact 19 :=
  .seq (.op (.const 18 val))
       (storeHeaderCode off 18)

/-- Branches on `0 < mem[base + off]` using `reg 15, 16` as scratch. -/
@[expose]
def branchHeaderPosCode (off : ℕ) (posCode zeroCode : Code .exact 19) : Code .exact 19 :=
  .seq (loadHeaderCode 16 off)
  (.seq (.op (.const 15 0))
        (.branch (.lt 15 16) posCode zeroCode))

private def probeCheckOccupiedCode : Code .exact 19 :=
  .seq (.op (.const 15 1))
  (.seq (.op (.exactBin .sub 17 17 15))
  (.seq (loadHeaderCode 16 9)
  (.seq (.op (.exactBin .add 16 16 17))
  (.seq (.op (.load 16 16))
  (.seq (loadHeaderCode 18 11)
  (.branch (.eq 16 18)
    (.seq (storeHeaderConstCode 13 1)
          (storeHeaderCode 14 17))
    (.op (.const 15 0))))))))

/-- Probes sub-table `T₁` (`second = false`) or `T₂` (`second = true`) for the key `u` stored in
`mem[base + 11]`. If the probed slot holds `some e` with `e.key = u`, sets `mem[base + 13] = 1`
and `mem[base + 14] = e.idx`; otherwise leaves `mem[base + 13]` and `mem[base + 14]` unchanged. -/
private def probeTableSlotCode (second : Bool) (c_exp n_max : ℕ) : Code .exact 19 :=
  .seq (loadHeaderCode 1 11)
  (.seq (evalHashAtBaseCode second c_exp n_max)
  (.seq (loadHeaderCode 16 (cond second 8 7))
  (.seq (.op (.exactBin .add 16 16 2))
  (.seq (.op (.load 17 16))
  (.seq (.op (.const 15 0))
  (.branch (.lt 15 17)
    probeCheckOccupiedCode
    (.op (.const 15 0))))))))

private def probeTableSlotSteps (c_exp n_max U : ℕ) : ℕ :=
  evalHashAtBaseSteps c_exp n_max U + 31

private theorem probeCheckOccupiedCode_execWithin {w base c_exp n_max U : ℕ}
    {ks : List (Fin U)} {e : SlotEntry U} {u : Fin U} {x : Data 19}
    (h0 : x.regs 0 = base)
    (h17 : x.regs 17 = e.idx + 1)
    (hm9 : x.mem (base + 9) = keysBase base c_exp n_max)
    (hm11 : x.mem (base + 11) = u.val)
    (hidx_lt : e.idx < ks.length)
    (hlen_le : ks.length ≤ n_max)
    (hkey_idx : ks[e.idx]? = some e.key)
    (hmem_key : x.mem (keysBase base c_exp n_max + e.idx) = ks[e.idx].val)
    (hfit_end : Fits w (base + space c_exp n_max)) :
    ∃ y : Data 19,
      ExecWithin w probeCheckOccupiedCode x y 19 ∧
      y.regs 0 = base ∧
      y.mem (base + 13) = (if e.key = u then 1 else x.mem (base + 13)) ∧
      y.mem (base + 14) = (if e.key = u then e.idx else x.mem (base + 14)) ∧
      (∀ a, a ≠ base + 13 → a ≠ base + 14 → y.mem a = x.mem a) := by
  have hle_sp := le_space c_exp n_max
  have hks_eq : ks[e.idx] = e.key := by
    rw [List.getElem?_eq_getElem hidx_lt] at hkey_idx
    exact Option.some.inj hkey_idx
  unfold probeCheckOccupiedCode loadHeaderCode storeHeaderConstCode storeHeaderCode
  by_cases hku : e.key = u <;>
    wram_exec [h0, h17, hm9, hm11, hmem_key, hks_eq, hku, Fin.val_inj, Nat.add_sub_cancel] <;>
    exact ⟨by regs_frame, by wram_simp [hku], by wram_simp [hku], by mem_frame⟩

/-- Every entry in `tbl` comes from `ks` at its recorded index `e.idx`. -/
@[expose]
def TableIdxValid {U m : ℕ} (ks : List (Fin U)) (tbl : PureTable U m) : Prop :=
  ∀ e : SlotEntry U, EntryIn tbl e → e.idx < ks.length ∧ ks[e.idx]? = some e.key

theorem pureReplay_tableIdxValid {U m : ℕ} {h₁ h₂ : Fin U → Fin m} {maxLoop : ℕ}
    {ks : List (Fin U)} {tbl : PureTable U m} (hnodup : ks.Nodup)
    (hrep : pureReplay h₁ h₂ maxLoop ks = some tbl) :
    TableIdxValid ks tbl := by
  obtain ⟨_, hent⟩ := pureReplay_spec hnodup hrep
  intro e he
  rw [hent, List.mem_zipIdx_iff_getElem?] at he
  exact ⟨(List.getElem?_eq_some_iff.mp he).1, he⟩

private theorem probeTableSlotCode_execWithin (second : Bool) {w base c_exp n_max U : ℕ}
    {θ : Seed c_exp n_max U (tableBits n_max)} {ks : List (Fin U)}
    {tbl : PureTable U (2 ^ tableBits n_max)} {u : Fin U} {x : Data 19}
    (hhdr : HeaderConstsRep base c_exp n_max U x.mem)
    (hrep_hash : HashPairRep (hashBase base) c_exp n_max U (tableBits n_max) θ x.mem)
    (hslots : TableSlotsRep (t1Base base c_exp n_max) (t2Base base c_exp n_max) tbl x.mem)
    (htiv : TableIdxValid ks tbl)
    (hlen_le : ks.length ≤ n_max)
    (hmem_keys : ∀ idx (hlt : idx < ks.length),
      x.mem (keysBase base c_exp n_max + idx) = ks[idx].val)
    (h0 : x.regs 0 = base)
    (hm11 : x.mem (base + 11) = u.val)
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space c_exp n_max)) :
    let slotOpt := cond second (tbl.t2 (evalHash2 θ u)) (tbl.t1 (evalHash1 θ u))
    ∃ y : Data 19,
      ExecWithin w (probeTableSlotCode second c_exp n_max) x y
        (probeTableSlotSteps c_exp n_max U) ∧
      y.regs 0 = base ∧
      y.mem (base + 13) =
        (match slotOpt with
         | some e => if e.key = u then 1 else x.mem (base + 13)
         | none => x.mem (base + 13)) ∧
      y.mem (base + 14) =
        (match slotOpt with
         | some e => if e.key = u then e.idx else x.mem (base + 14)
         | none => x.mem (base + 14)) ∧
      (∀ a, a ≠ base + 13 → a ≠ base + 14 → y.mem a = x.mem a) := by
  intro slotOpt
  have ⟨_, _, _, _, _, _, hm7, hm8, hm9, _⟩ := hhdr
  have hle_sp := le_space c_exp n_max
  have hhp := le_hashPairSpace c_exp n_max
  have hts : tableSize n_max = 2 ^ tableBits n_max := rfl
  let tablePtrOff := cond second 8 7
  let tableBase := cond second (t2Base base c_exp n_max) (t1Base base c_exp n_max)
  let b := cond second (evalHash2 θ u) (evalHash1 θ u)
  have hb_lt := b.isLt
  have hoff_le : tablePtrOff ≤ 10 := by cases second <;> decide
  have hm_ptr : x.mem (base + tablePtrOff) = tableBase := by
    cases second <;> [exact hm7; exact hm8]
  have htb_hi : tableBase + 2 ^ tableBits n_max ≤ base + space c_exp n_max := by
    rw [← hts]
    cases second <;> dsimp only [tableBase, Bool.cond_false, Bool.cond_true] <;> wram_omega
  have hslot_mem : x.mem (tableBase + b.val) = encodeSlot slotOpt := by
    cases second <;> [exact hslots.1 _; exact hslots.2 _]
  have hslot_valid : ∀ e, slotOpt = some e → e.idx < ks.length ∧ ks[e.idx]? = some e.key := by
    intro e he
    cases second
    · exact htiv e (Or.inl ⟨evalHash1 θ u, he⟩)
    · exact htiv e (Or.inr ⟨evalHash2 θ u, he⟩)
  unfold probeTableSlotCode probeTableSlotSteps loadHeaderCode
  wram_exec [h0, hm11]
  wram_call (evalHashAtBaseCode_execWithin second (u := u) hrep_hash (by regs_frame) (by wram_simp)
      hw hfit_end)
    with s2 ⟨hs2_0, hs2_2, hs2_mem⟩
  have hs2_mem_x : s2.mem = x.mem := hs2_mem
  change s2.regs 2 = b.val at hs2_2
  wram_exec -split [hs2_0, hs2_2, (show s2.mem (base + cond second 8 7) = tableBase by
      rw [hs2_mem_x]; exact hm_ptr),
    (show s2.mem (tableBase + b.val) = encodeSlot slotOpt by rw [hs2_mem_x]; exact hslot_mem)]
  cases hslot_eq : slotOpt with
  | none =>
    wram_exec [encodeSlot_none]
    exact ⟨by regs_frame, congrFun hs2_mem_x _, congrFun hs2_mem_x _,
      fun a _ _ => congrFun hs2_mem_x a⟩
  | some e =>
    obtain ⟨hidx_lt, hkey_idx⟩ := hslot_valid e hslot_eq
    wram_exec [encodeSlot_some]
    wram_call (probeCheckOccupiedCode_execWithin (c_exp := c_exp) (e := e) (u := u)
      (by regs_frame) (by wram_simp [encodeSlot_some])
      (by dsimp only [Data.set]; rw [hs2_mem_x]; exact hm9)
      (by dsimp only [Data.set]; rw [hs2_mem_x]; exact hm11)
      hidx_lt hlen_le hkey_idx
      (by dsimp only [Data.set]; rw [hs2_mem_x]; exact hmem_keys _ hidx_lt) hfit_end)
      with s7 ⟨hs7_0, hs7_13, hs7_14, hs7_frame⟩
    dsimp only [Data.set] at hs7_13 hs7_14 hs7_frame
    rw [hs2_mem_x] at hs7_13 hs7_14
    exact ⟨by omega, hs7_0, hs7_13, hs7_14,
      fun a h13 h14 => (hs7_frame a h13 h14).trans (congrFun hs2_mem_x a)⟩

/-- Two-probe cuckoo lookup (`probeKeyCode`): probes `T₁[h₁(u)]`, and if `u` is not found in `T₁`,
probes `T₂[h₂(u)]`. Stores `foundFlag ∈ {0, 1}` in `mem[base + 13]` and `foundIdx` in
`mem[base + 14]`. -/
def probeKeyCode (c_exp n_max : ℕ) : Code .exact 19 :=
  .seq (storeHeaderConstCode 13 0)
  (.seq (probeTableSlotCode false c_exp n_max)
  (.seq (loadHeaderCode 16 13)
  (.seq (.op (.const 15 0))
  (.branch (.eq 16 15)
    (probeTableSlotCode true c_exp n_max)
    (.op (.const 15 0))))))

/-- Step bound for `probeKeyCode`. -/
def probeKeySteps (c_exp n_max U : ℕ) : ℕ :=
  2 * probeTableSlotSteps c_exp n_max U + 12

theorem probeKeyCode_execWithin {w base c_exp n_max U : ℕ}
    {θ : Seed c_exp n_max U (tableBits n_max)} {ks : List (Fin U)}
    {tbl : PureTable U (2 ^ tableBits n_max)} {u : Fin U} {x : Data 19}
    (hhdr : HeaderConstsRep base c_exp n_max U x.mem)
    (hrep_hash : HashPairRep (hashBase base) c_exp n_max U (tableBits n_max) θ x.mem)
    (hslots : TableSlotsRep (t1Base base c_exp n_max) (t2Base base c_exp n_max) tbl x.mem)
    (htiv : TableIdxValid ks tbl)
    (hlen_le : ks.length ≤ n_max)
    (hmem_keys : ∀ idx (hlt : idx < ks.length),
      x.mem (keysBase base c_exp n_max + idx) = ks[idx].val)
    (h0 : x.regs 0 = base)
    (hm11 : x.mem (base + 11) = u.val)
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space c_exp n_max)) :
    ∃ y : Data 19,
      ExecWithin w (probeKeyCode c_exp n_max) x y (probeKeySteps c_exp n_max U) ∧
      y.regs 0 = base ∧
      (match lookupEntry (evalHash1 θ) (evalHash2 θ) tbl u with
       | some e => y.mem (base + 13) = 1 ∧ y.mem (base + 14) = e.idx
       | none => y.mem (base + 13) = 0) ∧
      (∀ a, a ≠ base + 13 → a ≠ base + 14 → y.mem a = x.mem a) := by
  have hle_sp := le_space c_exp n_max
  have hhp := le_hashPairSpace c_exp n_max
  have hts : tableSize n_max = 2 ^ tableBits n_max := rfl
  unfold probeKeyCode probeKeySteps storeHeaderConstCode storeHeaderCode loadHeaderCode
  wram_exec [h0]
  refine WP.name fun s1 hs1 => ?_
  have hs1_13 : s1.mem (base + 13) = 0 := by mem_frame
  wram_call (probeTableSlotCode_execWithin false (θ := θ) (ks := ks) (tbl := tbl) (u := u)
      (by struct_frame hhdr) (hrep_hash.congr_of_ge_hashBase (by mem_frame))
      (by struct_frame hslots) htiv hlen_le (by mem_frame)
      (by regs_frame) (by mem_frame) hw hfit_end)
    with s2 ⟨hs2_0, hs2_13, hs2_14, hs2_frame⟩
  dsimp only [Bool.cond_false] at hs2_13 hs2_14
  rw [hs1_13] at hs2_13
  by_cases hfound1 : ∃ e₁, tbl.t1 (evalHash1 θ u) = some e₁ ∧ e₁.key = u
  · obtain ⟨e₁, ht1, hk1⟩ := hfound1
    simp only [ht1, hk1, ↓reduceIte] at hs2_13 hs2_14
    wram_exec [hs2_0, hs2_13]
    refine ⟨by regs_frame, ?_, by mem_frame⟩
    simp only [lookupEntry, ht1, hk1, ↓reduceIte]
    exact ⟨hs2_13, hs2_14⟩
  · have hs2_13_eq : s2.mem (base + 13) = 0 := by
      rw [hs2_13]
      cases ht1 : tbl.t1 (evalHash1 θ u) with
      | none => rfl
      | some e₁ => simp only [show e₁.key ≠ u from fun h => hfound1 ⟨e₁, ht1, h⟩, ↓reduceIte]
    wram_exec [hs2_0, hs2_13_eq]
    wram_call (probeTableSlotCode_execWithin true (θ := θ) (ks := ks) (tbl := tbl) (u := u)
        (by struct_frame hhdr) (hrep_hash.congr_of_ge_hashBase (by mem_frame))
        (by struct_frame hslots) htiv hlen_le (by mem_frame)
        (by regs_frame) (by mem_frame) hw hfit_end)
      with s5 ⟨hs5_0, hs5_13, hs5_14, hs5_frame⟩
    dsimp only [Bool.cond_true, Data.set] at hs5_13 hs5_14
    refine ⟨by omega, hs5_0, ?_, by mem_frame⟩
    have hlookup_eq : lookupEntry (evalHash1 θ) (evalHash2 θ) tbl u =
        (match tbl.t2 (evalHash2 θ u) with
         | some e₂ => if e₂.key = u then some e₂ else none
         | none => none) := by
      dsimp only [lookupEntry]
      cases ht1 : tbl.t1 (evalHash1 θ u) with
      | none => rfl
      | some e₁ =>
        simp only [show e₁.key ≠ u from fun h => hfound1 ⟨e₁, ht1, h⟩, ↓reduceIte]
        cases tbl.t2 (evalHash2 θ u) <;> rfl
    rw [hlookup_eq]
    cases ht2 : tbl.t2 (evalHash2 θ u) with
    | none =>
      rw [hs5_13, ht2]
      exact hs2_13_eq
    | some e₂ =>
      by_cases hk2 : e₂.key = u
      · simp only [hk2, ↓reduceIte, hs5_13, hs5_14, ht2, true_and]
      · simp only [hk2, ↓reduceIte, hs5_13, ht2]
        exact hs2_13_eq

private def queryFoundBranchCode : Code .exact 19 :=
  .seq (loadHeaderCode 17 14)
  (.seq (loadHeaderCode 16 10)
  (.seq (.op (.exactBin .add 16 16 17))
  (.seq (.op (.load 16 16))
  (.seq (.op (.const 15 1))
        (.op (.exactBin .add 2 16 15))))))

/-- Lookup operation (`queryCode`): stores `u.val` from `reg 3` into `mem[base + 11]`, runs
`probeKeyCode`, and writes `encodeOptionNat (s u)` into `reg 2`. -/
def queryCode (c_exp n_max : ℕ) : Code .exact 19 :=
  .seq (storeHeaderCode 11 3)
  (.seq (probeKeyCode c_exp n_max)
        (branchHeaderPosCode 13 queryFoundBranchCode (.op (.const 2 0))))

/-- Step bound for `queryCode`. -/
def querySteps (c_exp n_max U : ℕ) : ℕ :=
  probeKeySteps c_exp n_max U + 19

theorem queryCode_execWithin {w base c_exp n_max U V : ℕ}
    {ks : List (Fin U)} {s : Dictionary.State U}
    {u : Fin U} {x : Data 19}
    (hrep : RepWithKeys w base c_exp n_max U V ks s x)
    (h3 : x.regs 3 = u.val)
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space c_exp n_max))
    (hfit_V : Fits w V) :
    ∃ y : Data 19,
      ExecWithin w (queryCode c_exp n_max) x y (querySteps c_exp n_max U) ∧
      y.regs 2 = encodeOptionNat (s u) ∧
      RepWithKeys w base c_exp n_max U V ks s y ∧
      extractSeed (hashBase base) c_exp n_max U (tableBits n_max) y.mem =
        extractSeed (hashBase base) c_exp n_max U (tableBits n_max) x.mem ∧
      Modifies (Block.mk base (space c_exp n_max)).footprint x.mem y.mem := by
  obtain ⟨hx_bdd, h0, hhdr, hhash, hkv, tbl, hreplay, hslots⟩ := hrep
  obtain ⟨hnodup, hlen_le, hm5, hdom_iff, hkv_idx, hvb⟩ := id hkv
  have hle_sp := le_space c_exp n_max
  have hhp := le_hashPairSpace c_exp n_max
  have hts : tableSize n_max = 2 ^ tableBits n_max := rfl
  unfold queryCode querySteps branchHeaderPosCode queryFoundBranchCode storeHeaderCode
    loadHeaderCode
  refine WP.exists_execWithin (WP.bounded hx_bdd ?_)
  wram_exec [h0, h3]
  refine WP.name fun s1 hs1 => ?_
  wram_call (probeKeyCode_execWithin (ks := ks) (tbl := tbl) (u := u)
      (by struct_frame hhdr) (hhash.congr_of_ge_hashBase (by mem_frame)) (by struct_frame hslots)
      (pureReplay_tableIdxValid hnodup hreplay) hlen_le
      (fun idx hlt => by have := (hkv_idx idx hlt).1; mem_frame)
      (by regs_frame) (by mem_frame) hw hfit_end)
    with s2 ⟨hs2_0, hs2_lookup, hs2_frame⟩
  have hs2_mod : Modifies (Block.mk base (space c_exp n_max)).footprint x.mem s2.mem := by
    mem_frame
  have hs2_seed_x : extractSeed (hashBase base) c_exp n_max U (tableBits n_max) s2.mem =
      extractSeed (hashBase base) c_exp n_max U (tableBits n_max) x.mem :=
    extractSeed_congr_of_ge_hashBase (by mem_frame)
  have hs2_hdr : HeaderConstsRep base c_exp n_max U s2.mem := by struct_frame hhdr
  have hs2_kv : KeysValsRep base c_exp n_max U V ks s s2.mem := by struct_frame hkv
  have hrep2 : ∀ y : Data 19, y.Bounded w → y.regs 0 = base → y.mem = s2.mem →
      RepWithKeys w base c_exp n_max U V ks s y := fun y hb hy0 hym =>
    ⟨hb, hy0, hym ▸ hs2_hdr, hym ▸ hs2_seed_x ▸ hhash.congr_of_ge_hashBase (by mem_frame),
      hym ▸ hs2_kv, tbl, hym ▸ hs2_seed_x ▸ hreplay,
      hym ▸ (by struct_frame hslots : TableSlotsRep _ _ tbl s2.mem)⟩
  by_cases hmem : u ∈ ks
  · obtain ⟨idx, hlt, hks_idx⟩ := List.mem_iff_getElem.mp hmem
    have hlkp := pureReplay_lookupEntry_of_mem hnodup hreplay hlt
    rw [hks_idx] at hlkp
    rw [hlkp] at hs2_lookup
    have hsu : s u = some (s2.mem (valsBase base c_exp n_max + idx)) :=
      hks_idx ▸ (hs2_kv.2.2.2.2.1 idx hlt).2
    have hv_lt : s2.mem (valsBase base c_exp n_max + idx) < V := hvb u _ hsu
    wram_exec [hs2_0, hs2_lookup.1, hs2_lookup.2, hs2_hdr.2.2.2.2.2.2.2.2.2]
    exact fun hb => ⟨by omega, by wram_simp [hsu, encodeOptionNat],
      hrep2 _ hb (by regs_frame) rfl, hs2_seed_x, hs2_mod⟩
  · have hlkp := pureReplay_lookupEntry_of_notMem hnodup hreplay hmem
    rw [hlkp] at hs2_lookup
    have hsu : s u = none := by
      rw [← Dictionary.notMem_dom_iff]
      exact fun h => hmem ((hdom_iff u).mpr h)
    wram_exec [hs2_0, hs2_lookup]
    exact fun hb => ⟨by omega, by wram_simp [hsu, encodeOptionNat],
      hrep2 _ hb (by regs_frame) rfl, hs2_seed_x, hs2_mod⟩

/-! ### Section 4: Bounded cuckoo eviction loop (`putTableSlotCode`, `evictLoopCode`) -/

private theorem slotUpdate_valid {U m : ℕ} {ks : List (Fin U)}
    {slotFn : Fin m → Option (SlotEntry U)} {b₀ : Fin m} {e d : SlotEntry U}
    (horig : ∀ b, slotFn b = some d → d.idx < ks.length ∧ ks[d.idx]? = some d.key)
    (he : e.idx < ks.length ∧ ks[e.idx]? = some e.key) {b : Fin m}
    (hb : Function.update slotFn b₀ (some e) b = some d) :
    d.idx < ks.length ∧ ks[d.idx]? = some d.key := by
  by_cases hbb₀ : b = b₀
  · subst hbb₀
    rw [Function.update_self, Option.some.injEq] at hb
    exact hb ▸ he
  · rw [Function.update_of_ne hbb₀] at hb
    exact horig b hb

private theorem TableIdxValid.putSide (second : Bool) {U m : ℕ}
    {h₁ h₂ : Fin U → Fin m} {ks : List (Fin U)} {tbl : PureTable U m} {e : SlotEntry U}
    (htiv : TableIdxValid ks tbl) (he : e.idx < ks.length ∧ ks[e.idx]? = some e.key) :
    TableIdxValid ks (cond second (putT2 h₂ tbl e).1 (putT1 h₁ tbl e).1) := by
  cases second <;> rintro d (⟨b, hb⟩ | ⟨b, hb⟩)
  · exact slotUpdate_valid (fun b' hb' => htiv d (Or.inl ⟨b', hb'⟩)) he hb
  · exact htiv d (Or.inr ⟨b, hb⟩)
  · exact htiv d (Or.inl ⟨b, hb⟩)
  · exact slotUpdate_valid (fun b' hb' => htiv d (Or.inr ⟨b', hb'⟩)) he hb

private def putDisplacedBranchCode : Code .exact 19 :=
  .seq (.op (.const 15 1))
  (.seq (.op (.exactBin .sub 17 17 15))
  (.seq (storeHeaderCode 12 17)
  (.seq (loadHeaderCode 16 9)
  (.seq (.op (.exactBin .add 16 16 17))
  (.seq (.op (.load 17 16))
  (.seq (storeHeaderCode 11 17)
        (storeHeaderConstCode 16 1)))))))

private def putSlotSwapCode (second : Bool) (c_exp n_max : ℕ) : Code .exact 19 :=
  .seq (loadHeaderCode 1 11)
  (.seq (evalHashAtBaseCode second c_exp n_max)
  (.seq (loadHeaderCode 16 (cond second 8 7))
  (.seq (.op (.exactBin .add 16 16 2))
  (.seq (.op (.load 17 16))
  (.seq (loadHeaderCode 18 12)
  (.seq (.op (.const 15 1))
  (.seq (.op (.exactBin .add 18 18 15))
        (.op (.store 16 18)))))))))

private def putTableSlotCode (second : Bool) (c_exp n_max : ℕ) : Code .exact 19 :=
  .seq (putSlotSwapCode second c_exp n_max)
  (.seq (.op (.const 15 0))
  (.branch (.lt 15 17)
    putDisplacedBranchCode
    (storeHeaderConstCode 16 0)))

private def putTableSlotSteps (c_exp n_max U : ℕ) : ℕ :=
  evalHashAtBaseSteps c_exp n_max U + 35

private theorem putTableSlotCode_execWithin (second : Bool) {w base c_exp n_max U : ℕ}
    {θ : Seed c_exp n_max U (tableBits n_max)} {ks : List (Fin U)}
    {tbl : PureTable U (2 ^ tableBits n_max)} {e : SlotEntry U} {x : Data 19}
    (hhdr : HeaderConstsRep base c_exp n_max U x.mem)
    (hrep_hash : HashPairRep (hashBase base) c_exp n_max U (tableBits n_max) θ x.mem)
    (hslots : TableSlotsRep (t1Base base c_exp n_max) (t2Base base c_exp n_max) tbl x.mem)
    (htiv : TableIdxValid ks tbl)
    (he : e.idx < ks.length ∧ ks[e.idx]? = some e.key)
    (hlen_le : ks.length ≤ n_max)
    (hmem_keys : ∀ idx (hlt : idx < ks.length),
      x.mem (keysBase base c_exp n_max + idx) = ks[idx].val)
    (h0 : x.regs 0 = base)
    (hm11 : x.mem (base + 11) = e.key.val)
    (hm12 : x.mem (base + 12) = e.idx)
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space c_exp n_max)) :
    let res := cond second (putT2 (evalHash2 θ) tbl e) (putT1 (evalHash1 θ) tbl e)
    ∃ y : Data 19,
      ExecWithin w (putTableSlotCode second c_exp n_max) x y
        (putTableSlotSteps c_exp n_max U) ∧
      y.regs 0 = base ∧
      TableSlotsRep (t1Base base c_exp n_max) (t2Base base c_exp n_max) res.1 y.mem ∧
      TableIdxValid ks res.1 ∧
      (match res.2 with
       | none => y.mem (base + 16) = 0
       | some e_old =>
         y.mem (base + 16) = 1 ∧ y.mem (base + 11) = e_old.key.val ∧
           y.mem (base + 12) = e_old.idx ∧
           e_old.idx < ks.length ∧ ks[e_old.idx]? = some e_old.key) ∧
      (∀ a, a ≠ base + 11 → a ≠ base + 12 → a ≠ base + 16 →
        (a < t1Base base c_exp n_max ∨ keysBase base c_exp n_max ≤ a) → y.mem a = x.mem a) := by
  intro res
  have ⟨_, _, _, _, _, _, hm7, hm8, hm9, _⟩ := hhdr
  have hle_sp := le_space c_exp n_max
  have hle_hp := le_hashPairSpace c_exp n_max
  have hts : tableSize n_max = 2 ^ tableBits n_max := rfl
  have he_idx : e.idx < n_max := lt_of_lt_of_le he.1 hlen_le
  let tablePtrOff := cond second 8 7
  let tableBase := cond second (t2Base base c_exp n_max) (t1Base base c_exp n_max)
  let b₀ := cond second (evalHash2 θ e.key) (evalHash1 θ e.key)
  let slotFn := cond second tbl.t2 tbl.t1
  have hb_lt := b₀.isLt
  have hptr_lt : tablePtrOff < 20 := by cases second <;> decide
  have hm_ptr : x.mem (base + tablePtrOff) = tableBase := by
    cases second <;> [exact hm7; exact hm8]
  have htb_ge : t1Base base c_exp n_max ≤ tableBase := by
    cases second <;> dsimp only [tableBase, Bool.cond_false, Bool.cond_true] <;> wram_omega
  have htb_le : tableBase + 2 ^ tableBits n_max ≤ keysBase base c_exp n_max := by
    rw [← hts]
    cases second <;> dsimp only [tableBase, Bool.cond_false, Bool.cond_true] <;> wram_omega
  have hslots_side : ∀ b : Fin (2 ^ tableBits n_max),
      x.mem (tableBase + b.val) = encodeSlot (slotFn b) := by
    intro b; cases second <;> [exact hslots.1 b; exact hslots.2 b]
  have hvalid_slot : ∀ e_old, slotFn b₀ = some e_old →
      e_old.idx < ks.length ∧ ks[e_old.idx]? = some e_old.key := by
    intro e_old hold
    cases second
    · exact htiv e_old (Or.inl ⟨evalHash1 θ e.key, hold⟩)
    · exact htiv e_old (Or.inr ⟨evalHash2 θ e.key, hold⟩)
  have hne : ∀ b : Fin (2 ^ tableBits n_max), b ≠ b₀ →
      tableBase + b.val ≠ tableBase + b₀.val := fun b hb hbe => hb (Fin.ext (by omega))
  have hslots_post : ∀ (m : ℕ → ℕ),
      m (tableBase + b₀.val) = e.idx + 1 →
      (∀ a, a ≠ base + 11 → a ≠ base + 12 → a ≠ base + 16 →
        a ≠ tableBase + b₀.val → m a = x.mem a) →
      TableSlotsRep (t1Base base c_exp n_max) (t2Base base c_exp n_max) res.1 m := by
    intro m hm_self hm_other
    have hupd : ∀ b : Fin (2 ^ tableBits n_max),
        m (tableBase + b.val) = encodeSlot (Function.update slotFn b₀ (some e) b) := by
      intro b
      by_cases hb : b = b₀
      · subst hb; rw [Function.update_self, hm_self]; rfl
      · rw [Function.update_of_ne hb,
          hm_other _ (by wram_omega) (by wram_omega) (by wram_omega) (hne b hb)]
        exact hslots_side b
    have hother : ∀ b : Fin (2 ^ tableBits n_max),
        m (cond second (t1Base base c_exp n_max) (t2Base base c_exp n_max) + b.val) =
          encodeSlot (cond second tbl.t1 tbl.t2 b) := by
      intro b
      have hb_ts : b.val < tableSize n_max := by rw [hts]; exact b.isLt
      have hb0_ts : b₀.val < tableSize n_max := by rw [hts]; exact b₀.isLt
      rw [hm_other _ (by cases second <;> dsimp only [Bool.cond_false, Bool.cond_true] <;>
            wram_omega)
          (by cases second <;> dsimp only [Bool.cond_false, Bool.cond_true] <;> wram_omega)
          (by cases second <;> dsimp only [Bool.cond_false, Bool.cond_true] <;> wram_omega)
          (by cases second <;>
            dsimp only [tableBase, Bool.cond_false, Bool.cond_true] at * <;> wram_omega)]
      cases second <;> [exact hslots.2 b; exact hslots.1 b]
    cases second <;> [exact ⟨hupd, hother⟩; exact ⟨hother, hupd⟩]
  have hres_fst : res.1 = cond second (putT2 (evalHash2 θ) tbl e).1
      (putT1 (evalHash1 θ) tbl e).1 := by cases second <;> rfl
  have hres_snd : res.2 = slotFn b₀ := by cases second <;> rfl
  have htiv_res : TableIdxValid ks res.1 := hres_fst ▸ htiv.putSide second he
  unfold putTableSlotCode putTableSlotSteps putSlotSwapCode putDisplacedBranchCode
    storeHeaderConstCode storeHeaderCode loadHeaderCode
  wram_exec [h0, hm11]
  wram_call (evalHashAtBaseCode_execWithin second (u := e.key) hrep_hash (by regs_frame)
      (by wram_simp) hw hfit_end)
    with s2 ⟨hs2_0, hs2_2, hs2_mem⟩
  change s2.regs 2 = b₀.val at hs2_2
  rw [hres_snd]
  cases hold : slotFn b₀ with
  | none =>
    wram_exec [hs2_0, hs2_2,
      (show s2.mem (base + cond second 8 7) = tableBase by rw [hs2_mem]; exact hm_ptr),
      (show s2.mem (base + 12) = e.idx by rw [hs2_mem]; exact hm12),
      (show s2.mem (tableBase + b₀.val) = encodeSlot (slotFn b₀) by
        rw [hs2_mem]; exact hslots_side b₀),
      hold, encodeSlot_none]
    exact ⟨by regs_frame, hslots_post _ (by mem_frame) (by mem_frame), htiv_res,
      by mem_frame, by mem_frame⟩
  | some e_old =>
    obtain ⟨hidx_lt, hkey_idx⟩ := hvalid_slot e_old hold
    have hks_eq : ks[e_old.idx] = e_old.key := by
      rw [List.getElem?_eq_getElem hidx_lt] at hkey_idx
      exact Option.some.inj hkey_idx
    wram_exec [hs2_0, hs2_2,
      (show s2.mem (base + cond second 8 7) = tableBase by rw [hs2_mem]; exact hm_ptr),
      (show s2.mem (base + 12) = e.idx by rw [hs2_mem]; exact hm12),
      (show s2.mem (tableBase + b₀.val) = encodeSlot (slotFn b₀) by
        rw [hs2_mem]; exact hslots_side b₀),
      hold, encodeSlot_some,
      (show s2.mem (base + 9) = keysBase base c_exp n_max by rw [hs2_mem]; exact hm9),
      (show s2.mem (keysBase base c_exp n_max + e_old.idx) = ks[e_old.idx].val by
        rw [hs2_mem]; exact hmem_keys _ hidx_lt),
      hks_eq, Nat.add_sub_cancel]
    exact ⟨by regs_frame, hslots_post _ (by mem_frame) (by mem_frame), htiv_res,
      ⟨by mem_frame, by mem_frame, by mem_frame, hidx_lt, hkey_idx⟩, by mem_frame⟩

private def decHeader15Code : Code .exact 19 :=
  .seq (loadHeaderCode 17 15)
  (.seq (.op (.const 15 1))
  (.seq (.op (.exactBin .sub 17 17 15))
        (storeHeaderCode 15 17)))

private def evictRoundBodyCode (c_exp n_max : ℕ) : Code .exact 19 :=
  .seq (putTableSlotCode false c_exp n_max)
  (.seq (branchHeaderPosCode 16 (putTableSlotCode true c_exp n_max) (.op (.const 15 0)))
        decHeader15Code)

private def evictRoundSteps (c_exp n_max U : ℕ) : ℕ :=
  2 * putTableSlotSteps c_exp n_max U + 15

private theorem evictRoundBodyCode_execWithin {w base c_exp n_max U fuel : ℕ}
    {θ : Seed c_exp n_max U (tableBits n_max)} {ks : List (Fin U)}
    {tbl : PureTable U (2 ^ tableBits n_max)} {e : SlotEntry U} {x : Data 19}
    (hhdr : HeaderConstsRep base c_exp n_max U x.mem)
    (hrep_hash : HashPairRep (hashBase base) c_exp n_max U (tableBits n_max) θ x.mem)
    (hslots : TableSlotsRep (t1Base base c_exp n_max) (t2Base base c_exp n_max) tbl x.mem)
    (htiv : TableIdxValid ks tbl)
    (he : e.idx < ks.length ∧ ks[e.idx]? = some e.key)
    (hlen_le : ks.length ≤ n_max)
    (hmem_keys : ∀ idx (hlt : idx < ks.length),
      x.mem (keysBase base c_exp n_max + idx) = ks[idx].val)
    (h0 : x.regs 0 = base)
    (hm11 : x.mem (base + 11) = e.key.val)
    (hm12 : x.mem (base + 12) = e.idx)
    (hm15 : x.mem (base + 15) = fuel + 1)
    (hfit_fuel : Fits w fuel)
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space c_exp n_max)) :
    let res := pureEvictRound (evalHash1 θ) (evalHash2 θ) tbl e
    ∃ y : Data 19,
      ExecWithin w (evictRoundBodyCode c_exp n_max) x y (evictRoundSteps c_exp n_max U) ∧
      y.regs 0 = base ∧
      HeaderConstsRep base c_exp n_max U y.mem ∧
      HashPairRep (hashBase base) c_exp n_max U (tableBits n_max) θ y.mem ∧
      TableSlotsRep (t1Base base c_exp n_max) (t2Base base c_exp n_max) res.1 y.mem ∧
      TableIdxValid ks res.1 ∧
      y.mem (base + 15) = fuel ∧
      (match res.2 with
       | none => y.mem (base + 16) = 0
       | some e' =>
         y.mem (base + 16) = 1 ∧ y.mem (base + 11) = e'.key.val ∧ y.mem (base + 12) = e'.idx ∧
           e'.idx < ks.length ∧ ks[e'.idx]? = some e'.key) ∧
      (∀ a, a ≠ base + 11 → a ≠ base + 12 → a ≠ base + 15 → a ≠ base + 16 →
        (a < t1Base base c_exp n_max ∨ keysBase base c_exp n_max ≤ a) → y.mem a = x.mem a) := by
  intro res
  have hle_sp := le_space c_exp n_max
  have hle_hp := le_hashPairSpace c_exp n_max
  have hts : tableSize n_max = 2 ^ tableBits n_max := rfl
  unfold evictRoundBodyCode evictRoundSteps branchHeaderPosCode decHeader15Code
    storeHeaderCode loadHeaderCode
  refine WP.exists_execWithin (WP.seq ?_)
  wram_call (putTableSlotCode_execWithin false hhdr hrep_hash hslots htiv he hlen_le hmem_keys
      h0 hm11 hm12 hw hfit_end)
    with s1 ⟨hs1_0, hs1_slots, hs1_tiv, hs1_out, hs1_frame⟩
  dsimp only [Bool.cond_false] at hs1_slots hs1_tiv hs1_out
  rcases hput1 : putT1 (evalHash1 θ) tbl e with ⟨tbl₁, disp₁⟩
  rw [hput1] at hs1_slots hs1_tiv hs1_out
  cases disp₁ with
  | none =>
    have hres_eq : res = (tbl₁, none) := by
      dsimp only [res, pureEvictRound]
      rw [hput1]
    rw [hres_eq]
    wram_exec [hs1_0, hs1_out, Nat.add_sub_cancel,
      (by mem_frame : s1.mem (base + 15) = fuel + 1)]
    exact ⟨by regs_frame, by struct_frame hhdr, hrep_hash.congr_of_footprint (by mem_frame),
      by struct_frame hs1_slots, hs1_tiv, by mem_frame, by mem_frame, by mem_frame⟩
  | some e₁ =>
    have hres_eq : res = putT2 (evalHash2 θ) tbl₁ e₁ := by
      dsimp only [res, pureEvictRound]
      rw [hput1]
    rw [hres_eq]
    obtain ⟨hs1_16, hs1_11, hs1_12, he₁⟩ := hs1_out
    wram_exec [hs1_0, hs1_16]
    wram_call (putTableSlotCode_execWithin true (by struct_frame hhdr)
        (hrep_hash.congr_of_footprint (by mem_frame)) hs1_slots hs1_tiv he₁ hlen_le
        (by mem_frame) (by regs_frame) hs1_11 hs1_12 hw hfit_end)
      with s4 ⟨hs4_0, hs4_slots, hs4_tiv, hs4_out, hs4_frame⟩
    dsimp only [Bool.cond_true] at hs4_slots hs4_tiv hs4_out
    wram_exec [hs4_0, Nat.add_sub_cancel, (by mem_frame : s4.mem (base + 15) = fuel + 1)]
    refine ⟨by regs_frame, by struct_frame hhdr, hrep_hash.congr_of_footprint (by mem_frame),
      by struct_frame hs4_slots, hs4_tiv, by mem_frame, ?_, by mem_frame⟩
    cases hput2 : (putT2 (evalHash2 θ) tbl₁ e₁).2 with
    | none => rw [hput2] at hs4_out; mem_frame
    | some e₂ =>
      rw [hput2] at hs4_out
      exact ⟨by mem_frame, by mem_frame, by mem_frame, hs4_out.2.2.2.1, hs4_out.2.2.2.2⟩

private def syncEvictCondCode : Code .exact 19 :=
  .seq (loadHeaderCode 16 16)
  (.seq (loadHeaderCode 17 15)
  (.seq (.op (.exactBin .mul 17 16 17))
        (.op (.const 18 0))))

private theorem syncEvictCondCode_exec {w base c_exp n_max act fuel : ℕ} {x : Data 19}
    (h0 : x.regs 0 = base)
    (hm15 : x.mem (base + 15) = fuel)
    (hm16 : x.mem (base + 16) = act)
    (hact : act ≤ 1)
    (hfit_fuel : Fits w fuel)
    (hfit_end : Fits w (base + space c_exp n_max)) :
    ∃ y : Data 19,
      Exec w syncEvictCondCode x y 8 ∧
      y.regs 0 = base ∧
      y.regs 17 = act * fuel ∧
      y.regs 18 = 0 ∧
      y.mem = x.mem := by
  have hle_sp := le_space c_exp n_max
  have hfit_prod : Fits w (act * fuel) :=
    hfit_fuel.of_le ((Nat.mul_le_mul_right fuel hact).trans_eq (Nat.one_mul fuel))
  unfold syncEvictCondCode loadHeaderCode
  wram_exec [h0, hm15, hm16]
  exact ⟨by regs_frame, by wram_simp, by wram_simp, rfl⟩

private def evictLoopInner (c_exp n_max : ℕ) : Code .exact 19 :=
  .loop (.lt 18 17) (.seq (evictRoundBodyCode c_exp n_max) syncEvictCondCode)

/-- Bounded cuckoo eviction loop (`evictLoopCode`): executes up to `remFuel = mem[base + 15]`
displacement rounds starting from `(curKey = mem[base + 11], curIdx = mem[base + 12])` with
`activeFlag = mem[base + 16] = 1`. -/
def evictLoopCode (c_exp n_max : ℕ) : Code .exact 19 :=
  .seq syncEvictCondCode (evictLoopInner c_exp n_max)

/-- Step bound per displacement round in `evictLoopCode`. -/
def evictIterSteps (c_exp n_max U : ℕ) : ℕ :=
  evictRoundSteps c_exp n_max U + 10

private theorem evictLoopInner_execWithin {w base c_exp n_max U : ℕ}
    {θ : Seed c_exp n_max U (tableBits n_max)} {ks : List (Fin U)}
    (hlen_le : ks.length ≤ n_max)
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space c_exp n_max)) :
    ∀ (fuel : ℕ) {tbl : PureTable U (2 ^ tableBits n_max)} {e : SlotEntry U} {x : Data 19},
      HeaderConstsRep base c_exp n_max U x.mem →
      HashPairRep (hashBase base) c_exp n_max U (tableBits n_max) θ x.mem →
      TableSlotsRep (t1Base base c_exp n_max) (t2Base base c_exp n_max) tbl x.mem →
      TableIdxValid ks tbl →
      (e.idx < ks.length ∧ ks[e.idx]? = some e.key) →
      (∀ idx (hlt : idx < ks.length), x.mem (keysBase base c_exp n_max + idx) = ks[idx].val) →
      x.regs 0 = base →
      x.regs 17 = fuel →
      x.regs 18 = 0 →
      x.mem (base + 11) = e.key.val →
      x.mem (base + 12) = e.idx →
      x.mem (base + 15) = fuel →
      x.mem (base + 16) = 1 →
      Fits w fuel →
      ∃ y : Data 19,
        ExecWithin w (evictLoopInner c_exp n_max) x y
          (evictRounds (evalHash1 θ) (evalHash2 θ) fuel tbl e *
            evictIterSteps c_exp n_max U + 2) ∧
        y.regs 0 = base ∧
        HeaderConstsRep base c_exp n_max U y.mem ∧
        HashPairRep (hashBase base) c_exp n_max U (tableBits n_max) θ y.mem ∧
        (match pureEvict (evalHash1 θ) (evalHash2 θ) fuel tbl e with
         | some tbl' =>
           y.mem (base + 16) = 0 ∧
           TableSlotsRep (t1Base base c_exp n_max) (t2Base base c_exp n_max) tbl' y.mem ∧
           TableIdxValid ks tbl'
         | none =>
           y.mem (base + 16) = 1) ∧
        (∀ a, a ≠ base + 11 → a ≠ base + 12 → a ≠ base + 15 → a ≠ base + 16 →
          (a < t1Base base c_exp n_max ∨ keysBase base c_exp n_max ≤ a) → y.mem a = x.mem a)
  | 0, tbl, e, x, hhdr, hhash, _, _, _, _, h0, h17, h18, _, _, _, hm16, _ => by
    have hcond : ¬(Cond.lt 18 17 : Cond 19).Holds x := by
      simp [Cond.Holds, h17, h18]
    refine ⟨x, ⟨2, by simp [evictRounds], Exec.loop_exit hcond⟩,
      h0, hhdr, hhash, hm16, fun _ _ _ _ _ _ => rfl⟩
  | fuel + 1, tbl, e, x, hhdr, hhash, hslots, htiv, he, hmem_keys,
      h0, h17, h18, hm11, hm12, hm15, _, hfit_fuel1 => by
    have hcond : (Cond.lt 18 17 : Cond 19).Holds x := by
      simp [Cond.Holds, h17, h18]
    have hfit_fuel : Fits w fuel := by fits
    obtain ⟨s1, he_bd, hs1_0, hs1_hdr, hs1_hash, hs1_slots, hs1_tiv, hs1_15, hs1_res,
        hs1_frame⟩ :=
      evictRoundBodyCode_execWithin (fuel := fuel) hhdr hhash hslots htiv he hlen_le hmem_keys
        h0 hm11 hm12 hm15 hfit_fuel hw hfit_end
    unfold pureEvict evictRounds
    cases hround : pureEvictRound (evalHash1 θ) (evalHash2 θ) tbl e with
    | mk tbl' oe =>
      rw [hround] at hs1_slots hs1_tiv hs1_res
      cases oe with
      | none =>
        obtain ⟨s2, he_sync, hs2_0, hs2_17, hs2_18, hs2_mem⟩ :=
          syncEvictCondCode_exec (act := 0) (fuel := fuel) hs1_0 hs1_15 hs1_res
            (by decide) hfit_fuel hfit_end
        have hcond2 : ¬(Cond.lt 18 17 : Cond 19).Holds s2 := by
          simp [Cond.Holds, hs2_17, hs2_18]
        refine ⟨s2, ((he_bd.seq he_sync.within).loop_iter hcond
          (ExecWithin.loop_exit hcond2)).mono (by dsimp only [evictIterSteps]; omega), hs2_0, ?_⟩
        rw [hs2_mem]
        exact ⟨hs1_hdr, hs1_hash, ⟨hs1_res, hs1_slots, hs1_tiv⟩, hs1_frame⟩
      | some e' =>
        obtain ⟨hs1_16, hs1_11, hs1_12, he'⟩ := hs1_res
        obtain ⟨s2, he_sync, hs2_0, hs2_17, hs2_18, hs2_mem⟩ :=
          syncEvictCondCode_exec (act := 1) (fuel := fuel) hs1_0 hs1_15 hs1_16
            le_rfl hfit_fuel hfit_end
        rw [Nat.one_mul] at hs2_17
        rw [← hs2_mem] at hs1_hdr hs1_hash hs1_slots hs1_11 hs1_12 hs1_15 hs1_16 hs1_frame
        obtain ⟨y, he_rec, hy_0, hy_hdr, hy_hash, hy_res, hy_frame⟩ :=
          evictLoopInner_execWithin hlen_le hw hfit_end fuel hs1_hdr hs1_hash hs1_slots hs1_tiv
            he' (by mem_frame) hs2_0 hs2_17 hs2_18 hs1_11 hs1_12 hs1_15 hs1_16 hfit_fuel
        refine ⟨y, ((he_bd.seq he_sync.within).loop_iter hcond he_rec).mono ?_, hy_0, hy_hdr,
          hy_hash, hy_res, by mem_frame⟩
        change _ ≤ (1 + evictRounds (evalHash1 θ) (evalHash2 θ) fuel tbl' e') *
          evictIterSteps c_exp n_max U + 2
        rw [Nat.add_mul, Nat.one_mul]
        dsimp only [evictIterSteps]
        omega

/-- Deterministic execution specification for `evictLoopCode`, bounding steps in terms of
`evictRounds` and relating the post-state to `pureEvict`. -/
theorem evictLoopCode_execWithin {w base c_exp n_max U fuel : ℕ}
    {θ : Seed c_exp n_max U (tableBits n_max)} {ks : List (Fin U)}
    {tbl : PureTable U (2 ^ tableBits n_max)} {e : SlotEntry U} {x : Data 19}
    (hhdr : HeaderConstsRep base c_exp n_max U x.mem)
    (hrep_hash : HashPairRep (hashBase base) c_exp n_max U (tableBits n_max) θ x.mem)
    (hslots : TableSlotsRep (t1Base base c_exp n_max) (t2Base base c_exp n_max) tbl x.mem)
    (htiv : TableIdxValid ks tbl)
    (he : e.idx < ks.length ∧ ks[e.idx]? = some e.key)
    (hlen_le : ks.length ≤ n_max)
    (hmem_keys : ∀ idx (hlt : idx < ks.length),
      x.mem (keysBase base c_exp n_max + idx) = ks[idx].val)
    (h0 : x.regs 0 = base)
    (hm11 : x.mem (base + 11) = e.key.val)
    (hm12 : x.mem (base + 12) = e.idx)
    (hm15 : x.mem (base + 15) = fuel)
    (hm16 : x.mem (base + 16) = 1)
    (hfit_fuel : Fits w fuel)
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space c_exp n_max)) :
    ∃ y : Data 19,
      ExecWithin w (evictLoopCode c_exp n_max) x y
        (evictRounds (evalHash1 θ) (evalHash2 θ) fuel tbl e *
          evictIterSteps c_exp n_max U + 10) ∧
      y.regs 0 = base ∧
      HeaderConstsRep base c_exp n_max U y.mem ∧
      HashPairRep (hashBase base) c_exp n_max U (tableBits n_max) θ y.mem ∧
      (match pureEvict (evalHash1 θ) (evalHash2 θ) fuel tbl e with
       | some tbl' =>
         y.mem (base + 16) = 0 ∧
         TableSlotsRep (t1Base base c_exp n_max) (t2Base base c_exp n_max) tbl' y.mem ∧
         TableIdxValid ks tbl'
       | none =>
         y.mem (base + 16) = 1) ∧
      (∀ a, a ≠ base + 11 → a ≠ base + 12 → a ≠ base + 15 → a ≠ base + 16 →
        (a < t1Base base c_exp n_max ∨ keysBase base c_exp n_max ≤ a) → y.mem a = x.mem a) := by
  obtain ⟨s1, he_sync, hs1_0, hs1_17, hs1_18, hs1_mem⟩ :=
    syncEvictCondCode_exec (act := 1) (fuel := fuel) h0 hm15 hm16 le_rfl hfit_fuel hfit_end
  rw [Nat.one_mul] at hs1_17
  rw [← hs1_mem] at hhdr hrep_hash hslots hmem_keys hm11 hm12 hm15 hm16
  obtain ⟨y, he_in, hy_0, hy_hdr, hy_hash, hy_res, hy_frame⟩ :=
    evictLoopInner_execWithin hlen_le hw hfit_end fuel hhdr hrep_hash hslots htiv he hmem_keys
      hs1_0 hs1_17 hs1_18 hm11 hm12 hm15 hm16 hfit_fuel
  rw [hs1_mem] at hy_frame
  exact ⟨y, (he_sync.within.seq he_in).mono (by omega), hy_0, hy_hdr, hy_hash, hy_res, hy_frame⟩

/-! ### Step-bound inequalities for `probeKeyCode`, `queryCode`, and `evictLoopCode` -/

private theorem tableBits_le_clog (c_exp n_max : ℕ) :
    tableBits n_max ≤ max c_exp 1 * Nat.clog 2 (max n_max 4) + 5 := by
  have h1 := tableBits_le n_max
  have h2 : 1 * Nat.clog 2 (max n_max 4) ≤ max c_exp 1 * Nat.clog 2 (max n_max 4) :=
    Nat.mul_le_mul_right _ (le_max_right c_exp 1)
  omega

private theorem evalHashSteps_tableBits_le {c_exp n_max U : ℕ}
    (hU : U ≤ max n_max 4 ^ c_exp) :
    evalHashSteps c_exp n_max U (tableBits n_max) ≤ evalHashBound c_exp :=
  evalHashSteps_le hU (tableBits_le_clog c_exp n_max)

theorem probeKeySteps_le {c_exp n_max U : ℕ}
    (hU : U ≤ max n_max 4 ^ c_exp) :
    probeKeySteps c_exp n_max U ≤ 2 * (evalHashBound c_exp + 35) + 12 := by
  have hev := evalHashSteps_tableBits_le hU
  dsimp only [probeKeySteps, probeTableSlotSteps, evalHashAtBaseSteps]
  omega

/-- `O(c_exp⁴) = O_{c_exp}(1)` worst-case step bound for `queryCode c_exp n_max`, independent of
`n_max` and `U` whenever `U ≤ max n_max 4 ^ c_exp`. -/
@[expose]
def queryStepsBound (c_exp : ℕ) : ℕ :=
  2 * (evalHashBound c_exp + 36) + 31

theorem querySteps_le {c_exp n_max U : ℕ}
    (hU : U ≤ max n_max 4 ^ c_exp) :
    querySteps c_exp n_max U ≤ queryStepsBound c_exp := by
  have hp := probeKeySteps_le hU
  dsimp only [querySteps, queryStepsBound]
  omega

theorem evictIterSteps_le_add {c_exp n_max U : ℕ}
    (hU : U ≤ max n_max 4 ^ c_exp) :
    evictIterSteps c_exp n_max U ≤ 2 * (evalHashBound c_exp + 54) + 59 := by
  have hev := evalHashSteps_tableBits_le hU
  dsimp only [evictIterSteps, evictRoundSteps, putTableSlotSteps, evalHashAtBaseSteps]
  omega

end Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing
