/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.Dynamic.Spec
public import CslibFrontier.DataStructure.Dictionary.WordRAM.BitPackedArray
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlotInv
public import CslibFrontier.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise
import Mathlib.Tactic.Ring
public import CslibFrontier.Tactic.WramOmega.Init

/-!
# Compacted Epoch Parameters and Dense Pair-Stream Packing

This module defines the 8-word persistent root header, the 225-word active epoch header, the
metadata-first compacted epoch layout, and the dense `[0, n)` `(quotient, value)` pair-stream
packing for the resizable succinct dynamic dictionary of [Bender, Farach-Colton, J. Kuszmaul and
W. Kuszmaul, SOSA 2024][BenderFarachColtonKuszmaulKuszmaul2024].

## Memory layout (`[metaBase, +offCompItems)` and `[itemBase, +compactedItemWords)`)

1. **Persistent 8-word root header (`[metaBase, metaBase + 8)`):**
   `[U - 1, V - 1, w, keyBits U, valBits V, N, n, n_init]` (storing `U - 1` and `V - 1` so
   `V = 2 ^ w` fits in a `w`-bit word). When `n = 0` (`N = 0`), the resting dictionary occupies
   only these `8` words (`compactedEpochWords U V w 0 0 = 8`).
2. **Active epoch parameter and hash-scratch header (`[metaBase + 8, metaBase + 225)`):**
   * `[metaBase + 8, metaBase + 27)`: 19 words of `RuntimeReducedKWise.HashParams`.
   * `[metaBase + 27, metaBase + 63)`: 36 words of `CompParams`.
   * `[metaBase + 63, metaBase + 225)`: 162-word limb scratch (`RuntimeReducedKWise.scratchWords`).
3. **Epoch metadata prefix (`[metaBase + 225, metaBase + offCompItems U w N)`):**
   `Hash` (`Succinct.hashSpace U w N`), `LocalMeta` (`9 * Succinct.lmSubWords N w`), `GlobalMeta`,
   `TailToDense`, and `DenseToTail`.
4. **Dense `[0, n)` item stream (`[itemBase, itemBase + compactedItemWords U V w N n)`):**
   `n` active `(quotient, value)` pairs packed densely at global bit offsets
   `d * (quotientBits U N + valBits V)` and `d * (quotientBits U N + valBits V) + quotientBits U N`.
   Parameterizing `itemBase` separately from `metaBase` allows both resting in-epoch states
   (`itemBase = metaBase + offCompItems U w N`) and single-tape epoch migration (Zone 1 metadata +
   Zone 3 shared item arena) to share the exact same `Memory.Prog` operations.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.rootHdrWords`, `RootHeaderValid`,
  `EpochValid`, `targetCap`: root header and epoch capacity invariants.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.wOffQ`, `bOffQ`, `wOffV`, `bOffV`,
  `compactedItemWords`, `compQuotAt`, `compValAt`, `writeCompQuot`, `writeCompVal`: overflow-free
  dense `[0, n)` pair-stream packing.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.epochHdrWords`, `offCompLM`,
  `offCompLMSub`, `offCompGM`, `offTailToDense`, `offDenseToTail`, `offCompItems`,
  `compactedEpochWords`: compacted epoch word offsets and total footprint.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompParams`, `mkCompParams`,
  `EpochParamsStored`: 36-word runtime parameter block and header storage predicate.

## Main results

* `compactedItemWords_succ_sub_le_two`: adding one item grows `compactedItemWords` by `≤ 2` words.
* `quotientBits_le_add_six_of_le_four_mul`, `succinctWords_mul_w_le_bits`: quotient-bit and
  word-to-bit space conversion helpers.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–4][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.HashFamily.WordRAM

/-! ## Section 1: Dense `[0, n)` Pair-Stream Bit Packing -/

/-- Overflow-free word offset of the quotient field `q_d` at dense index `d` in a stream of
`(q_bits, v_bits)` pairs on a `w`-bit machine. -/
@[expose] def wOffQ (q_bits v_bits w d : ℕ) : ℕ :=
  wordOffset q_bits w d + wordOffset v_bits w d +
    (bitOffset q_bits w d + bitOffset v_bits w d) / w

/-- Intra-word bit offset `< w` of the quotient field `q_d` at dense index `d`. -/
@[expose] def bOffQ (q_bits v_bits w d : ℕ) : ℕ :=
  (bitOffset q_bits w d + bitOffset v_bits w d) % w

/-- Overflow-free word offset of the value field `v_d` at dense index `d`. -/
@[expose] def wOffV (q_bits v_bits w d : ℕ) : ℕ :=
  wOffQ q_bits v_bits w d + (bOffQ q_bits v_bits w d + q_bits) / w

/-- Intra-word bit offset `< w` of the value field `v_d` at dense index `d`. -/
@[expose] def bOffV (q_bits v_bits w d : ℕ) : ℕ :=
  (bOffQ q_bits v_bits w d + q_bits) % w

theorem bOffQ_lt {q_bits v_bits w d : ℕ} (hw : 0 < w) : bOffQ q_bits v_bits w d < w :=
  Nat.mod_lt _ hw

theorem bOffV_lt {q_bits v_bits w d : ℕ} (hw : 0 < w) : bOffV q_bits v_bits w d < w :=
  Nat.mod_lt _ hw

/-- Exact global bit-offset identity `wOffQ * w + bOffQ = d * (q_bits + v_bits)`. -/
theorem wOffQ_mul_add_bOffQ {q_bits v_bits w d : ℕ} :
    wOffQ q_bits v_bits w d * w + bOffQ q_bits v_bits w d = d * (q_bits + v_bits) := by
  unfold wOffQ bOffQ
  calc (wordOffset q_bits w d + wordOffset v_bits w d +
          (bitOffset q_bits w d + bitOffset v_bits w d) / w) * w +
        (bitOffset q_bits w d + bitOffset v_bits w d) % w
      = wordOffset q_bits w d * w + wordOffset v_bits w d * w +
          (w * ((bitOffset q_bits w d + bitOffset v_bits w d) / w) +
            (bitOffset q_bits w d + bitOffset v_bits w d) % w) := by ring
    _ = wordOffset q_bits w d * w + wordOffset v_bits w d * w +
          (bitOffset q_bits w d + bitOffset v_bits w d) := by rw [Nat.div_add_mod]
    _ = (wordOffset q_bits w d * w + bitOffset q_bits w d) +
          (wordOffset v_bits w d * w + bitOffset v_bits w d) := by ring
    _ = d * q_bits + d * v_bits := by
          rw [wordOffset_mul_add_bitOffset, wordOffset_mul_add_bitOffset]
    _ = d * (q_bits + v_bits) := by ring

/-- Exact global bit-offset identity `wOffV * w + bOffV = d * (q_bits + v_bits) + q_bits`. -/
theorem wOffV_mul_add_bOffV {q_bits v_bits w d : ℕ} :
    wOffV q_bits v_bits w d * w + bOffV q_bits v_bits w d =
      d * (q_bits + v_bits) + q_bits := by
  unfold wOffV bOffV
  calc (wOffQ q_bits v_bits w d + (bOffQ q_bits v_bits w d + q_bits) / w) * w +
        (bOffQ q_bits v_bits w d + q_bits) % w
      = wOffQ q_bits v_bits w d * w +
          (w * ((bOffQ q_bits v_bits w d + q_bits) / w) +
            (bOffQ q_bits v_bits w d + q_bits) % w) := by ring
    _ = wOffQ q_bits v_bits w d * w + (bOffQ q_bits v_bits w d + q_bits) := by
          rw [Nat.div_add_mod]
    _ = (wOffQ q_bits v_bits w d * w + bOffQ q_bits v_bits w d) + q_bits := by ring
    _ = d * (q_bits + v_bits) + q_bits := by rw [wOffQ_mul_add_bOffQ]

/-- Word footprint of `n` densely packed `(quotient, value)` entries in epoch `N`. -/
@[expose, wram_arith] def compactedItemWords (U V w N n : ℕ) : ℕ :=
  (n * (quotientBits U N + valBits V) + w - 1) / w + 2

private theorem wOff_add_one_lt_compactedItemWords {U V w N n wOff bOff g : ℕ}
    (hw : 0 < w) (hb : bOff < w) (hid : wOff * w + bOff = g)
    (hle : g ≤ n * (quotientBits U N + valBits V)) :
    wOff + 1 < compactedItemWords U V w N n := by
  unfold compactedItemWords
  have hdiv : wOff ≤ (n * (quotientBits U N + valBits V) + w - 1) / w := by
    simpa [← hid, Nat.mul_comm _ w, Nat.mul_add_div hw, Nat.div_eq_of_lt hb] using
      Nat.div_le_div_right (c := w) (hle.trans (by omega))
  omega

theorem wOffQ_add_one_lt_compactedItemWords {U V w N n d : ℕ} (hw : 0 < w) (hd : d < n) :
    wOffQ (quotientBits U N) (valBits V) w d + 1 < compactedItemWords U V w N n :=
  wOff_add_one_lt_compactedItemWords hw (bOffQ_lt hw) wOffQ_mul_add_bOffQ
    (Nat.mul_le_mul_right _ hd.le)

theorem wOffV_add_one_lt_compactedItemWords {U V w N n d : ℕ} (hw : 0 < w) (hd : d < n) :
    wOffV (quotientBits U N) (valBits V) w d + 1 < compactedItemWords U V w N n :=
  wOff_add_one_lt_compactedItemWords hw (bOffV_lt hw) wOffV_mul_add_bOffV (by
    have := Nat.add_one_mul d (quotientBits U N + valBits V) ▸ Nat.mul_le_mul_right _ hd
    omega)

theorem compactedItemWords_mono {U V w N n₁ n₂ : ℕ} (h : n₁ ≤ n₂) :
    compactedItemWords U V w N n₁ ≤ compactedItemWords U V w N n₂ := by
  unfold compactedItemWords
  gcongr

/-- Adding `1` live item increases `compactedItemWords` by at most `2` words when `U, V ≤ 2 ^ w`. -/
theorem compactedItemWords_succ_sub_le_two {U V w N n : ℕ} (hw : 0 < w)
    (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w) :
    compactedItemWords U V w N (n + 1) - compactedItemWords U V w N n ≤ 2 := by
  have hq : quotientBits U N ≤ w := quotientBits_le_of_le_pow hU
  have hv : valBits V ≤ w := Nat.clog_le_of_le_pow hV
  unfold compactedItemWords
  have hdiv : ((n + 1) * (quotientBits U N + valBits V) + w - 1) / w ≤
      (n * (quotientBits U N + valBits V) + w - 1) / w + 2 := by
    rw [Nat.add_mul, Nat.one_mul]
    calc (n * (quotientBits U N + valBits V) + (quotientBits U N + valBits V) + w - 1) / w
        ≤ (n * (quotientBits U N + valBits V) + w - 1 + 2 * w) / w := by gcongr; omega
      _ = (n * (quotientBits U N + valBits V) + w - 1) / w + 2 :=
          Nat.add_mul_div_right _ _ hw
  omega

/-- Pure extraction function for dense quotient `d < n` at `itemBase`. -/
@[expose] def compQuotAt (itemBase U V w N n : ℕ) (mem : ℕ → ℕ) (d : ℕ) : ℕ :=
  if d < n then
    let q_bits := quotientBits U N
    let v_bits := valBits V
    readBitSlice itemBase (wOffQ q_bits v_bits w d) (bOffQ q_bits v_bits w d) q_bits w mem
  else 0

/-- Pure extraction function for dense value `d < n` at `itemBase`. -/
@[expose] def compValAt (itemBase U V w N n : ℕ) (mem : ℕ → ℕ) (d : ℕ) : ℕ :=
  if d < n then
    let q_bits := quotientBits U N
    let v_bits := valBits V
    readBitSlice itemBase (wOffV q_bits v_bits w d) (bOffV q_bits v_bits w d) v_bits w mem
  else 0

/-- Write `q` into dense quotient `d` at `itemBase`. -/
@[expose] def writeCompQuot (itemBase U V w N : ℕ) (mem : ℕ → ℕ) (d q : ℕ) : ℕ → ℕ :=
  let q_bits := quotientBits U N
  let v_bits := valBits V
  writeBitSlice itemBase (wOffQ q_bits v_bits w d) (bOffQ q_bits v_bits w d) q_bits w mem q

/-- Write `v` into dense value `d` at `itemBase`. -/
@[expose] def writeCompVal (itemBase U V w N : ℕ) (mem : ℕ → ℕ) (d v : ℕ) : ℕ → ℕ :=
  let q_bits := quotientBits U N
  let v_bits := valBits V
  writeBitSlice itemBase (wOffV q_bits v_bits w d) (bOffV q_bits v_bits w d) v_bits w mem v

theorem compQuotAt_lt (itemBase U V w N n : ℕ) (mem : ℕ → ℕ) (d : ℕ) :
    compQuotAt itemBase U V w N n mem d < 2 ^ quotientBits U N := by
  unfold compQuotAt
  split_ifs
  exacts [readBitSlice_lt _ _ _ _ _ _, by positivity]

theorem compValAt_lt (itemBase U V w N n : ℕ) (mem : ℕ → ℕ) (d : ℕ) :
    compValAt itemBase U V w N n mem d < 2 ^ valBits V := by
  unfold compValAt
  split_ifs
  exacts [readBitSlice_lt _ _ _ _ _ _, by positivity]

theorem compQuotAt_writeCompQuot_self {itemBase U V w N n d q : ℕ} (mem : ℕ → ℕ)
    (hd : d < n) (hq : q < 2 ^ quotientBits U N) :
    compQuotAt itemBase U V w N n (writeCompQuot itemBase U V w N mem d q) d = q := by
  simpa [compQuotAt, writeCompQuot, hd] using readBitSlice_writeBitSlice_self _ _ _ _ _ _ hq

private theorem pair_bitRange_disjoint {q v d₁ d₂ o₁ k₁ o₂ k₂ : ℕ}
    (h₁ : o₁ + k₁ ≤ q + v) (h₂ : o₂ + k₂ ≤ q + v)
    (hdisj : d₁ = d₂ → o₁ + k₁ ≤ o₂ ∨ o₂ + k₂ ≤ o₁) :
    d₁ * (q + v) + o₁ + k₁ ≤ d₂ * (q + v) + o₂ ∨
    d₂ * (q + v) + o₂ + k₂ ≤ d₁ * (q + v) + o₁ := by
  rcases lt_trichotomy d₁ d₂ with hlt | rfl | hgt
  · have := Nat.add_one_mul d₁ (q + v) ▸ Nat.mul_le_mul_right (q + v) hlt
    exact Or.inl (by omega)
  · exact (hdisj rfl).imp (by omega) (by omega)
  · have := Nat.add_one_mul d₂ (q + v) ▸ Nat.mul_le_mul_right (q + v) hgt
    exact Or.inr (by omega)

theorem compQuotAt_writeCompQuot_of_ne {itemBase U V w N n d d' q : ℕ} (hw : 0 < w)
    (mem : ℕ → ℕ) (hne : d' ≠ d) :
    compQuotAt itemBase U V w N n (writeCompQuot itemBase U V w N mem d q) d' =
      compQuotAt itemBase U V w N n mem d' := by
  unfold compQuotAt writeCompQuot
  split_ifs with hd'
  · refine readBitSlice_writeBitSlice_of_disjoint (bOffQ_lt hw) (bOffQ_lt hw) ?_ mem q
    rw [wOffQ_mul_add_bOffQ, wOffQ_mul_add_bOffQ]
    simpa only [Nat.add_zero] using pair_bitRange_disjoint (o₁ := 0) (o₂ := 0)
      (by omega) (by omega) fun h => absurd h.symm hne
  · rfl

theorem compValAt_writeCompQuot {itemBase U V w N n d d' q : ℕ} (hw : 0 < w) (mem : ℕ → ℕ) :
    compValAt itemBase U V w N n (writeCompQuot itemBase U V w N mem d q) d' =
      compValAt itemBase U V w N n mem d' := by
  unfold compValAt writeCompQuot
  split_ifs with hd'
  · refine readBitSlice_writeBitSlice_of_disjoint (bOffQ_lt hw) (bOffV_lt hw) ?_ mem q
    rw [wOffQ_mul_add_bOffQ, wOffV_mul_add_bOffV]
    simpa only [Nat.add_zero] using pair_bitRange_disjoint (o₁ := 0)
      (by omega) le_rfl fun _ => Or.inl (by omega)
  · rfl

theorem compValAt_writeCompVal_self {itemBase U V w N n d v : ℕ} (mem : ℕ → ℕ)
    (hd : d < n) (hv : v < 2 ^ valBits V) :
    compValAt itemBase U V w N n (writeCompVal itemBase U V w N mem d v) d = v := by
  simpa [compValAt, writeCompVal, hd] using readBitSlice_writeBitSlice_self _ _ _ _ _ _ hv

theorem compValAt_writeCompVal_of_ne {itemBase U V w N n d d' v : ℕ} (hw : 0 < w)
    (mem : ℕ → ℕ) (hne : d' ≠ d) :
    compValAt itemBase U V w N n (writeCompVal itemBase U V w N mem d v) d' =
      compValAt itemBase U V w N n mem d' := by
  unfold compValAt writeCompVal
  split_ifs with hd'
  · refine readBitSlice_writeBitSlice_of_disjoint (bOffV_lt hw) (bOffV_lt hw) ?_ mem v
    rw [wOffV_mul_add_bOffV, wOffV_mul_add_bOffV]
    exact pair_bitRange_disjoint le_rfl le_rfl fun h => absurd h.symm hne
  · rfl

theorem compQuotAt_writeCompVal {itemBase U V w N n d d' v : ℕ} (hw : 0 < w) (mem : ℕ → ℕ) :
    compQuotAt itemBase U V w N n (writeCompVal itemBase U V w N mem d v) d' =
      compQuotAt itemBase U V w N n mem d' := by
  unfold compQuotAt writeCompVal
  split_ifs with hd'
  · refine readBitSlice_writeBitSlice_of_disjoint (bOffV_lt hw) (bOffQ_lt hw) ?_ mem v
    rw [wOffV_mul_add_bOffV, wOffQ_mul_add_bOffQ]
    simpa only [Nat.add_zero] using pair_bitRange_disjoint (o₂ := 0)
      le_rfl (by omega) fun _ => Or.inr (by omega)
  · rfl

theorem writeCompQuot_outside {itemBase U V w N n d q addr : ℕ} (hw : 0 < w) (hd : d < n)
    (mem : ℕ → ℕ) (haddr : ¬(itemBase ≤ addr ∧ addr < itemBase + compactedItemWords U V w N n)) :
    writeCompQuot itemBase U V w N mem d q addr = mem addr := by
  unfold writeCompQuot writeBitSlice
  have hlt := wOffQ_add_one_lt_compactedItemWords (U := U) (V := V) (N := N) hw hd
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

theorem writeCompVal_outside {itemBase U V w N n d v addr : ℕ} (hw : 0 < w) (hd : d < n)
    (mem : ℕ → ℕ) (haddr : ¬(itemBase ≤ addr ∧ addr < itemBase + compactedItemWords U V w N n)) :
    writeCompVal itemBase U V w N mem d v addr = mem addr := by
  unfold writeCompVal writeBitSlice
  have hlt := wOffV_add_one_lt_compactedItemWords (U := U) (V := V) (N := N) hw hd
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

theorem compQuotAt_congr {itemBase U V w N n : ℕ} (hw : 0 < w) {mem₁ mem₂ : ℕ → ℕ}
    (heq : ∀ addr, itemBase ≤ addr ∧ addr < itemBase + compactedItemWords U V w N n →
      mem₁ addr = mem₂ addr) :
    compQuotAt itemBase U V w N n mem₁ = compQuotAt itemBase U V w N n mem₂ := by
  funext d; unfold compQuotAt readBitSlice
  split_ifs with hd
  · dsimp only
    have hlt := wOffQ_add_one_lt_compactedItemWords (U := U) (V := V) (N := N) hw hd
    rw [heq _ ⟨by omega, by omega⟩, heq _ ⟨by omega, by omega⟩]
  · rfl

theorem compValAt_congr {itemBase U V w N n : ℕ} (hw : 0 < w) {mem₁ mem₂ : ℕ → ℕ}
    (heq : ∀ addr, itemBase ≤ addr ∧ addr < itemBase + compactedItemWords U V w N n →
      mem₁ addr = mem₂ addr) :
    compValAt itemBase U V w N n mem₁ = compValAt itemBase U V w N n mem₂ := by
  funext d; unfold compValAt readBitSlice
  split_ifs with hd
  · dsimp only
    have hlt := wOffV_add_one_lt_compactedItemWords (U := U) (V := V) (N := N) hw hd
    rw [heq _ ⟨by omega, by omega⟩, heq _ ⟨by omega, by omega⟩]
  · rfl

theorem compQuotAt_of_lt {itemBase U V w N n₁ n₂ d : ℕ} (mem : ℕ → ℕ)
    (hd₁ : d < n₁) (hd₂ : d < n₂) :
    compQuotAt itemBase U V w N n₁ mem d = compQuotAt itemBase U V w N n₂ mem d := by
  simp [compQuotAt, hd₁, hd₂]

theorem compValAt_of_lt {itemBase U V w N n₁ n₂ d : ℕ} (mem : ℕ → ℕ)
    (hd₁ : d < n₁) (hd₂ : d < n₂) :
    compValAt itemBase U V w N n₁ mem d = compValAt itemBase U V w N n₂ mem d := by
  simp [compValAt, hd₁, hd₂]

/-! ## Section 2: Persistent Root Header, Compacted Epoch Layout, and `1 · OPT` Space Bounds -/

/-- The 8-word persistent root header `[U - 1, V - 1, w, keyBits U, valBits V, N, n, n_init]`. -/
@[expose] def rootHdrWords : ℕ := 8
/-- Word offset `8` of the 19-word `RuntimeReducedKWise.HashParams` vector. -/
@[expose] def offHashParams : ℕ := 8
/-- Word offset `27` of the 36-word `CompParams` vector. -/
@[expose] def offCompParams : ℕ := 27
/-- Word offset `63` of the 162-word limb scratch slice (`63 + 162 = 225`). -/
@[expose] def offScratch : ℕ := 63
/-- Word offset `225` where the active epoch's `ReducedKWise` hash table and seed begin. -/
@[expose, wram_arith] def epochHdrWords : ℕ := 225

/-- Persistent 8-word root header invariant at `metaBase`. -/
structure RootHeaderValid (U V w N n n_init metaBase : ℕ) (mem : ℕ → ℕ) : Prop where
  fits_U : Fits w U
  pos_U : 0 < U
  pos_V : 0 < V
  hdr_U : mem metaBase = U - 1
  hdr_V : mem (metaBase + 1) = V - 1
  hdr_w : mem (metaBase + 2) = w
  hdr_keyBits : mem (metaBase + 3) = keyBits U
  hdr_valBits : mem (metaBase + 4) = valBits V
  hdr_N : mem (metaBase + 5) = N
  hdr_n : mem (metaBase + 6) = n
  hdr_n_init : mem (metaBase + 7) = n_init

/-- Epoch capacity invariant: `N = 0` when `n = 0`, else `1 ≤ n ≤ N ≤ 4 * n ∧ N ≤ U`. -/
@[expose] def EpochValid (U n N : ℕ) : Prop :=
  (n = 0 ∧ N = 0) ∨ (1 ≤ n ∧ n ≤ N ∧ N ≤ 4 * n ∧ N ≤ U)

/-- A valid epoch bounds its size by its capacity, and its capacity by four times the size
and by the universe size. These inequalities force zero capacity for an empty epoch. -/
theorem epochValid_iff_capacity_bounds {U n N : ℕ} :
    EpochValid U n N ↔ n ≤ N ∧ N ≤ 4 * n ∧ N ≤ U := by
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨_, hnN, hN4, hNU⟩)
    · exact ⟨le_rfl, Nat.zero_le _, Nat.zero_le _⟩
    · exact ⟨hnN, hN4, hNU⟩
  · rintro ⟨hnN, hN4, hNU⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Or.inl ⟨rfl, Nat.eq_zero_of_le_zero hN4⟩
    · exact Or.inr ⟨hn, hnN, hN4, hNU⟩

/-- Target epoch capacity `min (2 * n) U` (`0` when `n = 0`). -/
@[expose] def targetCap (U n : ℕ) : ℕ :=
  if n = 0 then 0 else min (2 * n) U

/-- The minimum formula for the target epoch capacity also holds at zero. -/
theorem targetCap_eq_min (U n : ℕ) : targetCap U n = min (2 * n) U := by
  by_cases hn : n = 0 <;> simp [targetCap, hn]

/-- The target capacity of a nonempty epoch fits the universe and is at most twice its size. -/
theorem targetCap_bounds_of_pos {U n : ℕ} (hn : 1 ≤ n) (hnU : n ≤ U) :
    1 ≤ targetCap U n ∧ n ≤ targetCap U n ∧ targetCap U n ≤ 2 * n ∧ targetCap U n ≤ U := by
  rw [targetCap_eq_min]
  have hcap : n ≤ min (2 * n) U := le_min (by lia) hnU
  exact ⟨hn.trans hcap, hcap, min_le_left _ _, min_le_right _ _⟩

theorem epochValid_targetCap {U n : ℕ} (hnU : n ≤ U) : EpochValid U n (targetCap U n) := by
  rw [epochValid_iff_capacity_bounds, targetCap_eq_min]
  exact ⟨le_min (by lia) hnU, (min_le_left _ _).trans (by lia), min_le_right _ _⟩

/-- Effective quotient bit-width `max (quotientBits U N) 1` (`= Succinct.qBits U N`). -/
abbrev epochQBits (U N : ℕ) : ℕ := max (quotientBits U N) 1

/-- Reduction target bit-width `totalMicroBits N + 1` (`= Succinct.hashB N`). -/
abbrev epochHashB (N : ℕ) : ℕ := totalMicroBits N + 1

/-- Word footprint of the epoch quotient hash (`= Succinct.hashSpace U w N`). -/
abbrev epochHashSpace (U w N : ℕ) : ℕ :=
  ReducedKWise.space w (epochQBits U N) (epochHashB N) (totalMicroBits N) 3

/-- Word offset of `LocalMeta` relative to `metaBase` in a compacted epoch of capacity `N`. -/
@[expose, wram_arith] def offCompLM (U w N : ℕ) : ℕ :=
  epochHdrWords + epochHashSpace U w N

/-- Word offset of the `c`-th `LocalMeta` sub-array (`c < 9`) relative to `metaBase`. -/
@[expose, wram_arith] def offCompLMSub (U w N c : ℕ) : ℕ :=
  offCompLM U w N + c * lmSubWords N w

/-- Word offset of `GlobalMeta` relative to `metaBase` in a compacted epoch of capacity `N`. -/
@[expose, wram_arith] def offCompGM (U w N : ℕ) : ℕ :=
  offCompLM U w N + 9 * lmSubWords N w

/-- Word offset of `TailToDense` relative to `metaBase`. -/
@[expose, wram_arith] def offTailToDense (U w N : ℕ) : ℕ :=
  offCompGM U w N + packedWords (globalMetaLen N) (globalPtrBits N) w

/-- Word offset of `DenseToTail` relative to `metaBase`. -/
@[expose, wram_arith] def offDenseToTail (U w N : ℕ) : ℕ :=
  offTailToDense U w N + packedWords (maxTailItems N) (globalPtrBits N) w

/-- Word offset of the dense `[0, n)` active `(quotient, value)` stream relative to `metaBase`. -/
@[expose, wram_arith] def offCompItems (U w N : ℕ) : ℕ :=
  offDenseToTail U w N + packedWords (maxTailItems N) (globalPtrBits N) w

/-- The compacted item stream starts after the fixed epoch header and scratch region. -/
theorem le_offCompItems_225 (U w N : ℕ) : 225 ≤ offCompItems U w N :=
  calc
    225 ≤ offCompLM U w N := Nat.le_add_right _ _
    _ ≤ offCompGM U w N := Nat.le_add_right _ _
    _ ≤ offTailToDense U w N := Nat.le_add_right _ _
    _ ≤ offDenseToTail U w N := Nat.le_add_right _ _
    _ ≤ offCompItems U w N := Nat.le_add_right _ _

/-- Total resting word footprint of a compacted epoch `(N, n)`:
`8` words when `n = 0` (`rootHdrWords`), and `offCompItems U w N + compactedItemWords U V w N n`
when `0 < n`. -/
@[expose] def compactedEpochWords (U V w N n : ℕ) : ℕ :=
  if n = 0 then rootHdrWords else offCompItems U w N + compactedItemWords U V w N n

theorem eight_le_compactedEpochWords (U V w N n : ℕ) :
    8 ≤ compactedEpochWords U V w N n := by
  unfold compactedEpochWords rootHdrWords offCompItems offDenseToTail offTailToDense offCompGM
    offCompLM epochHdrWords
  split_ifs <;> omega

theorem compactedEpochWords_mono {U V w N n₁ n₂ : ℕ} (h : n₁ ≤ n₂) :
    compactedEpochWords U V w N n₁ ≤ compactedEpochWords U V w N n₂ := by
  rcases eq_or_ne n₁ 0 with rfl | hn₁
  · exact eight_le_compactedEpochWords U V w N n₂
  · simp only [compactedEpochWords, hn₁, ((Nat.pos_of_ne_zero hn₁).trans_le h).ne', ↓reduceIte]
    exact Nat.add_le_add_left (compactedItemWords_mono h) _

theorem quotientBits_le_add_six_of_le_four_mul {n N : ℕ} (U : ℕ)
    (hnN : n ≤ N) (hN4 : N ≤ 4 * n) :
    quotientBits U N ≤ quotientBits U n + 6 := by
  have hlog : Nat.log 2 n ≤ Nat.log 2 N := Nat.log_mono_right hnN
  have hll : Dynamic.logLogFactor N ≤ Dynamic.logLogFactor n + 2 :=
    (Dynamic.logLogFactor_mono hN4).trans (Dynamic.logLogFactor_four_mul_le_add_two n)
  unfold quotientBits bucketBits
  omega

theorem succinctWords_mul_w_le_bits (C C₀ U V w n : ℕ) :
    w * Dynamic.succinctWords C C₀ U V w n ≤
      Dynamic.optBits U V n + C * n * Dynamic.logLogFactor n + (C₀ + 1) * w := by
  unfold Dynamic.succinctWords
  set B := Dynamic.optBits U V n + C * n * Dynamic.logLogFactor n
  calc w * ((B + w - 1) / w + C₀)
      = w * ((B + w - 1) / w) + C₀ * w := by ring
    _ ≤ (B + w - 1) + C₀ * w := Nat.add_le_add_right (Nat.mul_div_le _ _) _
    _ ≤ B + (C₀ + 1) * w := by rw [Nat.succ_mul]; omega

/-! ## Section 3: Pure Metadata Extractors and Runtime `CompParams` -/

/-- Pure extraction function for `LocalMeta` in a compacted epoch at `metaBase`. -/
@[expose] def compLmAt (metaBase U w N : ℕ) (mem : ℕ → ℕ) : ℕ × ℕ → ℕ
  | (c, idx) =>
    if c < 9 ∧ idx < totalMicroBuckets N then
      readPacked (metaBase + offCompLMSub U w N c) (effBucketPosBits N) w mem idx
    else 0

/-- Pure extraction function for `GlobalMeta` in a compacted epoch at `metaBase`. -/
@[expose] def compGmAt (metaBase U w N : ℕ) (mem : ℕ → ℕ) (idx : ℕ) : ℕ :=
  if idx < globalMetaLen N then
    readPacked (metaBase + offCompGM U w N) (globalPtrBits N) w mem idx
  else 0

/-- Pure extraction function for `TailToDense[t]` (`0` when `t ≥ maxTailItems N`). -/
@[expose] def compTDAt (metaBase U w N : ℕ) (mem : ℕ → ℕ) (t : ℕ) : ℕ :=
  if t < maxTailItems N then
    readPacked (metaBase + offTailToDense U w N) (globalPtrBits N) w mem t
  else 0

/-- Pure extraction function for `DenseToTail[r]` (`0` when `r ≥ maxTailItems N`). -/
@[expose] def compDTAt (metaBase U w N : ℕ) (mem : ℕ → ℕ) (r : ℕ) : ℕ :=
  if r < maxTailItems N then
    readPacked (metaBase + offDenseToTail U w N) (globalPtrBits N) w mem r
  else 0

/-- Runtime 36-word parameter vector stored at `[metaBase + offCompParams, +36)`. -/
@[expose] def CompParams : Type := Fin 36 → ℕ

instance : WordEncoding CompParams := ⟨36, Function.Embedding.refl (Fin 36 → ℕ)⟩

/-- Populate the 36-word `CompParams` vector for `(U, V, w, N)`. -/
@[expose] def mkCompParams (U V w N : ℕ) : CompParams := fun i =>
  match i.val with
  | 0 => w
  | 1 => N
  | 2 => N - 1
  | 3 => quotientBits U N
  | 4 => valBits V
  | 5 => offCompLMSub U w N 0
  | 6 => offCompLMSub U w N 1
  | 7 => offCompLMSub U w N 2
  | 8 => offCompLMSub U w N 3
  | 9 => offCompLMSub U w N 4
  | 10 => offCompLMSub U w N 5
  | 11 => offCompLMSub U w N 6
  | 12 => offCompLMSub U w N 7
  | 13 => offCompLMSub U w N 8
  | 14 => effBucketPosBits N
  | 15 => offCompGM U w N
  | 16 => globalPtrBits N
  | 17 => offTailToDense U w N
  | 18 => offDenseToTail U w N
  | 19 => maxTailItems N
  | 20 => bucketBits N
  | 21 => 2 ^ bucketBits N - 1
  | 22 => slabSize N
  | 23 => slabSize N - 1
  | 24 => 2 * slabSize N
  | 25 => dirSlabsPerBucket N
  | 26 => dirSlabsPerBucket N - 1
  | 27 => tailCapPerBucket N
  | 28 => gmSlabDirBase N
  | 29 => gmTailPtrBase N
  | 30 => gmTailOwnerBase N
  | 31 => gmSlabMetaBase N
  | 32 => numMicroPerBucket N
  | 33 => min N (effBucketCap N)
  | 34 => offCompItems U w N
  | 35 => epochHashSpace U w N
  | _ => 0

/-- Word width $w$. -/
abbrev cpW (cp : CompParams) : ℕ := cp ⟨0, by decide⟩
/-- Capacity parameter $N$. -/
abbrev cpN (cp : CompParams) : ℕ := cp ⟨1, by decide⟩
/-- Capacity minus one, $N - 1$. -/
abbrev cpNSubOne (cp : CompParams) : ℕ := cp ⟨2, by decide⟩
/-- Quotient bit width $q$. -/
abbrev cpQuotBits (cp : CompParams) : ℕ := cp ⟨3, by decide⟩
/-- Value bit width $v$. -/
abbrev cpValBits (cp : CompParams) : ℕ := cp ⟨4, by decide⟩
/-- Local metadata subtable offset for coordinate $c < 9$. -/
abbrev cpOffLMSub (c : Fin 9) (cp : CompParams) : ℕ :=
  match c.val with
  | 0 => cp ⟨5, by decide⟩ | 1 => cp ⟨6, by decide⟩ | 2 => cp ⟨7, by decide⟩
  | 3 => cp ⟨8, by decide⟩ | 4 => cp ⟨9, by decide⟩ | 5 => cp ⟨10, by decide⟩
  | 6 => cp ⟨11, by decide⟩ | 7 => cp ⟨12, by decide⟩ | _ => cp ⟨13, by decide⟩
/-- Local metadata entry bit-length. -/
abbrev cpLmBits (cp : CompParams) : ℕ := cp ⟨14, by decide⟩
/-- Global metadata table offset. -/
abbrev cpOffGM (cp : CompParams) : ℕ := cp ⟨15, by decide⟩
/-- Global metadata entry bit-length. -/
abbrev cpGmBits (cp : CompParams) : ℕ := cp ⟨16, by decide⟩
/-- Tail-to-dense permutation offset. -/
abbrev cpOffTD (cp : CompParams) : ℕ := cp ⟨17, by decide⟩
/-- Dense-to-tail permutation offset. -/
abbrev cpOffDT (cp : CompParams) : ℕ := cp ⟨18, by decide⟩
/-- Maximum tail item capacity. -/
abbrev cpMaxTail (cp : CompParams) : ℕ := cp ⟨19, by decide⟩
/-- Number of bucket bits $\lceil \log_2 N \rceil$. -/
abbrev cpBucketBits (cp : CompParams) : ℕ := cp ⟨20, by decide⟩
/-- Bitmask for bucket bits $2^{\mathrm{bucketBits}} - 1$. -/
abbrev cpBucketMask (cp : CompParams) : ℕ := cp ⟨21, by decide⟩
/-- Bucket slab size parameter $K$. -/
abbrev cpSlabSize (cp : CompParams) : ℕ := cp ⟨22, by decide⟩
/-- Slab size minus one $K - 1$. -/
abbrev cpSlabSizeSubOne (cp : CompParams) : ℕ := cp ⟨23, by decide⟩
/-- Twice slab size $2K$. -/
abbrev cpTwoSlabSize (cp : CompParams) : ℕ := cp ⟨24, by decide⟩
/-- Direct slab count. -/
abbrev cpDirSlabs (cp : CompParams) : ℕ := cp ⟨25, by decide⟩
/-- Direct slab count minus one. -/
abbrev cpDirSlabsSubOne (cp : CompParams) : ℕ := cp ⟨26, by decide⟩
/-- Tail capacity parameter. -/
abbrev cpTailCap (cp : CompParams) : ℕ := cp ⟨27, by decide⟩
/-- Global metadata slab directory base index. -/
abbrev cpGmSlabDirBase (cp : CompParams) : ℕ := cp ⟨28, by decide⟩
/-- Global metadata tail pointer base index. -/
abbrev cpGmTailPtrBase (cp : CompParams) : ℕ := cp ⟨29, by decide⟩
/-- Global metadata tail owner base index. -/
abbrev cpGmTailOwnerBase (cp : CompParams) : ℕ := cp ⟨30, by decide⟩
/-- Global metadata slab metadata base index. -/
abbrev cpGmSlabMetaBase (cp : CompParams) : ℕ := cp ⟨31, by decide⟩
/-- Micro-block count. -/
abbrev cpNumMicro (cp : CompParams) : ℕ := cp ⟨32, by decide⟩
/-- Minimum capacity bound. -/
abbrev cpMinCap (cp : CompParams) : ℕ := cp ⟨33, by decide⟩
/-- Item array offset. -/
abbrev cpOffItems (cp : CompParams) : ℕ := cp ⟨34, by decide⟩
/-- Hash family workspace allocation words. -/
abbrev cpHashSpace (cp : CompParams) : ℕ := cp ⟨35, by decide⟩

@[simp] theorem cpOffLMSub_mk (U V w N : ℕ) (c : Fin 9) :
    cpOffLMSub c (mkCompParams U V w N) = offCompLMSub U w N c.val := by
  rcases c with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | c, hc⟩ <;> try rfl
  omega

@[simp] theorem cpW_mk (U V w N : ℕ) : cpW (mkCompParams U V w N) = w := rfl
@[simp] theorem cpN_mk (U V w N : ℕ) : cpN (mkCompParams U V w N) = N := rfl
@[simp] theorem cpNSubOne_mk (U V w N : ℕ) : cpNSubOne (mkCompParams U V w N) = N - 1 := rfl
@[simp] theorem cpQuotBits_mk (U V w N : ℕ) :
    cpQuotBits (mkCompParams U V w N) = quotientBits U N := rfl
@[simp] theorem cpValBits_mk (U V w N : ℕ) : cpValBits (mkCompParams U V w N) = valBits V := rfl
@[simp] theorem cpLmBits_mk (U V w N : ℕ) :
    cpLmBits (mkCompParams U V w N) = effBucketPosBits N := rfl
@[simp] theorem cpOffGM_mk (U V w N : ℕ) : cpOffGM (mkCompParams U V w N) = offCompGM U w N := rfl
@[simp] theorem cpGmBits_mk (U V w N : ℕ) :
    cpGmBits (mkCompParams U V w N) = globalPtrBits N := rfl
@[simp] theorem cpOffTD_mk (U V w N : ℕ) :
    cpOffTD (mkCompParams U V w N) = offTailToDense U w N := rfl
@[simp] theorem cpOffDT_mk (U V w N : ℕ) :
    cpOffDT (mkCompParams U V w N) = offDenseToTail U w N := rfl
@[simp] theorem cpMaxTail_mk (U V w N : ℕ) :
    cpMaxTail (mkCompParams U V w N) = maxTailItems N := rfl
@[simp] theorem cpBucketBits_mk (U V w N : ℕ) :
    cpBucketBits (mkCompParams U V w N) = bucketBits N := rfl
@[simp] theorem cpBucketMask_mk (U V w N : ℕ) :
    cpBucketMask (mkCompParams U V w N) = 2 ^ bucketBits N - 1 := rfl
@[simp] theorem cpSlabSize_mk (U V w N : ℕ) : cpSlabSize (mkCompParams U V w N) = slabSize N := rfl
@[simp] theorem cpSlabSizeSubOne_mk (U V w N : ℕ) :
    cpSlabSizeSubOne (mkCompParams U V w N) = slabSize N - 1 := rfl
@[simp] theorem cpTwoSlabSize_mk (U V w N : ℕ) :
    cpTwoSlabSize (mkCompParams U V w N) = 2 * slabSize N := rfl
@[simp] theorem cpDirSlabs_mk (U V w N : ℕ) :
    cpDirSlabs (mkCompParams U V w N) = dirSlabsPerBucket N := rfl
@[simp] theorem cpDirSlabsSubOne_mk (U V w N : ℕ) :
    cpDirSlabsSubOne (mkCompParams U V w N) = dirSlabsPerBucket N - 1 := rfl
@[simp] theorem cpTailCap_mk (U V w N : ℕ) :
    cpTailCap (mkCompParams U V w N) = tailCapPerBucket N := rfl
@[simp] theorem cpGmSlabDirBase_mk (U V w N : ℕ) :
    cpGmSlabDirBase (mkCompParams U V w N) = gmSlabDirBase N := rfl
@[simp] theorem cpGmTailPtrBase_mk (U V w N : ℕ) :
    cpGmTailPtrBase (mkCompParams U V w N) = gmTailPtrBase N := rfl
@[simp] theorem cpGmTailOwnerBase_mk (U V w N : ℕ) :
    cpGmTailOwnerBase (mkCompParams U V w N) = gmTailOwnerBase N := rfl
@[simp] theorem cpGmSlabMetaBase_mk (U V w N : ℕ) :
    cpGmSlabMetaBase (mkCompParams U V w N) = gmSlabMetaBase N := rfl
@[simp] theorem cpNumMicro_mk (U V w N : ℕ) :
    cpNumMicro (mkCompParams U V w N) = numMicroPerBucket N := rfl
@[simp] theorem cpMinCap_mk (U V w N : ℕ) :
    cpMinCap (mkCompParams U V w N) = min N (effBucketCap N) := rfl
@[simp] theorem cpOffItems_mk (U V w N : ℕ) :
    cpOffItems (mkCompParams U V w N) = offCompItems U w N := rfl
@[simp] theorem cpHashSpace_mk (U V w N : ℕ) :
    cpHashSpace (mkCompParams U V w N) = epochHashSpace U w N := rfl

/-- Stored runtime parameter blocks in `[metaBase + 8, metaBase + 63)` for active epoch `N`. -/
structure EpochParamsStored (U V w N metaBase : ℕ) (mem : ℕ → ℕ) : Prop where
  hp_eq : ∀ i : Fin 19, mem (metaBase + offHashParams + i.val) =
    RuntimeReducedKWise.mkHashParams w (epochQBits U N) (epochHashB N) (totalMicroBits N) 3 i
  cp_eq : ∀ i : Fin 36, mem (metaBase + offCompParams + i.val) = mkCompParams U V w N i

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
