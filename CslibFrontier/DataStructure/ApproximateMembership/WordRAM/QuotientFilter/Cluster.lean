/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.ApproximateMembership.WordRAM.QuotientFilter.SlotArray
public import CslibFrontier.Computability.WordRAM.Realization.WordEncoding.Equiv
import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
import CslibFrontier.Computability.WordRAM.Realization.WhileAbsorb
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize
import CslibFrontier.Tactic.ValidProg
import Mathlib.Data.Nat.Bitwise

/-!
# Memory-Program Realization of Quotient-Filter Cluster Operations

This module implements and certifies the deterministic cluster-level operations (`queryCluster`,
`insertCluster`, `deleteCluster`) of the Word-RAM quotient filter as a unified `Memory.Prog`
program `clusterOpProg`, certified for width-independent compilation via the `realize` tactic
(`realizes_clusterOp`). Word-RAM register assignment and machine-code assembly live in
`CslibFrontier/DataStructure/ApproximateMembership/WordRAM/QuotientFilter/Code.lean`.

## Main definitions

* `ClusterInput`, `ClusterInput.words`, `mkClusterInput`, `ClusterSafe`: 15-field runtime
  parameter record for cluster operations, its 15-word vector embedding for `WordEncoding`,
  concrete constructor, and word-width safety envelope.
* `ScanEnv`, `ScanEnv.equiv`, `ScanState`, `ScanState.equiv`, `ScanStepCtx`, `ScanStepCtx.equiv`,
  `scanStepTargetProg`, `scanStepQueryProg`: named records and step helpers for the cluster scan.
* `clusterOpProg`: unified deterministic `Memory.Prog` cluster operation
  (`0` = insert, `1` = delete, `2` = query).
* `SlotFrame`: memory-frame relation restricting modifications to the four bit-packed slot arrays
  `[fullBase base w w₀ n, base + space w w₀ n k)`.

## Main results

* `quotBits_lt_w_of_fits_space`: `quotBits w₀ n < w` holds whenever `0 < w₀`, `2 * w₀ ≤ w`, and
  `Fits w (base + space w w₀ n k)`.
* `clusterSafe_mkClusterInput`, `ClusterSafe.fits_encode`: `mkClusterInput` satisfies
  `ClusterSafe`, and every encoded word of a `ClusterSafe` input fits in `w` bits.
* `realizes_scanStepQuery`, `validHistory_scanStepQuery`, `memoryCost_scanStepQuery`:
  width-independent realization, memory admissibility, and zero memory cost for
  `scanStepQueryProg`.
* `realizes_clusterOp`, `validHistory_clusterOp_mk`, `memoryCost_clusterOp_mk_le`:
  width-independent `Realizes .exact` certificate, memory admissibility, and `11 * ℓ + 13`
  memory-operation bound for `clusterOpProg`.
* `clusterOpProg_mk_insert`, `clusterOpProg_mk_delete`, `clusterOpProg_mk_query`: pure
  `FilterState` refinement and `SlotFrame` specifications coupling `clusterOpProg` to
  `FilterInv.insertState`, `FilterInv.deleteState`, and `bucketRun` membership.
-/

public section

namespace Cslib.DataStructure.ApproximateMembership.QuotientFilter

open Finset
open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure
open Cslib.DataStructure.StateTransitionSpec
  (clientResult_bind clientState_bind clientResult_pure clientState_pure)
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.Dictionary.WordRAM.LinearProbing

-- Scope imported `simp` rules locally so they do not leak into downstream modules.
attribute [local simp] Cslib.WordRAM.Realization.memoryCost_bind'
attribute [local simp] Cslib.DataStructure.StateTransitionSpec.clientResult_pure

/-! ## Section 1: Cluster operation input record (`ClusterInput`) -/

/-- The 15-word runtime input record passed to the quotient-filter cluster program `clusterOpProg`.
The fields appear in register order `0..14` matching `ClusterInput.words`. -/
@[ext] structure ClusterInput where
  /-- Target quotient slot `q.val`. -/
  qVal : ℕ
  /-- Target remainder `r.val`. -/
  rVal : ℕ
  /-- Operation tag (`0` = insert, `1` = delete, `2` = query). -/
  opTag : ℕ
  /-- Slot capacity `2 ^ b` (`b = quotBits w₀ n`). -/
  slotCap : ℕ
  /-- Cyclic slot bitmask `2 ^ b - 1`. -/
  slotMask : ℕ
  /-- Base word address of the `isFull` bitmap. -/
  fullBase : ℕ
  /-- Base word address of the `isOcc` bitmap. -/
  occBase : ℕ
  /-- Base word address of the `isRunStart` bitmap. -/
  runBase : ℕ
  /-- Base word address of the `remAt` packed array. -/
  remBase : ℕ
  /-- Log₂ packing factor `slotPackShift b 1 w` for `1`-bit bitmaps. -/
  pBit : ℕ
  /-- Intra-word bit-index mask `2 ^ pBit - 1` for `1`-bit bitmaps. -/
  pBitMask : ℕ
  /-- Log₂ packing factor `slotPackShift b f w` for `f`-bit remainders. -/
  pRem : ℕ
  /-- Intra-word entry-index mask `2 ^ pRem - 1` for `f`-bit remainders. -/
  pRemMask : ℕ
  /-- Remainder bit-width `remBits w₀ k`. -/
  f : ℕ
  /-- Remainder value mask `2 ^ f - 1`. -/
  fMask : ℕ
deriving Repr, DecidableEq, Inhabited

/-- Faithful 15-word vector encoding of a `ClusterInput` in declaration order `0..14`. -/
@[expose] def ClusterInput.words : ClusterInput ↪ (Fin 15 → ℕ) where
  toFun d :=
    ![d.qVal, d.rVal, d.opTag, d.slotCap, d.slotMask,
      d.fullBase, d.occBase, d.runBase, d.remBase,
      d.pBit, d.pBitMask, d.pRem, d.pRemMask, d.f, d.fMask]
  inj' _ _ h := ClusterInput.ext
    (congrFun h 0) (congrFun h 1) (congrFun h 2) (congrFun h 3) (congrFun h 4)
    (congrFun h 5) (congrFun h 6) (congrFun h 7) (congrFun h 8) (congrFun h 9)
    (congrFun h 10) (congrFun h 11) (congrFun h 12) (congrFun h 13) (congrFun h 14)

instance : WordEncoding ClusterInput := ⟨15, ClusterInput.words⟩

/-- Construct the `ClusterInput` parameter record for `(base, w, w₀, n, k)` and `(q, r, opTag)`. -/
@[expose] def mkClusterInput (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ) : ClusterInput :=
  let b := quotBits w₀ n
  let f := remBits w₀ k
  let pBit := slotPackShift b 1 w
  let pRem := slotPackShift b f w
  { qVal := q.val
    rVal := r.val
    opTag := opTag
    slotCap := 2 ^ b
    slotMask := 2 ^ b - 1
    fullBase := fullBase base w w₀ n
    occBase := occBase base w w₀ n
    runBase := runBase base w w₀ n
    remBase := remBase base w w₀ n
    pBit := pBit
    pBitMask := 2 ^ pBit - 1
    pRem := pRem
    pRemMask := 2 ^ pRem - 1
    f := f
    fMask := 2 ^ f - 1 }

/-- Word-level safety envelope for `ClusterInput` at word width `w`. -/
structure ClusterSafe (w : ℕ) (d : ClusterInput) : Prop where
  one_lt_two_pow : 1 < 2 ^ w
  cap_pos : 0 < d.slotCap
  q_lt : d.qVal < d.slotCap
  r_le : d.rVal ≤ d.fMask
  op_lt : d.opTag < 4
  cap_ge_eight : 8 ≤ d.slotCap
  two_cap_le : 2 * d.slotCap ≤ 2 ^ w
  mask_lt : d.slotMask < d.slotCap
  full_lt : d.fullBase + (d.slotMask >>> d.pBit) < 2 ^ w
  occ_lt : d.occBase + (d.slotMask >>> d.pBit) < 2 ^ w
  run_lt : d.runBase + (d.slotMask >>> d.pBit) < 2 ^ w
  rem_lt : d.remBase + (d.slotMask >>> d.pRem) < 2 ^ w
  pBit_lt : d.pBit < w
  pBitMask_lt : d.pBitMask < w
  pRem_lt : d.pRem < w
  pRemMask_lt : d.pRemMask < 2 ^ w
  f_lt : d.f < w
  remPack_le : (d.pRemMask + 1) * d.f ≤ w
  fMask_lt_f : d.fMask < 2 ^ d.f
  fMask_lt : d.fMask < 2 ^ w

private theorem ClusterSafe.two_cap_lt {w : ℕ} {d : ClusterInput} (h : ClusterSafe w d) :
    8 ≤ d.slotCap ∧ 2 * d.slotCap ≤ 2 ^ w :=
  ⟨h.cap_ge_eight, h.two_cap_le⟩

/-- Whenever `0 < w₀`, `2 * w₀ ≤ w`, and `Fits w (base + space w w₀ n k)`, the quotient bit-width
`quotBits w₀ n` is strictly less than `w`. -/
theorem quotBits_lt_w_of_fits_space {base w w₀ n k : ℕ}
    (hw₀ : 0 < w₀) (hw : 2 * w₀ ≤ w)
    (hfit : Fits w (base + space w w₀ n k)) :
    quotBits w₀ n < w := by
  let b := quotBits w₀ n
  by_contra! hle
  have hb3 : b ≤ w₀ + 3 := quotBits_le_add_three w₀ n
  have hw6 : w ≤ 6 := by omega
  have hlog : Nat.log 2 (w / 2) < 2 :=
    Nat.log_lt_of_lt_pow (by omega) (by omega)
  have hp_le : slotPackShift b 1 w ≤ 1 := by
    have : slotPackShift b 1 w ≤ Nat.log 2 (w / 2) := min_le_right b _
    omega
  have hpow_le : 2 ^ (w - 1) ≤ packedWords b 1 w :=
    Nat.pow_le_pow_right two_pos (by omega)
  have hpow_w : 2 ^ w = 2 * 2 ^ (w - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ w), pow_succ']
  have hlt : base + space w w₀ n k < 2 ^ w := hfit
  dsimp only [space, b] at hpow_le hlt
  omega

private theorem mkClusterInput_slotAddr_lt {base w w₀ n k bound : ℕ}
    (hsp : base + space w w₀ n k ≤ bound)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ) :
    let d := mkClusterInput base w w₀ n k q r opTag
    d.fullBase + (d.slotMask >>> d.pBit) < bound ∧
    d.occBase + (d.slotMask >>> d.pBit) < bound ∧
    d.runBase + (d.slotMask >>> d.pBit) < bound ∧
    d.remBase + (d.slotMask >>> d.pRem) < bound := by
  let b := quotBits w₀ n
  let maxSlot : Fin (2 ^ b) := ⟨2 ^ b - 1, Nat.sub_lt (Nat.two_pow_pos b) one_pos⟩
  have hbit : (2 ^ b - 1) >>> slotPackShift b 1 w < packedWords b 1 w :=
    shiftRight_lt_packedWords b 1 w maxSlot
  have hrem : (2 ^ b - 1) >>> slotPackShift b (remBits w₀ k) w <
      packedWords b (remBits w₀ k) w :=
    shiftRight_lt_packedWords b (remBits w₀ k) w maxSlot
  have hremEnd : remBase base w w₀ n + packedWords (quotBits w₀ n) (remBits w₀ k) w ≤ bound := by
    rwa [remBase_add_packedWords_eq]
  dsimp only [b, mkClusterInput, remBase, runBase, occBase] at hbit hrem hremEnd ⊢
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- Every `mkClusterInput` record satisfies `ClusterSafe w` once `0 < w₀`, `2 * w₀ ≤ w`,
`Fits w (base + space w w₀ n k)`, and `opTag < 4`. -/
theorem clusterSafe_mkClusterInput {base w w₀ n k : ℕ}
    (hw₀ : 0 < w₀) (hw : 2 * w₀ ≤ w)
    (hfit : Fits w (base + space w w₀ n k))
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k))
    {opTag : ℕ} (hop : opTag < 4) :
    ClusterSafe w (mkClusterInput base w w₀ n k q r opTag) := by
  have hb_lt := quotBits_lt_w_of_fits_space hw₀ hw hfit
  have hf_pos := remBits_pos (k := k) hw₀
  have hfw₀ := remBits_le_w₀ w₀ k
  have hpow_b : 0 < 2 ^ quotBits w₀ n := Nat.two_pow_pos _
  have hpow_f : 0 < 2 ^ remBits w₀ k := Nat.two_pow_pos _
  have h8 : 8 ≤ 2 ^ quotBits w₀ n := Nat.pow_le_pow_right two_pos (three_le_quotBits w₀ n)
  have h2cap : 2 * 2 ^ quotBits w₀ n ≤ 2 ^ w := by
    simpa only [pow_succ'] using Nat.pow_le_pow_right two_pos hb_lt
  obtain ⟨h5, h6, h7, h8'⟩ := mkClusterInput_slotAddr_lt hfit.le q r opTag
  have hpBit_le : slotPackShift (quotBits w₀ n) 1 w ≤ quotBits w₀ n := min_le_left _ _
  have hpRem_le :
      slotPackShift (quotBits w₀ n) (remBits w₀ k) w ≤ quotBits w₀ n := min_le_left _ _
  have hpBit_pow := two_pow_slotPackShift_mul_le (b := quotBits w₀ n) (w := w) one_pos (by omega)
  have hpRem_mul := two_pow_slotPackShift_mul_le (b := quotBits w₀ n) (w := w) hf_pos (by omega)
  have hpow_pRem : 0 < 2 ^ slotPackShift (quotBits w₀ n) (remBits w₀ k) w := Nat.two_pow_pos _
  have hpow_pRem_le := Nat.pow_le_pow_right two_pos hpRem_le
  have hpow_f_le := Nat.pow_le_pow_right two_pos hfw₀
  have hpow_w₀_lt := Nat.pow_lt_pow_right one_lt_two (by omega : w₀ < w)
  refine ⟨by omega, hpow_b, q.isLt, Nat.le_sub_one_of_lt r.isLt, hop, h8, h2cap,
    Nat.sub_lt hpow_b one_pos, h5, h6, h7, h8',
    by change slotPackShift _ 1 w < w; omega,
    by change 2 ^ slotPackShift _ 1 w - 1 < w; omega,
    by change slotPackShift _ _ w < w; omega,
    by change 2 ^ slotPackShift _ _ w - 1 < 2 ^ w; omega,
    by change remBits w₀ k < w; omega, ?_,
    Nat.sub_lt hpow_f one_pos,
    by change 2 ^ remBits w₀ k - 1 < 2 ^ w; omega⟩
  change (2 ^ slotPackShift _ _ w - 1 + 1) * remBits w₀ k ≤ w
  rw [Nat.sub_add_cancel hpow_pRem]; omega

/-- Every encoded word of a `ClusterSafe w` input record fits in `w` bits. -/
theorem ClusterSafe.fits_encode {w : ℕ} {d : ClusterInput} (hcs : ClusterSafe w d)
    (i : Fin (WordEncoding.width ClusterInput)) :
    Fits w (WordEncoding.encode d i) := by
  have := hcs.pBit_lt.trans Nat.lt_two_pow_self
  have := hcs.pBitMask_lt.trans Nat.lt_two_pow_self
  have := hcs.pRem_lt.trans Nat.lt_two_pow_self
  have := hcs.f_lt.trans Nat.lt_two_pow_self
  have h5 := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hcs.full_lt
  have h6 := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hcs.occ_lt
  have h7 := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hcs.run_lt
  have h8 := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hcs.rem_lt
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hcs
  obtain ⟨h0, h1, h2, h3, h4, h5', h6', h7', h8', h9, h10, h11, h12, h13, h14⟩ :
      Fits w d.qVal ∧ Fits w d.rVal ∧ Fits w d.opTag ∧ Fits w d.slotCap ∧ Fits w d.slotMask ∧
      Fits w d.fullBase ∧ Fits w d.occBase ∧ Fits w d.runBase ∧ Fits w d.remBase ∧ Fits w d.pBit ∧
      Fits w d.pBitMask ∧ Fits w d.pRem ∧ Fits w d.pRemMask ∧ Fits w d.f ∧ Fits w d.fMask := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> fits
  fin_cases i
  exacts [h0, h1, h2, h3, h4, h5', h6', h7', h8', h9, h10, h11, h12, h13, h14]

/-! ## Section 2: Bit-packed accessor programs -/

private theorem masked_addr_lt {base idx mask sh bound : ℕ}
    (h : base + (mask >>> sh) < bound) :
    base + ((idx &&& mask) >>> sh) < bound := by
  have h1 : (idx &&& mask) >>> sh ≤ mask >>> sh := by
    simp only [Nat.shiftRight_eq_div_pow]
    exact Nat.div_le_div_right Nat.and_le_right
  omega

private theorem fits_writeBit_diff_sh {w word sh val : ℕ} (hsh : sh < w)
    (hval : val < 2) :
    Fits w (((word >>> sh &&& 1) ^^^ val) <<< sh) :=
  Fits.mono (Nat.shiftLeft_lt (n := 1)
    (Nat.xor_lt_two_pow (Nat.and_lt_two_pow _ (by decide)) hval)) (by omega)

private theorem fits_writeBit_newWord {w word sh val : ℕ} (hw : word < 2 ^ w)
    (hsh : sh < w) (hval : val < 2) :
    Fits w (word ^^^ (((word >>> sh &&& 1) ^^^ val) <<< sh)) :=
  Nat.xor_lt_two_pow hw (fits_writeBit_diff_sh hsh hval)

/-- Read `isFull` at slot index `x.2 &&& d.slotMask`. -/
private def readFullProg (x : ClusterInput × ℕ) : Memory.Prog ℕ := do
  let idx := x.2 &&& x.1.slotMask
  let wVal ← Memory.read (x.1.fullBase + (idx >>> x.1.pBit))
  pure ((wVal >>> (idx &&& x.1.pBitMask)) &&& 1)

private theorem realizes_readFull :
    Realizes .exact readFullProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1) (fun _ _ => 0) := by
  realize
  · exact masked_addr_lt h.full_lt
  · exact h.one_lt_two_pow

/-- Read `isOcc` at slot index `x.2 &&& d.slotMask`. -/
private def readOccProg (x : ClusterInput × ℕ) : Memory.Prog ℕ := do
  let idx := x.2 &&& x.1.slotMask
  let wVal ← Memory.read (x.1.occBase + (idx >>> x.1.pBit))
  pure ((wVal >>> (idx &&& x.1.pBitMask)) &&& 1)

private theorem realizes_readOcc :
    Realizes .exact readOccProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1) (fun _ _ => 0) := by
  realize
  · exact masked_addr_lt h.occ_lt
  · exact h.one_lt_two_pow

/-- Read `isRunStart` at slot index `x.2 &&& d.slotMask`. -/
private def readRunStartProg (x : ClusterInput × ℕ) : Memory.Prog ℕ := do
  let idx := x.2 &&& x.1.slotMask
  let wVal ← Memory.read (x.1.runBase + (idx >>> x.1.pBit))
  pure ((wVal >>> (idx &&& x.1.pBitMask)) &&& 1)

private theorem realizes_readRunStart :
    Realizes .exact readRunStartProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1) (fun _ _ => 0) := by
  realize
  · exact masked_addr_lt h.run_lt
  · exact h.one_lt_two_pow

/-- Write `isFull` at slot index `slot &&& d.slotMask` with bit `bit`. -/
private def writeFullProg (x : ClusterInput × (ℕ × ℕ)) : Memory.Prog Unit :=
  let (d, slot, bit) := x
  do
    let idx := slot &&& d.slotMask
    let addr := d.fullBase + (idx >>> d.pBit)
    let sh := idx &&& d.pBitMask
    let oldWord ← Memory.read addr
    let oldBit := (oldWord >>> sh) &&& 1
    let newWord := oldWord ^^^ ((oldBit ^^^ bit) <<< sh)
    Memory.write addr newWord

private theorem realizes_writeFull :
    Realizes .exact writeFullProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1 ∧ x.2.2 < 2) (fun _ _ => 0) := by
  realize; exacts [masked_addr_lt h.1.full_lt,
    fits_writeBit_newWord (hmem.mem_fits _) (Nat.and_le_right.trans_lt h.1.pBitMask_lt) h.2,
    fits_writeBit_diff_sh (Nat.and_le_right.trans_lt h.1.pBitMask_lt) h.2, h.1.one_lt_two_pow]

/-- Write `isOcc` at slot index `slot &&& d.slotMask` with bit `bit`. -/
private def writeOccProg (x : ClusterInput × (ℕ × ℕ)) : Memory.Prog Unit :=
  let (d, slot, bit) := x
  do
    let idx := slot &&& d.slotMask
    let addr := d.occBase + (idx >>> d.pBit)
    let sh := idx &&& d.pBitMask
    let oldWord ← Memory.read addr
    let oldBit := (oldWord >>> sh) &&& 1
    let newWord := oldWord ^^^ ((oldBit ^^^ bit) <<< sh)
    Memory.write addr newWord

private theorem realizes_writeOcc :
    Realizes .exact writeOccProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1 ∧ x.2.2 < 2) (fun _ _ => 0) := by
  realize; exacts [masked_addr_lt h.1.occ_lt,
    fits_writeBit_newWord (hmem.mem_fits _) (Nat.and_le_right.trans_lt h.1.pBitMask_lt) h.2,
    fits_writeBit_diff_sh (Nat.and_le_right.trans_lt h.1.pBitMask_lt) h.2, h.1.one_lt_two_pow]

/-- Write `isRunStart` at slot index `slot &&& d.slotMask` with bit `bit`. -/
private def writeRunStartProg (x : ClusterInput × (ℕ × ℕ)) : Memory.Prog Unit :=
  let (d, slot, bit) := x
  do
    let idx := slot &&& d.slotMask
    let addr := d.runBase + (idx >>> d.pBit)
    let sh := idx &&& d.pBitMask
    let oldWord ← Memory.read addr
    let oldBit := (oldWord >>> sh) &&& 1
    let newWord := oldWord ^^^ ((oldBit ^^^ bit) <<< sh)
    Memory.write addr newWord

private theorem realizes_writeRunStart :
    Realizes .exact writeRunStartProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1 ∧ x.2.2 < 2) (fun _ _ => 0) := by
  realize; exacts [masked_addr_lt h.1.run_lt,
    fits_writeBit_newWord (hmem.mem_fits _) (Nat.and_le_right.trans_lt h.1.pBitMask_lt) h.2,
    fits_writeBit_diff_sh (Nat.and_le_right.trans_lt h.1.pBitMask_lt) h.2, h.1.one_lt_two_pow]

private theorem fits_rem_sh {w idx mask f : ℕ} (hf : f < w) (hm : (mask + 1) * f ≤ w) :
    (idx &&& mask) * f < w := by
  have h1 : idx &&& mask ≤ mask := Nat.and_le_right
  have h2 : (idx &&& mask) * f ≤ mask * f := Nat.mul_le_mul_right f h1
  have h3 : mask * f + f = (mask + 1) * f := by ring
  rcases Nat.eq_zero_or_pos f with rfl | hf_pos
  · simpa using hf
  · omega

private theorem fits_writeRem_diff_sh {w word idx mask f fMask val : ℕ}
    (hm : (mask + 1) * f ≤ w) (hfMask : fMask < 2 ^ f) (hval : val ≤ fMask) :
    Fits w (((word >>> ((idx &&& mask) * f) &&& fMask) ^^^ val) <<< ((idx &&& mask) * f)) :=
  Fits.mono (Nat.shiftLeft_lt
    (Nat.xor_lt_two_pow (Nat.and_le_right.trans_lt hfMask) (hval.trans_lt hfMask)))
    (by
      have := Nat.mul_le_mul_right f (Nat.and_le_right (n := idx) (m := mask))
      linarith)

/-- Read an `f`-bit remainder entry from `d.remBase` at slot index `x.2 &&& d.slotMask`. -/
private def readRemProg (x : ClusterInput × ℕ) : Memory.Prog ℕ := do
  let idx := x.2 &&& x.1.slotMask
  let wVal ← Memory.read (x.1.remBase + (idx >>> x.1.pRem))
  pure ((wVal >>> ((idx &&& x.1.pRemMask) * x.1.f)) &&& x.1.fMask)

private theorem realizes_readRem :
    Realizes .exact readRemProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1) (fun _ _ => 0) := by
  realize
  · exact masked_addr_lt h.rem_lt
  · exact (fits_rem_sh h.f_lt h.remPack_le).trans Nat.lt_two_pow_self

/-- Write an `f`-bit remainder entry `val ≤ d.fMask` into `d.remBase` at `slot &&& d.slotMask`. -/
private def writeRemProg (x : ClusterInput × (ℕ × ℕ)) : Memory.Prog Unit :=
  let (d, slot, val) := x
  do
    let idx := slot &&& d.slotMask
    let addr := d.remBase + (idx >>> d.pRem)
    let sh := (idx &&& d.pRemMask) * d.f
    let oldWord ← Memory.read addr
    let oldLimb := (oldWord >>> sh) &&& d.fMask
    let newWord := oldWord ^^^ ((oldLimb ^^^ val) <<< sh)
    Memory.write addr newWord

private theorem realizes_writeRem :
    Realizes .exact writeRemProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1 ∧ x.2.2 ≤ x.1.fMask) (fun _ _ => 0) := by
  realize
  · exact masked_addr_lt h.1.rem_lt
  · exact Nat.xor_lt_two_pow (hmem.mem_fits _)
      (fits_writeRem_diff_sh h.1.remPack_le h.1.fMask_lt_f h.2)
  · exact fits_writeRem_diff_sh h.1.remPack_le h.1.fMask_lt_f h.2
  · exact (fits_rem_sh h.1.f_lt h.1.remPack_le).trans Nat.lt_two_pow_self

private theorem clientResult_readFull_le (s : Memory.State) (x : ClusterInput × ℕ) :
    (Memory.spec 0).clientResult s (readFullProg x) ≤ 1 :=
  Nat.and_le_right

private theorem clientState_readFull (s : Memory.State) (x : ClusterInput × ℕ) :
    (Memory.spec 0).clientState s (readFullProg x) = s := rfl

private theorem clientResult_readOcc_le (s : Memory.State) (x : ClusterInput × ℕ) :
    (Memory.spec 0).clientResult s (readOccProg x) ≤ 1 :=
  Nat.and_le_right

private theorem clientState_readOcc (s : Memory.State) (x : ClusterInput × ℕ) :
    (Memory.spec 0).clientState s (readOccProg x) = s := rfl

private theorem clientResult_readRunStart_le (s : Memory.State) (x : ClusterInput × ℕ) :
    (Memory.spec 0).clientResult s (readRunStartProg x) ≤ 1 :=
  Nat.and_le_right

private theorem clientState_readRunStart (s : Memory.State) (x : ClusterInput × ℕ) :
    (Memory.spec 0).clientState s (readRunStartProg x) = s := rfl

private theorem clientResult_readRem_le (s : Memory.State) (x : ClusterInput × ℕ) :
    (Memory.spec 0).clientResult s (readRemProg x) ≤ x.1.fMask :=
  Nat.and_le_right

private theorem clientState_readRem (s : Memory.State) (x : ClusterInput × ℕ) :
    (Memory.spec 0).clientState s (readRemProg x) = s := rfl

/-! ## Section 3: Backward and forward cluster-extent discovery (`findClusterProg`) -/

/-- One step of backward cluster scan: reads `isFull` at `(q + 2^b - (cnt + 1)) &&& (2^b - 1)`
and updates `(cnt, rem)` to `(cnt, 0)` if empty or `(cnt + 1, rem - 1)` if full. -/
private def backLenStep (x : ClusterInput × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) :=
  let (d, cnt, rem) := x
  do
    let rawIdx ← pure (d.qVal + d.slotCap - (cnt + 1))
    let f' ← readFullProg (d, rawIdx)
    if f' = 0 then pure (cnt, 0) else pure (cnt + 1, rem - 1)

private theorem clientResult_backLenStep (t : Memory.State) (x : ClusterInput × (ℕ × ℕ)) :
    (Memory.spec 0).clientResult t (backLenStep x) =
      if (Memory.spec 0).clientResult t
          (readFullProg (x.1, x.1.qVal + x.1.slotCap - (x.2.1 + 1))) = 0
      then (x.2.1, 0) else (x.2.1 + 1, x.2.2 - 1) := by
  change (Memory.spec 0).clientResult t
    (readFullProg (x.1, x.1.qVal + x.1.slotCap - (x.2.1 + 1)) >>=
    (fun f' => if f' = 0 then pure (x.2.1, 0) else pure (x.2.1 + 1, x.2.2 - 1))) = _
  rw [clientResult_bind, clientState_readFull]
  split_ifs <;> rfl

private theorem clientState_backLenStep (t : Memory.State) (x : ClusterInput × (ℕ × ℕ)) :
    (Memory.spec 0).clientState t (backLenStep x) = t := by
  change (Memory.spec 0).clientState t
    (readFullProg (x.1, x.1.qVal + x.1.slotCap - (x.2.1 + 1)) >>=
    (fun f' => if f' = 0 then pure (x.2.1, 0) else pure (x.2.1 + 1, x.2.2 - 1))) = _
  rw [clientState_bind, clientState_readFull]
  split_ifs <;> rfl

/-- Backward cluster scan from `d.qVal` (`q.val`). -/
private def backLenProg (d : ClusterInput) : Memory.Prog (ℕ × ℕ) :=
  boundedWhile (fun _ (st : ℕ × ℕ) => 0 < st.2) backLenStep d d.slotCap (0, d.slotCap)

private theorem realizes_backLen :
    Realizes .exact backLenProg WordEncoding.encode WordEncoding.encode
      (fun w d _ => ClusterSafe w d) (fun _ _ => 0) := by
  realize [realizes_readFull]
  intro hv
  refine whileSafe_of_measure _ _ _ w d
    (fun m _ => m.1 + m.2 ≤ d.slotCap)
    (fun m _ => m.2)
    (fun m _ _ hz hg => by omega) ?_ (by omega) le_rfl hv
  rintro ⟨cnt, rem⟩ t hinv hg _
  have h2w := h.two_cap_lt
  have hd0 := h.q_lt
  refine ⟨⟨⟨by dsimp only; omega, by fits⟩, h, ?_⟩, ?_, ?_⟩
  · split_ifs
    exact ⟨by dsimp only at *; omega, by dsimp only at *; fits⟩
  all_goals (rw [clientResult_backLenStep]; dsimp only; split_ifs <;> omega)

private theorem clientResult_backLen_fst_le (s : Memory.State) (d : ClusterInput) :
    ((Memory.spec 0).clientResult s (backLenProg d)).1 ≤ d.slotCap := by
  dsimp only [backLenProg]
  have h := boundedWhile_invariant_of (fun _ (st : ℕ × ℕ) => 0 < st.2) backLenStep d
    (fun m _ => m.1 + m.2 ≤ d.slotCap)
    (fun ⟨cnt, rem⟩ t hinv hg => by
      rw [clientResult_backLenStep]
      dsimp only at *
      split_ifs <;> omega)
    d.slotCap (0, d.slotCap) s (by omega)
  omega

private theorem clientState_backLen (s : Memory.State) (d : ClusterInput) :
    (Memory.spec 0).clientState s (backLenProg d) = s :=
  clientState_boundedWhile_eq_of _ backLenStep d
    (fun _ t _ => clientState_backLenStep t _) _ _ s

/-- One step of forward cluster scan: reads `isFull` at `(q + cnt) &&& (2^b - 1)`
and updates `(cnt, rem)` to `(cnt, 0)` if empty or `(cnt + 1, rem - 1)` if full. -/
private def fwdLenStep (x : ClusterInput × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) :=
  let (d, cnt, rem) := x
  do
    let rawIdx ← pure (d.qVal + cnt)
    let f' ← readFullProg (d, rawIdx)
    if f' = 0 then pure (cnt, 0) else pure (cnt + 1, rem - 1)

private theorem clientResult_fwdLenStep (t : Memory.State) (x : ClusterInput × (ℕ × ℕ)) :
    (Memory.spec 0).clientResult t (fwdLenStep x) =
      if (Memory.spec 0).clientResult t (readFullProg (x.1, x.1.qVal + x.2.1)) = 0
      then (x.2.1, 0) else (x.2.1 + 1, x.2.2 - 1) := by
  change (Memory.spec 0).clientResult t (readFullProg (x.1, x.1.qVal + x.2.1) >>=
    (fun f' => if f' = 0 then pure (x.2.1, 0) else pure (x.2.1 + 1, x.2.2 - 1))) = _
  rw [clientResult_bind, clientState_readFull]
  split_ifs <;> rfl

private theorem clientState_fwdLenStep (t : Memory.State) (x : ClusterInput × (ℕ × ℕ)) :
    (Memory.spec 0).clientState t (fwdLenStep x) = t := by
  change (Memory.spec 0).clientState t (readFullProg (x.1, x.1.qVal + x.2.1) >>=
    (fun f' => if f' = 0 then pure (x.2.1, 0) else pure (x.2.1 + 1, x.2.2 - 1))) = _
  rw [clientState_bind, clientState_readFull]
  split_ifs <;> rfl

/-- Forward cluster scan from `d.qVal` (`q.val`) with remaining budget `d.slotCap - a`. -/
private def fwdLenProg (x : ClusterInput × ℕ) : Memory.Prog (ℕ × ℕ) :=
  boundedWhile (fun _ (st : ℕ × ℕ) => 0 < st.2) fwdLenStep x.1 x.1.slotCap (0, x.1.slotCap - x.2)

private theorem realizes_fwdLen :
    Realizes .exact fwdLenProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1 ∧ x.2 ≤ x.1.slotCap) (fun _ _ => 0) := by
  realize [realizes_readFull]
  · exact h.2
  · intro hv
    refine whileSafe_of_measure _ _ _ w d.1
      (fun m _ => m.1 + m.2 ≤ d.1.slotCap - d.2)
      (fun m _ => m.2)
      (fun m _ _ hz hg => by omega) ?_ (by omega) (by have := h.2; omega) hv
    rintro ⟨cnt, rem⟩ t hinv hg _
    have h2w := h.1.two_cap_lt
    have hd0 := h.1.q_lt
    have ha := h.2
    refine ⟨⟨by dsimp only; fits, h.1, ?_⟩, ?_, ?_⟩
    · split_ifs
      exact ⟨by dsimp only at *; omega, by dsimp only at *; fits⟩
    all_goals (rw [clientResult_fwdLenStep]; dsimp only; split_ifs <;> omega)

private theorem clientResult_fwdLen_fst_le (s : Memory.State) (x : ClusterInput × ℕ) :
    ((Memory.spec 0).clientResult s (fwdLenProg x)).1 ≤ x.1.slotCap - x.2 := by
  dsimp only [fwdLenProg]
  have h := boundedWhile_invariant_of (fun _ (st : ℕ × ℕ) => 0 < st.2) fwdLenStep x.1
    (fun m _ => m.1 + m.2 ≤ x.1.slotCap - x.2)
    (fun ⟨cnt, rem⟩ t hinv hg => by
      rw [clientResult_fwdLenStep]
      dsimp only at *
      split_ifs <;> omega)
    x.1.slotCap (0, x.1.slotCap - x.2) s (by omega)
  omega

private theorem clientState_fwdLen (s : Memory.State) (x : ClusterInput × ℕ) :
    (Memory.spec 0).clientState s (fwdLenProg x) = s :=
  clientState_boundedWhile_eq_of _ fwdLenStep x.1
    (fun _ t _ => clientState_fwdLenStep t _) _ _ s

/-- Find the cluster extent `(o, (a, ℓ))` around `d.qVal` (`q.val`). -/
private def findClusterProg (d : ClusterInput) : Memory.Prog (ℕ × (ℕ × ℕ)) := do
  let backRes ← backLenProg d
  let fwdRes ← fwdLenProg (d, backRes.1)
  pure ((d.qVal + d.slotCap - backRes.1) &&& d.slotMask, (backRes.1, backRes.1 + fwdRes.1))

private theorem backLen_add_fwdLen_le (s : Memory.State) (d : ClusterInput) :
    ((Memory.spec 0).clientResult s (backLenProg d)).1 +
      ((Memory.spec 0).clientResult ((Memory.spec 0).clientState s (backLenProg d))
        (fwdLenProg (d, ((Memory.spec 0).clientResult s (backLenProg d)).1))).1 ≤ d.slotCap := by
  have ha := clientResult_backLen_fst_le s d
  have ht := clientResult_fwdLen_fst_le ((Memory.spec 0).clientState s (backLenProg d))
    (d, ((Memory.spec 0).clientResult s (backLenProg d)).1)
  dsimp only at ht
  omega

private theorem realizes_findCluster :
    Realizes .exact findClusterProg WordEncoding.encode WordEncoding.encode
      (fun w d _ => ClusterSafe w d) (fun _ _ => 0) := by
  realize [realizes_backLen, realizes_fwdLen]
  · exact h
  · exact clientResult_backLen_fst_le s d
  · have := clientResult_backLen_fst_le s d
    have := h.q_lt; have := h.two_cap_lt; omega
  · fits [h.q_lt, h.two_cap_le]
  · fits [backLen_add_fwdLen_le s d, h.two_cap_le]

private theorem clientResult_findCluster_bounds {w : ℕ} (s : Memory.State) (d : ClusterInput)
    (h : ClusterSafe w d) :
    let res := (Memory.spec 0).clientResult s (findClusterProg d)
    res.1 < d.slotCap ∧ res.2.1 ≤ res.2.2 ∧ res.2.2 ≤ d.slotCap := by
  dsimp only
  unfold findClusterProg
  rw [clientResult_bind, clientResult_bind,
    clientResult_pure]
  dsimp only
  exact ⟨Nat.and_le_right.trans_lt h.mask_lt, Nat.le_add_right _ _, backLen_add_fwdLen_le s d⟩

private theorem clientState_findCluster (s : Memory.State) (d : ClusterInput) :
    (Memory.spec 0).clientState s (findClusterProg d) = s := by
  unfold findClusterProg
  rw [clientState_bind, clientState_bind,
    clientState_pure, clientState_fwdLen, clientState_backLen]

/-! ## Section 4: Prefix `occBefore` and full cluster scan (`scanClusterProg`) -/

/-- One step of `occBefore` prefix scan: reads `isOcc` at `o + m` and increments `(m, occ)`. -/
private def occBeforeStep (x : (ClusterInput × ℕ) × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) :=
  let ((d, o), m, occ) := x
  do
    let rawIdx ← pure (o + m)
    let occBit ← readOccProg (d, rawIdx)
    pure (m + 1, occ + occBit)

private theorem clientResult_occBeforeStep (t : Memory.State) (x : (ClusterInput × ℕ) × (ℕ × ℕ)) :
    (Memory.spec 0).clientResult t (occBeforeStep x) =
      (x.2.1 + 1, x.2.2 + (Memory.spec 0).clientResult t (readOccProg (x.1.1, x.1.2 + x.2.1))) := by
  change (Memory.spec 0).clientResult t (readOccProg (x.1.1, x.1.2 + x.2.1) >>=
    (fun occBit => pure (x.2.1 + 1, x.2.2 + occBit))) = _
  rw [clientResult_bind, clientResult_pure]

private theorem clientState_occBeforeStep (t : Memory.State) (x : (ClusterInput × ℕ) × (ℕ × ℕ)) :
    (Memory.spec 0).clientState t (occBeforeStep x) = t := by
  change (Memory.spec 0).clientState t (readOccProg (x.1.1, x.1.2 + x.2.1) >>=
    (fun occBit => pure (x.2.1 + 1, x.2.2 + occBit))) = _
  rw [clientState_bind, clientState_pure, clientState_readOcc]

/-- Compute `(a, occBefore st o a)` by iterating `occBeforeStep` `a` times from `(0, 0)`. -/
private def occBeforeProg (x : ClusterInput × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) :=
  let (d, o, a) := x
  iterate occBeforeStep (d, o) a (0, 0)

private theorem realizes_occBefore :
    Realizes .exact occBeforeProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1 ∧ x.2.1 < x.1.slotCap ∧ x.2.2 ≤ x.1.slotCap)
      (fun _ _ => 0) := by
  realize [realizes_readOcc]
  rcases d with ⟨d0, o, a⟩
  obtain ⟨hcs, ho, ha⟩ := h
  have h2w := hcs.two_cap_lt
  dsimp only at h2w ho ha
  refine iterationSafe_of_stepInv _ _ w (d0, o, a)
    (fun j (m : ℕ × ℕ) _ => m.1 + j = a ∧ m.2 ≤ m.1) ?_ ⟨by simp, by simp⟩
  rintro j ⟨m, occ⟩ t ⟨hmj, hocc⟩
  have hb := clientResult_readOcc_le t (d0, o + m)
  refine ⟨⟨by dsimp only at *; fits, hcs, by dsimp only at *; fits, by dsimp only at *; fits⟩, ?_⟩
  rw [clientResult_occBeforeStep]
  dsimp only at *
  omega

private theorem clientResult_occBefore_bounds (s : Memory.State) (x : ClusterInput × (ℕ × ℕ)) :
    let res := (Memory.spec 0).clientResult s (occBeforeProg x)
    res.1 = x.2.2 ∧ res.2 ≤ x.2.2 := by
  rcases x with ⟨d, o, a⟩
  have h := iterate_invariant_of occBeforeStep (d, o)
    (fun j m _ => m.1 + j = a ∧ m.2 ≤ m.1)
    (fun j ⟨m, occ⟩ t ⟨hmj, hocc⟩ => by
      have hb := clientResult_readOcc_le t (d, o + m)
      rw [clientResult_occBeforeStep]
      dsimp only at *
      omega)
    (n := a) (a := (0, 0)) (s := s) ⟨by omega, by omega⟩
  dsimp only [occBeforeProg]
  omega

private theorem clientState_occBefore (s : Memory.State) (x : ClusterInput × (ℕ × ℕ)) :
    (Memory.spec 0).clientState s (occBeforeProg x) = s :=
  clientState_iterate_eq_of occBeforeStep (x.1, x.2.1)
    (fun _ t => clientState_occBeforeStep t _) _ _ s

/-- Environment of the cluster scan `scanLoopProg`. The words are listed in the order
`((d, (o, (a, ℓ))), (occA, occA1))`. -/
@[ext] structure ScanEnv where
  /-- Cluster operation input. -/
  d : ClusterInput
  /-- Cluster start slot. -/
  o : ℕ
  /-- Offset of the target quotient within the cluster. -/
  a : ℕ
  /-- Cluster length. -/
  ℓ : ℕ
  /-- Occupied quotients before the target, `occBefore st o a`. -/
  occA : ℕ
  /-- Occupied quotients up to and including the target, `occBefore st o (a + 1)`. -/
  occA1 : ℕ

/-- The word layout of a `ScanEnv`. -/
@[expose] def ScanEnv.equiv : ScanEnv ≃ (ClusterInput × (ℕ × (ℕ × ℕ))) × (ℕ × ℕ) where
  toFun env := ((env.d, (env.o, (env.a, env.ℓ))), (env.occA, env.occA1))
  invFun := fun ((d, (o, (a, ℓ))), (occA, occA1)) => ⟨d, o, a, ℓ, occA, occA1⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding ScanEnv := .ofEquiv ScanEnv.equiv

/-- Loop state of the cluster scan after `i` slots. The words are listed in the order
`((i, (runs, occI)), ((s₀, s), (e, qFound)))`. -/
@[ext] structure ScanState where
  /-- Slots scanned so far. -/
  i : ℕ
  /-- Run starts among the scanned slots. -/
  runs : ℕ
  /-- Occupied quotients among the scanned slots. -/
  occI : ℕ
  /-- Start of the target run, `calcRunStart`. -/
  s₀ : ℕ
  /-- Insertion target slot, `calcTargetSlot`. -/
  s : ℕ
  /-- End of the shift for a delete, `calcDeleteStop`. -/
  e : ℕ
  /-- Whether the target remainder was found (`0` or `1`), `queryAnyPrefix`. -/
  qFound : ℕ

/-- The word layout of a `ScanState`. -/
@[expose] def ScanState.equiv : ScanState ≃ (ℕ × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ)) where
  toFun m := ((m.i, (m.runs, m.occI)), ((m.s₀, m.s), (m.e, m.qFound)))
  invFun := fun ((i, (runs, occI)), ((s₀, s), (e, qFound))) => ⟨i, runs, occI, s₀, s, e, qFound⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding ScanState := .ofEquiv ScanState.equiv

/-- Bounds on the scan environment at word width `w`. -/
private def ScanEnv.Safe (w : ℕ) (env : ScanEnv) : Prop :=
  ClusterSafe w env.d ∧ env.o < env.d.slotCap ∧ env.a ≤ env.ℓ ∧ env.ℓ ≤ env.d.slotCap ∧
    env.occA ≤ env.d.slotCap ∧ env.occA1 ≤ env.d.slotCap + 1

/-- Bounds kept by the scan state: the counters and targets are at most the slots scanned, the
delete stop is at most the cluster length, and `qFound` is a bit. -/
private def ScanState.Bounds (env : ScanEnv) (m : ScanState) : Prop :=
  m.runs ≤ m.i ∧ m.occI ≤ m.i ∧ m.s₀ ≤ m.i ∧ m.s ≤ m.i ∧ m.e ≤ env.ℓ ∧ m.qFound ≤ 1

/-- Safety predicate for one step of `scanLoopProg`. -/
private def ScanStepSafe (w : ℕ) (x : ScanEnv × ScanState) : Prop :=
  x.1.Safe w ∧ x.2.i < x.1.ℓ ∧ x.2.Bounds x.1

/-- The three bits and fields read at one slot of the scan. The words are listed in the order
`(occ, (run, rem))`. -/
@[ext] private structure ScanReads where
  /-- Occupied bit. -/
  occ : ℕ
  /-- Run-start bit. -/
  run : ℕ
  /-- Stored remainder. -/
  rem : ℕ

/-- The word layout of a `ScanReads`. -/
private def ScanReads.equiv : ScanReads ≃ ℕ × (ℕ × ℕ) where
  toFun r := (r.occ, (r.run, r.rem))
  invFun := fun (occ, (run, rem)) => ⟨occ, run, rem⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding ScanReads := .ofEquiv ScanReads.equiv

/-- Read the occupied bit, run-start bit and remainder at slot offset `o + i`. -/
private def scanStepReadsProg (x : ScanEnv × ScanState) : Memory.Prog ScanReads := do
  let rawIdx ← pure (x.1.o + x.2.i)
  let occBit ← readOccProg (x.1.d, rawIdx)
  let runBit ← readRunStartProg (x.1.d, rawIdx)
  let remVal ← readRemProg (x.1.d, rawIdx)
  pure ⟨occBit, runBit, remVal⟩

private theorem realizes_scanStepReads :
    Realizes .exact scanStepReadsProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1.d ∧ x.1.o + x.2.i < 2 ^ w) (fun _ _ => 0) := by
  realize [realizes_readOcc, realizes_readRunStart, realizes_readRem]
  · exact h.2
  · exact h.1

private theorem clientResult_scanStepReads (t : Memory.State) (x : ScanEnv × ScanState) :
    (Memory.spec 0).clientResult t (scanStepReadsProg x) =
      ⟨(Memory.spec 0).clientResult t (readOccProg (x.1.d, x.1.o + x.2.i)),
        (Memory.spec 0).clientResult t (readRunStartProg (x.1.d, x.1.o + x.2.i)),
        (Memory.spec 0).clientResult t (readRemProg (x.1.d, x.1.o + x.2.i))⟩ := by
  unfold scanStepReadsProg
  rw [clientResult_bind, clientResult_pure, clientState_pure,
    clientResult_bind, clientState_readOcc,
    clientResult_bind, clientState_readRunStart,
    clientResult_bind, clientState_readRem, clientResult_pure]

private theorem clientState_scanStepReads (t : Memory.State) (x : ScanEnv × ScanState) :
    (Memory.spec 0).clientState t (scanStepReadsProg x) = t := by
  unfold scanStepReadsProg
  rw [clientState_bind, clientResult_pure, clientState_pure,
    clientState_bind, clientState_readOcc,
    clientState_bind, clientState_readRunStart,
    clientState_bind, clientState_readRem, clientState_pure]

/-- Input of the target, stop and query updates in one step of `scanLoopProg`: the environment,
the state before the step, the run count including the current slot, and the current slot's
remainder. The words are listed in the order `((env, st), (runs, rem))`. -/
structure ScanStepCtx where
  /-- Scan environment. -/
  env : ScanEnv
  /-- State before the step. -/
  st : ScanState
  /-- Run starts up to and including the current slot. -/
  runs : ℕ
  /-- Remainder stored at the current slot. -/
  rem : ℕ

/-- The word layout of a `ScanStepCtx`. -/
@[expose] def ScanStepCtx.equiv : ScanStepCtx ≃ (ScanEnv × ScanState) × (ℕ × ℕ) where
  toFun c := ((c.env, c.st), (c.runs, c.rem))
  invFun := fun ((env, st), (runs, rem)) => ⟨env, st, runs, rem⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding ScanStepCtx := .ofEquiv ScanStepCtx.equiv

/-- Update `(s₀, s)` during one step of `scanLoopProg`. -/
@[expose] def scanStepTargetProg (c : ScanStepCtx) : Memory.Prog (ℕ × ℕ) :=
  if c.runs ≤ c.env.occA then
    pure (c.st.s₀ + 1, c.st.s + 1)
  else if c.runs ≤ c.env.occA1 then
    if c.rem < c.env.d.rVal then pure (c.st.s₀, c.st.s + 1) else pure (c.st.s₀, c.st.s)
  else
    pure (c.st.s₀, c.st.s)

private theorem realizes_scanStepTarget :
    Realizes .exact scanStepTargetProg WordEncoding.encode WordEncoding.encode
      (fun w c _ => c.st.s₀ + 1 < 2 ^ w ∧ c.st.s + 1 < 2 ^ w)
      (fun _ _ => 0) := by
  realize <;> fits [h.1, h.2]

private theorem clientResult_scanStepTarget (t : Memory.State) (c : ScanStepCtx) :
    (Memory.spec 0).clientResult t (scanStepTargetProg c) =
      (if c.runs ≤ c.env.occA then c.st.s₀ + 1 else c.st.s₀,
        if c.runs ≤ c.env.occA ∨ (c.runs ≤ c.env.occA1 ∧ c.rem < c.env.d.rVal)
        then c.st.s + 1 else c.st.s) := by
  unfold scanStepTargetProg
  split_ifs <;> simp only [clientResult_pure, Prod.mk.injEq] <;> omega

private theorem clientState_scanStepTarget (t : Memory.State) (c : ScanStepCtx) :
    (Memory.spec 0).clientState t (scanStepTargetProg c) = t := by
  unfold scanStepTargetProg
  split_ifs <;> rfl

/-- Update `e` (`calcDeleteStop`) during one step of `scanLoopProg`. -/
private def scanStepStopProg (c : ScanStepCtx) : Memory.Prog ℕ :=
  if c.env.a < c.st.i then
    if c.st.occI < c.runs then
      if c.st.e = c.env.ℓ then pure c.st.i else pure c.st.e
    else pure c.st.e
  else pure c.st.e

private theorem realizes_scanStepStop :
    Realizes .exact scanStepStopProg WordEncoding.encode WordEncoding.encode
      (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

private theorem clientResult_scanStepStop (t : Memory.State) (c : ScanStepCtx) :
    (Memory.spec 0).clientResult t (scanStepStopProg c) =
      if c.env.a < c.st.i ∧ c.st.occI < c.runs ∧ c.st.e = c.env.ℓ
      then c.st.i else c.st.e := by
  unfold scanStepStopProg
  split_ifs <;> simp only [clientResult_pure] <;> tauto

private theorem clientState_scanStepStop (t : Memory.State) (c : ScanStepCtx) :
    (Memory.spec 0).clientState t (scanStepStopProg c) = t := by
  unfold scanStepStopProg
  split_ifs <;> rfl

/-- Update `qFound` (`queryAnyPrefix`) during one step of `scanLoopProg`. -/
@[expose] def scanStepQueryProg (c : ScanStepCtx) : Memory.Prog ℕ :=
  if c.env.occA < c.runs then
    if c.runs ≤ c.env.occA1 then
      if c.rem = c.env.d.rVal then pure 1 else pure c.st.qFound
    else pure c.st.qFound
  else pure c.st.qFound

theorem realizes_scanStepQuery :
    Realizes .exact scanStepQueryProg WordEncoding.encode WordEncoding.encode
      (fun w _ _ => 1 < 2 ^ w) (fun _ _ => 0) := by
  realize
  exact h

private theorem clientResult_scanStepQuery (t : Memory.State) (c : ScanStepCtx) :
    (Memory.spec 0).clientResult t (scanStepQueryProg c) =
      if (c.env.occA < c.runs ∧ c.runs ≤ c.env.occA1) ∧ c.rem = c.env.d.rVal
      then 1 else c.st.qFound := by
  unfold scanStepQueryProg
  split_ifs <;> simp only [clientResult_pure] <;> omega

private theorem clientState_scanStepQuery (t : Memory.State) (c : ScanStepCtx) :
    (Memory.spec 0).clientState t (scanStepQueryProg c) = t := by
  unfold scanStepQueryProg
  split_ifs <;> rfl

/-- One step of the cluster scan over `i ∈ [0, ℓ)`. -/
private def scanLoopStep (x : ScanEnv × ScanState) : Memory.Prog ScanState := do
  let reads ← scanStepReadsProg x
  let runs ← pure (x.2.runs + reads.run)
  let tgt ← scanStepTargetProg ⟨x.1, x.2, runs, reads.rem⟩
  let e ← scanStepStopProg ⟨x.1, x.2, runs, reads.rem⟩
  let qFound ← scanStepQueryProg ⟨x.1, x.2, runs, reads.rem⟩
  pure ⟨x.2.i + 1, runs, x.2.occI + reads.occ, tgt.1, tgt.2, e, qFound⟩

private theorem realizes_scanLoopStep :
    Realizes .exact scanLoopStep WordEncoding.encode WordEncoding.encode
      (fun w x _ => ScanStepSafe w x) (fun _ _ => 0) := by
  realize [realizes_scanStepReads, realizes_scanStepTarget, realizes_scanStepStop,
      realizes_scanStepQuery] <;> {
    rcases h with ⟨⟨hcs, ho, ha, hℓ, hoccA, hoccA1⟩, hi, hruns, hoccI, hs₀, hs, he, hq⟩
    have h2w := hcs.two_cap_lt
    have h1w := hcs.one_lt_two_pow
    first
    | exact hcs
    | exact h1w
    | {
        have hb_occ := clientResult_readOcc_le s (d.1.d, d.1.o + d.2.i)
        have hb_run := clientResult_readRunStart_le s (d.1.d, d.1.o + d.2.i)
        try rw [clientResult_scanStepReads]
        try dsimp only at *
        fits
      }
  }

private theorem clientState_scanLoopStep (t : Memory.State) (x : ScanEnv × ScanState) :
    (Memory.spec 0).clientState t (scanLoopStep x) = t := by
  unfold scanLoopStep
  rw [clientState_bind, clientState_scanStepReads,
    clientState_bind, clientResult_pure, clientState_pure,
    clientState_bind, clientState_scanStepTarget,
    clientState_bind, clientState_scanStepStop,
    clientState_bind, clientState_scanStepQuery, clientState_pure]

/-- One scan step advances `i` and keeps `ScanState.Bounds`. -/
private theorem clientResult_scanLoopStep_bounds (t : Memory.State) (x : ScanEnv × ScanState)
    (hi : x.2.i < x.1.ℓ) (hb : x.2.Bounds x.1) :
    let res := (Memory.spec 0).clientResult t (scanLoopStep x)
    res.i = x.2.i + 1 ∧ res.Bounds x.1 := by
  rcases hb with ⟨hruns, hoccI, hs₀, hs, he, hq⟩
  dsimp only
  unfold scanLoopStep
  rw [clientResult_bind, clientState_scanStepReads,
    clientResult_bind, clientResult_pure, clientState_pure,
    clientResult_bind, clientState_scanStepTarget,
    clientResult_bind, clientState_scanStepStop,
    clientResult_bind, clientState_scanStepQuery, clientResult_pure,
    clientResult_scanStepTarget, clientResult_scanStepStop, clientResult_scanStepQuery,
    clientResult_scanStepReads]
  dsimp only [ScanState.Bounds]
  have hb_occ := clientResult_readOcc_le t (x.1.d, x.1.o + x.2.i)
  have hb_run := clientResult_readRunStart_le t (x.1.d, x.1.o + x.2.i)
  split_ifs <;> refine ⟨rfl, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- Iterate `scanLoopStep` `ℓ` times from `⟨0, 0, 0, 0, 0, ℓ, 0⟩`. -/
private def scanLoopProg (env : ScanEnv) : Memory.Prog ScanState :=
  iterate scanLoopStep env env.ℓ ⟨0, 0, 0, 0, 0, env.ℓ, 0⟩

private theorem realizes_scanLoop :
    Realizes .exact scanLoopProg WordEncoding.encode WordEncoding.encode
      (fun w env _ => env.Safe w) (fun _ _ => 0) := by
  realize [realizes_scanLoopStep]
  refine iterationSafe_of_stepInv _ _ w d
    (fun j (m : ScanState) _ => m.i + j = d.ℓ ∧ m.Bounds d) ?_
    ⟨Nat.zero_add _, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, Nat.zero_le 1⟩
  rintro j m t ⟨hij, hb⟩
  have hi : m.i < d.ℓ := by omega
  obtain ⟨hi', hb'⟩ := clientResult_scanLoopStep_bounds t (d, m) hi hb
  dsimp only at hi'
  exact ⟨⟨h, hi, hb⟩, by omega, hb'⟩

private theorem clientResult_scanLoop_bounds (s : Memory.State) (env : ScanEnv) :
    let res := (Memory.spec 0).clientResult s (scanLoopProg env)
    res.i = env.ℓ ∧ res.Bounds env := by
  dsimp only [scanLoopProg]
  have h := iterate_invariant_of scanLoopStep env
    (fun j (m : ScanState) _ => m.i + j = env.ℓ ∧ m.Bounds env)
    (fun j m t ⟨hij, hb⟩ => by
      have hi : m.i < env.ℓ := by omega
      obtain ⟨hi', hb'⟩ := clientResult_scanLoopStep_bounds t (env, m) hi hb
      dsimp only at hi'
      exact ⟨by omega, hb'⟩)
    (n := env.ℓ) (a := ⟨0, 0, 0, 0, 0, env.ℓ, 0⟩) (s := s)
    ⟨Nat.zero_add _, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, Nat.zero_le 1⟩
  exact ⟨h.1, h.2⟩

private theorem clientState_scanLoop (s : Memory.State) (env : ScanEnv) :
    (Memory.spec 0).clientState s (scanLoopProg env) = s :=
  clientState_iterate_eq_of scanLoopStep env (fun _ t => clientState_scanLoopStep t _) _ _ s

/-- Result of the full cluster scan `scanClusterProg`. The words are listed in the order
`(occQ, ((s₀, s), (e, qFound)))`. -/
@[ext] private structure ScanResult where
  /-- Whether the target quotient is occupied (`0` or `1`). -/
  occQ : ℕ
  /-- Start of the target run, `calcRunStart`. -/
  s₀ : ℕ
  /-- Insertion target slot, `calcTargetSlot`. -/
  s : ℕ
  /-- End of the shift for a delete, `calcDeleteStop`. -/
  e : ℕ
  /-- Whether the target remainder was found (`0` or `1`), `queryAnyPrefix`. -/
  qFound : ℕ

/-- The word layout of a `ScanResult`. -/
private def ScanResult.equiv : ScanResult ≃ ℕ × ((ℕ × ℕ) × (ℕ × ℕ)) where
  toFun r := (r.occQ, ((r.s₀, r.s), (r.e, r.qFound)))
  invFun := fun (occQ, ((s₀, s), (e, qFound))) => ⟨occQ, s₀, s, e, qFound⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding ScanResult := .ofEquiv ScanResult.equiv

/-- Bounds on a scan of a cluster of length `ℓ`: the two flags are bits and the run start,
target slot and delete stop are at most `ℓ`. -/
private def ScanResult.Bounds (ℓ : ℕ) (r : ScanResult) : Prop :=
  r.occQ ≤ 1 ∧ r.s₀ ≤ ℓ ∧ r.s ≤ ℓ ∧ r.e ≤ ℓ ∧ r.qFound ≤ 1

/-- Full cluster scan of the cluster at `x = (d, (o, (a, ℓ)))`. -/
private def scanClusterProg (x : ClusterInput × (ℕ × (ℕ × ℕ))) : Memory.Prog ScanResult :=
  let (d, o, a, ℓ) := x
  do
    let occRes ← occBeforeProg (d, (o, a))
    let occQ ← readOccProg (d, d.qVal)
    let occA1 ← pure (occRes.2 + occQ)
    let m ← scanLoopProg ⟨d, o, a, ℓ, occRes.2, occA1⟩
    pure ⟨occQ, m.s₀, m.s, m.e, m.qFound⟩

private theorem realizes_scanCluster :
    Realizes .exact scanClusterProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1 ∧ x.2.1 < x.1.slotCap ∧
        x.2.2.1 ≤ x.2.2.2 ∧ x.2.2.2 ≤ x.1.slotCap) (fun _ _ => 0) := by
  realize [realizes_occBefore, realizes_readOcc, realizes_scanLoop] <;> {
    first
    | exact h.1
    | exact h.2.1
    | exact h.2.2.1.trans h.2.2.2
    | {
        have h_occ := (clientResult_occBefore_bounds s (d.1, d.2.1, d.2.2.1)).2
        have h_occQ := clientResult_readOcc_le s (d.1, d.1.qVal)
        rw [clientState_occBefore]
        rcases d with ⟨d0, o, a, ℓ⟩; rcases h with ⟨hcs, ho, ha, hℓ⟩
        have h2w := hcs.two_cap_lt
        first
        | (dsimp only at h2w ha hℓ h_occ h_occQ ⊢; fits)
        | exact ⟨hcs, ho, ha, hℓ, by dsimp only at *; omega, by dsimp only at *; omega⟩
      }
  }

private theorem clientResult_scanCluster_bounds (s : Memory.State)
    (x : ClusterInput × (ℕ × (ℕ × ℕ))) :
    ((Memory.spec 0).clientResult s (scanClusterProg x)).Bounds x.2.2.2 := by
  rcases x with ⟨d, o, a, ℓ⟩
  unfold scanClusterProg
  rw [clientResult_bind, clientState_occBefore,
    clientResult_bind, clientState_readOcc,
    clientResult_bind, clientResult_pure, clientState_pure,
    clientResult_bind, clientState_scanLoop, clientResult_pure]
  have h_occQ := clientResult_readOcc_le s (d, d.qVal)
  obtain ⟨hi, _, _, hs₀, hs, he, hq⟩ := clientResult_scanLoop_bounds s
    ⟨d, o, a, ℓ,
      ((Memory.spec 0).clientResult s (occBeforeProg (d, o, a))).2,
      ((Memory.spec 0).clientResult s (occBeforeProg (d, o, a))).2 +
        (Memory.spec 0).clientResult s (readOccProg (d, d.qVal))⟩
  exact ⟨h_occQ, by dsimp only at hi ⊢; omega, by dsimp only at hi ⊢; omega, he, hq⟩

private theorem clientState_scanCluster (s : Memory.State) (x : ClusterInput × (ℕ × (ℕ × ℕ))) :
    (Memory.spec 0).clientState s (scanClusterProg x) = s := by
  unfold scanClusterProg
  rw [clientState_bind, clientState_occBefore,
    clientState_bind, clientState_readOcc,
    clientState_bind, clientResult_pure, clientState_pure,
    clientState_bind, clientState_scanLoop, clientState_pure]

/-! ## Section 5: Right-Shift Loop and `insertAfterScanProg` -/

/-- One step of the right-shift loop: copies `(isRunStart, remAt)` from `o + (pos - 1)` to
`o + pos` and decrements `pos`. -/
private def shiftRightStep (x : (ClusterInput × ℕ) × ℕ) : Memory.Prog ℕ :=
  let ((d, o), pos) := x
  do
    let src ← pure (o + (pos - 1))
    let dst ← pure (o + pos)
    let runBit ← readRunStartProg (d, src)
    let remVal ← readRemProg (d, src)
    let _ ← writeRunStartProg (d, (dst, runBit))
    let _ ← writeRemProg (d, (dst, remVal))
    pure (pos - 1)

private theorem realizes_shiftRightStep :
    Realizes .exact shiftRightStep WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1.1 ∧ x.1.2 < x.1.1.slotCap ∧ 1 ≤ x.2 ∧ x.2 ≤ x.1.1.slotCap)
      (fun _ _ => 0) := by
  realize [realizes_readRunStart, realizes_readRem, realizes_writeRunStart, realizes_writeRem] <;> {
    rcases d with ⟨⟨d0, o⟩, pos⟩
    rcases h with ⟨hcs, ho, h1, hpos⟩
    have h2w := hcs.two_cap_lt
    first
    | exact hcs
    | {
        have hb_run := clientResult_readRunStart_le s (d0, o + (pos - 1))
        have hb_rem := clientResult_readRem_le
          ((Memory.spec 0).clientState s (readRunStartProg (d0, o + (pos - 1))))
          (d0, o + (pos - 1))
        dsimp only at *
        first | fits [hcs.fMask_lt] | omega
      }
  }

private theorem clientResult_shiftRightStep (t : Memory.State) (x : (ClusterInput × ℕ) × ℕ) :
    (Memory.spec 0).clientResult t (shiftRightStep x) = x.2 - 1 := by
  unfold shiftRightStep
  rw [clientResult_bind, clientResult_pure, clientState_pure,
    clientResult_bind, clientResult_pure, clientState_pure,
    clientResult_bind, clientState_readRunStart,
    clientResult_bind, clientState_readRem,
    clientResult_bind,
    clientResult_bind, clientResult_pure]

/-- Iterate `shiftRightStep` `count` times starting at `pos`. -/
private def shiftRightProg (x : (ClusterInput × ℕ) × (ℕ × ℕ)) : Memory.Prog ℕ :=
  let (env, pos, count) := x
  iterate shiftRightStep env count pos

private theorem realizes_shiftRight :
    Realizes .exact shiftRightProg WordEncoding.encode WordEncoding.encode
      (fun w x _ =>
        ClusterSafe w x.1.1 ∧ x.1.2 < x.1.1.slotCap ∧ x.2.2 ≤ x.2.1 ∧ x.2.1 ≤ x.1.1.slotCap)
      (fun _ _ => 0) := by
  realize [realizes_shiftRightStep]
  refine iterationSafe_of_stepInv _ _ w d
    (fun j (pos : ℕ) _ => j ≤ pos ∧ pos ≤ d.2.1)
    ?_ ⟨h.2.2.1, le_rfl⟩
  rintro j pos t ⟨hj, hpos⟩
  rcases h with ⟨hcs, ho, hle, hmax⟩
  refine ⟨⟨hcs, ho, by change 1 ≤ pos; omega, by change pos ≤ d.1.1.slotCap; omega⟩, ?_⟩
  rw [clientResult_shiftRightStep]
  exact ⟨by dsimp only; omega, by dsimp only; omega⟩

/-- Clear old `isRunStart` at `o + s₀` when `occQ = 1` and `s = s₀`. -/
private def insertClearOldProg (x : (ClusterInput × ℕ) × (ℕ × (ℕ × ℕ))) : Memory.Prog Unit :=
  let ((d, o), occQ, s₀, s) := x
  do
    let idx ← pure (o + s₀)
    let z ← pure 0
    if occQ = 1 then
      if s = s₀ then
        writeRunStartProg (d, (idx, z))
      else
        pure ()
    else
      pure ()

private theorem realizes_insertClearOld :
    Realizes .exact insertClearOldProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1.1 ∧ x.1.2 + x.2.2.1 < 2 ^ w) (fun _ _ => 0) := by
  realize [realizes_writeRunStart] <;> {
    rcases h with ⟨hcs, hlt⟩
    have h1w := hcs.one_lt_two_pow
    first
    | exact hcs
    | exact hlt
    | exact h1w
    | { omega }
  }

/-- Write the newly inserted slot at `o + s`, set `isOcc` at `q`, and set `isFull` at `o + ℓ`. -/
private def insertWriteNewProg (x : (ClusterInput × ℕ) × ((ℕ × ℕ) × ℕ)) : Memory.Prog ℕ :=
  let ((d, o), (s₀, s), ℓ) := x
  do
    let isStart ← pure (if s = s₀ then 1 else 0)
    let dstS ← pure (o + s)
    let dstL ← pure (o + ℓ)
    let one ← pure 1
    let _ ← writeRunStartProg (d, (dstS, isStart))
    let _ ← writeRemProg (d, (dstS, d.rVal))
    let _ ← writeOccProg (d, (d.qVal, one))
    let _ ← writeFullProg (d, (dstL, one))
    pure 0

private theorem realizes_insertWriteNew :
    Realizes .exact insertWriteNewProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1.1 ∧ x.1.2 < x.1.1.slotCap ∧
        x.2.1.2 ≤ x.2.2 ∧ x.2.2 ≤ x.1.1.slotCap) (fun _ _ => 0) := by
  realize [realizes_writeRunStart, realizes_writeRem, realizes_writeOcc, realizes_writeFull] <;> {
    rcases d with ⟨⟨d0, o⟩, ⟨s₀, s_idx⟩, ℓ⟩
    rcases h with ⟨hcs, ho, hs, hℓ⟩
    have h2w := hcs.two_cap_lt
    have h1w := hcs.one_lt_two_pow
    have hq := hcs.q_lt
    have hr := hcs.r_le
    first
    | exact hcs
    | exact h1w
    | {
        dsimp only at *
        (try split_ifs) <;> first | fits [hcs.fMask_lt] | omega
      }
  }

/-- Post-scan phase of `insertCluster`: clear old run-start if superseded, right-shift
`[s .. ℓ)`, and write the new entry and metadata bits. -/
private def insertAfterScanProg (x : (ClusterInput × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) :
    Memory.Prog ℕ :=
  let (env, (occQ, ℓ), (s₀, s)) := x
  do
    let _ ← insertClearOldProg (env, (occQ, (s₀, s)))
    let count ← pure (ℓ - s)
    let _ ← shiftRightProg (env, (ℓ, count))
    insertWriteNewProg (env, ((s₀, s), ℓ))

private theorem realizes_insertAfterScan :
    Realizes .exact insertAfterScanProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1.1 ∧ x.1.2 < x.1.1.slotCap ∧
        x.2.2.1 ≤ x.2.1.2 ∧ x.2.2.2 ≤ x.2.1.2 ∧ x.2.1.2 ≤ x.1.1.slotCap) (fun _ _ => 0) := by
  realize [realizes_insertClearOld, realizes_shiftRight, realizes_insertWriteNew] <;> {
    rcases d with ⟨⟨d0, o⟩, ⟨occQ, ℓ⟩, ⟨s₀, s_idx⟩⟩
    rcases h with ⟨hcs, ho, hs₀, hs, hℓ⟩
    have h2w := hcs.two_cap_lt
    first
    | exact hcs
    | exact ho
    | exact hs
    | exact hℓ
    | { dsimp only at *; first | fits | omega }
  }

/-! ## Section 6: Left-Shift Loop and `deleteAfterScanProg` -/

/-- One step of the left-shift loop: copies `(isRunStart, remAt)` from `o + (pos + 1)` to
`o + pos` and increments `pos`. -/
private def shiftLeftStep (x : (ClusterInput × ℕ) × ℕ) : Memory.Prog ℕ :=
  let ((d, o), pos) := x
  do
    let src ← pure (o + (pos + 1))
    let dst ← pure (o + pos)
    let runBit ← readRunStartProg (d, src)
    let remVal ← readRemProg (d, src)
    let _ ← writeRunStartProg (d, (dst, runBit))
    let _ ← writeRemProg (d, (dst, remVal))
    pure (pos + 1)

private theorem realizes_shiftLeftStep :
    Realizes .exact shiftLeftStep WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1.1 ∧ x.1.2 < x.1.1.slotCap ∧ x.2 + 1 ≤ x.1.1.slotCap)
      (fun _ _ => 0) := by
  realize [realizes_readRunStart, realizes_readRem, realizes_writeRunStart, realizes_writeRem] <;> {
    rcases d with ⟨⟨d0, o⟩, pos⟩
    rcases h with ⟨hcs, ho, hpos⟩
    have h2w := hcs.two_cap_lt
    first
    | exact hcs
    | {
        have hb_run := clientResult_readRunStart_le s (d0, o + (pos + 1))
        have hb_rem := clientResult_readRem_le
          ((Memory.spec 0).clientState s (readRunStartProg (d0, o + (pos + 1))))
          (d0, o + (pos + 1))
        dsimp only at *
        first | fits [hcs.fMask_lt] | omega
      }
  }

private theorem clientResult_shiftLeftStep (t : Memory.State) (x : (ClusterInput × ℕ) × ℕ) :
    (Memory.spec 0).clientResult t (shiftLeftStep x) = x.2 + 1 := by
  unfold shiftLeftStep
  rw [clientResult_bind, clientResult_pure, clientState_pure,
    clientResult_bind, clientResult_pure, clientState_pure,
    clientResult_bind, clientState_readRunStart,
    clientResult_bind, clientState_readRem,
    clientResult_bind,
    clientResult_bind, clientResult_pure]

/-- Iterate `shiftLeftStep` `count` times starting at `pos`. -/
private def shiftLeftProg (x : (ClusterInput × ℕ) × (ℕ × ℕ)) : Memory.Prog ℕ :=
  let (env, pos, count) := x
  iterate shiftLeftStep env count pos

private theorem realizes_shiftLeft :
    Realizes .exact shiftLeftProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1.1 ∧ x.1.2 < x.1.1.slotCap ∧ x.2.1 + x.2.2 ≤ x.1.1.slotCap)
      (fun _ _ => 0) := by
  realize [realizes_shiftLeftStep]
  refine iterationSafe_of_stepInv _ _ w d
    (fun j (pos : ℕ) _ => pos + j ≤ d.1.1.slotCap)
    ?_ h.2.2
  rintro j pos t hpos
  rcases h with ⟨hcs, ho, _⟩
  refine ⟨⟨hcs, ho, by change pos + 1 ≤ d.1.1.slotCap; omega⟩, ?_⟩
  rw [clientResult_shiftLeftStep]
  dsimp only at *
  omega

/-- Compute `hasMore = (decide (s₀ + 1 < e) && !st.isRunStart (probeSlot b o (s₀ + 1))).toNat`. -/
private def deleteHasMoreProg (x : (ClusterInput × ℕ) × (ℕ × ℕ)) : Memory.Prog ℕ :=
  let ((d, o), s₀, e) := x
  if s₀ + 1 < e then do
    let rNext ← readRunStartProg (d, o + (s₀ + 1))
    if rNext = 0 then pure 1 else pure 0
  else
    pure 0

private theorem realizes_deleteHasMore :
    Realizes .exact deleteHasMoreProg WordEncoding.encode WordEncoding.encode
      (fun w x _ =>
        ClusterSafe w x.1.1 ∧ x.1.2 < x.1.1.slotCap ∧
          x.2.1 ≤ x.1.1.slotCap ∧ x.2.2 ≤ x.1.1.slotCap)
      (fun _ _ => 0) := by
  realize [realizes_readRunStart] <;> {
    rcases d with ⟨⟨d0, o⟩, s₀, e⟩
    rcases h with ⟨hcs, ho, hs₀, he⟩
    have h2w := hcs.two_cap_lt
    have h1w := hcs.one_lt_two_pow
    dsimp only at *
    first | exact hcs | exact h1w | fits
  }

/-- Update `isOcc` at `q` or `isRunStart` at `o + s₀` after `shiftLeft`. -/
private def deleteUpdateRunProg (x : (ClusterInput × ℕ) × (ℕ × (ℕ × ℕ))) : Memory.Prog Unit :=
  let ((d, o), hasMore, s₀, s) := x
  do
    let idx ← pure (o + s₀)
    let z ← pure 0
    let one ← pure 1
    if hasMore = 0 then
      writeOccProg (d, (d.qVal, z))
    else if s = s₀ then
      writeRunStartProg (d, (idx, one))
    else
      pure ()

private theorem realizes_deleteUpdateRun :
    Realizes .exact deleteUpdateRunProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1.1 ∧ x.1.2 + x.2.2.1 < 2 ^ w) (fun _ _ => 0) := by
  realize [realizes_writeOcc, realizes_writeRunStart] <;> {
    rcases h with ⟨hcs, hlt⟩
    have h1w := hcs.one_lt_two_pow
    have hq := hcs.q_lt
    first
    | exact hcs
    | exact hlt
    | exact h1w
    | { omega }
  }

/-- Clear `(isFull, isRunStart, remAt)` at `o + (e - 1)`. -/
private def deleteClearEndProg (x : (ClusterInput × ℕ) × ℕ) : Memory.Prog Unit :=
  let ((d, o), e) := x
  do
    let rawEnd ← pure (o + (e - 1))
    let z ← pure 0
    let _ ← writeFullProg (d, (rawEnd, z))
    let _ ← writeRunStartProg (d, (rawEnd, z))
    writeRemProg (d, (rawEnd, z))

private theorem realizes_deleteClearEnd :
    Realizes .exact deleteClearEndProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1.1 ∧ x.1.2 < x.1.1.slotCap ∧ 1 ≤ x.2 ∧ x.2 ≤ x.1.1.slotCap)
      (fun _ _ => 0) := by
  realize [realizes_writeFull, realizes_writeRunStart, realizes_writeRem] <;> {
    rcases d with ⟨⟨d0, o⟩, e⟩
    rcases h with ⟨hcs, ho, h1, he⟩
    have h2w := hcs.two_cap_lt
    dsimp only at *
    first | exact hcs | fits | omega
  }

/-- Post-scan phase of `deleteCluster`: compute `hasMore`, left-shift `[s + 1 .. e)`, update
`isOcc` / `isRunStart`, and clear `o + (e - 1)`. -/
private def deleteAfterScanProg (x : (ClusterInput × ℕ) × ((ℕ × ℕ) × ℕ)) : Memory.Prog ℕ :=
  let (env, (s₀, s), e) := x
  if s < e then do
    let hasMore ← deleteHasMoreProg (env, (s₀, e))
    let count ← pure (e - 1 - s)
    let _ ← shiftLeftProg (env, (s, count))
    let _ ← deleteUpdateRunProg (env, (hasMore, (s₀, s)))
    let _ ← deleteClearEndProg (env, e)
    pure 0
  else
    pure 0

private theorem realizes_deleteAfterScan :
    Realizes .exact deleteAfterScanProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1.1 ∧ x.1.2 < x.1.1.slotCap ∧
        x.2.1.1 ≤ x.1.1.slotCap ∧ x.2.1.2 ≤ x.1.1.slotCap ∧ x.2.2 ≤ x.1.1.slotCap)
      (fun _ _ => 0) := by
  realize [realizes_deleteHasMore, realizes_shiftLeft, realizes_deleteUpdateRun,
      realizes_deleteClearEnd] <;> {
    rcases d with ⟨⟨d0, o⟩, ⟨s₀, s_idx⟩, e⟩
    rcases h with ⟨hcs, ho, hs₀, hs, he⟩
    have h2w := hcs.two_cap_lt
    first
    | exact hcs
    | exact ho
    | exact hs₀
    | exact he
    | { dsimp only at *; first | fits | omega }
  }

/-! ## Section 7: Unified Cluster Operation `clusterOpProg` -/

/-- Dispatch after `findClusterProg` and `scanClusterProg` based on `d.opTag`
(`0 = insert`, `1 = delete`, `2 = query`). Every value of `d.opTag` other than `0` and `1` takes the
query branch. -/
private def clusterDispatchProg
    (x : (ClusterInput × (ℕ × (ℕ × ℕ))) × ScanResult) : Memory.Prog ℕ :=
  let ((d, o, _, ℓ), scan) := x
  if d.opTag = 0 then
    insertAfterScanProg ((d, o), ((scan.occQ, ℓ), (scan.s₀, scan.s)))
  else if d.opTag = 1 then
    deleteAfterScanProg ((d, o), ((scan.s₀, scan.s), scan.e))
  else
    pure (scan.occQ * scan.qFound)

private theorem realizes_clusterDispatch :
    Realizes .exact clusterDispatchProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1.1 ∧ x.1.2.1 < x.1.1.slotCap ∧ x.1.2.2.2 ≤ x.1.1.slotCap ∧
        x.2.Bounds x.1.2.2.2) (fun _ _ => 0) := by
  realize [realizes_insertAfterScan, realizes_deleteAfterScan] <;> {
    rcases d with ⟨⟨d0, o, a, ℓ⟩, scan⟩
    rcases h with ⟨hcs, ho, hℓ, hoccQ, hs₀, hs, he, hqFound⟩
    have h1w := hcs.one_lt_two_pow
    dsimp only at *
    first
    | exact hcs
    | exact ho
    | exact hs₀
    | exact hs
    | exact hℓ
    | { have := Nat.mul_le_mul hoccQ hqFound; first | fits | omega }
  }

/-- Unified deterministic cluster operation (`0 = insert`, `1 = delete`, `2 = query`). -/
def clusterOpProg (d : ClusterInput) : Memory.Prog ℕ := do
  let ext ← findClusterProg d
  let scan ← scanClusterProg (d, ext)
  clusterDispatchProg ((d, ext), scan)

theorem realizes_clusterOp :
    Realizes .exact clusterOpProg WordEncoding.encode WordEncoding.encode
      (fun w d _ => ClusterSafe w d) (fun _ _ => 0) := by
  realize [realizes_findCluster, realizes_scanCluster, realizes_clusterDispatch] <;> {
    have hcs := h
    have h_ext := clientResult_findCluster_bounds s d h
    have h_scan := clientResult_scanCluster_bounds s
      (d, (Memory.spec 0).clientResult s (findClusterProg d))
    try rw [clientState_findCluster]
    dsimp only at h_ext ⊢
    first
    | exact hcs
    | exact h_ext.1
    | exact h_ext.2.1
    | exact h_ext.2.2
    | exact h_scan
  }

/-! ## Section 8A: Memory Admissibility (`ValidHistory`) and `memoryCost` Bound -/

/-- State-side safety predicate for `clusterOpProg`: memory is well-formed at width `w` and all four
slot arrays lie below `s.frontier`. -/
private def ClusterMemSafe (w : ℕ) (d : ClusterInput) (s : Memory.State) : Prop :=
  Memory.WellFormed w s ∧
  d.fullBase + (d.slotMask >>> d.pBit) < s.frontier ∧
  d.occBase + (d.slotMask >>> d.pBit) < s.frontier ∧
  d.runBase + (d.slotMask >>> d.pBit) < s.frontier ∧
  d.remBase + (d.slotMask >>> d.pRem) < s.frontier

private theorem clusterMemSafe_mkClusterInput {base w w₀ n k : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hfront : base + space w w₀ n k ≤ s.frontier)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ) :
    ClusterMemSafe w (mkClusterInput base w w₀ n k q r opTag) s :=
  ⟨hwf, mkClusterInput_slotAddr_lt hfront q r opTag⟩

private theorem clusterMemSafe_clientState {α : Type} {w : ℕ} {d : ClusterInput} {s : Memory.State}
    (hms : ClusterMemSafe w d s) {p : Memory.Prog α}
    (hv : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p)) :
    ClusterMemSafe w d ((Memory.spec 0).clientState s p) :=
  have hle := Memory.frontier_le_clientState (w := 0) s p
  ⟨Cslib.WordRAM.Realization.wellFormed_clientState hms.1 hv,
    hms.2.1.trans_le hle, hms.2.2.1.trans_le hle,
    hms.2.2.2.1.trans_le hle, hms.2.2.2.2.trans_le hle⟩

private instance instMonotoneMemInv_clusterMemSafe (w : ℕ) (d : ClusterInput) :
    MonotoneMemInv w (ClusterMemSafe w d) :=
  ⟨fun hms hv => clusterMemSafe_clientState hms hv⟩

@[local valid_prog]
private theorem validHistory_scanStepTarget (w : ℕ) (s : Memory.State) (x : ScanStepCtx) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (scanStepTargetProg x)) := by
  unfold scanStepTargetProg; split_ifs <;> trivial

@[local valid_prog]
private theorem validHistory_scanStepStop (w : ℕ) (s : Memory.State) (x : ScanStepCtx) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (scanStepStopProg x)) := by
  unfold scanStepStopProg; split_ifs <;> trivial

@[local valid_prog]
theorem validHistory_scanStepQuery (w : ℕ) (s : Memory.State) (x : ScanStepCtx) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (scanStepQueryProg x)) := by
  unfold scanStepQueryProg; split_ifs <;> trivial

@[local valid_prog]
private theorem validHistory_readFull {w : ℕ} {s : Memory.State} {x : ClusterInput × ℕ}
    (hms : ClusterMemSafe w x.1 s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (readFullProg x)) :=
  ⟨masked_addr_lt hms.2.1, trivial⟩

@[local valid_prog]
private theorem validHistory_readOcc {w : ℕ} {s : Memory.State} {x : ClusterInput × ℕ}
    (hms : ClusterMemSafe w x.1 s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (readOccProg x)) :=
  ⟨masked_addr_lt hms.2.2.1, trivial⟩

@[local valid_prog]
private theorem validHistory_readRunStart {w : ℕ} {s : Memory.State} {x : ClusterInput × ℕ}
    (hms : ClusterMemSafe w x.1 s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (readRunStartProg x)) :=
  ⟨masked_addr_lt hms.2.2.2.1, trivial⟩

@[local valid_prog]
private theorem validHistory_readRem {w : ℕ} {s : Memory.State} {x : ClusterInput × ℕ}
    (hms : ClusterMemSafe w x.1 s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (readRemProg x)) :=
  ⟨masked_addr_lt hms.2.2.2.2, trivial⟩

private theorem validHistory_writeBit {w : ℕ} {d : ClusterInput} {s : Memory.State}
    {arr slot val : ℕ} (hcs : ClusterSafe w d) (hwf : Memory.WellFormed w s)
    (harr : arr + (d.slotMask >>> d.pBit) < s.frontier) (hbit : val < 2) :
    let idx := slot &&& d.slotMask
    let addr := arr + (idx >>> d.pBit)
    let sh := idx &&& d.pBitMask
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (do
      let oldWord ← Memory.read addr
      Memory.write addr (oldWord ^^^ (((oldWord >>> sh) &&& 1 ^^^ val) <<< sh)))) :=
  have hlt := masked_addr_lt (idx := slot) harr
  ⟨hlt, ⟨hlt,
      fits_writeBit_newWord (hwf.mem_fits _) (Nat.and_le_right.trans_lt hcs.pBitMask_lt) hbit⟩,
    trivial⟩

@[local valid_prog]
private theorem validHistory_writeFull {w : ℕ} {s : Memory.State} {x : ClusterInput × (ℕ × ℕ)}
    (hcs : ClusterSafe w x.1) (hms : ClusterMemSafe w x.1 s) (hbit : x.2.2 < 2) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (writeFullProg x)) :=
  validHistory_writeBit hcs hms.1 hms.2.1 hbit

@[local valid_prog]
private theorem validHistory_writeOcc {w : ℕ} {s : Memory.State} {x : ClusterInput × (ℕ × ℕ)}
    (hcs : ClusterSafe w x.1) (hms : ClusterMemSafe w x.1 s) (hbit : x.2.2 < 2) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (writeOccProg x)) :=
  validHistory_writeBit hcs hms.1 hms.2.2.1 hbit

@[local valid_prog]
private theorem validHistory_writeRunStart {w : ℕ} {s : Memory.State} {x : ClusterInput × (ℕ × ℕ)}
    (hcs : ClusterSafe w x.1) (hms : ClusterMemSafe w x.1 s) (hbit : x.2.2 < 2) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (writeRunStartProg x)) :=
  validHistory_writeBit hcs hms.1 hms.2.2.2.1 hbit

@[local valid_prog]
private theorem validHistory_writeRem {w : ℕ} {s : Memory.State} {x : ClusterInput × (ℕ × ℕ)}
    (hcs : ClusterSafe w x.1) (hms : ClusterMemSafe w x.1 s) (hval : x.2.2 ≤ x.1.fMask) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (writeRemProg x)) :=
  have hlt := masked_addr_lt (idx := x.2.1) hms.2.2.2.2
  ⟨hlt, ⟨hlt, Nat.xor_lt_two_pow (hms.1.mem_fits _)
    (fits_writeRem_diff_sh hcs.remPack_le hcs.fMask_lt_f hval)⟩, trivial⟩

private abbrev copySlotProg (d : ClusterInput) (src dst next : ℕ) : Memory.Prog ℕ := do
  let runBit ← readRunStartProg (d, src)
  let remVal ← readRemProg (d, src)
  let _ ← writeRunStartProg (d, (dst, runBit))
  let _ ← writeRemProg (d, (dst, remVal))
  pure next

@[local valid_prog]
private theorem validHistory_findCluster {w : ℕ} {d : ClusterInput} {s : Memory.State}
    (hms : ClusterMemSafe w d s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (findClusterProg d)) := by
  unfold findClusterProg backLenProg fwdLenProg backLenStep fwdLenStep
  valid_prog

@[local valid_prog]
private theorem validHistory_scanCluster {w : ℕ} {x : ClusterInput × (ℕ × (ℕ × ℕ))}
    {s : Memory.State} (hms : ClusterMemSafe w x.1 s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (scanClusterProg x)) := by
  unfold scanClusterProg occBeforeProg occBeforeStep scanLoopProg scanLoopStep scanStepReadsProg
  valid_prog

@[local valid_prog]
private theorem validHistory_insertAfterScan {w : ℕ}
    {x : (ClusterInput × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))} {s : Memory.State}
    (hcs : ClusterSafe w x.1.1) (hms : ClusterMemSafe w x.1.1 s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (insertAfterScanProg x)) := by
  unfold insertAfterScanProg insertClearOldProg shiftRightProg shiftRightStep insertWriteNewProg
  valid_prog [clientResult_readRunStart_le, clientResult_readRem_le, hcs.r_le]
  dsimp only; split_ifs <;> decide

@[local valid_prog]
private theorem validHistory_deleteAfterScan {w : ℕ}
    {x : (ClusterInput × ℕ) × ((ℕ × ℕ) × ℕ)} {s : Memory.State}
    (hcs : ClusterSafe w x.1.1) (hms : ClusterMemSafe w x.1.1 s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (deleteAfterScanProg x)) := by
  unfold deleteAfterScanProg deleteHasMoreProg shiftLeftProg shiftLeftStep
    deleteUpdateRunProg deleteClearEndProg
  valid_prog [clientResult_readRunStart_le, clientResult_readRem_le]

private theorem validHistory_clusterOp {w : ℕ} {d : ClusterInput} {s : Memory.State}
    (hcs : ClusterSafe w d) (hms : ClusterMemSafe w d s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (clusterOpProg d)) := by
  unfold clusterOpProg clusterDispatchProg
  valid_prog

@[simp] private theorem memoryCost_scanStepTarget (x : ScanStepCtx)
    (s : Memory.State) :
    memoryCost (scanStepTargetProg x) s = 0 := by
  unfold scanStepTargetProg; split_ifs <;> rfl

@[simp] private theorem memoryCost_scanStepStop (x : ScanStepCtx)
    (s : Memory.State) :
    memoryCost (scanStepStopProg x) s = 0 := by
  unfold scanStepStopProg; split_ifs <;> rfl

@[simp] theorem memoryCost_scanStepQuery (x : ScanStepCtx)
    (s : Memory.State) :
    memoryCost (scanStepQueryProg x) s = 0 := by
  unfold scanStepQueryProg; split_ifs <;> rfl

@[simp] private theorem memoryCost_readFull (x : ClusterInput × ℕ) (s : Memory.State) :
    memoryCost (readFullProg x) s = 1 := rfl

@[simp] private theorem memoryCost_readOcc (x : ClusterInput × ℕ) (s : Memory.State) :
    memoryCost (readOccProg x) s = 1 := rfl

@[simp] private theorem memoryCost_readRunStart (x : ClusterInput × ℕ) (s : Memory.State) :
    memoryCost (readRunStartProg x) s = 1 := rfl

@[simp] private theorem memoryCost_readRem (x : ClusterInput × ℕ) (s : Memory.State) :
    memoryCost (readRemProg x) s = 1 := rfl

@[simp] private theorem memoryCost_writeFull (x : ClusterInput × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (writeFullProg x) s = 2 := rfl

@[simp] private theorem memoryCost_writeOcc (x : ClusterInput × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (writeOccProg x) s = 2 := rfl

@[simp] private theorem memoryCost_writeRunStart (x : ClusterInput × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (writeRunStartProg x) s = 2 := rfl

@[simp] private theorem memoryCost_writeRem (x : ClusterInput × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (writeRemProg x) s = 2 := rfl

private theorem boundedWhile_snd_zero {δ : Type}
    (body : δ × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)) (d : δ) (n : ℕ) (cnt : ℕ) :
    boundedWhile (fun _ (st : ℕ × ℕ) => 0 < st.2) body d n (cnt, 0) = pure (cnt, 0) := by
  cases n <;> simp [boundedWhile]

private theorem memoryCost_countWhile {δ : Type}
    (body : δ × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)) (d : δ) (s : Memory.State) (stop : ℕ → Prop)
    [DecidablePred stop]
    (hstate : ∀ x, (Memory.spec 0).clientState s (body (d, x)) = s)
    (hcost : ∀ x, memoryCost (body (d, x)) s = 1)
    (hresult : ∀ cnt rem, (Memory.spec 0).clientResult s (body (d, (cnt, rem))) =
      if stop cnt then (cnt, 0) else (cnt + 1, rem - 1)) (n cnt rem : ℕ) :
    memoryCost (boundedWhile (fun _ (st : ℕ × ℕ) => 0 < st.2) body d n (cnt, rem)) s + cnt ≤
      ((Memory.spec 0).clientResult s
        (boundedWhile (fun _ (st : ℕ × ℕ) => 0 < st.2) body d n (cnt, rem))).1 + 1 := by
  induction n generalizing cnt rem with
  | zero =>
    change 0 + cnt ≤ cnt + 1
    omega
  | succ n ih =>
    by_cases hg : 0 < rem
    · simp only [boundedWhile, hg, ↓reduceIte, memoryCost_bind',
        clientResult_bind, hstate, hcost, hresult]
      split_ifs
      · rw [boundedWhile_snd_zero, memoryCost_pure, clientResult_pure]
        dsimp only
        omega
      · have hih := ih (cnt + 1) (rem - 1)
        omega
    · simp only [boundedWhile, hg, ↓reduceIte, memoryCost_pure, clientResult_pure]
      omega

private theorem memoryCost_findCluster_le (d : ClusterInput) (s : Memory.State) :
    memoryCost (findClusterProg d) s ≤
      ((Memory.spec 0).clientResult s (findClusterProg d)).2.2 + 2 := by
  unfold findClusterProg
  rw [memoryCost_bind', memoryCost_bind', clientResult_bind,
    clientResult_bind, clientState_backLen, clientState_fwdLen,
    memoryCost_pure, clientResult_pure]
  have hb := memoryCost_countWhile backLenStep d s
    (fun c => (Memory.spec 0).clientResult s (readFullProg (d, d.qVal + d.slotCap - (c + 1))) = 0)
    (fun _ => clientState_backLenStep _ _)
    (fun _ => by change memoryCost ((readFullProg _).bind _) s = 1
                 rw [memoryCost_bind, memoryCost_readFull]; split_ifs <;> rfl)
    (fun c r => clientResult_backLenStep s (d, (c, r))) d.slotCap 0 d.slotCap
  have hf := memoryCost_countWhile fwdLenStep d s
    (fun c => (Memory.spec 0).clientResult s (readFullProg (d, d.qVal + c)) = 0)
    (fun _ => clientState_fwdLenStep _ _)
    (fun _ => by change memoryCost ((readFullProg _).bind _) s = 1
                 rw [memoryCost_bind, memoryCost_readFull]; split_ifs <;> rfl)
    (fun c r => clientResult_fwdLenStep s (d, (c, r)))
    d.slotCap 0 (d.slotCap - ((Memory.spec 0).clientResult s (backLenProg d)).1)
  dsimp only [backLenProg, fwdLenProg] at hb hf ⊢
  omega

private theorem memoryCost_copySlot (d : ClusterInput) (src dst next : ℕ) (t : Memory.State) :
    memoryCost (copySlotProg d src dst next) t = 6 := by
  unfold copySlotProg
  prog_cost [memoryCost_readRunStart, memoryCost_readRem, memoryCost_writeRunStart,
    memoryCost_writeRem]

private theorem memoryCost_scanCluster_le (x : ClusterInput × (ℕ × (ℕ × ℕ))) (s : Memory.State)
    (ha : x.2.2.1 ≤ x.2.2.2) :
    memoryCost (scanClusterProg x) s ≤ 4 * x.2.2.2 + 1 := by
  rcases x with ⟨d, o, a, ℓ⟩
  unfold scanClusterProg
  simp only [pure_bind, memoryCost_bind', memoryCost_readOcc, memoryCost_pure]
  rw [clientState_occBefore, clientState_readOcc]
  have hocc : memoryCost (occBeforeProg (d, o, a)) s ≤ 1 * a :=
    memoryCost_iterate_le_of occBeforeStep 1 _
      (fun _ _ => by unfold occBeforeStep; prog_cost [memoryCost_readOcc]) _ _ s
  have hloop : memoryCost (scanLoopProg
      ⟨d, o, a, ℓ, ((Memory.spec 0).clientResult s (occBeforeProg (d, o, a))).2,
        ((Memory.spec 0).clientResult s (occBeforeProg (d, o, a))).2 +
          (Memory.spec 0).clientResult s (readOccProg (d, d.qVal))⟩) s ≤ 3 * ℓ :=
    memoryCost_iterate_le_of scanLoopStep 3 _ (fun _ _ => by
      unfold scanLoopStep scanStepReadsProg
      prog_cost [memoryCost_readOcc, memoryCost_readRunStart, memoryCost_readRem,
        memoryCost_scanStepTarget, memoryCost_scanStepStop, memoryCost_scanStepQuery]) _ _ s
  dsimp only at ha ⊢
  omega

private theorem memoryCost_insertAfterScan_le
    (x : (ClusterInput × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (s : Memory.State) :
    memoryCost (insertAfterScanProg x) s ≤ 6 * x.2.1.2 + 10 := by
  rcases x with ⟨⟨d, o⟩, ⟨occQ, ℓ⟩, s₀, s_idx⟩
  simp only [insertAfterScanProg, pure_bind, memoryCost_bind']
  set s₁ := (Memory.spec 0).clientState s (insertClearOldProg ((d, o), occQ, s₀, s_idx))
  set s₂ := (Memory.spec 0).clientState s₁ (shiftRightProg ((d, o), ℓ, ℓ - s_idx))
  have hclear : memoryCost (insertClearOldProg ((d, o), occQ, s₀, s_idx)) s ≤ 2 := by
    unfold insertClearOldProg; prog_cost [memoryCost_writeRunStart]
  have hshift : memoryCost (shiftRightProg ((d, o), ℓ, ℓ - s_idx)) s₁ ≤ 6 * (ℓ - s_idx) :=
    memoryCost_iterate_le_of shiftRightStep 6 _ (fun _ _ => (memoryCost_copySlot ..).le) _ _ s₁
  have hwrite : memoryCost (insertWriteNewProg ((d, o), (s₀, s_idx), ℓ)) s₂ = 8 := by
    unfold insertWriteNewProg
    prog_cost [memoryCost_writeRunStart, memoryCost_writeRem,
      memoryCost_writeOcc, memoryCost_writeFull]
  have : 6 * (ℓ - s_idx) ≤ 6 * ℓ := Nat.mul_le_mul_left 6 (Nat.sub_le _ _)
  omega

private theorem memoryCost_deleteAfterScan_le
    (x : (ClusterInput × ℕ) × ((ℕ × ℕ) × ℕ)) (s : Memory.State) :
    memoryCost (deleteAfterScanProg x) s ≤ 6 * x.2.2 + 9 := by
  rcases x with ⟨⟨d, o⟩, ⟨s₀, s_idx⟩, e⟩
  dsimp only [deleteAfterScanProg]
  split_ifs
  · simp only [pure_bind, memoryCost_bind', memoryCost_pure]
    set a := (Memory.spec 0).clientResult s (deleteHasMoreProg ((d, o), s₀, e))
    set s₁ := (Memory.spec 0).clientState s (deleteHasMoreProg ((d, o), s₀, e))
    set s₂ := (Memory.spec 0).clientState s₁ (shiftLeftProg ((d, o), s_idx, e - 1 - s_idx))
    set s₃ := (Memory.spec 0).clientState s₂ (deleteUpdateRunProg ((d, o), a, s₀, s_idx))
    have hmore : memoryCost (deleteHasMoreProg ((d, o), s₀, e)) s ≤ 1 := by
      unfold deleteHasMoreProg
      prog_cost [memoryCost_readRunStart]
    have hshift : memoryCost (shiftLeftProg ((d, o), s_idx, e - 1 - s_idx)) s₁ ≤
        6 * (e - 1 - s_idx) :=
      memoryCost_iterate_le_of shiftLeftStep 6 _ (fun _ _ => (memoryCost_copySlot ..).le) _ _ s₁
    have hupd : memoryCost (deleteUpdateRunProg ((d, o), a, s₀, s_idx)) s₂ ≤ 2 := by
      unfold deleteUpdateRunProg; prog_cost [memoryCost_writeOcc, memoryCost_writeRunStart]
    have hclr : memoryCost (deleteClearEndProg ((d, o), e)) s₃ = 6 := by
      unfold deleteClearEndProg
      prog_cost [memoryCost_writeFull, memoryCost_writeRunStart, memoryCost_writeRem]
    have : 6 * (e - 1 - s_idx) ≤ 6 * e :=
      Nat.mul_le_mul_left 6 ((Nat.sub_le _ _).trans (Nat.sub_le _ _))
    omega
  · simp

private theorem memoryCost_clusterOp_le (d : ClusterInput) (s : Memory.State) :
    memoryCost (clusterOpProg d) s ≤
      11 * ((Memory.spec 0).clientResult s (findClusterProg d)).2.2 + 13 := by
  unfold clusterOpProg
  rw [memoryCost_bind', clientState_findCluster, memoryCost_bind', clientState_scanCluster]
  set ext := (Memory.spec 0).clientResult s (findClusterProg d)
  set scan := (Memory.spec 0).clientResult s (scanClusterProg (d, ext))
  have hf := memoryCost_findCluster_le d s
  have ha : ext.2.1 ≤ ext.2.2 := by
    simp only [ext, findClusterProg, clientResult_bind, clientResult_pure]
    omega
  have hsc := memoryCost_scanCluster_le (d, ext) s ha
  dsimp only at hsc
  have hdisp : memoryCost (clusterDispatchProg ((d, ext), scan)) s ≤ 6 * ext.2.2 + 10 := by
    dsimp only [clusterDispatchProg]
    split_ifs
    · exact memoryCost_insertAfterScan_le ((d, ext.1), (scan.occQ, ext.2.2), (scan.s₀, scan.s)) s
    · have hd := memoryCost_deleteAfterScan_le ((d, ext.1), (scan.s₀, scan.s), scan.e) s
      have he : scan.e ≤ ext.2.2 := (clientResult_scanCluster_bounds s (d, ext)).2.2.2.1
      dsimp only at hd
      omega
    · simp
  dsimp only [ext] at hsc hdisp ⊢
  omega

/-! ## Section 8B: Semantic Correctness of `clusterOpProg` on `mkClusterInput` -/

/-- Cyclic slot `⟨idx &&& (2 ^ b - 1), _⟩ : Fin (2 ^ b)`. -/
private def maskedSlot (b idx : ℕ) : Fin (2 ^ b) :=
  ⟨idx &&& (2 ^ b - 1), Nat.and_lt_two_pow idx (Nat.sub_lt (Nat.two_pow_pos b) one_pos)⟩

@[simp] private theorem maskedSlot_val (b idx : ℕ) :
    (maskedSlot b idx).val = idx &&& (2 ^ b - 1) := rfl

@[simp] private theorem maskedSlot_fin {b : ℕ} (q : Fin (2 ^ b)) :
    maskedSlot b q.val = q := by
  ext
  simp [maskedSlot, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt q.isLt]

private theorem maskedSlot_probeSlot {b : ℕ} (o : Fin (2 ^ b)) (m : ℕ) :
    maskedSlot b (o.val + m) = probeSlot b o m := by
  ext
  exact add_and_eq_probeSlot_val o m

private theorem maskedSlot_backSlot {b : ℕ} (q : Fin (2 ^ b)) {a : ℕ} (ha : a ≤ 2 ^ b) :
    maskedSlot b (q.val + 2 ^ b - a) = backSlot b q a := by
  ext
  exact add_sub_and_eq_backSlot_val q ha

/-- `SlotFrame base w w₀ n k s₁ s₂` states that `s₂` preserves `s₁.frontier` and modifies `mem`
only within the four packed slot arrays `[fullBase base w w₀ n, base + space w w₀ n k)`. -/
@[expose] def SlotFrame (base w w₀ n k : ℕ) (s₁ s₂ : Memory.State) : Prop :=
  s₂.frontier = s₁.frontier ∧
  ∀ a, (a < fullBase base w w₀ n ∨ base + space w w₀ n k ≤ a) → s₂.mem a = s₁.mem a

theorem SlotFrame.refl (base w w₀ n k : ℕ) (s : Memory.State) :
    SlotFrame base w w₀ n k s s :=
  ⟨rfl, fun _ _ => rfl⟩

theorem SlotFrame.trans {base w w₀ n k : ℕ} {s₁ s₂ s₃ : Memory.State}
    (h₁₂ : SlotFrame base w w₀ n k s₁ s₂) (h₂₃ : SlotFrame base w w₀ n k s₂ s₃) :
    SlotFrame base w w₀ n k s₁ s₃ :=
  ⟨h₂₃.1.trans h₁₂.1, fun a ha => (h₂₃.2 a ha).trans (h₁₂.2 a ha)⟩

private theorem readBit_eq_toNat (arrBase b w : ℕ) (mem : ℕ → ℕ) (idx : ℕ) :
    let m := idx &&& (2 ^ b - 1)
    let p := slotPackShift b 1 w
    (mem (arrBase + (m >>> p)) >>> (m &&& (2 ^ p - 1))) &&& 1 =
      (extractBit arrBase b w mem (maskedSlot b idx)).toNat := by
  rw [← extractPacked_one_val_eq_toNat arrBase b w mem (maskedSlot b idx)]
  change _ = Cslib.Probability.getLimb 1 _ _
  dsimp only [Cslib.Probability.getLimb]
  rw [mul_one]
  rfl

private theorem clientResult_readFull_mk (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) (idx : ℕ) :
    (Memory.spec 0).clientResult s
      (readFullProg (mkClusterInput base w w₀ n k q r opTag, idx)) =
      ((extractFilterState base w w₀ n k s.mem).isFull
        (maskedSlot (quotBits w₀ n) idx)).toNat :=
  readBit_eq_toNat (fullBase base w w₀ n) (quotBits w₀ n) w s.mem idx

private theorem clientResult_readOcc_mk (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) (idx : ℕ) :
    (Memory.spec 0).clientResult s
      (readOccProg (mkClusterInput base w w₀ n k q r opTag, idx)) =
      ((extractFilterState base w w₀ n k s.mem).isOcc
        (maskedSlot (quotBits w₀ n) idx)).toNat :=
  readBit_eq_toNat (occBase base w w₀ n) (quotBits w₀ n) w s.mem idx

private theorem clientResult_readRunStart_mk (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) (idx : ℕ) :
    (Memory.spec 0).clientResult s
      (readRunStartProg (mkClusterInput base w w₀ n k q r opTag, idx)) =
      ((extractFilterState base w w₀ n k s.mem).isRunStart
        (maskedSlot (quotBits w₀ n) idx)).toNat :=
  readBit_eq_toNat (runBase base w w₀ n) (quotBits w₀ n) w s.mem idx

private theorem clientResult_readRem_mk (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) (idx : ℕ) :
    (Memory.spec 0).clientResult s
      (readRemProg (mkClusterInput base w w₀ n k q r opTag, idx)) =
      ((extractFilterState base w w₀ n k s.mem).remAt
        (maskedSlot (quotBits w₀ n) idx)).val := rfl

private theorem mem_clientState_writeFull_mk (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) (idx : ℕ) (bval : Bool) :
    ((Memory.spec 0).clientState s
      (writeFullProg (mkClusterInput base w w₀ n k q r opTag, (idx, bval.toNat)))).mem =
      writeBitMem (fullBase base w w₀ n) (quotBits w₀ n) w s.mem
        (maskedSlot (quotBits w₀ n) idx) bval := by
  dsimp only [writeFullProg, mkClusterInput, writeBitMem, writePackedMem, maskedSlot]
  simp only [mul_one]
  rfl

private theorem mem_clientState_writeOcc_mk (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) (idx : ℕ) (bval : Bool) :
    ((Memory.spec 0).clientState s
      (writeOccProg (mkClusterInput base w w₀ n k q r opTag, (idx, bval.toNat)))).mem =
      writeBitMem (occBase base w w₀ n) (quotBits w₀ n) w s.mem
        (maskedSlot (quotBits w₀ n) idx) bval := by
  dsimp only [writeOccProg, mkClusterInput, writeBitMem, writePackedMem, maskedSlot]
  simp only [mul_one]
  rfl

private theorem mem_clientState_writeRunStart_mk (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) (idx : ℕ) (bval : Bool) :
    ((Memory.spec 0).clientState s
      (writeRunStartProg (mkClusterInput base w w₀ n k q r opTag, (idx, bval.toNat)))).mem =
      writeBitMem (runBase base w w₀ n) (quotBits w₀ n) w s.mem
        (maskedSlot (quotBits w₀ n) idx) bval := by
  dsimp only [writeRunStartProg, mkClusterInput, writeBitMem, writePackedMem, maskedSlot]
  simp only [mul_one]
  rfl

private theorem mem_clientState_writeRem_mk (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) (idx : ℕ) (val : ℕ) :
    ((Memory.spec 0).clientState s
      (writeRemProg (mkClusterInput base w w₀ n k q r opTag, (idx, val)))).mem =
      writePackedMem (remBase base w w₀ n) (quotBits w₀ n) (remBits w₀ k) w s.mem
        (maskedSlot (quotBits w₀ n) idx) val := rfl

private theorem extractFilterState_writeFull_mk (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) (idx : ℕ) (bval : Bool) :
    extractFilterState base w w₀ n k
      ((Memory.spec 0).clientState s
        (writeFullProg (mkClusterInput base w w₀ n k q r opTag, (idx, bval.toNat)))).mem =
      (extractFilterState base w w₀ n k s.mem).setFull
        (maskedSlot (quotBits w₀ n) idx) bval := by
  rw [mem_clientState_writeFull_mk, extractFilterState_writeFull]

private theorem extractFilterState_writeOcc_mk (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) (idx : ℕ) (bval : Bool) :
    extractFilterState base w w₀ n k
      ((Memory.spec 0).clientState s
        (writeOccProg (mkClusterInput base w w₀ n k q r opTag, (idx, bval.toNat)))).mem =
      (extractFilterState base w w₀ n k s.mem).setOcc
        (maskedSlot (quotBits w₀ n) idx) bval := by
  rw [mem_clientState_writeOcc_mk, extractFilterState_writeOcc]

private theorem extractFilterState_writeRunStart_mk (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) (idx : ℕ) (bval : Bool) :
    extractFilterState base w w₀ n k
      ((Memory.spec 0).clientState s
        (writeRunStartProg (mkClusterInput base w w₀ n k q r opTag, (idx, bval.toNat)))).mem =
      (extractFilterState base w w₀ n k s.mem).setRunStart
        (maskedSlot (quotBits w₀ n) idx) bval := by
  rw [mem_clientState_writeRunStart_mk, extractFilterState_writeRunStart]

private theorem extractFilterState_writeRem_mk (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) (idx : ℕ) (r' : Fin (2 ^ remBits w₀ k)) :
    extractFilterState base w w₀ n k
      ((Memory.spec 0).clientState s
        (writeRemProg (mkClusterInput base w w₀ n k q r opTag, (idx, r'.val)))).mem =
      (extractFilterState base w w₀ n k s.mem).setRem
        (maskedSlot (quotBits w₀ n) idx) r' := by
  rw [mem_clientState_writeRem_mk, extractFilterState_writeRem]

private theorem slotFrame_of_writePackedMem {base w w₀ n k : ℕ}
    (arrBase d : ℕ) (q : Fin (2 ^ quotBits w₀ n)) (val : ℕ) {s s' : Memory.State}
    (hf : s'.frontier = s.frontier)
    (hm : s'.mem = writePackedMem arrBase (quotBits w₀ n) d w s.mem q val)
    (hlo : fullBase base w w₀ n ≤ arrBase)
    (hhi : arrBase + packedWords (quotBits w₀ n) d w ≤ base + space w w₀ n k) :
    SlotFrame base w w₀ n k s s' :=
  ⟨hf, fun a ha => hm ▸ writePackedMem_outside _ _ _ _ _ _ _ (by omega)⟩

private theorem slotFrame_writeBit_mk {base w w₀ n k : ℕ} (arrBase : ℕ)
    (s : Memory.State) (idx val : ℕ)
    (hlo : fullBase base w w₀ n ≤ arrBase)
    (hhi : arrBase + packedWords (quotBits w₀ n) 1 w ≤ base + space w w₀ n k) :
    let b := quotBits w₀ n
    let p := slotPackShift b 1 w
    let i := idx &&& (2 ^ b - 1)
    let addr := arrBase + (i >>> p)
    let sh := i &&& (2 ^ p - 1)
    SlotFrame base w w₀ n k s ((Memory.spec 0).clientState s (do
      let oldWord ← Memory.read addr
      Memory.write addr (oldWord ^^^ (((oldWord >>> sh) &&& 1 ^^^ val) <<< sh)))) :=
  slotFrame_of_writePackedMem arrBase 1 (maskedSlot (quotBits w₀ n) idx) val rfl
    (by dsimp only [writePackedMem, maskedSlot]; simp only [mul_one]; rfl) hlo hhi

private theorem slotFrame_writeFull_mk (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) (idx val : ℕ) :
    SlotFrame base w w₀ n k s
      ((Memory.spec 0).clientState s
        (writeFullProg (mkClusterInput base w w₀ n k q r opTag, (idx, val)))) :=
  slotFrame_writeBit_mk (fullBase base w w₀ n) s idx val le_rfl (by
    have := remBase_add_packedWords_eq base w w₀ n k
    dsimp only [remBase, runBase, occBase] at this; omega)

private theorem slotFrame_writeOcc_mk (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) (idx val : ℕ) :
    SlotFrame base w w₀ n k s
      ((Memory.spec 0).clientState s
        (writeOccProg (mkClusterInput base w w₀ n k q r opTag, (idx, val)))) :=
  slotFrame_writeBit_mk (occBase base w w₀ n) s idx val (by dsimp only [occBase]; omega) (by
    have := remBase_add_packedWords_eq base w w₀ n k
    dsimp only [remBase, runBase, occBase] at this ⊢; omega)

private theorem slotFrame_writeRunStart_mk (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) (idx val : ℕ) :
    SlotFrame base w w₀ n k s
      ((Memory.spec 0).clientState s
        (writeRunStartProg (mkClusterInput base w w₀ n k q r opTag, (idx, val)))) :=
  slotFrame_writeBit_mk (runBase base w w₀ n) s idx val
    (by dsimp only [runBase, occBase]; omega) (by
      have := remBase_add_packedWords_eq base w w₀ n k
      dsimp only [remBase, runBase, occBase] at this ⊢; omega)

private theorem slotFrame_writeRem_mk (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) (idx val : ℕ) :
    SlotFrame base w w₀ n k s
      ((Memory.spec 0).clientState s
        (writeRemProg (mkClusterInput base w w₀ n k q r opTag, (idx, val)))) :=
  slotFrame_of_writePackedMem (remBase base w w₀ n) (remBits w₀ k) (maskedSlot (quotBits w₀ n) idx)
    val rfl (mem_clientState_writeRem_mk base w w₀ n k q r opTag s idx val)
    (by dsimp only [remBase, runBase, occBase]; omega)
    (remBase_add_packedWords_eq base w w₀ n k).le

/-- A bounded counting loop whose state-preserving step reads the flag `full cnt`, advancing
`(cnt, rem)` to `(cnt + 1, rem - 1)` while it is set and stopping with `rem = 0` otherwise, ends
at the first unset count `a` once its fuel and budget suffice. -/
private theorem clientResult_countWhile {δ : Type}
    (body : δ × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)) (d : δ) (s : Memory.State) (full : ℕ → Bool)
    {a : ℕ} (hstate : ∀ x, (Memory.spec 0).clientState s (body (d, x)) = s)
    (hresult : ∀ cnt ≤ a, ∀ rem, (Memory.spec 0).clientResult s (body (d, (cnt, rem))) =
      if (full cnt).toNat = 0 then (cnt, 0) else (cnt + 1, rem - 1))
    (hfull : ∀ c < a, full c = true) (hempty : full a = false) :
    ∀ fuel cnt rem, cnt ≤ a → a - cnt < fuel → a - cnt < rem →
      (Memory.spec 0).clientResult s
        (boundedWhile (fun _ (st : ℕ × ℕ) => 0 < st.2) body d fuel (cnt, rem)) = (a, 0) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ hlt _; omega
  | succ fuel ih =>
    intro cnt rem hcnt hfuel hrem
    have hg : 0 < rem := by omega
    simp only [boundedWhile, hg, ↓reduceIte]
    rw [clientResult_bind, hstate, hresult cnt hcnt]
    rcases lt_or_eq_of_le hcnt with hlt | rfl
    · rw [hfull cnt hlt]
      simp only [Bool.toNat_true, one_ne_zero, ↓reduceIte]
      exact ih (cnt + 1) (rem - 1) (by omega) (by omega) (by omega)
    · rw [hempty]
      simp only [Bool.toNat_false, ↓reduceIte]
      rw [boundedWhile_snd_zero]; rfl

private theorem clientResult_backLen_aux (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) {a : ℕ} (ha_lt : a < 2 ^ quotBits w₀ n)
    (hfull : ∀ c < a,
      (extractFilterState base w w₀ n k s.mem).isFull
        (backSlot (quotBits w₀ n) q (c + 1)) = true)
    (hempty : (extractFilterState base w w₀ n k s.mem).isFull
      (backSlot (quotBits w₀ n) q (a + 1)) = false) :
    ∀ fuel cnt rem, cnt ≤ a → a - cnt < fuel → a - cnt < rem →
      (Memory.spec 0).clientResult s
        (boundedWhile (fun _ (st : ℕ × ℕ) => 0 < st.2) backLenStep
          (mkClusterInput base w w₀ n k q r opTag) fuel (cnt, rem)) = (a, 0) :=
  clientResult_countWhile backLenStep _ s
    (fun c => (extractFilterState base w w₀ n k s.mem).isFull (backSlot (quotBits w₀ n) q (c + 1)))
    (fun _ => clientState_backLenStep _ _)
    (fun cnt hcnt rem => by
      rw [clientResult_backLenStep]
      rw [show (mkClusterInput base w w₀ n k q r opTag).qVal = q.val from rfl,
        show (mkClusterInput base w w₀ n k q r opTag).slotCap = 2 ^ quotBits w₀ n from rfl,
        clientResult_readFull_mk, maskedSlot_backSlot q (a := cnt + 1) (by omega)])
    hfull hempty

private theorem clientResult_backLen_mk {U : ℕ} {S : Finset (Fin U)} (base w w₀ n k : ℕ)
    {quot : Fin U → Fin (2 ^ quotBits w₀ n)} {rem : Fin U → Fin (2 ^ remBits w₀ k)}
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k))
    (opTag : ℕ) (s : Memory.State)
    (hinv : FilterInv n S quot rem (extractFilterState base w w₀ n k s.mem))
    (hS_lt : #S < 2 ^ quotBits w₀ n) :
    (Memory.spec 0).clientResult s
      (backLenProg (mkClusterInput base w w₀ n k q r opTag)) =
      (hinv.backLen hS_lt q, 0) := by
  have ha_le : hinv.backLen hS_lt q ≤ #S := hinv.backLen_le_card hS_lt q
  have ha_lt : hinv.backLen hS_lt q < 2 ^ quotBits w₀ n := lt_of_le_of_lt ha_le hS_lt
  unfold backLenProg
  rw [show (mkClusterInput base w w₀ n k q r opTag).slotCap = 2 ^ quotBits w₀ n from rfl]
  exact clientResult_backLen_aux base w w₀ n k q r opTag s ha_lt
    (fun c hc => hinv.isFull_backSlot_of_le_backLen hS_lt q (by omega) (by omega))
    (hinv.isFull_backSlot_succ_backLen hS_lt q)
    (2 ^ quotBits w₀ n) 0 (2 ^ quotBits w₀ n) (Nat.zero_le _) (by omega) (by omega)

private theorem clientResult_fwdLen_aux (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) {t : ℕ}
    (hfull : ∀ c < t,
      (extractFilterState base w w₀ n k s.mem).isFull
        (probeSlot (quotBits w₀ n) q c) = true)
    (hempty : (extractFilterState base w w₀ n k s.mem).isFull
      (probeSlot (quotBits w₀ n) q t) = false) :
    ∀ fuel cnt rem, cnt ≤ t → t - cnt < fuel → t - cnt < rem →
      (Memory.spec 0).clientResult s
        (boundedWhile (fun _ (st : ℕ × ℕ) => 0 < st.2) fwdLenStep
          (mkClusterInput base w w₀ n k q r opTag) fuel (cnt, rem)) = (t, 0) :=
  clientResult_countWhile fwdLenStep _ s
    (fun c => (extractFilterState base w w₀ n k s.mem).isFull (probeSlot (quotBits w₀ n) q c))
    (fun _ => clientState_fwdLenStep _ _)
    (fun cnt _ rem => by
      rw [clientResult_fwdLenStep]
      rw [show (mkClusterInput base w w₀ n k q r opTag).qVal = q.val from rfl,
        clientResult_readFull_mk, maskedSlot_probeSlot q cnt])
    hfull hempty

private theorem clientResult_fwdLen_mk {U : ℕ} {S : Finset (Fin U)} (base w w₀ n k : ℕ)
    {quot : Fin U → Fin (2 ^ quotBits w₀ n)} {rem : Fin U → Fin (2 ^ remBits w₀ k)}
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k))
    (opTag : ℕ) (s : Memory.State)
    (hinv : FilterInv n S quot rem (extractFilterState base w w₀ n k s.mem))
    (hS_lt : #S < 2 ^ quotBits w₀ n) :
    (Memory.spec 0).clientResult s
      (fwdLenProg (mkClusterInput base w w₀ n k q r opTag, hinv.backLen hS_lt q)) =
      (hinv.fwdLen hS_lt q, 0) := by
  have ha_le : hinv.backLen hS_lt q ≤ #S := hinv.backLen_le_card hS_lt q
  have ht_le : hinv.fwdLen hS_lt q ≤ #S - hinv.backLen hS_lt q := hinv.fwdLen_le_sub hS_lt q
  unfold fwdLenProg
  dsimp only
  rw [show (mkClusterInput base w w₀ n k q r opTag).slotCap = 2 ^ quotBits w₀ n from rfl]
  exact clientResult_fwdLen_aux base w w₀ n k q r opTag s
    (fun c hc => hinv.isFull_probeSlot_of_lt_fwdLen hS_lt q hc)
    (hinv.isFull_probeSlot_fwdLen hS_lt q)
    (2 ^ quotBits w₀ n) 0 (2 ^ quotBits w₀ n - hinv.backLen hS_lt q)
    (Nat.zero_le _) (by omega) (by omega)

private theorem clientResult_findCluster_mk {U : ℕ} {S : Finset (Fin U)} (base w w₀ n k : ℕ)
    {quot : Fin U → Fin (2 ^ quotBits w₀ n)} {rem : Fin U → Fin (2 ^ remBits w₀ k)}
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k))
    (opTag : ℕ) (s : Memory.State)
    (hinv : FilterInv n S quot rem (extractFilterState base w w₀ n k s.mem))
    (hS_lt : #S < 2 ^ quotBits w₀ n) :
    (Memory.spec 0).clientResult s
      (findClusterProg (mkClusterInput base w w₀ n k q r opTag)) =
      ((hinv.clusterStart hS_lt q).val, (hinv.backLen hS_lt q, hinv.clusterLen hS_lt q)) := by
  have ha_le : hinv.backLen hS_lt q ≤ 2 ^ quotBits w₀ n :=
    (hinv.backLen_le_card hS_lt q).trans hS_lt.le
  unfold findClusterProg
  rw [clientResult_bind, clientState_backLen,
    clientResult_backLen_mk _ _ _ _ _ _ _ _ _ hinv hS_lt,
    clientResult_bind, clientState_fwdLen,
    clientResult_fwdLen_mk _ _ _ _ _ _ _ _ _ hinv hS_lt, clientResult_pure]
  simp only [mkClusterInput, add_sub_and_eq_backSlot_val q ha_le]
  rfl

private theorem calcRunStart_zero {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a : ℕ) :
    calcRunStart st o a 0 = 0 := rfl

private theorem calcRunStart_succ {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a m : ℕ) :
    calcRunStart st o a (m + 1) =
      calcRunStart st o a m + (decide (runsBefore st o (m + 1) ≤ occBefore st o a)).toNat := by
  simp only [calcRunStart, List.range_succ, List.filter_append, List.length_append,
    List.filter_cons, List.filter_nil]
  cases decide (runsBefore st o (m + 1) ≤ occBefore st o a) <;> rfl

private theorem calcTargetSlot_zero {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a : ℕ)
    (r : Fin (2 ^ f)) :
    calcTargetSlot st o a 0 r = 0 := rfl

private theorem calcTargetSlot_succ {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a m : ℕ)
    (r : Fin (2 ^ f)) :
    calcTargetSlot st o a (m + 1) r =
      calcTargetSlot st o a m r +
        (decide (runsBefore st o (m + 1) ≤ occBefore st o a) ||
          (decide (runsBefore st o (m + 1) ≤ occBefore st o (a + 1)) &&
            decide (st.remAt (probeSlot b o m) < r))).toNat := by
  simp only [calcTargetSlot, List.range_succ, List.filter_append, List.length_append,
    List.filter_cons, List.filter_nil, Bool.decide_or, Bool.decide_and]
  cases (decide (runsBefore st o (m + 1) ≤ occBefore st o a) ||
    (decide (runsBefore st o (m + 1) ≤ occBefore st o (a + 1)) &&
      decide (st.remAt (probeSlot b o m) < r))) <;> rfl

private theorem calcDeleteStopPrefix_zero {b f : ℕ} (st : FilterState b f)
    (o : Fin (2 ^ b)) (a ℓ : ℕ) :
    calcDeleteStopPrefix st o a ℓ 0 = ℓ := rfl

private theorem calcDeleteStopPrefix_succ {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b))
    (a ℓ : ℕ) {m : ℕ} (hm : m < ℓ) :
    let e := calcDeleteStopPrefix st o a ℓ m
    let cond :=
      decide (e = ℓ) && decide (a < m) && decide (occBefore st o m < runsBefore st o (m + 1))
    calcDeleteStopPrefix st o a ℓ (m + 1) = if cond then m else e := by
  intro e cond
  let P : ℕ → Bool := fun k => decide (a < k ∧ occBefore st o k < runsBefore st o (k + 1))
  have hcond_P : (decide (a < m) && decide (occBefore st o m < runsBefore st o (m + 1))) = P m := by
    simp [P, Bool.decide_and]
  change ((List.range (m + 1)).filter P).head?.getD ℓ =
    if (decide (((List.range m).filter P).head?.getD ℓ = ℓ) &&
      decide (a < m) && decide (occBefore st o m < runsBefore st o (m + 1))) = true then m
    else ((List.range m).filter P).head?.getD ℓ
  rw [Bool.and_assoc, hcond_P, List.range_succ, List.filter_append]
  cases hL : List.filter P (List.range m) with
  | nil =>
    simp only [List.nil_append, List.head?_nil, Option.getD_none, decide_true, Bool.true_and,
      List.filter_cons, List.filter_nil]
    cases P m <;> rfl
  | cons x xs =>
    have hx_mem : x ∈ List.filter P (List.range m) := by simp [hL]
    have hx_lt : x < m := List.mem_range.mp (List.mem_of_mem_filter hx_mem)
    have hne : x ≠ ℓ := by omega
    simp [hne]

private theorem queryAnyPrefix_zero {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a : ℕ)
    (r : Fin (2 ^ f)) :
    queryAnyPrefix st o a 0 r = false := rfl

private theorem queryAnyPrefix_succ {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a m : ℕ)
    (r : Fin (2 ^ f)) :
    queryAnyPrefix st o a (m + 1) r =
      (queryAnyPrefix st o a m r ||
        (decide (occBefore st o a < runsBefore st o (m + 1)) &&
          decide (runsBefore st o (m + 1) ≤ occBefore st o (a + 1)) &&
          decide (st.remAt (probeSlot b o m) = r))) := by
  simp [queryAnyPrefix, List.range_succ, List.any_append, Bool.decide_and, Bool.and_assoc]

private theorem clientResult_occBefore_mk (base w w₀ n k : ℕ)
    (q o : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) (a : ℕ) :
    (Memory.spec 0).clientResult s
      (occBeforeProg (mkClusterInput base w w₀ n k q r opTag, (o.val, a))) =
      (a, occBefore (extractFilterState base w w₀ n k s.mem) o a) := by
  dsimp only [occBeforeProg]
  have h := iterate_invariant_of occBeforeStep (mkClusterInput base w w₀ n k q r opTag, o.val)
    (fun j (m : ℕ × ℕ) t =>
      t = s ∧ m.1 + j = a ∧ m.2 = occBefore (extractFilterState base w w₀ n k s.mem) o m.1)
    (fun j ⟨m, occ⟩ t ⟨ht, hmj, hocc⟩ => by
      subst t
      rw [clientResult_occBeforeStep, clientState_occBeforeStep, clientResult_readOcc_mk,
        maskedSlot_probeSlot o m]
      refine ⟨rfl, by dsimp only; omega, ?_⟩
      dsimp only at hocc ⊢
      rw [hocc, occBefore_succ]
      cases (extractFilterState base w w₀ n k s.mem).isOcc (probeSlot (quotBits w₀ n) o m) <;> simp)
    (n := a) (a := (0, 0)) (s := s) ⟨rfl, by omega, rfl⟩
  rcases h with ⟨_, hm1, hm2⟩
  ext
  · omega
  · rw [hm2, show ((Memory.spec 0).clientResult s
      (iterate occBeforeStep (mkClusterInput base w w₀ n k q r opTag, o.val) a (0, 0))).1 = a
      by omega]

private theorem clientResult_scanLoop_mk (base w w₀ n k : ℕ)
    (q o : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) (a ℓ : ℕ) :
    let d := mkClusterInput base w w₀ n k q r opTag
    let st := extractFilterState base w w₀ n k s.mem
    let env : ScanEnv := ⟨d, o.val, a, ℓ, occBefore st o a, occBefore st o (a + 1)⟩
    (Memory.spec 0).clientResult s (scanLoopProg env) =
      ⟨ℓ, runsBefore st o ℓ, occBefore st o ℓ, calcRunStart st o a ℓ, calcTargetSlot st o a ℓ r,
        calcDeleteStop st o a ℓ, (queryAnyPrefix st o a ℓ r).toNat⟩ := by
  intro d st env
  let snap (i : ℕ) : ScanState :=
    ⟨i, runsBefore st o i, occBefore st o i, calcRunStart st o a i, calcTargetSlot st o a i r,
      calcDeleteStopPrefix st o a ℓ i, (queryAnyPrefix st o a i r).toNat⟩
  have h := iterate_invariant_of scanLoopStep env
    (fun j m t => t = s ∧ j ≤ ℓ ∧ m = snap (ℓ - j))
    (fun j m t ⟨ht, hj, hm⟩ => by
      subst ht hm
      set i := ℓ - (j + 1)
      rw [clientState_scanLoopStep, show ℓ - j = i + 1 by omega]
      refine ⟨rfl, by omega, ?_⟩
      unfold scanLoopStep
      rw [clientResult_bind, clientState_scanStepReads,
        clientResult_bind, clientResult_pure, clientState_pure,
        clientResult_bind, clientState_scanStepTarget,
        clientResult_bind, clientState_scanStepStop,
        clientResult_bind, clientState_scanStepQuery, clientResult_pure,
        clientResult_scanStepTarget, clientResult_scanStepStop, clientResult_scanStepQuery,
        clientResult_scanStepReads]
      have hr_val : (mkClusterInput base w w₀ n k q r opTag).rVal = r.val := rfl
      simp only [snap, env, d, hr_val, clientResult_readOcc_mk,
        clientResult_readRunStart_mk, clientResult_readRem_mk, maskedSlot_probeSlot o i]
      have hruns : runsBefore st o i +
          (st.isRunStart (probeSlot (quotBits w₀ n) o i)).toNat = runsBefore st o (i + 1) := by
        rw [runsBefore_succ]; cases st.isRunStart _ <;> simp
      have hocc : occBefore st o i +
          (st.isOcc (probeSlot (quotBits w₀ n) o i)).toNat = occBefore st o (i + 1) := by
        rw [occBefore_succ]; cases st.isOcc _ <;> simp
      rw [hruns, hocc]
      ext
      iterate 3 rfl
      · rw [calcRunStart_succ]; split_ifs <;> simp [*]
      · rw [calcTargetSlot_succ]
        dsimp only [snap]
        change (if runsBefore st o (i + 1) ≤ occBefore st o a ∨
            runsBefore st o (i + 1) ≤ occBefore st o (a + 1) ∧
              st.remAt (probeSlot (quotBits w₀ n) o i) < r then
            calcTargetSlot st o a i r + 1 else calcTargetSlot st o a i r) = _
        by_cases h1 : runsBefore st o (i + 1) ≤ occBefore st o a <;>
          by_cases h2 : runsBefore st o (i + 1) ≤ occBefore st o (a + 1) <;>
          by_cases h3 : st.remAt (probeSlot (quotBits w₀ n) o i) < r <;> simp [h1, h2, h3]
      · rw [calcDeleteStopPrefix_succ st o a ℓ (by omega)]; split_ifs <;> simp_all
      · rw [queryAnyPrefix_succ]
        dsimp only [st]
        simp only [← Fin.ext_iff]
        cases queryAnyPrefix (extractFilterState base w w₀ n k t.mem) o a i r <;>
          by_cases h1 : occBefore (extractFilterState base w w₀ n k t.mem) o a <
            runsBefore (extractFilterState base w w₀ n k t.mem) o (i + 1) <;>
          by_cases h2 : runsBefore (extractFilterState base w w₀ n k t.mem) o (i + 1) ≤
            occBefore (extractFilterState base w w₀ n k t.mem) o (a + 1) <;>
          by_cases h3 : (extractFilterState base w w₀ n k t.mem).remAt
              (probeSlot (quotBits w₀ n) o i) = r <;> simp [h1, h2, h3])
    (n := ℓ) (a := ⟨0, 0, 0, 0, 0, ℓ, 0⟩) (s := s)
    ⟨rfl, le_rfl, by simp [snap, calcDeleteStopPrefix_zero, queryAnyPrefix_zero,
      calcRunStart_zero, calcTargetSlot_zero, runsBefore, occBefore]⟩
  exact (Nat.sub_zero ℓ ▸ h.2.2)

private theorem clientResult_scanCluster_mk (base w w₀ n k : ℕ)
    (q o : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) (a ℓ : ℕ) (hq : probeSlot (quotBits w₀ n) o a = q) :
    let d := mkClusterInput base w w₀ n k q r opTag
    let st := extractFilterState base w w₀ n k s.mem
    (Memory.spec 0).clientResult s (scanClusterProg (d, (o.val, (a, ℓ)))) =
      ⟨(st.isOcc q).toNat, calcRunStart st o a ℓ, calcTargetSlot st o a ℓ r,
        calcDeleteStop st o a ℓ, (queryAnyPrefix st o a ℓ r).toNat⟩ := by
  intro d st
  unfold scanClusterProg
  rw [clientResult_bind, clientState_occBefore, clientResult_occBefore_mk,
    clientResult_bind, clientState_readOcc,
    clientResult_bind, clientResult_pure, clientState_pure,
    clientResult_bind, clientState_scanLoop, clientResult_pure]
  dsimp only [d]
  rw [show (mkClusterInput base w w₀ n k q r opTag).qVal = q.val from rfl,
    clientResult_readOcc_mk, maskedSlot_fin q]
  have hocc_a1 : occBefore st o a + (st.isOcc q).toNat = occBefore st o (a + 1) := by
    rw [occBefore_succ, hq]
    cases st.isOcc q <;> rfl
  rw [hocc_a1, clientResult_scanLoop_mk]

private theorem copySlot_spec_mk (base w w₀ n k : ℕ)
    (q o : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) (srcIdx dstIdx next : ℕ) :
    let d := mkClusterInput base w w₀ n k q r opTag
    let st := extractFilterState base w w₀ n k s.mem
    let src := probeSlot (quotBits w₀ n) o srcIdx
    let dst := probeSlot (quotBits w₀ n) o dstIdx
    let prog := copySlotProg d (o.val + srcIdx) (o.val + dstIdx) next
    extractFilterState base w w₀ n k ((Memory.spec 0).clientState s prog).mem =
      (st.setRunStart dst (st.isRunStart src)).setRem dst (st.remAt src) ∧
    SlotFrame base w w₀ n k s ((Memory.spec 0).clientState s prog) := by
  intro d st src dst prog
  dsimp only [prog, copySlotProg]
  rw [clientState_bind, clientState_readRunStart,
    clientState_bind, clientState_readRem,
    clientState_bind, clientState_bind, clientState_pure,
    clientResult_readRunStart_mk, clientResult_readRem_mk, maskedSlot_probeSlot o srcIdx]
  refine ⟨?_, (slotFrame_writeRunStart_mk _ _ _ _ _ _ _ _ _ _ _).trans
    (slotFrame_writeRem_mk _ _ _ _ _ _ _ _ _ _ _)⟩
  rw [extractFilterState_writeRem_mk, extractFilterState_writeRunStart_mk,
    maskedSlot_probeSlot o dstIdx]

private theorem extractFilterState_shiftRight_aux (base w w₀ n k : ℕ)
    (q o : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s_idx rem : ℕ) (s : Memory.State) :
    let d := mkClusterInput base w w₀ n k q r opTag
    extractFilterState base w w₀ n k
      ((Memory.spec 0).clientState s
        (iterate shiftRightStep (d, o.val) rem (s_idx + rem))).mem =
      shiftRight (extractFilterState base w w₀ n k s.mem) o s_idx rem ∧
    SlotFrame base w w₀ n k s
      ((Memory.spec 0).clientState s
        (iterate shiftRightStep (d, o.val) rem (s_idx + rem))) := by
  intro d
  induction rem generalizing s with
  | zero => exact ⟨rfl, SlotFrame.refl _ _ _ _ _ _⟩
  | succ rem ih =>
    change extractFilterState _ _ _ _ _
      ((Memory.spec 0).clientState s
        (shiftRightStep ((d, o.val), s_idx + (rem + 1)) >>=
          iterate shiftRightStep (d, o.val) rem)).mem = _ ∧ _
    have hstep := copySlot_spec_mk base w w₀ n k q o r opTag s
      (s_idx + rem) (s_idx + rem + 1) (s_idx + rem)
    have heq_step : shiftRightStep ((d, o.val), s_idx + (rem + 1)) =
        copySlotProg d (o.val + (s_idx + rem)) (o.val + (s_idx + rem + 1)) (s_idx + rem) := by
      simp only [shiftRightStep, copySlotProg, pure_bind]
      rw [show s_idx + (rem + 1) - 1 = s_idx + rem by omega,
        show s_idx + (rem + 1) = s_idx + rem + 1 by omega]
    rw [clientState_bind, clientResult_shiftRightStep,
      show ((d, o.val), s_idx + (rem + 1)).2 - 1 = s_idx + rem by dsimp only; omega, heq_step]
    have ih' := ih ((Memory.spec 0).clientState s
      (copySlotProg d (o.val + (s_idx + rem)) (o.val + (s_idx + rem + 1)) (s_idx + rem)))
    exact ⟨by rw [ih'.1, hstep.1]; rfl, hstep.2.trans ih'.2⟩

private theorem extractFilterState_shiftRight_mk (base w w₀ n k : ℕ)
    (q o : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) {s_idx ℓ : ℕ} (hs_le : s_idx ≤ ℓ) :
    let d := mkClusterInput base w w₀ n k q r opTag
    extractFilterState base w w₀ n k
      ((Memory.spec 0).clientState s
        (shiftRightProg ((d, o.val), (ℓ, ℓ - s_idx)))).mem =
      shiftRight (extractFilterState base w w₀ n k s.mem) o s_idx (ℓ - s_idx) ∧
    SlotFrame base w w₀ n k s
      ((Memory.spec 0).clientState s
        (shiftRightProg ((d, o.val), (ℓ, ℓ - s_idx)))) := by
  intro d
  dsimp only [shiftRightProg]
  have h := extractFilterState_shiftRight_aux base w w₀ n k q o r opTag s_idx (ℓ - s_idx) s
  rwa [Nat.add_sub_of_le hs_le] at h

private theorem extractFilterState_insertClearOld_mk (base w w₀ n k : ℕ)
    (q o : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) (s₀ s_idx : ℕ) :
    let d := mkClusterInput base w w₀ n k q r opTag
    let st := extractFilterState base w w₀ n k s.mem
    extractFilterState base w w₀ n k
      ((Memory.spec 0).clientState s
        (insertClearOldProg ((d, o.val), ((st.isOcc q).toNat, (s₀, s_idx))))).mem =
      (if st.isOcc q && decide (s_idx = s₀) then
        st.setRunStart (probeSlot (quotBits w₀ n) o s₀) false
      else st) ∧
    SlotFrame base w w₀ n k s
      ((Memory.spec 0).clientState s
        (insertClearOldProg ((d, o.val), ((st.isOcc q).toNat, (s₀, s_idx))))) := by
  intro d st
  simp only [insertClearOldProg, pure_bind]
  cases hocc : st.isOcc q <;> by_cases hs : s_idx = s₀
  · simp only [Bool.toNat_false, Bool.false_and]
    exact ⟨rfl, SlotFrame.refl _ _ _ _ _ _⟩
  · simp only [Bool.toNat_false, Bool.false_and]
    exact ⟨rfl, SlotFrame.refl _ _ _ _ _ _⟩
  · simp only [Bool.toNat_true, ↓reduceIte, hs, Bool.true_and, decide_true]
    have hz : writeRunStartProg (d, o.val + s₀, 0) =
        writeRunStartProg (d, o.val + s₀, false.toNat) := rfl
    rw [hz, extractFilterState_writeRunStart_mk, maskedSlot_probeSlot o s₀]
    exact ⟨rfl, slotFrame_writeRunStart_mk _ _ _ _ _ _ _ _ _ _ _⟩
  · simp only [Bool.toNat_true, ↓reduceIte, hs, Bool.true_and, decide_false, Bool.false_eq_true]
    exact ⟨rfl, SlotFrame.refl _ _ _ _ _ _⟩

private theorem extractFilterState_insertWriteNew_mk (base w w₀ n k : ℕ)
    (q o : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) (s₀ s_idx ℓ : ℕ) :
    let d := mkClusterInput base w w₀ n k q r opTag
    let st := extractFilterState base w w₀ n k s.mem
    (Memory.spec 0).clientResult s
      (insertWriteNewProg ((d, o.val), ((s₀, s_idx), ℓ))) = 0 ∧
    extractFilterState base w w₀ n k
      ((Memory.spec 0).clientState s
        (insertWriteNewProg ((d, o.val), ((s₀, s_idx), ℓ)))).mem =
      (((st.setRunStart (probeSlot (quotBits w₀ n) o s_idx) (decide (s_idx = s₀))).setRem
        (probeSlot (quotBits w₀ n) o s_idx) r).setOcc q true).setFull
        (probeSlot (quotBits w₀ n) o ℓ) true ∧
    SlotFrame base w w₀ n k s
      ((Memory.spec 0).clientState s
        (insertWriteNewProg ((d, o.val), ((s₀, s_idx), ℓ)))) := by
  intro d st
  unfold insertWriteNewProg
  simp only [pure_bind]
  have hisStart : (if s_idx = s₀ then 1 else 0) = (decide (s_idx = s₀)).toNat := by
    by_cases h : s_idx = s₀ <;> simp [h]
  rw [hisStart,
    clientResult_bind, clientResult_bind, clientResult_bind, clientResult_bind, clientResult_pure,
    clientState_bind, clientState_bind, clientState_bind, clientState_bind, clientState_pure]
  dsimp only [d]
  rw [show (mkClusterInput base w w₀ n k q r opTag).qVal = q.val from rfl,
    show (mkClusterInput base w w₀ n k q r opTag).rVal = r.val from rfl]
  refine ⟨rfl, ?_, (((slotFrame_writeRunStart_mk _ _ _ _ _ _ _ _ _ _ _).trans
      (slotFrame_writeRem_mk _ _ _ _ _ _ _ _ _ _ _)).trans
      (slotFrame_writeOcc_mk _ _ _ _ _ _ _ _ _ _ _)).trans
      (slotFrame_writeFull_mk _ _ _ _ _ _ _ _ _ _ _)⟩
  have h1 : writeOccProg (mkClusterInput base w w₀ n k q r opTag, q.val, 1) =
      writeOccProg (mkClusterInput base w w₀ n k q r opTag, q.val, true.toNat) := rfl
  have h2 : writeFullProg (mkClusterInput base w w₀ n k q r opTag, o.val + ℓ, 1) =
      writeFullProg (mkClusterInput base w w₀ n k q r opTag, o.val + ℓ, true.toNat) := rfl
  rw [h2, extractFilterState_writeFull_mk, h1, extractFilterState_writeOcc_mk,
    extractFilterState_writeRem_mk, extractFilterState_writeRunStart_mk,
    maskedSlot_probeSlot o s_idx, maskedSlot_fin q, maskedSlot_probeSlot o ℓ]

private theorem extractFilterState_insertAfterScan_mk (base w w₀ n k : ℕ)
    (q o : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) (a ℓ : ℕ) (hq : probeSlot (quotBits w₀ n) o a = q) :
    let d := mkClusterInput base w w₀ n k q r opTag
    let st := extractFilterState base w w₀ n k s.mem
    let s₀ := calcRunStart st o a ℓ
    let s_idx := calcTargetSlot st o a ℓ r
    (Memory.spec 0).clientResult s
      (insertAfterScanProg ((d, o.val), (((st.isOcc q).toNat, ℓ), (s₀, s_idx)))) = 0 ∧
    extractFilterState base w w₀ n k
      ((Memory.spec 0).clientState s
        (insertAfterScanProg ((d, o.val), (((st.isOcc q).toNat, ℓ), (s₀, s_idx))))).mem =
      insertCluster st o a ℓ r ∧
    SlotFrame base w w₀ n k s
      ((Memory.spec 0).clientState s
        (insertAfterScanProg ((d, o.val), (((st.isOcc q).toNat, ℓ), (s₀, s_idx))))) := by
  intro d st s₀ s_idx
  have hs_le : s_idx ≤ ℓ := (List.length_filter_le _ _).trans (by simp)
  unfold insertAfterScanProg
  rw [clientResult_bind, clientResult_bind,
    clientResult_pure, clientState_pure, clientResult_bind,
    clientState_bind, clientState_bind,
    clientResult_pure, clientState_pure, clientState_bind]
  have h1 := extractFilterState_insertClearOld_mk base w w₀ n k q o r opTag s s₀ s_idx
  set s₁ := (Memory.spec 0).clientState s
    (insertClearOldProg ((d, o.val), ((st.isOcc q).toNat, (s₀, s_idx))))
  have h2 := extractFilterState_shiftRight_mk base w w₀ n k q o r opTag s₁ hs_le
  set s₂ := (Memory.spec 0).clientState s₁ (shiftRightProg ((d, o.val), (ℓ, ℓ - s_idx)))
  have h3 := extractFilterState_insertWriteNew_mk base w w₀ n k q o r opTag s₂ s₀ s_idx ℓ
  refine ⟨h3.1, ?_, (h1.2.trans h2.2).trans h3.2.2⟩
  rw [h3.2.1, h2.1, h1.1]; dsimp only [insertCluster, s₀, s_idx]; rw [hq]

private theorem clientResult_deleteHasMore_mk (base w w₀ n k : ℕ)
    (q o : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) (s₀ e : ℕ) :
    let d := mkClusterInput base w w₀ n k q r opTag
    let st := extractFilterState base w w₀ n k s.mem
    (Memory.spec 0).clientResult s (deleteHasMoreProg ((d, o.val), (s₀, e))) =
      (decide (s₀ + 1 < e) && !st.isRunStart (probeSlot (quotBits w₀ n) o (s₀ + 1))).toNat := by
  intro d st
  unfold deleteHasMoreProg
  by_cases hlt : s₀ + 1 < e
  · simp only [hlt, ↓reduceIte, clientResult_bind, decide_true, Bool.true_and]
    rw [clientState_readRunStart]
    dsimp only [d]
    rw [clientResult_readRunStart_mk, maskedSlot_probeSlot o (s₀ + 1)]
    cases st.isRunStart (probeSlot (quotBits w₀ n) o (s₀ + 1)) <;> simp
  · simp [hlt]

private theorem clientState_deleteHasMore (s : Memory.State)
    (x : (ClusterInput × ℕ) × (ℕ × ℕ)) :
    (Memory.spec 0).clientState s (deleteHasMoreProg x) = s := by
  rcases x with ⟨⟨d, o⟩, s₀, e⟩
  unfold deleteHasMoreProg
  by_cases hlt : s₀ + 1 < e
  · simp only [hlt, ↓reduceIte]
    rw [clientState_bind, clientState_readRunStart]
    split_ifs <;> rfl
  · simp only [hlt, ↓reduceIte]; rfl

private theorem extractFilterState_shiftLeft_mk (base w w₀ n k : ℕ)
    (q o : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (rem s_idx : ℕ) (s : Memory.State) :
    let d := mkClusterInput base w w₀ n k q r opTag
    extractFilterState base w w₀ n k
      ((Memory.spec 0).clientState s
        (shiftLeftProg ((d, o.val), (s_idx, rem)))).mem =
      shiftLeft (extractFilterState base w w₀ n k s.mem) o s_idx rem ∧
    SlotFrame base w w₀ n k s
      ((Memory.spec 0).clientState s
        (shiftLeftProg ((d, o.val), (s_idx, rem)))) := by
  intro d
  dsimp only [shiftLeftProg]
  induction rem generalizing s s_idx with
  | zero => exact ⟨rfl, SlotFrame.refl _ _ _ _ _ _⟩
  | succ rem ih =>
    change extractFilterState _ _ _ _ _
      ((Memory.spec 0).clientState s
        (shiftLeftStep ((d, o.val), s_idx) >>= iterate shiftLeftStep (d, o.val) rem)).mem = _ ∧ _
    rw [clientState_bind, clientResult_shiftLeftStep]
    have hstep := copySlot_spec_mk base w w₀ n k q o r opTag s (s_idx + 1) s_idx (s_idx + 1)
    have heq_step : shiftLeftStep ((d, o.val), s_idx) =
        copySlotProg d (o.val + (s_idx + 1)) (o.val + s_idx) (s_idx + 1) := rfl
    rw [heq_step]
    have ih' := ih (s_idx + 1) ((Memory.spec 0).clientState s
      (copySlotProg d (o.val + (s_idx + 1)) (o.val + s_idx) (s_idx + 1)))
    exact ⟨by rw [ih'.1, hstep.1]; rfl, hstep.2.trans ih'.2⟩

private theorem extractFilterState_deleteUpdateRun_mk (base w w₀ n k : ℕ)
    (q o : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) (hasMore : Bool) (s₀ s_idx : ℕ) :
    let d := mkClusterInput base w w₀ n k q r opTag
    let st := extractFilterState base w w₀ n k s.mem
    extractFilterState base w w₀ n k
      ((Memory.spec 0).clientState s
        (deleteUpdateRunProg ((d, o.val), (hasMore.toNat, (s₀, s_idx))))).mem =
      (if !hasMore then
        st.setOcc q false
      else if s_idx = s₀ then
        st.setRunStart (probeSlot (quotBits w₀ n) o s₀) true
      else st) ∧
    SlotFrame base w w₀ n k s
      ((Memory.spec 0).clientState s
        (deleteUpdateRunProg ((d, o.val), (hasMore.toNat, (s₀, s_idx))))) := by
  intro d st
  simp only [deleteUpdateRunProg, pure_bind]
  cases hasMore
  · simp only [Bool.toNat_false, ↓reduceIte, Bool.not_false]
    have hz : writeOccProg (mkClusterInput base w w₀ n k q r opTag, q.val, 0) =
        writeOccProg (mkClusterInput base w w₀ n k q r opTag, q.val, false.toNat) := rfl
    rw [show d.qVal = q.val from rfl, hz, extractFilterState_writeOcc_mk, maskedSlot_fin q]
    exact ⟨rfl, slotFrame_writeOcc_mk _ _ _ _ _ _ _ _ _ _ _⟩
  · by_cases hs : s_idx = s₀
    · simp only [Bool.toNat_true, one_ne_zero, ↓reduceIte, hs, Bool.not_true, Bool.false_eq_true]
      have h1 : writeRunStartProg (mkClusterInput base w w₀ n k q r opTag, o.val + s₀, 1) =
          writeRunStartProg (mkClusterInput base w w₀ n k q r opTag, o.val + s₀, true.toNat) := rfl
      rw [h1, extractFilterState_writeRunStart_mk, maskedSlot_probeSlot o s₀]
      exact ⟨rfl, slotFrame_writeRunStart_mk _ _ _ _ _ _ _ _ _ _ _⟩
    · simp only [Bool.toNat_true, one_ne_zero, ↓reduceIte, hs, Bool.not_true, Bool.false_eq_true]
      exact ⟨rfl, SlotFrame.refl _ _ _ _ _ _⟩

private theorem extractFilterState_deleteClearEnd_mk (base w w₀ n k : ℕ)
    (q o : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) (e : ℕ) :
    let d := mkClusterInput base w w₀ n k q r opTag
    let st := extractFilterState base w w₀ n k s.mem
    let p_end := probeSlot (quotBits w₀ n) o (e - 1)
    extractFilterState base w w₀ n k
      ((Memory.spec 0).clientState s (deleteClearEndProg ((d, o.val), e))).mem =
      ((st.setFull p_end false).setRunStart p_end false).setRem p_end
        ⟨0, Nat.two_pow_pos (remBits w₀ k)⟩ ∧
    SlotFrame base w w₀ n k s
      ((Memory.spec 0).clientState s (deleteClearEndProg ((d, o.val), e))) := by
  intro d st p_end
  unfold deleteClearEndProg
  rw [clientState_bind, clientResult_pure, clientState_pure,
    clientState_bind, clientResult_pure, clientState_pure,
    clientState_bind, clientState_bind]
  refine ⟨?_, ((slotFrame_writeFull_mk _ _ _ _ _ _ _ _ _ _ _).trans
    (slotFrame_writeRunStart_mk _ _ _ _ _ _ _ _ _ _ _)).trans
    (slotFrame_writeRem_mk _ _ _ _ _ _ _ _ _ _ _)⟩
  let zeroRem : Fin (2 ^ remBits w₀ k) := ⟨0, Nat.two_pow_pos _⟩
  have hrm : writeRemProg (d, o.val + (e - 1), 0) =
      writeRemProg (d, o.val + (e - 1), zeroRem.val) := rfl
  have hrs : writeRunStartProg (d, o.val + (e - 1), 0) =
      writeRunStartProg (d, o.val + (e - 1), false.toNat) := rfl
  have hfl : writeFullProg (d, o.val + (e - 1), 0) =
      writeFullProg (d, o.val + (e - 1), false.toNat) := rfl
  rw [hrm, extractFilterState_writeRem_mk, hrs, extractFilterState_writeRunStart_mk,
    hfl, extractFilterState_writeFull_mk, maskedSlot_probeSlot o (e - 1)]

private theorem deleteAfterScan_spec_of_lt (base w w₀ n k : ℕ)
    (q o : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) (s₀ s_idx e : ℕ) (hlt : s_idx < e) :
    let d := mkClusterInput base w w₀ n k q r opTag
    let st := extractFilterState base w w₀ n k s.mem
    let hasMore := decide (s₀ + 1 < e) && !st.isRunStart (probeSlot (quotBits w₀ n) o (s₀ + 1))
    let st1 := shiftLeft st o s_idx (e - 1 - s_idx)
    let st2 := if !hasMore then st1.setOcc q false
      else if s_idx = s₀ then st1.setRunStart (probeSlot (quotBits w₀ n) o s₀) true else st1
    let p_end := probeSlot (quotBits w₀ n) o (e - 1)
    (Memory.spec 0).clientResult s (deleteAfterScanProg ((d, o.val), ((s₀, s_idx), e))) = 0 ∧
    extractFilterState base w w₀ n k
      ((Memory.spec 0).clientState s (deleteAfterScanProg ((d, o.val), ((s₀, s_idx), e)))).mem =
      ((st2.setFull p_end false).setRunStart p_end false).setRem p_end
        ⟨0, Nat.two_pow_pos (remBits w₀ k)⟩ ∧
    SlotFrame base w w₀ n k s
      ((Memory.spec 0).clientState s (deleteAfterScanProg ((d, o.val), ((s₀, s_idx), e)))) := by
  intro d st hasMore st1 st2 p_end
  unfold deleteAfterScanProg; simp only [hlt, ↓reduceIte, pure_bind]
  rw [clientResult_bind, clientState_deleteHasMore,
    clientResult_deleteHasMore_mk, clientResult_bind,
    clientResult_bind, clientResult_bind, clientResult_pure,
    clientState_bind, clientState_deleteHasMore,
    clientResult_deleteHasMore_mk, clientState_bind,
    clientState_bind, clientState_bind, clientState_pure]
  have h1 := extractFilterState_shiftLeft_mk base w w₀ n k q o r opTag (e - 1 - s_idx) s_idx s
  set s₁ := (Memory.spec 0).clientState s (shiftLeftProg ((d, o.val), (s_idx, e - 1 - s_idx)))
  have h2 := extractFilterState_deleteUpdateRun_mk base w w₀ n k q o r opTag s₁ hasMore s₀ s_idx
  set s₂ := (Memory.spec 0).clientState s₁
    (deleteUpdateRunProg ((d, o.val), (hasMore.toNat, (s₀, s_idx))))
  have h3 := extractFilterState_deleteClearEnd_mk base w w₀ n k q o r opTag s₂ e
  exact ⟨rfl, by rw [h3.1, h2.1, h1.1], (h1.2.trans h2.2).trans h3.2⟩

private theorem extractFilterState_deleteAfterScan_mk (base w w₀ n k : ℕ)
    (q o : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) (a ℓ : ℕ) (hq : probeSlot (quotBits w₀ n) o a = q)
    (hs_lt_e :
      calcTargetSlot (extractFilterState base w w₀ n k s.mem) o a ℓ r <
        calcDeleteStop (extractFilterState base w w₀ n k s.mem) o a ℓ) :
    let d := mkClusterInput base w w₀ n k q r opTag
    let st := extractFilterState base w w₀ n k s.mem
    let s₀ := calcRunStart st o a ℓ
    let s_idx := calcTargetSlot st o a ℓ r
    let e := calcDeleteStop st o a ℓ
    (Memory.spec 0).clientResult s
      (deleteAfterScanProg ((d, o.val), ((s₀, s_idx), e))) = 0 ∧
    extractFilterState base w w₀ n k
      ((Memory.spec 0).clientState s
        (deleteAfterScanProg ((d, o.val), ((s₀, s_idx), e)))).mem =
      deleteCluster st o a ℓ r ∧
    SlotFrame base w w₀ n k s
      ((Memory.spec 0).clientState s
        (deleteAfterScanProg ((d, o.val), ((s₀, s_idx), e)))) := by
  intro d st s₀ s_idx e
  simpa only [deleteCluster, hq] using
    deleteAfterScan_spec_of_lt base w w₀ n k q o r opTag s s₀ s_idx e hs_lt_e

private theorem FilterInv.calcTargetSlot_lt_calcDeleteStop_of_mem {U b f n : ℕ}
    {S : Finset (Fin U)} {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)}
    {st : FilterState b f} (hinv : FilterInv n S quot rem st)
    (hS_lt : #S < 2 ^ b) {u : Fin U} (hu : u ∈ S) :
    let q := quot u
    let o := hinv.clusterStart hS_lt q
    let a := hinv.backLen hS_lt q
    let ℓ := hinv.clusterLen hS_lt q
    calcTargetSlot st o a ℓ (rem u) < calcDeleteStop st o a ℓ := by
  intro q o a ℓ
  have hq_probe : q = probeSlot b o a := by
    simpa [o, FilterInv.clusterStart] using (probeSlot_backSlot_add q a 0).symm
  have ha_lt : a < ℓ := Nat.lt_add_of_pos_right (hinv.fwdLen_pos_of_mem hS_lt hu)
  have hvalid₀ := hinv.intervalValid_cluster hS_lt q
  obtain ⟨ha_lt_e, _, he_run, _⟩ := hvalid₀.calcDeleteStop_spec hinv.isOcc_eq ha_lt
  have hs_eq := hvalid₀.calcTargetSlot_eq hinv.isOcc_eq ha_lt (rem u)
  have hr_mem : rem u ∈ bucketRun S quot rem (probeSlot b o a) :=
    (mem_bucketRun_iff S quot rem _ (rem u)).mpr ⟨u, hu, hq_probe, rfl⟩
  have hcnt_lt : (bucketRun S quot rem (probeSlot b o a)).countP (· < rem u) <
      (bucketRun S quot rem (probeSlot b o a)).length :=
    Nat.lt_of_le_of_ne List.countP_le_length fun h =>
      lt_irrefl (rem u) (by simpa using List.countP_eq_length.mp h (rem u) hr_mem)
  rw [hs_eq]
  exact (Nat.add_lt_add_left hcnt_lt _).trans_le
    (by rw [← runOffset_succ, ← he_run]; exact runOffset_mono S quot rem o ha_lt_e)

private theorem clusterOpProg_mk_eq {U : ℕ} {S : Finset (Fin U)} (base w w₀ n k : ℕ)
    {quot : Fin U → Fin (2 ^ quotBits w₀ n)} {rem : Fin U → Fin (2 ^ remBits w₀ k)}
    (u : Fin U) (opTag : ℕ) (s : Memory.State)
    (hinv : FilterInv n S quot rem (extractFilterState base w w₀ n k s.mem))
    (hS_lt : #S < 2 ^ quotBits w₀ n) :
    let d := mkClusterInput base w w₀ n k (quot u) (rem u) opTag
    let st := extractFilterState base w w₀ n k s.mem
    let o := hinv.clusterStart hS_lt (quot u)
    let a := hinv.backLen hS_lt (quot u)
    let ℓ := hinv.clusterLen hS_lt (quot u)
    let scan : ScanResult := ⟨(st.isOcc (quot u)).toNat, calcRunStart st o a ℓ,
      calcTargetSlot st o a ℓ (rem u), calcDeleteStop st o a ℓ,
      (queryAnyPrefix st o a ℓ (rem u)).toNat⟩
    probeSlot (quotBits w₀ n) o a = quot u ∧
    (Memory.spec 0).clientResult s (clusterOpProg d) =
      (Memory.spec 0).clientResult s (clusterDispatchProg ((d, (o.val, (a, ℓ))), scan)) ∧
    (Memory.spec 0).clientState s (clusterOpProg d) =
      (Memory.spec 0).clientState s (clusterDispatchProg ((d, (o.val, (a, ℓ))), scan)) := by
  intro d st o a ℓ scan
  have hq : probeSlot (quotBits w₀ n) o a = quot u := by
    simpa [o, FilterInv.clusterStart] using probeSlot_backSlot_add (quot u) a 0
  unfold clusterOpProg
  rw [clientResult_bind, clientState_findCluster,
    clientResult_findCluster_mk _ _ _ _ _ _ _ _ _ hinv hS_lt,
    clientResult_bind, clientState_scanCluster,
    clientResult_scanCluster_mk _ _ _ _ _ _ _ _ _ _ _ _ hq,
    clientState_bind, clientState_findCluster,
    clientResult_findCluster_mk _ _ _ _ _ _ _ _ _ hinv hS_lt,
    clientState_bind, clientState_scanCluster,
    clientResult_scanCluster_mk _ _ _ _ _ _ _ _ _ _ _ _ hq]
  exact ⟨hq, rfl, rfl⟩

theorem clusterOpProg_mk_insert {U : ℕ} {S : Finset (Fin U)} (base w w₀ n k : ℕ)
    {quot : Fin U → Fin (2 ^ quotBits w₀ n)} {rem : Fin U → Fin (2 ^ remBits w₀ k)}
    (u : Fin U) (s : Memory.State)
    (hinv : FilterInv n S quot rem (extractFilterState base w w₀ n k s.mem))
    (hS_lt : #S < 2 ^ quotBits w₀ n) :
    let d := mkClusterInput base w w₀ n k (quot u) (rem u) 0
    (Memory.spec 0).clientResult s (clusterOpProg d) = 0 ∧
    extractFilterState base w w₀ n k ((Memory.spec 0).clientState s (clusterOpProg d)).mem =
      hinv.insertState hS_lt u ∧
    SlotFrame base w w₀ n k s ((Memory.spec 0).clientState s (clusterOpProg d)) := by
  intro _
  obtain ⟨hq, hres, hst⟩ := clusterOpProg_mk_eq base w w₀ n k u 0 s hinv hS_lt
  rw [hres, hst]
  unfold clusterDispatchProg
  simp only [mkClusterInput, ↓reduceIte]
  exact extractFilterState_insertAfterScan_mk base w w₀ n k (quot u)
    (hinv.clusterStart hS_lt (quot u)) (rem u) 0 s
    (hinv.backLen hS_lt (quot u)) (hinv.clusterLen hS_lt (quot u)) hq

theorem clusterOpProg_mk_delete {U : ℕ} {S : Finset (Fin U)} (base w w₀ n k : ℕ)
    {quot : Fin U → Fin (2 ^ quotBits w₀ n)} {rem : Fin U → Fin (2 ^ remBits w₀ k)}
    {u : Fin U} (hu : u ∈ S) (s : Memory.State)
    (hinv : FilterInv n S quot rem (extractFilterState base w w₀ n k s.mem))
    (hS_lt : #S < 2 ^ quotBits w₀ n) :
    let d := mkClusterInput base w w₀ n k (quot u) (rem u) 1
    (Memory.spec 0).clientResult s (clusterOpProg d) = 0 ∧
    extractFilterState base w w₀ n k ((Memory.spec 0).clientState s (clusterOpProg d)).mem =
      hinv.deleteState hS_lt u ∧
    SlotFrame base w w₀ n k s ((Memory.spec 0).clientState s (clusterOpProg d)) := by
  intro _
  obtain ⟨hq, hres, hst⟩ := clusterOpProg_mk_eq base w w₀ n k u 1 s hinv hS_lt
  rw [hres, hst]
  unfold clusterDispatchProg
  simp only [mkClusterInput, one_ne_zero, ↓reduceIte]
  exact extractFilterState_deleteAfterScan_mk base w w₀ n k (quot u)
    (hinv.clusterStart hS_lt (quot u)) (rem u) 1 s
    (hinv.backLen hS_lt (quot u)) (hinv.clusterLen hS_lt (quot u)) hq
    (hinv.calcTargetSlot_lt_calcDeleteStop_of_mem hS_lt hu)

theorem clusterOpProg_mk_query {U : ℕ} {S : Finset (Fin U)} (base w w₀ n k : ℕ)
    {quot : Fin U → Fin (2 ^ quotBits w₀ n)} {rem : Fin U → Fin (2 ^ remBits w₀ k)}
    (u : Fin U) (s : Memory.State)
    (hinv : FilterInv n S quot rem (extractFilterState base w w₀ n k s.mem))
    (hS_lt : #S < 2 ^ quotBits w₀ n) :
    let d := mkClusterInput base w w₀ n k (quot u) (rem u) 2
    (Memory.spec 0).clientResult s (clusterOpProg d) =
      (decide (rem u ∈ bucketRun S quot rem (quot u))).toNat ∧
    (Memory.spec 0).clientState s (clusterOpProg d) = s := by
  intro _
  obtain ⟨hq, hres, hst⟩ := clusterOpProg_mk_eq base w w₀ n k u 2 s hinv hS_lt
  rw [hres, hst]
  simp only [clusterDispatchProg, mkClusterInput, OfNat.ofNat_ne_zero, Nat.reduceEqDiff,
    ↓reduceIte]
  refine ⟨?_, rfl⟩
  have hq_eq : queryCluster (extractFilterState base w w₀ n k s.mem)
      (hinv.clusterStart hS_lt (quot u)) (hinv.backLen hS_lt (quot u))
      (hinv.clusterLen hS_lt (quot u)) (rem u) =
      decide (rem u ∈ bucketRun S quot rem (quot u)) := by
    rw [Bool.eq_iff_iff, decide_eq_true_eq]
    exact (hinv.querySlot_eq_true_iff hS_lt u).trans (mem_bucketRun_iff S quot rem ..).symm
  rw [← hq_eq]; dsimp only [queryCluster]; rw [hq]
  cases (extractFilterState base w w₀ n k s.mem).isOcc (quot u) <;>
    cases queryAnyPrefix (extractFilterState base w w₀ n k s.mem)
      (hinv.clusterStart hS_lt (quot u)) (hinv.backLen hS_lt (quot u))
      (hinv.clusterLen hS_lt (quot u)) (rem u) <;> rfl


/-- Memory admissibility (`ValidHistory`) of `clusterOpProg` on `mkClusterInput`. -/
theorem validHistory_clusterOp_mk {base w w₀ n k : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hfront : base + space w w₀ n k ≤ s.frontier)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) {opTag : ℕ}
    (hcs : ClusterSafe w (mkClusterInput base w w₀ n k q r opTag)) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (clusterOpProg (mkClusterInput base w w₀ n k q r opTag))) :=
  validHistory_clusterOp hcs (clusterMemSafe_mkClusterInput hwf hfront q r opTag)

/-- On any `FilterInv`-valid state, `clusterOpProg` performs at most `11 * ℓ + 13` memory
operations on a cluster of length `ℓ = hinv.clusterLen hS_lt q`. -/
theorem memoryCost_clusterOp_mk_le {U : ℕ} {S : Finset (Fin U)} (base w w₀ n k : ℕ)
    {quot : Fin U → Fin (2 ^ quotBits w₀ n)} {rem : Fin U → Fin (2 ^ remBits w₀ k)}
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k))
    (opTag : ℕ) (s : Memory.State)
    (hinv : FilterInv n S quot rem (extractFilterState base w w₀ n k s.mem))
    (hS_lt : #S < 2 ^ quotBits w₀ n) :
    memoryCost (clusterOpProg (mkClusterInput base w w₀ n k q r opTag)) s ≤
      11 * hinv.clusterLen hS_lt q + 13 := by
  have hmc := memoryCost_clusterOp_le (mkClusterInput base w w₀ n k q r opTag) s
  rw [clientResult_findCluster_mk base w w₀ n k q r opTag s hinv hS_lt] at hmc
  exact hmc

end Cslib.DataStructure.ApproximateMembership.QuotientFilter
