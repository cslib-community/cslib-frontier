/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.ApproximateMembership.WordRAM.QuotientFilter.SlotArray
public import CslibFrontier.Computability.WordRAM.Realization.WhileAbsorb
public import CslibFrontier.Computability.WordRAM.Realization.Witness
public import CslibFrontier.Computability.WordRAM.Realization.WordEncoding.Equiv
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Tactic.FinIndex
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize
import CslibFrontier.Tactic.SuppCases
import Mathlib.Data.Nat.Bitwise

/-!
# Memory-Program Realization of Quotient-Filter Cluster Operations

This file implements and certifies the deterministic cluster-level operations (`queryCluster`,
`insertCluster`, `deleteCluster`) of the Word-RAM quotient filter as `Memory.Prog` programs
compiled to width-independent `WordRAM.Code` via the `realize` tactic.
-/

public section

namespace Cslib.DataStructure.ApproximateMembership.QuotientFilter

open Finset
open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.Dictionary.WordRAM.LinearProbing

-- Preserve the ordinary simplifier behavior formerly supplied by this module's duplicate rule.
attribute [simp] Cslib.WordRAM.Realization.memoryCost_bind'

/-! ## Section 1: Cluster operation input tuple (`ClusterInput`) -/

/-- The 15-word input tuple passed to the quotient-filter cluster operation program:
* `d 0 = q.val` (target quotient slot)
* `d 1 = r.val` (target remainder)
* `d 2 = opTag` (`0` = insert, `1` = delete, `2` = query)
* `d 3 = 2 ^ b` (slot count)
* `d 4 = 2 ^ b - 1` (slot mask)
* `d 5 = fullBase`
* `d 6 = occBase`
* `d 7 = runBase`
* `d 8 = remBase`
* `d 9 = pBit` (`slotPackShift b 1 w`)
* `d 10 = 2 ^ pBit - 1`
* `d 11 = pRem` (`slotPackShift b f w`)
* `d 12 = 2 ^ pRem - 1`
* `d 13 = f` (`remBits w₀ k`)
* `d 14 = 2 ^ f - 1` -/
abbrev ClusterInput : Type := Fin 15 → ℕ

instance : WordEncoding ClusterInput := ⟨15, .refl (Fin 15 → ℕ)⟩

/-- Construct the `ClusterInput` parameter vector for `(base, w, w₀, n, k)` and `(q, r, opTag)`. -/
@[expose] def mkClusterInput (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ) : ClusterInput :=
  let b := quotBits w₀ n
  let f := remBits w₀ k
  let pBit := slotPackShift b 1 w
  let pRem := slotPackShift b f w
  ![q.val, r.val, opTag, 2 ^ b, 2 ^ b - 1,
    fullBase base w w₀ n, occBase base w w₀ n, runBase base w w₀ n, remBase base w w₀ n,
    pBit, 2 ^ pBit - 1, pRem, 2 ^ pRem - 1, f, 2 ^ f - 1]

@[simp] theorem mkClusterInput_0 (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ) :
    mkClusterInput base w w₀ n k q r opTag 0 = q.val := rfl

@[simp] theorem mkClusterInput_1 (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ) :
    mkClusterInput base w w₀ n k q r opTag 1 = r.val := rfl

@[simp] theorem mkClusterInput_2 (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ) :
    mkClusterInput base w w₀ n k q r opTag 2 = opTag := rfl

@[simp] theorem mkClusterInput_3 (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ) :
    mkClusterInput base w w₀ n k q r opTag 3 = 2 ^ quotBits w₀ n := rfl

@[simp] theorem mkClusterInput_4 (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ) :
    mkClusterInput base w w₀ n k q r opTag 4 = 2 ^ quotBits w₀ n - 1 := rfl

@[simp] theorem mkClusterInput_5 (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ) :
    mkClusterInput base w w₀ n k q r opTag 5 = fullBase base w w₀ n := rfl

@[simp] theorem mkClusterInput_6 (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ) :
    mkClusterInput base w w₀ n k q r opTag 6 = occBase base w w₀ n := rfl

@[simp] theorem mkClusterInput_7 (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ) :
    mkClusterInput base w w₀ n k q r opTag 7 = runBase base w w₀ n := rfl

@[simp] theorem mkClusterInput_8 (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ) :
    mkClusterInput base w w₀ n k q r opTag 8 = remBase base w w₀ n := rfl

@[simp] theorem mkClusterInput_9 (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ) :
    mkClusterInput base w w₀ n k q r opTag 9 = slotPackShift (quotBits w₀ n) 1 w := rfl

@[simp] theorem mkClusterInput_10 (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ) :
    mkClusterInput base w w₀ n k q r opTag 10 =
      2 ^ slotPackShift (quotBits w₀ n) 1 w - 1 := rfl

@[simp] theorem mkClusterInput_11 (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ) :
    mkClusterInput base w w₀ n k q r opTag 11 =
      slotPackShift (quotBits w₀ n) (remBits w₀ k) w := rfl

@[simp] theorem mkClusterInput_12 (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ) :
    mkClusterInput base w w₀ n k q r opTag 12 =
      2 ^ slotPackShift (quotBits w₀ n) (remBits w₀ k) w - 1 := rfl

@[simp] theorem mkClusterInput_13 (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ) :
    mkClusterInput base w w₀ n k q r opTag 13 = remBits w₀ k := rfl

@[simp] theorem mkClusterInput_14 (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ) :
    mkClusterInput base w w₀ n k q r opTag 14 = 2 ^ remBits w₀ k - 1 := rfl

/-- Word-level safety envelope for `ClusterInput` at word width `w`. -/
structure ClusterSafe (w : ℕ) (d : ClusterInput) : Prop where
  one_lt_two_pow : 1 < 2 ^ w
  cap_pos : 0 < d 3
  q_lt : d 0 < d 3
  r_le : d 1 ≤ d 14
  op_lt : d 2 < 4
  cap_ge_eight : 8 ≤ d 3
  two_cap_le : 2 * d 3 ≤ 2 ^ w
  mask_lt : d 4 < d 3
  full_lt : d 5 + (d 4 >>> d 9) < 2 ^ w
  occ_lt : d 6 + (d 4 >>> d 9) < 2 ^ w
  run_lt : d 7 + (d 4 >>> d 9) < 2 ^ w
  rem_lt : d 8 + (d 4 >>> d 11) < 2 ^ w
  pBit_lt : d 9 < w
  pBitMask_lt : d 10 < w
  pRem_lt : d 11 < w
  pRemMask_lt : d 12 < 2 ^ w
  f_lt : d 13 < w
  remPack_le : (d 12 + 1) * d 13 ≤ w
  fMask_lt_f : d 14 < 2 ^ (d 13)
  fMask_lt : d 14 < 2 ^ w

private theorem ClusterSafe.two_cap_lt {w : ℕ} {d : ClusterInput} (h : ClusterSafe w d) :
    8 ≤ d 3 ∧ 2 * d 3 ≤ 2 ^ w :=
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
    d 5 + (d 4 >>> d 9) < bound ∧ d 6 + (d 4 >>> d 9) < bound ∧
    d 7 + (d 4 >>> d 9) < bound ∧ d 8 + (d 4 >>> d 11) < bound := by
  let b := quotBits w₀ n
  let maxSlot : Fin (2 ^ b) := ⟨2 ^ b - 1, Nat.sub_lt (Nat.two_pow_pos b) one_pos⟩
  have hbit : (2 ^ b - 1) >>> slotPackShift b 1 w < packedWords b 1 w :=
    shiftRight_lt_packedWords b 1 w maxSlot
  have hrem : (2 ^ b - 1) >>> slotPackShift b (remBits w₀ k) w <
      packedWords b (remBits w₀ k) w :=
    shiftRight_lt_packedWords b (remBits w₀ k) w maxSlot
  have hremEnd : remBase base w w₀ n + packedWords (quotBits w₀ n) (remBits w₀ k) w ≤ bound := by
    rwa [remBase_add_packedWords_eq]
  dsimp only [b, remBase, runBase, occBase] at hbit hrem hremEnd
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mkClusterInput_5, mkClusterInput_4, mkClusterInput_9]; omega
  · rw [mkClusterInput_6, mkClusterInput_4, mkClusterInput_9]; dsimp only [occBase]; omega
  · rw [mkClusterInput_7, mkClusterInput_4, mkClusterInput_9]; dsimp only [runBase, occBase]; omega
  · rw [mkClusterInput_8, mkClusterInput_4, mkClusterInput_11]
    dsimp only [remBase, runBase, occBase]; omega

private theorem clusterSafe_mkClusterInput {base w w₀ n k : ℕ}
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
  have hpRem_le : slotPackShift (quotBits w₀ n) (remBits w₀ k) w ≤ quotBits w₀ n := min_le_left _ _
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

private theorem encode_lt_of_clusterSafe {w : ℕ} {d : ClusterInput} (hcs : ClusterSafe w d)
    (i : Fin (WordEncoding.width ClusterInput)) :
    WordEncoding.encode d i < 2 ^ w := by
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
      d 0 < 2 ^ w ∧ d 1 < 2 ^ w ∧ d 2 < 2 ^ w ∧ d 3 < 2 ^ w ∧ d 4 < 2 ^ w ∧
      d 5 < 2 ^ w ∧ d 6 < 2 ^ w ∧ d 7 < 2 ^ w ∧ d 8 < 2 ^ w ∧ d 9 < 2 ^ w ∧
      d 10 < 2 ^ w ∧ d 11 < 2 ^ w ∧ d 12 < 2 ^ w ∧ d 13 < 2 ^ w ∧ d 14 < 2 ^ w := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> fits
  fin_cases i
  exacts [h0, h1, h2, h3, h4, h5', h6', h7', h8', h9, h10, h11, h12, h13, h14]

private theorem encode_mkClusterInput_lt {base w w₀ n k : ℕ}
    (hw₀ : 0 < w₀) (hw : 2 * w₀ ≤ w)
    (hfit : Fits w (base + space w w₀ n k))
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k))
    {opTag : ℕ} (hop : opTag < 4)
    (i : Fin (WordEncoding.width ClusterInput)) :
    WordEncoding.encode (mkClusterInput base w w₀ n k q r opTag) i < 2 ^ w :=
  encode_lt_of_clusterSafe (clusterSafe_mkClusterInput hw₀ hw hfit q r hop) i

/-! ## Section 2: Comparison and bit-packed accessor programs -/

@[simp] theorem clientResult_pure {α : Type} (s : Memory.State) (a : α) :
    (Memory.spec 0).clientResult s (pure a) = a := rfl

theorem clientState_pure {α : Type} (s : Memory.State) (a : α) :
    (Memory.spec 0).clientState s (pure a) = s := rfl

/-- `<` test returning `(a < b).toNat`. -/
@[expose] def cmpLtProg (x : ℕ × ℕ) : Memory.Prog ℕ :=
  if x.1 < x.2 then pure 1 else pure 0

private theorem realizes_cmpLt :
    Realizes .exact cmpLtProg WordEncoding.encode WordEncoding.encode
      (fun w _ _ => 1 < 2 ^ w) (fun _ _ => 0) := by
  realize
  exact h

@[simp] private theorem clientResult_cmpLt (s : Memory.State) (x : ℕ × ℕ) :
    (Memory.spec 0).clientResult s (cmpLtProg x) = (decide (x.1 < x.2)).toNat := by
  dsimp only [cmpLtProg]
  split_ifs with h <;> simp [h]

theorem clientResult_cmpLt_le (s : Memory.State) (x : ℕ × ℕ) :
    (Memory.spec 0).clientResult s (cmpLtProg x) ≤ 1 := by
  rw [clientResult_cmpLt]
  exact Bool.toNat_le _

private theorem clientState_cmpLt (s : Memory.State) (x : ℕ × ℕ) :
    (Memory.spec 0).clientState s (cmpLtProg x) = s := by
  dsimp only [cmpLtProg]
  split_ifs <;> rfl

/-- `=` test returning `(a = b).toNat`. -/
@[expose] def cmpEqProg (x : ℕ × ℕ) : Memory.Prog ℕ :=
  if x.1 = x.2 then pure 1 else pure 0

private theorem realizes_cmpEq :
    Realizes .exact cmpEqProg WordEncoding.encode WordEncoding.encode
      (fun w _ _ => 1 < 2 ^ w) (fun _ _ => 0) := by
  realize
  exact h

@[simp] private theorem clientResult_cmpEq (s : Memory.State) (x : ℕ × ℕ) :
    (Memory.spec 0).clientResult s (cmpEqProg x) = (decide (x.1 = x.2)).toNat := by
  dsimp only [cmpEqProg]
  split_ifs with h <;> simp [h]

private theorem clientResult_cmpEq_le (s : Memory.State) (x : ℕ × ℕ) :
    (Memory.spec 0).clientResult s (cmpEqProg x) ≤ 1 := by
  rw [clientResult_cmpEq]
  exact Bool.toNat_le _

private theorem clientState_cmpEq (s : Memory.State) (x : ℕ × ℕ) :
    (Memory.spec 0).clientState s (cmpEqProg x) = s := by
  dsimp only [cmpEqProg]
  split_ifs <;> rfl

/-- `= 0` test returning `(a = 0).toNat`. -/
@[expose] def cmpZeroProg (a : ℕ) : Memory.Prog ℕ :=
  if a = 0 then pure 1 else pure 0

private theorem realizes_cmpZero :
    Realizes .exact cmpZeroProg WordEncoding.encode WordEncoding.encode
      (fun w _ _ => 1 < 2 ^ w) (fun _ _ => 0) := by
  realize
  exact h

@[simp] private theorem clientResult_cmpZero (s : Memory.State) (a : ℕ) :
    (Memory.spec 0).clientResult s (cmpZeroProg a) = (decide (a = 0)).toNat := by
  dsimp only [cmpZeroProg]
  split_ifs with h <;> simp [h]

theorem clientResult_cmpZero_le (s : Memory.State) (a : ℕ) :
    (Memory.spec 0).clientResult s (cmpZeroProg a) ≤ 1 := by
  rw [clientResult_cmpZero]
  exact Bool.toNat_le _

private theorem clientState_cmpZero (s : Memory.State) (a : ℕ) :
    (Memory.spec 0).clientState s (cmpZeroProg a) = s := by
  dsimp only [cmpZeroProg]
  split_ifs <;> rfl

/-- Conditional selector `if 0 < c then t else e`. -/
@[expose] def selectPosProg (x : ℕ × (ℕ × ℕ)) : Memory.Prog ℕ :=
  let (cond, t, e) := x
  if 0 < cond then pure t else pure e

theorem realizes_selectPos :
    Realizes .exact selectPosProg WordEncoding.encode WordEncoding.encode
      (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

@[simp] theorem clientResult_selectPos (s : Memory.State) (x : ℕ × (ℕ × ℕ)) :
    (Memory.spec 0).clientResult s (selectPosProg x) =
      let (cond, t, e) := x
      if 0 < cond then t else e := by
  dsimp only [selectPosProg]
  split_ifs <;> rfl

theorem clientState_selectPos (s : Memory.State) (x : ℕ × (ℕ × ℕ)) :
    (Memory.spec 0).clientState s (selectPosProg x) = s := by
  dsimp only [selectPosProg]
  split_ifs <;> rfl

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

/-- Read `isFull` at slot index `x.2 &&& d 4`. -/
@[expose] def readFullProg (x : ClusterInput × ℕ) : Memory.Prog ℕ := do
  let idx := x.2 &&& x.1 4
  let wVal ← Memory.read (x.1 5 + (idx >>> x.1 9))
  pure ((wVal >>> (idx &&& x.1 10)) &&& 1)

private theorem realizes_readFull :
    Realizes .exact readFullProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1) (fun _ _ => 0) := by
  realize
  · exact masked_addr_lt h.full_lt
  · exact h.one_lt_two_pow

/-- Read `isOcc` at slot index `x.2 &&& d 4`. -/
@[expose] def readOccProg (x : ClusterInput × ℕ) : Memory.Prog ℕ := do
  let idx := x.2 &&& x.1 4
  let wVal ← Memory.read (x.1 6 + (idx >>> x.1 9))
  pure ((wVal >>> (idx &&& x.1 10)) &&& 1)

private theorem realizes_readOcc :
    Realizes .exact readOccProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1) (fun _ _ => 0) := by
  realize
  · exact masked_addr_lt h.occ_lt
  · exact h.one_lt_two_pow

/-- Read `isRunStart` at slot index `x.2 &&& d 4`. -/
@[expose] def readRunStartProg (x : ClusterInput × ℕ) : Memory.Prog ℕ := do
  let idx := x.2 &&& x.1 4
  let wVal ← Memory.read (x.1 7 + (idx >>> x.1 9))
  pure ((wVal >>> (idx &&& x.1 10)) &&& 1)

private theorem realizes_readRunStart :
    Realizes .exact readRunStartProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1) (fun _ _ => 0) := by
  realize
  · exact masked_addr_lt h.run_lt
  · exact h.one_lt_two_pow

/-- Write `isFull` at slot index `slot &&& d 4` with bit `bit`. -/
@[expose] def writeFullProg (x : ClusterInput × (ℕ × ℕ)) : Memory.Prog Unit :=
  let (d, slot, bit) := x
  do
    let idx := slot &&& d 4
    let addr := d 5 + (idx >>> d 9)
    let sh := idx &&& d 10
    let oldWord ← Memory.read addr
    let oldBit := (oldWord >>> sh) &&& 1
    let newWord := oldWord ^^^ ((oldBit ^^^ bit) <<< sh)
    Memory.write addr newWord

private theorem realizes_writeFull :
    Realizes .exact writeFullProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1 ∧ x.2.2 < 2) (fun _ _ => 0) := by
  realize; exacts [masked_addr_lt h.1.full_lt,
    fits_writeBit_newWord (hmem.2 _) (Nat.and_le_right.trans_lt h.1.pBitMask_lt) h.2,
    fits_writeBit_diff_sh (Nat.and_le_right.trans_lt h.1.pBitMask_lt) h.2, h.1.one_lt_two_pow]

/-- Write `isOcc` at slot index `slot &&& d 4` with bit `bit`. -/
@[expose] def writeOccProg (x : ClusterInput × (ℕ × ℕ)) : Memory.Prog Unit :=
  let (d, slot, bit) := x
  do
    let idx := slot &&& d 4
    let addr := d 6 + (idx >>> d 9)
    let sh := idx &&& d 10
    let oldWord ← Memory.read addr
    let oldBit := (oldWord >>> sh) &&& 1
    let newWord := oldWord ^^^ ((oldBit ^^^ bit) <<< sh)
    Memory.write addr newWord

private theorem realizes_writeOcc :
    Realizes .exact writeOccProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1 ∧ x.2.2 < 2) (fun _ _ => 0) := by
  realize; exacts [masked_addr_lt h.1.occ_lt,
    fits_writeBit_newWord (hmem.2 _) (Nat.and_le_right.trans_lt h.1.pBitMask_lt) h.2,
    fits_writeBit_diff_sh (Nat.and_le_right.trans_lt h.1.pBitMask_lt) h.2, h.1.one_lt_two_pow]

/-- Write `isRunStart` at slot index `slot &&& d 4` with bit `bit`. -/
@[expose] def writeRunStartProg (x : ClusterInput × (ℕ × ℕ)) : Memory.Prog Unit :=
  let (d, slot, bit) := x
  do
    let idx := slot &&& d 4
    let addr := d 7 + (idx >>> d 9)
    let sh := idx &&& d 10
    let oldWord ← Memory.read addr
    let oldBit := (oldWord >>> sh) &&& 1
    let newWord := oldWord ^^^ ((oldBit ^^^ bit) <<< sh)
    Memory.write addr newWord

private theorem realizes_writeRunStart :
    Realizes .exact writeRunStartProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1 ∧ x.2.2 < 2) (fun _ _ => 0) := by
  realize; exacts [masked_addr_lt h.1.run_lt,
    fits_writeBit_newWord (hmem.2 _) (Nat.and_le_right.trans_lt h.1.pBitMask_lt) h.2,
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

/-- Read an `f`-bit remainder entry from `remBase` (`d 8`) at slot index `x.2 &&& d 4`. -/
@[expose] def readRemProg (x : ClusterInput × ℕ) : Memory.Prog ℕ := do
  let idx := x.2 &&& x.1 4
  let wVal ← Memory.read (x.1 8 + (idx >>> x.1 11))
  pure ((wVal >>> ((idx &&& x.1 12) * x.1 13)) &&& x.1 14)

private theorem realizes_readRem :
    Realizes .exact readRemProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1) (fun _ _ => 0) := by
  realize
  · exact masked_addr_lt h.rem_lt
  · exact (fits_rem_sh h.f_lt h.remPack_le).trans Nat.lt_two_pow_self

/-- Write an `f`-bit remainder entry `val ≤ d 14` into `remBase` (`d 8`) at `slot &&& d 4`. -/
@[expose] def writeRemProg (x : ClusterInput × (ℕ × ℕ)) : Memory.Prog Unit :=
  let (d, slot, val) := x
  do
    let idx := slot &&& d 4
    let addr := d 8 + (idx >>> d 11)
    let sh := (idx &&& d 12) * d 13
    let oldWord ← Memory.read addr
    let oldLimb := (oldWord >>> sh) &&& d 14
    let newWord := oldWord ^^^ ((oldLimb ^^^ val) <<< sh)
    Memory.write addr newWord

private theorem realizes_writeRem :
    Realizes .exact writeRemProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1 ∧ x.2.2 ≤ x.1 14) (fun _ _ => 0) := by
  realize
  · exact masked_addr_lt h.1.rem_lt
  · exact Nat.xor_lt_two_pow (hmem.2 _)
      (fits_writeRem_diff_sh h.1.remPack_le h.1.fMask_lt_f h.2)
  · exact fits_writeRem_diff_sh h.1.remPack_le h.1.fMask_lt_f h.2
  · exact (fits_rem_sh h.1.f_lt h.1.remPack_le).trans Nat.lt_two_pow_self

theorem clientResult_readFull_le (s : Memory.State) (x : ClusterInput × ℕ) :
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
    (Memory.spec 0).clientResult s (readRemProg x) ≤ x.1 14 :=
  Nat.and_le_right

private theorem clientState_readRem (s : Memory.State) (x : ClusterInput × ℕ) :
    (Memory.spec 0).clientState s (readRemProg x) = s := rfl

/-! ## Section 3: Backward and forward cluster-extent discovery (`findClusterProg`) -/

theorem boundedWhile_invariant {δ σ : Type}
    (guard : δ → σ → Prop) [∀ d a, Decidable (guard d a)]
    (body : δ × σ → Memory.Prog σ) (d : δ)
    (I : σ → Memory.State → Prop)
    (hstep : ∀ a s, I a s → guard d a →
      I ((Memory.spec 0).clientResult s (body (d, a)))
        ((Memory.spec 0).clientState s (body (d, a))))
    (n : ℕ) (a : σ) (s : Memory.State) (hi : I a s) :
    I ((Memory.spec 0).clientResult s (boundedWhile guard body d n a))
      ((Memory.spec 0).clientState s (boundedWhile guard body d n a)) := by
  induction n generalizing a s with
  | zero => exact hi
  | succ n ih =>
    by_cases hg : guard d a
    · simp only [boundedWhile, hg, ↓reduceIte, StateTransitionSpec.clientResult,
        StateTransitionSpec.clientState, ← PFunctor.FreeM.bind_eq_bind,
        StateTransitionSpec.runClient_bind]
      exact ih _ _ (hstep a s hi hg)
    · simp only [boundedWhile, hg, ↓reduceIte, StateTransitionSpec.clientResult,
        StateTransitionSpec.clientState, StateTransitionSpec.runClient_pure']
      exact hi

theorem iterationSafe_of_invariant {δ σ : Type}
    (body : δ × σ → Memory.Prog σ)
    (safe : ℕ → (δ × σ) → Memory.State → Prop) (w : ℕ) (d : δ)
    (I : ℕ → σ → Memory.State → Prop)
    (hstep : ∀ j a s, I (j + 1) a s →
      safe w (d, a) s ∧
        I j ((Memory.spec 0).clientResult s (body (d, a)))
          ((Memory.spec 0).clientState s (body (d, a))))
    {n : ℕ} {a : σ} {s : Memory.State} (hi : I n a s) :
    iterationSafe body safe w d n a s := by
  induction n generalizing a s with
  | zero => trivial
  | succ n ih =>
    obtain ⟨hs, hi'⟩ := hstep n a s hi
    exact ⟨hs, ih hi'⟩

theorem iterate_invariant {δ σ : Type}
    (body : δ × σ → Memory.Prog σ) (d : δ)
    (I : ℕ → σ → Memory.State → Prop)
    (hstep : ∀ j a s, I (j + 1) a s →
      I j ((Memory.spec 0).clientResult s (body (d, a)))
        ((Memory.spec 0).clientState s (body (d, a))))
    {n : ℕ} {a : σ} {s : Memory.State} (hi : I n a s) :
    I 0 ((Memory.spec 0).clientResult s (iterate body d n a))
      ((Memory.spec 0).clientState s (iterate body d n a)) := by
  induction n generalizing a s with
  | zero => exact hi
  | succ n ih =>
    rw [show iterate body d (n + 1) a = (body (d, a) >>= iterate body d n) from rfl,
      StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind]
    exact ih (hstep n a s hi)

/-- One step of backward cluster scan: reads `isFull` at `(q + 2^b - (cnt + 1)) &&& (2^b - 1)`
and updates `(cnt, rem)` to `(cnt, 0)` if empty or `(cnt + 1, rem - 1)` if full. -/
@[expose] def backLenStep (x : ClusterInput × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) :=
  let (d, cnt, rem) := x
  do
    let rawIdx ← pure (d 0 + d 3 - (cnt + 1))
    let f' ← readFullProg (d, rawIdx)
    if f' = 0 then pure (cnt, 0) else pure (cnt + 1, rem - 1)

private theorem clientResult_backLenStep (t : Memory.State) (x : ClusterInput × (ℕ × ℕ)) :
    (Memory.spec 0).clientResult t (backLenStep x) =
      if (Memory.spec 0).clientResult t (readFullProg (x.1, x.1 0 + x.1 3 - (x.2.1 + 1))) = 0
      then (x.2.1, 0) else (x.2.1 + 1, x.2.2 - 1) := by
  change (Memory.spec 0).clientResult t (readFullProg (x.1, x.1 0 + x.1 3 - (x.2.1 + 1)) >>=
    (fun f' => if f' = 0 then pure (x.2.1, 0) else pure (x.2.1 + 1, x.2.2 - 1))) = _
  rw [StateTransitionSpec.clientResult_bind, clientState_readFull]
  split_ifs <;> rfl

private theorem clientState_backLenStep (t : Memory.State) (x : ClusterInput × (ℕ × ℕ)) :
    (Memory.spec 0).clientState t (backLenStep x) = t := by
  change (Memory.spec 0).clientState t (readFullProg (x.1, x.1 0 + x.1 3 - (x.2.1 + 1)) >>=
    (fun f' => if f' = 0 then pure (x.2.1, 0) else pure (x.2.1 + 1, x.2.2 - 1))) = _
  rw [StateTransitionSpec.clientState_bind, clientState_readFull]
  split_ifs <;> rfl

/-- Backward cluster scan from `d 0` (`q.val`). -/
@[expose] def backLenProg (d : ClusterInput) : Memory.Prog (ℕ × ℕ) :=
  boundedWhile (fun _ (st : ℕ × ℕ) => 0 < st.2) backLenStep d (d 3) (0, d 3)

private theorem realizes_backLen :
    Realizes .exact backLenProg WordEncoding.encode WordEncoding.encode
      (fun w d _ => ClusterSafe w d) (fun _ _ => 0) := by
  have hReadFull := realizes_readFull
  realize
  intro hv
  refine whileSafe_of_measure _ _ _ w d
    (fun m _ => m.1 + m.2 ≤ d 3)
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
    ((Memory.spec 0).clientResult s (backLenProg d)).1 ≤ d 3 := by
  dsimp only [backLenProg]
  have h := boundedWhile_invariant (fun _ (st : ℕ × ℕ) => 0 < st.2) backLenStep d
    (fun m _ => m.1 + m.2 ≤ d 3)
    (fun ⟨cnt, rem⟩ t hinv hg => by
      rw [clientResult_backLenStep]
      dsimp only at *
      split_ifs <;> omega)
    (d 3) (0, d 3) s (by omega)
  omega

private theorem clientState_backLen (s : Memory.State) (d : ClusterInput) :
    (Memory.spec 0).clientState s (backLenProg d) = s :=
  boundedWhile_invariant (fun _ (st : ℕ × ℕ) => 0 < st.2) backLenStep d
    (fun _ t => t = s)
    (fun _ t ht _ => by rw [clientState_backLenStep, ht])
    (d 3) (0, d 3) s rfl

/-- One step of forward cluster scan: reads `isFull` at `(q + cnt) &&& (2^b - 1)`
and updates `(cnt, rem)` to `(cnt, 0)` if empty or `(cnt + 1, rem - 1)` if full. -/
@[expose] def fwdLenStep (x : ClusterInput × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) :=
  let (d, cnt, rem) := x
  do
    let rawIdx ← pure (d 0 + cnt)
    let f' ← readFullProg (d, rawIdx)
    if f' = 0 then pure (cnt, 0) else pure (cnt + 1, rem - 1)

private theorem clientResult_fwdLenStep (t : Memory.State) (x : ClusterInput × (ℕ × ℕ)) :
    (Memory.spec 0).clientResult t (fwdLenStep x) =
      if (Memory.spec 0).clientResult t (readFullProg (x.1, x.1 0 + x.2.1)) = 0
      then (x.2.1, 0) else (x.2.1 + 1, x.2.2 - 1) := by
  change (Memory.spec 0).clientResult t (readFullProg (x.1, x.1 0 + x.2.1) >>=
    (fun f' => if f' = 0 then pure (x.2.1, 0) else pure (x.2.1 + 1, x.2.2 - 1))) = _
  rw [StateTransitionSpec.clientResult_bind, clientState_readFull]
  split_ifs <;> rfl

private theorem clientState_fwdLenStep (t : Memory.State) (x : ClusterInput × (ℕ × ℕ)) :
    (Memory.spec 0).clientState t (fwdLenStep x) = t := by
  change (Memory.spec 0).clientState t (readFullProg (x.1, x.1 0 + x.2.1) >>=
    (fun f' => if f' = 0 then pure (x.2.1, 0) else pure (x.2.1 + 1, x.2.2 - 1))) = _
  rw [StateTransitionSpec.clientState_bind, clientState_readFull]
  split_ifs <;> rfl

/-- Forward cluster scan from `d 0` (`q.val`) with remaining budget `d 3 - a`. -/
@[expose] def fwdLenProg (x : ClusterInput × ℕ) : Memory.Prog (ℕ × ℕ) :=
  boundedWhile (fun _ (st : ℕ × ℕ) => 0 < st.2) fwdLenStep x.1 (x.1 3) (0, x.1 3 - x.2)

private theorem realizes_fwdLen :
    Realizes .exact fwdLenProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1 ∧ x.2 ≤ x.1 3) (fun _ _ => 0) := by
  have hReadFull := realizes_readFull
  realize
  · exact h.2
  · intro hv
    refine whileSafe_of_measure _ _ _ w d.1
      (fun m _ => m.1 + m.2 ≤ d.1 3 - d.2)
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
    ((Memory.spec 0).clientResult s (fwdLenProg x)).1 ≤ x.1 3 - x.2 := by
  dsimp only [fwdLenProg]
  have h := boundedWhile_invariant (fun _ (st : ℕ × ℕ) => 0 < st.2) fwdLenStep x.1
    (fun m _ => m.1 + m.2 ≤ x.1 3 - x.2)
    (fun ⟨cnt, rem⟩ t hinv hg => by
      rw [clientResult_fwdLenStep]
      dsimp only at *
      split_ifs <;> omega)
    (x.1 3) (0, x.1 3 - x.2) s (by omega)
  omega

private theorem clientState_fwdLen (s : Memory.State) (x : ClusterInput × ℕ) :
    (Memory.spec 0).clientState s (fwdLenProg x) = s :=
  boundedWhile_invariant (fun _ (st : ℕ × ℕ) => 0 < st.2) fwdLenStep x.1
    (fun _ t => t = s)
    (fun _ t ht _ => by rw [clientState_fwdLenStep, ht])
    (x.1 3) (0, x.1 3 - x.2) s rfl

/-- Find the cluster extent `(o, (a, ℓ))` around `d 0` (`q.val`). -/
@[expose] def findClusterProg (d : ClusterInput) : Memory.Prog (ℕ × (ℕ × ℕ)) := do
  let backRes ← backLenProg d
  let fwdRes ← fwdLenProg (d, backRes.1)
  pure ((d 0 + d 3 - backRes.1) &&& d 4, (backRes.1, backRes.1 + fwdRes.1))

private theorem backLen_add_fwdLen_le (s : Memory.State) (d : ClusterInput) :
    ((Memory.spec 0).clientResult s (backLenProg d)).1 +
      ((Memory.spec 0).clientResult ((Memory.spec 0).clientState s (backLenProg d))
        (fwdLenProg (d, ((Memory.spec 0).clientResult s (backLenProg d)).1))).1 ≤ d 3 := by
  have ha := clientResult_backLen_fst_le s d
  have ht := clientResult_fwdLen_fst_le ((Memory.spec 0).clientState s (backLenProg d))
    (d, ((Memory.spec 0).clientResult s (backLenProg d)).1)
  dsimp only at ht
  omega

private theorem realizes_findCluster :
    Realizes .exact findClusterProg WordEncoding.encode WordEncoding.encode
      (fun w d _ => ClusterSafe w d) (fun _ _ => 0) := by
  have hBack := realizes_backLen
  have hFwd := realizes_fwdLen
  realize
  · exact h
  · exact clientResult_backLen_fst_le s d
  · have := clientResult_backLen_fst_le s d
    have := h.q_lt; have := h.two_cap_lt; omega
  · fits [h.q_lt, h.two_cap_le]
  · fits [backLen_add_fwdLen_le s d, h.two_cap_le]

private theorem clientResult_findCluster_bounds {w : ℕ} (s : Memory.State) (d : ClusterInput)
    (h : ClusterSafe w d) :
    let res := (Memory.spec 0).clientResult s (findClusterProg d)
    res.1 < d 3 ∧ res.2.1 ≤ res.2.2 ∧ res.2.2 ≤ d 3 := by
  dsimp only
  unfold findClusterProg
  rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
    clientResult_pure]
  dsimp only
  exact ⟨Nat.and_le_right.trans_lt h.mask_lt, Nat.le_add_right _ _, backLen_add_fwdLen_le s d⟩

private theorem clientState_findCluster (s : Memory.State) (d : ClusterInput) :
    (Memory.spec 0).clientState s (findClusterProg d) = s := by
  unfold findClusterProg
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
    clientState_pure, clientState_fwdLen, clientState_backLen]

/-! ## Section 4: Prefix `occBefore` and full cluster scan (`scanClusterProg`) -/

/-- One step of `occBefore` prefix scan: reads `isOcc` at `o + m` and increments `(m, occ)`. -/
@[expose] def occBeforeStep (x : (ClusterInput × ℕ) × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) :=
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
  rw [StateTransitionSpec.clientResult_bind, clientResult_pure]

private theorem clientState_occBeforeStep (t : Memory.State) (x : (ClusterInput × ℕ) × (ℕ × ℕ)) :
    (Memory.spec 0).clientState t (occBeforeStep x) = t := by
  change (Memory.spec 0).clientState t (readOccProg (x.1.1, x.1.2 + x.2.1) >>=
    (fun occBit => pure (x.2.1 + 1, x.2.2 + occBit))) = _
  rw [StateTransitionSpec.clientState_bind, clientState_pure, clientState_readOcc]

/-- Compute `(a, occBefore st o a)` by iterating `occBeforeStep` `a` times from `(0, 0)`. -/
@[expose] def occBeforeProg (x : ClusterInput × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) :=
  let (d, o, a) := x
  iterate occBeforeStep (d, o) a (0, 0)

private theorem realizes_occBefore :
    Realizes .exact occBeforeProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1 ∧ x.2.1 < x.1 3 ∧ x.2.2 ≤ x.1 3) (fun _ _ => 0) := by
  have hReadOcc := realizes_readOcc
  realize
  rcases d with ⟨d0, o, a⟩
  obtain ⟨hcs, ho, ha⟩ := h
  have h2w := hcs.two_cap_lt
  dsimp only at h2w ho ha
  refine iterationSafe_of_invariant _ _ w (d0, o, a)
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
  have h := iterate_invariant occBeforeStep (d, o)
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
  iterate_invariant occBeforeStep (x.1, x.2.1)
    (fun _ _ t => t = s)
    (fun _ _ t ht => by rw [clientState_occBeforeStep, ht])
    (n := x.2.2) (a := (0, 0)) (s := s) rfl

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
  ClusterSafe w env.d ∧ env.o < env.d 3 ∧ env.a ≤ env.ℓ ∧ env.ℓ ≤ env.d 3 ∧
    env.occA ≤ env.d 3 ∧ env.occA1 ≤ env.d 3 + 1

/-- Bounds kept by the scan state: the counters and targets are at most the slots scanned, the
delete stop is at most the cluster length, and `qFound` is a bit. -/
private def ScanState.Bounds (env : ScanEnv) (m : ScanState) : Prop :=
  m.runs ≤ m.i ∧ m.occI ≤ m.i ∧ m.s₀ ≤ m.i ∧ m.s ≤ m.i ∧ m.e ≤ env.ℓ ∧ m.qFound ≤ 1

/-- Safety predicate for one step of `scanLoopProg`. -/
private def ScanStepSafe (w : ℕ) (x : ScanEnv × ScanState) : Prop :=
  x.1.Safe w ∧ x.2.i < x.1.ℓ ∧ x.2.Bounds x.1

/-- The three bits and fields read at one slot of the scan. The words are listed in the order
`(occ, (run, rem))`. -/
@[ext] structure ScanReads where
  /-- Occupied bit. -/
  occ : ℕ
  /-- Run-start bit. -/
  run : ℕ
  /-- Stored remainder. -/
  rem : ℕ

/-- The word layout of a `ScanReads`. -/
@[expose] def ScanReads.equiv : ScanReads ≃ ℕ × (ℕ × ℕ) where
  toFun r := (r.occ, (r.run, r.rem))
  invFun := fun (occ, (run, rem)) => ⟨occ, run, rem⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding ScanReads := .ofEquiv ScanReads.equiv

/-- Read the occupied bit, run-start bit and remainder at slot offset `o + i`. -/
@[expose] def scanStepReadsProg (x : ScanEnv × ScanState) : Memory.Prog ScanReads := do
  let rawIdx ← pure (x.1.o + x.2.i)
  let occBit ← readOccProg (x.1.d, rawIdx)
  let runBit ← readRunStartProg (x.1.d, rawIdx)
  let remVal ← readRemProg (x.1.d, rawIdx)
  pure ⟨occBit, runBit, remVal⟩

private theorem realizes_scanStepReads :
    Realizes .exact scanStepReadsProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1.d ∧ x.1.o + x.2.i < 2 ^ w) (fun _ _ => 0) := by
  have hReadOcc := realizes_readOcc
  have hReadRun := realizes_readRunStart
  have hReadRem := realizes_readRem
  realize
  · exact h.2
  · exact h.1

private theorem clientResult_scanStepReads (t : Memory.State) (x : ScanEnv × ScanState) :
    (Memory.spec 0).clientResult t (scanStepReadsProg x) =
      ⟨(Memory.spec 0).clientResult t (readOccProg (x.1.d, x.1.o + x.2.i)),
        (Memory.spec 0).clientResult t (readRunStartProg (x.1.d, x.1.o + x.2.i)),
        (Memory.spec 0).clientResult t (readRemProg (x.1.d, x.1.o + x.2.i))⟩ := by
  unfold scanStepReadsProg
  rw [StateTransitionSpec.clientResult_bind, clientResult_pure, clientState_pure,
    StateTransitionSpec.clientResult_bind, clientState_readOcc,
    StateTransitionSpec.clientResult_bind, clientState_readRunStart,
    StateTransitionSpec.clientResult_bind, clientState_readRem, clientResult_pure]

private theorem clientState_scanStepReads (t : Memory.State) (x : ScanEnv × ScanState) :
    (Memory.spec 0).clientState t (scanStepReadsProg x) = t := by
  unfold scanStepReadsProg
  rw [StateTransitionSpec.clientState_bind, clientResult_pure, clientState_pure,
    StateTransitionSpec.clientState_bind, clientState_readOcc,
    StateTransitionSpec.clientState_bind, clientState_readRunStart,
    StateTransitionSpec.clientState_bind, clientState_readRem, clientState_pure]

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
    if c.rem < c.env.d 1 then pure (c.st.s₀, c.st.s + 1) else pure (c.st.s₀, c.st.s)
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
        if c.runs ≤ c.env.occA ∨ (c.runs ≤ c.env.occA1 ∧ c.rem < c.env.d 1)
        then c.st.s + 1 else c.st.s) := by
  unfold scanStepTargetProg
  split_ifs <;> simp only [clientResult_pure, Prod.mk.injEq] <;> omega

private theorem clientState_scanStepTarget (t : Memory.State) (c : ScanStepCtx) :
    (Memory.spec 0).clientState t (scanStepTargetProg c) = t := by
  unfold scanStepTargetProg
  split_ifs <;> rfl

/-- Update `e` (`calcDeleteStop`) during one step of `scanLoopProg`. -/
@[expose] def scanStepStopProg (c : ScanStepCtx) : Memory.Prog ℕ :=
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
      if c.rem = c.env.d 1 then pure 1 else pure c.st.qFound
    else pure c.st.qFound
  else pure c.st.qFound

theorem realizes_scanStepQuery :
    Realizes .exact scanStepQueryProg WordEncoding.encode WordEncoding.encode
      (fun w _ _ => 1 < 2 ^ w) (fun _ _ => 0) := by
  realize
  exact h

private theorem clientResult_scanStepQuery (t : Memory.State) (c : ScanStepCtx) :
    (Memory.spec 0).clientResult t (scanStepQueryProg c) =
      if (c.env.occA < c.runs ∧ c.runs ≤ c.env.occA1) ∧ c.rem = c.env.d 1
      then 1 else c.st.qFound := by
  unfold scanStepQueryProg
  split_ifs <;> simp only [clientResult_pure] <;> omega

private theorem clientState_scanStepQuery (t : Memory.State) (c : ScanStepCtx) :
    (Memory.spec 0).clientState t (scanStepQueryProg c) = t := by
  unfold scanStepQueryProg
  split_ifs <;> rfl

/-- One step of the cluster scan over `i ∈ [0, ℓ)`. -/
@[expose] def scanLoopStep (x : ScanEnv × ScanState) : Memory.Prog ScanState := do
  let reads ← scanStepReadsProg x
  let runs ← pure (x.2.runs + reads.run)
  let tgt ← scanStepTargetProg ⟨x.1, x.2, runs, reads.rem⟩
  let e ← scanStepStopProg ⟨x.1, x.2, runs, reads.rem⟩
  let qFound ← scanStepQueryProg ⟨x.1, x.2, runs, reads.rem⟩
  pure ⟨x.2.i + 1, runs, x.2.occI + reads.occ, tgt.1, tgt.2, e, qFound⟩

private theorem realizes_scanLoopStep :
    Realizes .exact scanLoopStep WordEncoding.encode WordEncoding.encode
      (fun w x _ => ScanStepSafe w x) (fun _ _ => 0) := by
  have hReads := realizes_scanStepReads
  have hTgt := realizes_scanStepTarget
  have hStop := realizes_scanStepStop
  have hQuery := realizes_scanStepQuery
  realize <;> {
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
  rw [StateTransitionSpec.clientState_bind, clientState_scanStepReads,
    StateTransitionSpec.clientState_bind, clientResult_pure, clientState_pure,
    StateTransitionSpec.clientState_bind, clientState_scanStepTarget,
    StateTransitionSpec.clientState_bind, clientState_scanStepStop,
    StateTransitionSpec.clientState_bind, clientState_scanStepQuery, clientState_pure]

/-- One scan step advances `i` and keeps `ScanState.Bounds`. -/
private theorem clientResult_scanLoopStep_bounds (t : Memory.State) (x : ScanEnv × ScanState)
    (hi : x.2.i < x.1.ℓ) (hb : x.2.Bounds x.1) :
    let res := (Memory.spec 0).clientResult t (scanLoopStep x)
    res.i = x.2.i + 1 ∧ res.Bounds x.1 := by
  rcases hb with ⟨hruns, hoccI, hs₀, hs, he, hq⟩
  dsimp only
  unfold scanLoopStep
  rw [StateTransitionSpec.clientResult_bind, clientState_scanStepReads,
    StateTransitionSpec.clientResult_bind, clientResult_pure, clientState_pure,
    StateTransitionSpec.clientResult_bind, clientState_scanStepTarget,
    StateTransitionSpec.clientResult_bind, clientState_scanStepStop,
    StateTransitionSpec.clientResult_bind, clientState_scanStepQuery, clientResult_pure,
    clientResult_scanStepTarget, clientResult_scanStepStop, clientResult_scanStepQuery,
    clientResult_scanStepReads]
  dsimp only [ScanState.Bounds]
  have hb_occ := clientResult_readOcc_le t (x.1.d, x.1.o + x.2.i)
  have hb_run := clientResult_readRunStart_le t (x.1.d, x.1.o + x.2.i)
  split_ifs <;> refine ⟨rfl, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- Iterate `scanLoopStep` `ℓ` times from `⟨0, 0, 0, 0, 0, ℓ, 0⟩`. -/
@[expose] def scanLoopProg (env : ScanEnv) : Memory.Prog ScanState :=
  iterate scanLoopStep env env.ℓ ⟨0, 0, 0, 0, 0, env.ℓ, 0⟩

private theorem realizes_scanLoop :
    Realizes .exact scanLoopProg WordEncoding.encode WordEncoding.encode
      (fun w env _ => env.Safe w) (fun _ _ => 0) := by
  have hStep := realizes_scanLoopStep
  realize
  refine iterationSafe_of_invariant _ _ w d
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
  have h := iterate_invariant scanLoopStep env
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
  iterate_invariant scanLoopStep env
    (fun _ _ t => t = s)
    (fun _ _ t ht => by rw [clientState_scanLoopStep, ht])
    (n := env.ℓ) (a := ⟨0, 0, 0, 0, 0, env.ℓ, 0⟩) (s := s) rfl

/-- Result of the full cluster scan `scanClusterProg`. The words are listed in the order
`(occQ, ((s₀, s), (e, qFound)))`. -/
@[ext] structure ScanResult where
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
@[expose] def ScanResult.equiv : ScanResult ≃ ℕ × ((ℕ × ℕ) × (ℕ × ℕ)) where
  toFun r := (r.occQ, ((r.s₀, r.s), (r.e, r.qFound)))
  invFun := fun (occQ, ((s₀, s), (e, qFound))) => ⟨occQ, s₀, s, e, qFound⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding ScanResult := .ofEquiv ScanResult.equiv

/-- Bounds on a scan of a cluster of length `ℓ`: the two flags are bits and the run start,
target slot and delete stop are at most `ℓ`. -/
private def ScanResult.Bounds (ℓ : ℕ) (r : ScanResult) : Prop :=
  r.occQ ≤ 1 ∧ r.s₀ ≤ ℓ ∧ r.s ≤ ℓ ∧ r.e ≤ ℓ ∧ r.qFound ≤ 1

/-- Full cluster scan of the cluster at `x = (d, (o, (a, ℓ)))`. -/
@[expose] def scanClusterProg (x : ClusterInput × (ℕ × (ℕ × ℕ))) : Memory.Prog ScanResult :=
  let (d, o, a, ℓ) := x
  do
    let occRes ← occBeforeProg (d, (o, a))
    let occQ ← readOccProg (d, d 0)
    let occA1 ← pure (occRes.2 + occQ)
    let m ← scanLoopProg ⟨d, o, a, ℓ, occRes.2, occA1⟩
    pure ⟨occQ, m.s₀, m.s, m.e, m.qFound⟩

private theorem realizes_scanCluster :
    Realizes .exact scanClusterProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1 ∧ x.2.1 < x.1 3 ∧
        x.2.2.1 ≤ x.2.2.2 ∧ x.2.2.2 ≤ x.1 3) (fun _ _ => 0) := by
  have hOcc := realizes_occBefore
  have hReadOcc := realizes_readOcc
  have hLoop := realizes_scanLoop
  realize <;> {
    first
    | exact h.1
    | exact h.2.1
    | exact h.2.2.1.trans h.2.2.2
    | {
        have h_occ := (clientResult_occBefore_bounds s (d.1, d.2.1, d.2.2.1)).2
        have h_occQ := clientResult_readOcc_le s (d.1, d.1 0)
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
  rw [StateTransitionSpec.clientResult_bind, clientState_occBefore,
    StateTransitionSpec.clientResult_bind, clientState_readOcc,
    StateTransitionSpec.clientResult_bind, clientResult_pure, clientState_pure,
    StateTransitionSpec.clientResult_bind, clientState_scanLoop, clientResult_pure]
  have h_occQ := clientResult_readOcc_le s (d, d 0)
  obtain ⟨hi, _, _, hs₀, hs, he, hq⟩ := clientResult_scanLoop_bounds s
    ⟨d, o, a, ℓ,
      ((Memory.spec 0).clientResult s (occBeforeProg (d, o, a))).2,
      ((Memory.spec 0).clientResult s (occBeforeProg (d, o, a))).2 +
        (Memory.spec 0).clientResult s (readOccProg (d, d 0))⟩
  exact ⟨h_occQ, by dsimp only at hi ⊢; omega, by dsimp only at hi ⊢; omega, he, hq⟩

private theorem clientState_scanCluster (s : Memory.State) (x : ClusterInput × (ℕ × (ℕ × ℕ))) :
    (Memory.spec 0).clientState s (scanClusterProg x) = s := by
  unfold scanClusterProg
  rw [StateTransitionSpec.clientState_bind, clientState_occBefore,
    StateTransitionSpec.clientState_bind, clientState_readOcc,
    StateTransitionSpec.clientState_bind, clientResult_pure, clientState_pure,
    StateTransitionSpec.clientState_bind, clientState_scanLoop, clientState_pure]

/-! ## Section 5: Right-Shift Loop and `insertAfterScanProg` -/

/-- One step of the right-shift loop: copies `(isRunStart, remAt)` from `o + (pos - 1)` to
`o + pos` and decrements `pos`. -/
@[expose] def shiftRightStep (x : (ClusterInput × ℕ) × ℕ) : Memory.Prog ℕ :=
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
      (fun w x _ => ClusterSafe w x.1.1 ∧ x.1.2 < x.1.1 3 ∧ 1 ≤ x.2 ∧ x.2 ≤ x.1.1 3)
      (fun _ _ => 0) := by
  have hReadRun := realizes_readRunStart
  have hReadRem := realizes_readRem
  have hWriteRun := realizes_writeRunStart
  have hWriteRem := realizes_writeRem
  realize <;> {
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
  rw [StateTransitionSpec.clientResult_bind, clientResult_pure, clientState_pure,
    StateTransitionSpec.clientResult_bind, clientResult_pure, clientState_pure,
    StateTransitionSpec.clientResult_bind, clientState_readRunStart,
    StateTransitionSpec.clientResult_bind, clientState_readRem,
    StateTransitionSpec.clientResult_bind,
    StateTransitionSpec.clientResult_bind, clientResult_pure]

/-- Iterate `shiftRightStep` `count` times starting at `pos`. -/
@[expose] def shiftRightProg (x : (ClusterInput × ℕ) × (ℕ × ℕ)) : Memory.Prog ℕ :=
  let (env, pos, count) := x
  iterate shiftRightStep env count pos

private theorem realizes_shiftRight :
    Realizes .exact shiftRightProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1.1 ∧ x.1.2 < x.1.1 3 ∧ x.2.2 ≤ x.2.1 ∧ x.2.1 ≤ x.1.1 3)
      (fun _ _ => 0) := by
  have hStep := realizes_shiftRightStep
  realize
  refine iterationSafe_of_invariant _ _ w d
    (fun j (pos : ℕ) _ => j ≤ pos ∧ pos ≤ d.2.1)
    ?_ ⟨h.2.2.1, le_rfl⟩
  rintro j pos t ⟨hj, hpos⟩
  rcases h with ⟨hcs, ho, hle, hmax⟩
  refine ⟨⟨hcs, ho, by change 1 ≤ pos; omega, by change pos ≤ d.1.1 3; omega⟩, ?_⟩
  rw [clientResult_shiftRightStep]
  exact ⟨by dsimp only; omega, by dsimp only; omega⟩

/-- Clear old `isRunStart` at `o + s₀` when `occQ = 1` and `s = s₀`. -/
@[expose] def insertClearOldProg (x : (ClusterInput × ℕ) × (ℕ × (ℕ × ℕ))) : Memory.Prog Unit :=
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
  have hWriteRun := realizes_writeRunStart
  realize <;> {
    rcases h with ⟨hcs, hlt⟩
    have h1w := hcs.one_lt_two_pow
    first
    | exact hcs
    | exact hlt
    | exact h1w
    | { dsimp only [ClusterInput] at *; omega }
  }

/-- Write the newly inserted slot at `o + s`, set `isOcc` at `q`, and set `isFull` at `o + ℓ`. -/
@[expose] def insertWriteNewProg (x : (ClusterInput × ℕ) × ((ℕ × ℕ) × ℕ)) : Memory.Prog ℕ :=
  let ((d, o), (s₀, s), ℓ) := x
  do
    let isStart ← cmpEqProg (s, s₀)
    let dstS ← pure (o + s)
    let dstL ← pure (o + ℓ)
    let one ← pure 1
    let _ ← writeRunStartProg (d, (dstS, isStart))
    let _ ← writeRemProg (d, (dstS, d 1))
    let _ ← writeOccProg (d, (d 0, one))
    let _ ← writeFullProg (d, (dstL, one))
    pure 0

private theorem realizes_insertWriteNew :
    Realizes .exact insertWriteNewProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1.1 ∧ x.1.2 < x.1.1 3 ∧
        x.2.1.2 ≤ x.2.2 ∧ x.2.2 ≤ x.1.1 3) (fun _ _ => 0) := by
  have hCmpEq := realizes_cmpEq
  have hWriteRun := realizes_writeRunStart
  have hWriteRem := realizes_writeRem
  have hWriteOcc := realizes_writeOcc
  have hWriteFull := realizes_writeFull
  realize <;> {
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
        have hb_eq := clientResult_cmpEq_le s (s_idx, s₀)
        dsimp only [ClusterInput] at *
        first | fits [hcs.fMask_lt] | omega
      }
  }

/-- Post-scan phase of `insertCluster`: clear old run-start if superseded, right-shift
`[s .. ℓ)`, and write the new entry and metadata bits. -/
@[expose] def insertAfterScanProg (x : (ClusterInput × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) :
    Memory.Prog ℕ :=
  let (env, (occQ, ℓ), (s₀, s)) := x
  do
    let _ ← insertClearOldProg (env, (occQ, (s₀, s)))
    let count ← pure (ℓ - s)
    let _ ← shiftRightProg (env, (ℓ, count))
    insertWriteNewProg (env, ((s₀, s), ℓ))

private theorem realizes_insertAfterScan :
    Realizes .exact insertAfterScanProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1.1 ∧ x.1.2 < x.1.1 3 ∧
        x.2.2.1 ≤ x.2.1.2 ∧ x.2.2.2 ≤ x.2.1.2 ∧ x.2.1.2 ≤ x.1.1 3) (fun _ _ => 0) := by
  have hClear := realizes_insertClearOld
  have hShift := realizes_shiftRight
  have hWrite := realizes_insertWriteNew
  realize <;> {
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
@[expose] def shiftLeftStep (x : (ClusterInput × ℕ) × ℕ) : Memory.Prog ℕ :=
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
      (fun w x _ => ClusterSafe w x.1.1 ∧ x.1.2 < x.1.1 3 ∧ x.2 + 1 ≤ x.1.1 3)
      (fun _ _ => 0) := by
  have hReadRun := realizes_readRunStart
  have hReadRem := realizes_readRem
  have hWriteRun := realizes_writeRunStart
  have hWriteRem := realizes_writeRem
  realize <;> {
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
  rw [StateTransitionSpec.clientResult_bind, clientResult_pure, clientState_pure,
    StateTransitionSpec.clientResult_bind, clientResult_pure, clientState_pure,
    StateTransitionSpec.clientResult_bind, clientState_readRunStart,
    StateTransitionSpec.clientResult_bind, clientState_readRem,
    StateTransitionSpec.clientResult_bind,
    StateTransitionSpec.clientResult_bind, clientResult_pure]

/-- Iterate `shiftLeftStep` `count` times starting at `pos`. -/
@[expose] def shiftLeftProg (x : (ClusterInput × ℕ) × (ℕ × ℕ)) : Memory.Prog ℕ :=
  let (env, pos, count) := x
  iterate shiftLeftStep env count pos

private theorem realizes_shiftLeft :
    Realizes .exact shiftLeftProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1.1 ∧ x.1.2 < x.1.1 3 ∧ x.2.1 + x.2.2 ≤ x.1.1 3)
      (fun _ _ => 0) := by
  have hStep := realizes_shiftLeftStep
  realize
  refine iterationSafe_of_invariant _ _ w d
    (fun j (pos : ℕ) _ => pos + j ≤ d.1.1 3)
    ?_ h.2.2
  rintro j pos t hpos
  rcases h with ⟨hcs, ho, _⟩
  refine ⟨⟨hcs, ho, by change pos + 1 ≤ d.1.1 3; omega⟩, ?_⟩
  rw [clientResult_shiftLeftStep]
  dsimp only at *
  omega

/-- Compute `hasMore = (decide (s₀ + 1 < e) && !st.isRunStart (probeSlot b o (s₀ + 1))).toNat`. -/
@[expose] def deleteHasMoreProg (x : (ClusterInput × ℕ) × (ℕ × ℕ)) : Memory.Prog ℕ :=
  let ((d, o), s₀, e) := x
  do
    let s₀1 ← pure (s₀ + 1)
    let cLt ← cmpLtProg (s₀1, e)
    let idx ← pure (o + cLt * s₀1)
    let rNext ← readRunStartProg (d, idx)
    let notRun ← cmpZeroProg rNext
    pure (cLt * notRun)

private theorem realizes_deleteHasMore :
    Realizes .exact deleteHasMoreProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1.1 ∧ x.1.2 < x.1.1 3 ∧ x.2.1 ≤ x.1.1 3 ∧ x.2.2 ≤ x.1.1 3)
      (fun _ _ => 0) := by
  have hCmpLt := realizes_cmpLt
  have hReadRun := realizes_readRunStart
  have hCmpZero := realizes_cmpZero
  realize <;> {
    rcases d with ⟨⟨d0, o⟩, s₀, e⟩
    rcases h with ⟨hcs, ho, hs₀, he⟩
    dsimp only at ho hs₀ he
    have h2w := hcs.two_cap_lt
    have h1w := hcs.one_lt_two_pow
    first
    | exact hcs
    | exact h1w
    | {
        let cLt := (Memory.spec 0).clientResult s (cmpLtProg (s₀ + 1, e))
        have hcLt := clientResult_cmpLt_le s (s₀ + 1, e)
        have hmul1 : cLt * (s₀ + 1) ≤ d0 3 := by
          dsimp only [cLt]; rw [clientResult_cmpLt]
          by_cases hlt : s₀ + 1 < e
          · simp only [hlt, decide_true, Bool.toNat_true, one_mul]; omega
          · simp only [hlt, decide_false, Bool.toNat_false, zero_mul, zero_le]
        have hnotRun := clientResult_cmpZero_le
          ((Memory.spec 0).clientState ((Memory.spec 0).clientState s (cmpLtProg (s₀ + 1, e)))
            (readRunStartProg (d0, o + cLt * (s₀ + 1))))
          ((Memory.spec 0).clientResult ((Memory.spec 0).clientState s (cmpLtProg (s₀ + 1, e)))
            (readRunStartProg (d0, o + cLt * (s₀ + 1))))
        have hmul2 := Nat.mul_le_mul hcLt hnotRun
        dsimp only [cLt] at hmul1 hnotRun hmul2
        dsimp only at *
        fits
      }
  }

/-- Update `isOcc` at `q` or `isRunStart` at `o + s₀` after `shiftLeft`. -/
@[expose] def deleteUpdateRunProg (x : (ClusterInput × ℕ) × (ℕ × (ℕ × ℕ))) : Memory.Prog Unit :=
  let ((d, o), hasMore, s₀, s) := x
  do
    let idx ← pure (o + s₀)
    let z ← pure 0
    let one ← pure 1
    if hasMore = 0 then
      writeOccProg (d, (d 0, z))
    else if s = s₀ then
      writeRunStartProg (d, (idx, one))
    else
      pure ()

private theorem realizes_deleteUpdateRun :
    Realizes .exact deleteUpdateRunProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1.1 ∧ x.1.2 + x.2.2.1 < 2 ^ w) (fun _ _ => 0) := by
  have hWriteOcc := realizes_writeOcc
  have hWriteRun := realizes_writeRunStart
  realize <;> {
    rcases h with ⟨hcs, hlt⟩
    have h1w := hcs.one_lt_two_pow
    have hq := hcs.q_lt
    first
    | exact hcs
    | exact hlt
    | exact h1w
    | { dsimp only [ClusterInput] at *; omega }
  }

/-- Clear `(isFull, isRunStart, remAt)` at `o + (e - 1)`. -/
@[expose] def deleteClearEndProg (x : (ClusterInput × ℕ) × ℕ) : Memory.Prog Unit :=
  let ((d, o), e) := x
  do
    let rawEnd ← pure (o + (e - 1))
    let z ← pure 0
    let _ ← writeFullProg (d, (rawEnd, z))
    let _ ← writeRunStartProg (d, (rawEnd, z))
    writeRemProg (d, (rawEnd, z))

private theorem realizes_deleteClearEnd :
    Realizes .exact deleteClearEndProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1.1 ∧ x.1.2 < x.1.1 3 ∧ 1 ≤ x.2 ∧ x.2 ≤ x.1.1 3)
      (fun _ _ => 0) := by
  have hWriteFull := realizes_writeFull
  have hWriteRun := realizes_writeRunStart
  have hWriteRem := realizes_writeRem
  realize <;> {
    rcases d with ⟨⟨d0, o⟩, e⟩
    rcases h with ⟨hcs, ho, h1, he⟩
    have h2w := hcs.two_cap_lt
    dsimp only at *
    first | exact hcs | fits | omega
  }

/-- Post-scan phase of `deleteCluster`: compute `hasMore`, left-shift `[s + 1 .. e)`, update
`isOcc` / `isRunStart`, and clear `o + (e - 1)`. -/
@[expose] def deleteAfterScanProg (x : (ClusterInput × ℕ) × ((ℕ × ℕ) × ℕ)) : Memory.Prog ℕ :=
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
      (fun w x _ => ClusterSafe w x.1.1 ∧ x.1.2 < x.1.1 3 ∧
        x.2.1.1 ≤ x.1.1 3 ∧ x.2.1.2 ≤ x.1.1 3 ∧ x.2.2 ≤ x.1.1 3) (fun _ _ => 0) := by
  have hHasMore := realizes_deleteHasMore
  have hShift := realizes_shiftLeft
  have hUpdate := realizes_deleteUpdateRun
  have hClear := realizes_deleteClearEnd
  realize <;> {
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

/-- Dispatch after `findClusterProg` and `scanClusterProg` based on `d 2`
(`0 = insert`, `1 = delete`, `2 = query`). Every value of `d 2` other than `0` and `1` takes the
query branch. -/
@[expose] def clusterDispatchProg
    (x : (ClusterInput × (ℕ × (ℕ × ℕ))) × ScanResult) : Memory.Prog ℕ :=
  let ((d, o, _, ℓ), scan) := x
  if d 2 = 0 then
    insertAfterScanProg ((d, o), ((scan.occQ, ℓ), (scan.s₀, scan.s)))
  else if d 2 = 1 then
    deleteAfterScanProg ((d, o), ((scan.s₀, scan.s), scan.e))
  else
    pure (scan.occQ * scan.qFound)

private theorem realizes_clusterDispatch :
    Realizes .exact clusterDispatchProg WordEncoding.encode WordEncoding.encode
      (fun w x _ => ClusterSafe w x.1.1 ∧ x.1.2.1 < x.1.1 3 ∧ x.1.2.2.2 ≤ x.1.1 3 ∧
        x.2.Bounds x.1.2.2.2) (fun _ _ => 0) := by
  have hIns := realizes_insertAfterScan
  have hDel := realizes_deleteAfterScan
  realize <;> {
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
@[expose] def clusterOpProg (d : ClusterInput) : Memory.Prog ℕ := do
  let ext ← findClusterProg d
  let scan ← scanClusterProg (d, ext)
  clusterDispatchProg ((d, ext), scan)

theorem realizes_clusterOp :
    Realizes .exact clusterOpProg WordEncoding.encode WordEncoding.encode
      (fun w d _ => ClusterSafe w d) (fun _ _ => 0) := by
  have hFind := realizes_findCluster
  have hScan := realizes_scanCluster
  have hDisp := realizes_clusterDispatch
  realize <;> {
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
  d 5 + (d 4 >>> d 9) < s.frontier ∧
  d 6 + (d 4 >>> d 9) < s.frontier ∧
  d 7 + (d 4 >>> d 9) < s.frontier ∧
  d 8 + (d 4 >>> d 11) < s.frontier

private theorem clusterMemSafe_mkClusterInput {base w w₀ n k : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hfront : base + space w w₀ n k ≤ s.frontier)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ) :
    ClusterMemSafe w (mkClusterInput base w w₀ n k q r opTag) s :=
  ⟨hwf, mkClusterInput_slotAddr_lt hfront q r opTag⟩

@[simp] theorem pure_bind_prog {α β : Type} (a : α) (f : α → Memory.Prog β) :
    (Pure.pure a : Memory.Prog α) >>= f = f a := rfl

theorem frontier_le_clientState {α : Type} (s : Memory.State) (p : Memory.Prog α) :
    s.frontier ≤ ((Memory.spec 0).clientState s p).frontier := by
  have h := Memory.frontier_le_run (w := 0) s ((Memory.spec 0).clientHistory s p)
  rwa [StateTransitionSpec.run_runClient] at h

theorem wellFormed_clientState {α : Type} {w : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    {p : Memory.Prog α} (hv : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p)) :
    Memory.WellFormed w ((Memory.spec 0).clientState s p) := by
  rw [← clientState_width w p s]
  have h := hwf.run hv
  rwa [StateTransitionSpec.run_runClient] at h

private theorem clusterMemSafe_clientState {α : Type} {w : ℕ} {d : ClusterInput} {s : Memory.State}
    (hms : ClusterMemSafe w d s) {p : Memory.Prog α}
    (hv : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p)) :
    ClusterMemSafe w d ((Memory.spec 0).clientState s p) := by
  have hle := frontier_le_clientState s p
  exact ⟨wellFormed_clientState hms.1 hv,
    hms.2.1.trans_le hle, hms.2.2.1.trans_le hle,
    hms.2.2.2.1.trans_le hle, hms.2.2.2.2.trans_le hle⟩

private theorem validHistory_bind_of_memSafe {α β : Type} {w : ℕ} {d : ClusterInput}
    {s : Memory.State} (hms : ClusterMemSafe w d s)
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hq : ∀ t, ClusterMemSafe w d t →
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (q ((Memory.spec 0).clientResult s p)))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) := by
  rw [← PFunctor.FreeM.bind_eq_bind, validHistory_bind]
  rw [clientState_width w p s, clientResult_width w p s]
  exact ⟨hp, hq _ (clusterMemSafe_clientState hms hp)⟩

theorem validHistory_pure {α : Type} (w : ℕ) (s : Memory.State) (a : α) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (pure a)) := trivial

private theorem validHistory_cmpLt (w : ℕ) (s : Memory.State) (x : ℕ × ℕ) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (cmpLtProg x)) := by
  dsimp only [cmpLtProg]; split_ifs <;> trivial

private theorem validHistory_cmpEq (w : ℕ) (s : Memory.State) (x : ℕ × ℕ) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (cmpEqProg x)) := by
  dsimp only [cmpEqProg]; split_ifs <;> trivial

private theorem validHistory_cmpZero (w : ℕ) (s : Memory.State) (a : ℕ) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (cmpZeroProg a)) := by
  dsimp only [cmpZeroProg]; split_ifs <;> trivial

theorem validHistory_selectPos (w : ℕ) (s : Memory.State) (x : ℕ × (ℕ × ℕ)) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (selectPosProg x)) := by
  dsimp only [selectPosProg]; split_ifs <;> trivial

private theorem validHistory_scanStepTarget (w : ℕ) (s : Memory.State) (x : ScanStepCtx) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (scanStepTargetProg x)) := by
  unfold scanStepTargetProg; split_ifs <;> trivial

private theorem validHistory_scanStepStop (w : ℕ) (s : Memory.State) (x : ScanStepCtx) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (scanStepStopProg x)) := by
  unfold scanStepStopProg; split_ifs <;> trivial

theorem validHistory_scanStepQuery (w : ℕ) (s : Memory.State) (x : ScanStepCtx) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (scanStepQueryProg x)) := by
  unfold scanStepQueryProg; split_ifs <;> trivial

private theorem validHistory_readFull {w : ℕ} {s : Memory.State} {x : ClusterInput × ℕ}
    (hms : ClusterMemSafe w x.1 s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (readFullProg x)) :=
  ⟨masked_addr_lt hms.2.1, trivial⟩

private theorem validHistory_readOcc {w : ℕ} {s : Memory.State} {x : ClusterInput × ℕ}
    (hms : ClusterMemSafe w x.1 s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (readOccProg x)) :=
  ⟨masked_addr_lt hms.2.2.1, trivial⟩

private theorem validHistory_readRunStart {w : ℕ} {s : Memory.State} {x : ClusterInput × ℕ}
    (hms : ClusterMemSafe w x.1 s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (readRunStartProg x)) :=
  ⟨masked_addr_lt hms.2.2.2.1, trivial⟩

private theorem validHistory_readRem {w : ℕ} {s : Memory.State} {x : ClusterInput × ℕ}
    (hms : ClusterMemSafe w x.1 s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (readRemProg x)) :=
  ⟨masked_addr_lt hms.2.2.2.2, trivial⟩

private theorem validHistory_writeBit {w : ℕ} {d : ClusterInput} {s : Memory.State}
    {arr slot val : ℕ} (hcs : ClusterSafe w d) (hwf : Memory.WellFormed w s)
    (harr : arr + (d 4 >>> d 9) < s.frontier) (hbit : val < 2) :
    let idx := slot &&& d 4
    let addr := arr + (idx >>> d 9)
    let sh := idx &&& d 10
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (do
      let oldWord ← Memory.read addr
      Memory.write addr (oldWord ^^^ (((oldWord >>> sh) &&& 1 ^^^ val) <<< sh)))) :=
  have hlt := masked_addr_lt (idx := slot) harr
  ⟨hlt, ⟨hlt, fits_writeBit_newWord (hwf.2 _) (Nat.and_le_right.trans_lt hcs.pBitMask_lt) hbit⟩,
    trivial⟩

private theorem validHistory_writeFull {w : ℕ} {s : Memory.State} {x : ClusterInput × (ℕ × ℕ)}
    (hcs : ClusterSafe w x.1) (hms : ClusterMemSafe w x.1 s) (hbit : x.2.2 < 2) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (writeFullProg x)) :=
  validHistory_writeBit hcs hms.1 hms.2.1 hbit

private theorem validHistory_writeOcc {w : ℕ} {s : Memory.State} {x : ClusterInput × (ℕ × ℕ)}
    (hcs : ClusterSafe w x.1) (hms : ClusterMemSafe w x.1 s) (hbit : x.2.2 < 2) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (writeOccProg x)) :=
  validHistory_writeBit hcs hms.1 hms.2.2.1 hbit

private theorem validHistory_writeRunStart {w : ℕ} {s : Memory.State} {x : ClusterInput × (ℕ × ℕ)}
    (hcs : ClusterSafe w x.1) (hms : ClusterMemSafe w x.1 s) (hbit : x.2.2 < 2) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (writeRunStartProg x)) :=
  validHistory_writeBit hcs hms.1 hms.2.2.2.1 hbit

private theorem validHistory_writeRem {w : ℕ} {s : Memory.State} {x : ClusterInput × (ℕ × ℕ)}
    (hcs : ClusterSafe w x.1) (hms : ClusterMemSafe w x.1 s) (hval : x.2.2 ≤ x.1 14) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (writeRemProg x)) :=
  have hlt := masked_addr_lt (idx := x.2.1) hms.2.2.2.2
  ⟨hlt, ⟨hlt, Nat.xor_lt_two_pow (hms.1.2 _)
    (fits_writeRem_diff_sh hcs.remPack_le hcs.fMask_lt_f hval)⟩, trivial⟩

private theorem validHistory_boundedWhile {δ σ : Type} {w : ℕ} {d₀ : ClusterInput}
    (guard : δ → σ → Prop) [∀ d a, Decidable (guard d a)]
    (body : δ × σ → Memory.Prog σ) (d : δ)
    (hstep : ∀ a t, ClusterMemSafe w d₀ t → guard d a →
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (body (d, a))))
    (n : ℕ) (a : σ) {s : Memory.State} (hms : ClusterMemSafe w d₀ s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (boundedWhile guard body d n a)) := by
  induction n generalizing a s with
  | zero => trivial
  | succ n ih =>
    by_cases hg : guard d a
    · simp only [boundedWhile, hg, ↓reduceIte]
      exact validHistory_bind_of_memSafe hms (hstep a s hms hg) fun t hms' => ih _ hms'
    · simp only [boundedWhile, hg, ↓reduceIte]
      trivial

private theorem validHistory_iterate {δ σ : Type} {w : ℕ} {d₀ : ClusterInput}
    (body : δ × σ → Memory.Prog σ) (d : δ)
    (hstep : ∀ a t, ClusterMemSafe w d₀ t →
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (body (d, a))))
    (n : ℕ) (a : σ) {s : Memory.State} (hms : ClusterMemSafe w d₀ s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (iterate body d n a)) := by
  induction n generalizing a s with
  | zero => trivial
  | succ n ih =>
    simp only [iterate]
    exact validHistory_bind_of_memSafe hms (hstep a s hms) fun t hms' => ih _ hms'

private theorem validHistory_readFullCountStep {w : ℕ} {d : ClusterInput} {t : Memory.State}
    (hms : ClusterMemSafe w d t) (rawIdx : ℕ) (a : ℕ × ℕ) :
    (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (do
      let f' ← readFullProg (d, rawIdx)
      if f' = 0 then pure (a.1, 0) else pure (a.1 + 1, a.2 - 1))) :=
  validHistory_bind_of_memSafe hms (validHistory_readFull hms) fun _ _ => by split_ifs <;> trivial

private abbrev copySlotProg (d : ClusterInput) (src dst next : ℕ) : Memory.Prog ℕ := do
  let runBit ← readRunStartProg (d, src)
  let remVal ← readRemProg (d, src)
  let _ ← writeRunStartProg (d, (dst, runBit))
  let _ ← writeRemProg (d, (dst, remVal))
  pure next

private theorem validHistory_copySlot {w : ℕ} {d : ClusterInput} {t : Memory.State}
    (hcs : ClusterSafe w d) (hms : ClusterMemSafe w d t) (src dst next : ℕ) :
    (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t
      (copySlotProg d src dst next)) :=
  validHistory_bind_of_memSafe hms (validHistory_readRunStart hms) fun t' hms' =>
    validHistory_bind_of_memSafe hms' (validHistory_readRem hms') fun _ hms'' =>
      validHistory_bind_of_memSafe hms''
        (validHistory_writeRunStart hcs hms''
          (Nat.lt_succ_of_le (clientResult_readRunStart_le t _)))
        fun _ hms''' =>
          validHistory_bind_of_memSafe hms'''
            (validHistory_writeRem hcs hms''' (clientResult_readRem_le t' _)) fun _ _ => trivial

private theorem validHistory_findCluster {w : ℕ} {d : ClusterInput} {s : Memory.State}
    (hms : ClusterMemSafe w d s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (findClusterProg d)) :=
  validHistory_bind_of_memSafe hms
    (validHistory_boundedWhile _ _ _
      (fun a _ hms' _ => validHistory_readFullCountStep hms' _ a) _ _ hms)
    fun _ hms1 => validHistory_bind_of_memSafe hms1
      (validHistory_boundedWhile _ _ _
        (fun a _ hms' _ => validHistory_readFullCountStep hms' _ a) _ _ hms1)
      fun _ _ => trivial

private theorem validHistory_scanCluster {w : ℕ} {x : ClusterInput × (ℕ × (ℕ × ℕ))}
    {s : Memory.State} (hms : ClusterMemSafe w x.1 s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (scanClusterProg x)) := by
  rcases x with ⟨d, o, a, ℓ⟩
  dsimp only [scanClusterProg, pure_bind_prog]
  refine validHistory_bind_of_memSafe hms
    (validHistory_iterate _ _ (fun _ _ hms_t => by
      dsimp only [occBeforeStep, pure_bind_prog]
      exact validHistory_bind_of_memSafe hms_t (validHistory_readOcc hms_t) fun _ _ => trivial)
      _ _ hms)
    fun _ hms1 => validHistory_bind_of_memSafe hms1 (validHistory_readOcc hms1) fun _ hms2 =>
      validHistory_bind_of_memSafe hms2 ?_ fun _ _ => trivial
  refine validHistory_iterate _ _ (fun _ _ hms_t => ?_) _ _ hms2
  dsimp only [scanLoopStep, pure_bind_prog]
  exact validHistory_bind_of_memSafe hms_t
    (by
      dsimp only [scanStepReadsProg, pure_bind_prog]
      exact validHistory_bind_of_memSafe hms_t (validHistory_readOcc hms_t) fun _ hms' =>
        validHistory_bind_of_memSafe hms' (validHistory_readRunStart hms') fun _ hms'' =>
          validHistory_bind_of_memSafe hms'' (validHistory_readRem hms'') fun _ _ => trivial)
    fun t1 hms1 => validHistory_bind_of_memSafe hms1 (validHistory_scanStepTarget w t1 _)
      fun t2 hms2 => validHistory_bind_of_memSafe hms2 (validHistory_scanStepStop w t2 _)
        fun t3 hms3 => validHistory_bind_of_memSafe hms3 (validHistory_scanStepQuery w t3 _)
          fun _ _ => trivial

private theorem validHistory_insertAfterScan {w : ℕ}
    {x : (ClusterInput × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))} {s : Memory.State}
    (hcs : ClusterSafe w x.1.1) (hms : ClusterMemSafe w x.1.1 s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (insertAfterScanProg x)) := by
  rcases x with ⟨⟨d, o⟩, ⟨occQ, ℓ⟩, s₀, s_idx⟩
  dsimp only [insertAfterScanProg, pure_bind_prog]
  refine validHistory_bind_of_memSafe hms ?_ fun _ hms1 =>
    validHistory_bind_of_memSafe hms1
      (validHistory_iterate _ _ (fun _ _ hms_t => by
        dsimp only [shiftRightStep, pure_bind_prog]
        exact validHistory_copySlot hcs hms_t _ _ _) _ _ hms1)
      fun t2 hms2 => ?_
  · dsimp only [insertClearOldProg, pure_bind_prog]
    split_ifs
    · exact validHistory_writeRunStart hcs hms Nat.zero_lt_two
    · trivial
    · trivial
  · dsimp only [insertWriteNewProg, pure_bind_prog]
    exact validHistory_bind_of_memSafe hms2 (validHistory_cmpEq w t2 _) fun _ hms3 =>
      validHistory_bind_of_memSafe hms3
        (validHistory_writeRunStart hcs hms3 (Nat.lt_succ_of_le (clientResult_cmpEq_le t2 _)))
        fun _ hms4 => validHistory_bind_of_memSafe hms4 (validHistory_writeRem hcs hms4 hcs.r_le)
          fun _ hms5 => validHistory_bind_of_memSafe hms5
            (validHistory_writeOcc hcs hms5 one_lt_two)
            fun _ hms6 => validHistory_bind_of_memSafe hms6
              (validHistory_writeFull hcs hms6 one_lt_two) fun _ _ => trivial

private theorem validHistory_deleteAfterScan {w : ℕ}
    {x : (ClusterInput × ℕ) × ((ℕ × ℕ) × ℕ)} {s : Memory.State}
    (hcs : ClusterSafe w x.1.1) (hms : ClusterMemSafe w x.1.1 s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (deleteAfterScanProg x)) := by
  rcases x with ⟨⟨d, o⟩, ⟨s₀, s_idx⟩, e⟩
  dsimp only [deleteAfterScanProg]
  split_ifs
  · dsimp only [pure_bind_prog]
    refine validHistory_bind_of_memSafe hms
      (by
        dsimp only [deleteHasMoreProg, pure_bind_prog]
        exact validHistory_bind_of_memSafe hms (validHistory_cmpLt w s _) fun _ hms' =>
          validHistory_bind_of_memSafe hms' (validHistory_readRunStart hms') fun t'' hms'' =>
            validHistory_bind_of_memSafe hms'' (validHistory_cmpZero w t'' _) fun _ _ => trivial)
      fun _ hms1 => validHistory_bind_of_memSafe hms1
        (validHistory_iterate _ _ (fun _ _ hms_t => by
          dsimp only [shiftLeftStep, pure_bind_prog]
          exact validHistory_copySlot hcs hms_t _ _ _) _ _ hms1)
        fun _ hms2 => validHistory_bind_of_memSafe hms2 ?_ fun _ hms3 =>
          validHistory_bind_of_memSafe hms3 (by
            dsimp only [deleteClearEndProg]
            simp only [pure_bind_prog]
            exact validHistory_bind_of_memSafe hms3
              (validHistory_writeFull hcs hms3 Nat.zero_lt_two) fun _ hms' =>
                validHistory_bind_of_memSafe hms'
                  (validHistory_writeRunStart hcs hms' Nat.zero_lt_two) fun _ hms'' =>
                    validHistory_writeRem hcs hms'' (Nat.zero_le _)) fun _ _ => trivial
    dsimp only [deleteUpdateRunProg, pure_bind_prog]
    split_ifs
    · exact validHistory_writeOcc hcs hms2 Nat.zero_lt_two
    · exact validHistory_writeRunStart hcs hms2 one_lt_two
    · trivial
  · trivial

private theorem validHistory_clusterOp {w : ℕ} {d : ClusterInput} {s : Memory.State}
    (hcs : ClusterSafe w d) (hms : ClusterMemSafe w d s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (clusterOpProg d)) := by
  refine validHistory_bind_of_memSafe hms (validHistory_findCluster hms) fun t1 hms1 =>
    validHistory_bind_of_memSafe hms1 (validHistory_scanCluster hms1) fun t2 hms2 => ?_
  dsimp only [clusterDispatchProg]
  split_ifs
  · exact validHistory_insertAfterScan hcs hms2
  · exact validHistory_deleteAfterScan hcs hms2
  · trivial

@[simp] private theorem memoryCost_cmpLt (x : ℕ × ℕ) (s : Memory.State) :
    memoryCost (cmpLtProg x) s = 0 := by
  dsimp only [cmpLtProg]; split_ifs <;> rfl

@[simp] private theorem memoryCost_cmpEq (x : ℕ × ℕ) (s : Memory.State) :
    memoryCost (cmpEqProg x) s = 0 := by
  dsimp only [cmpEqProg]; split_ifs <;> rfl

@[simp] private theorem memoryCost_cmpZero (a : ℕ) (s : Memory.State) :
    memoryCost (cmpZeroProg a) s = 0 := by
  dsimp only [cmpZeroProg]; split_ifs <;> rfl

@[simp] theorem memoryCost_selectPos (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (selectPosProg x) s = 0 := by
  dsimp only [selectPosProg]; split_ifs <;> rfl

@[simp] theorem memoryCost_scanStepTarget (x : ScanStepCtx)
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

theorem memoryCost_iterate_le {δ σ : Type} (body : δ × σ → Memory.Prog σ) (c : ℕ)
    (hstep : ∀ d a s, memoryCost (body (d, a)) s ≤ c)
    (d : δ) (n : ℕ) (a : σ) (s : Memory.State) :
    memoryCost (iterate body d n a) s ≤ c * n := by
  induction n generalizing a s with
  | zero => simp [iterate]
  | succ n ih =>
    change memoryCost ((body (d, a)).bind (iterate body d n)) s ≤ c * (n + 1)
    rw [memoryCost_bind]
    have h1 := hstep d a s
    have h2 := ih ((Memory.spec 0).clientResult s (body (d, a)))
      ((Memory.spec 0).clientState s (body (d, a)))
    rw [Nat.mul_succ]
    omega

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
        StateTransitionSpec.clientResult_bind, hstate, hcost, hresult]
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
  rw [memoryCost_bind', memoryCost_bind', StateTransitionSpec.clientResult_bind,
    StateTransitionSpec.clientResult_bind, clientState_backLen, clientState_fwdLen,
    memoryCost_pure, clientResult_pure]
  have hb := memoryCost_countWhile backLenStep d s
    (fun c => (Memory.spec 0).clientResult s (readFullProg (d, d 0 + d 3 - (c + 1))) = 0)
    (fun _ => clientState_backLenStep _ _)
    (fun _ => by change memoryCost ((readFullProg _).bind _) s = 1
                 rw [memoryCost_bind, memoryCost_readFull]; split_ifs <;> rfl)
    (fun c r => clientResult_backLenStep s (d, (c, r))) (d 3) 0 (d 3)
  have hf := memoryCost_countWhile fwdLenStep d s
    (fun c => (Memory.spec 0).clientResult s (readFullProg (d, d 0 + c)) = 0)
    (fun _ => clientState_fwdLenStep _ _)
    (fun _ => by change memoryCost ((readFullProg _).bind _) s = 1
                 rw [memoryCost_bind, memoryCost_readFull]; split_ifs <;> rfl)
    (fun c r => clientResult_fwdLenStep s (d, (c, r)))
    (d 3) 0 (d 3 - ((Memory.spec 0).clientResult s (backLenProg d)).1)
  dsimp only [backLenProg, fwdLenProg] at hb hf ⊢
  omega

private theorem memoryCost_copySlot (d : ClusterInput) (src dst next : ℕ) (t : Memory.State) :
    memoryCost (copySlotProg d src dst next) t = 6 := by
  simp only [copySlotProg, memoryCost_bind', memoryCost_readRunStart, memoryCost_readRem,
    memoryCost_writeRunStart, memoryCost_writeRem, memoryCost_pure]

private theorem memoryCost_scanCluster_le (x : ClusterInput × (ℕ × (ℕ × ℕ))) (s : Memory.State)
    (ha : x.2.2.1 ≤ x.2.2.2) :
    memoryCost (scanClusterProg x) s ≤ 4 * x.2.2.2 + 1 := by
  rcases x with ⟨d, o, a, ℓ⟩
  unfold scanClusterProg
  simp only [pure_bind_prog, memoryCost_bind', memoryCost_readOcc, memoryCost_pure]
  rw [clientState_occBefore, clientState_readOcc]
  have hocc : memoryCost (occBeforeProg (d, o, a)) s ≤ 1 * a :=
    memoryCost_iterate_le occBeforeStep 1 (fun _ _ _ => by
      simp only [occBeforeStep, pure_bind_prog, memoryCost_bind', memoryCost_readOcc,
        memoryCost_pure]; omega) _ _ _ s
  have hloop : memoryCost (scanLoopProg
      ⟨d, o, a, ℓ, ((Memory.spec 0).clientResult s (occBeforeProg (d, o, a))).2,
        ((Memory.spec 0).clientResult s (occBeforeProg (d, o, a))).2 +
          (Memory.spec 0).clientResult s (readOccProg (d, d 0))⟩) s ≤ 3 * ℓ :=
    memoryCost_iterate_le scanLoopStep 3 (fun _ _ _ => by
      simp only [scanLoopStep, scanStepReadsProg, pure_bind_prog, memoryCost_bind',
        memoryCost_readOcc, memoryCost_readRunStart, memoryCost_readRem,
        memoryCost_scanStepTarget, memoryCost_scanStepStop, memoryCost_scanStepQuery,
        memoryCost_pure]; omega) _ _ _ s
  dsimp only at ha ⊢
  omega

private theorem memoryCost_insertAfterScan_le
    (x : (ClusterInput × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (s : Memory.State) :
    memoryCost (insertAfterScanProg x) s ≤ 6 * x.2.1.2 + 10 := by
  rcases x with ⟨⟨d, o⟩, ⟨occQ, ℓ⟩, s₀, s_idx⟩
  simp only [insertAfterScanProg, pure_bind_prog, memoryCost_bind']
  set s₁ := (Memory.spec 0).clientState s (insertClearOldProg ((d, o), occQ, s₀, s_idx))
  set s₂ := (Memory.spec 0).clientState s₁ (shiftRightProg ((d, o), ℓ, ℓ - s_idx))
  have hclear : memoryCost (insertClearOldProg ((d, o), occQ, s₀, s_idx)) s ≤ 2 := by
    dsimp only [insertClearOldProg, pure_bind_prog]; split_ifs <;> simp
  have hshift : memoryCost (shiftRightProg ((d, o), ℓ, ℓ - s_idx)) s₁ ≤ 6 * (ℓ - s_idx) :=
    memoryCost_iterate_le shiftRightStep 6 (fun _ _ _ => (memoryCost_copySlot ..).le) _ _ _ s₁
  have hwrite : memoryCost (insertWriteNewProg ((d, o), (s₀, s_idx), ℓ)) s₂ = 8 := by
    simp only [insertWriteNewProg, pure_bind_prog, memoryCost_bind', memoryCost_cmpEq,
      memoryCost_writeRunStart, memoryCost_writeRem, memoryCost_writeOcc, memoryCost_writeFull,
      memoryCost_pure]
  have : 6 * (ℓ - s_idx) ≤ 6 * ℓ := Nat.mul_le_mul_left 6 (Nat.sub_le _ _)
  omega

private theorem memoryCost_deleteAfterScan_le
    (x : (ClusterInput × ℕ) × ((ℕ × ℕ) × ℕ)) (s : Memory.State) :
    memoryCost (deleteAfterScanProg x) s ≤ 6 * x.2.2 + 9 := by
  rcases x with ⟨⟨d, o⟩, ⟨s₀, s_idx⟩, e⟩
  dsimp only [deleteAfterScanProg]
  split_ifs
  · simp only [pure_bind_prog, memoryCost_bind', memoryCost_pure]
    set a := (Memory.spec 0).clientResult s (deleteHasMoreProg ((d, o), s₀, e))
    set s₁ := (Memory.spec 0).clientState s (deleteHasMoreProg ((d, o), s₀, e))
    set s₂ := (Memory.spec 0).clientState s₁ (shiftLeftProg ((d, o), s_idx, e - 1 - s_idx))
    set s₃ := (Memory.spec 0).clientState s₂ (deleteUpdateRunProg ((d, o), a, s₀, s_idx))
    have hmore : memoryCost (deleteHasMoreProg ((d, o), s₀, e)) s = 1 := by
      simp only [deleteHasMoreProg, pure_bind_prog, memoryCost_bind', memoryCost_cmpLt,
        memoryCost_readRunStart, memoryCost_cmpZero, memoryCost_pure]
    have hshift : memoryCost (shiftLeftProg ((d, o), s_idx, e - 1 - s_idx)) s₁ ≤
        6 * (e - 1 - s_idx) :=
      memoryCost_iterate_le shiftLeftStep 6 (fun _ _ _ => (memoryCost_copySlot ..).le) _ _ _ s₁
    have hupd : memoryCost (deleteUpdateRunProg ((d, o), a, s₀, s_idx)) s₂ ≤ 2 := by
      dsimp only [deleteUpdateRunProg, pure_bind_prog]; split_ifs <;> simp
    have hclr : memoryCost (deleteClearEndProg ((d, o), e)) s₃ = 6 := by
      simp only [deleteClearEndProg, pure_bind_prog, memoryCost_bind', memoryCost_writeFull,
        memoryCost_writeRunStart, memoryCost_writeRem]
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
    simp only [ext, findClusterProg, StateTransitionSpec.clientResult_bind, clientResult_pure]
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
@[expose] def maskedSlot (b idx : ℕ) : Fin (2 ^ b) :=
  ⟨idx &&& (2 ^ b - 1), Nat.and_lt_two_pow idx (Nat.sub_lt (Nat.two_pow_pos b) one_pos)⟩

@[simp] theorem maskedSlot_val (b idx : ℕ) :
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

private theorem clientResult_boundedWhile_zero_snd {δ : Type}
    (body : δ × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)) (d : δ) (fuel c : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s
      (boundedWhile (fun _ (st : ℕ × ℕ) => 0 < st.2) body d fuel (c, 0)) = (c, 0) := by
  cases fuel <;> simp [boundedWhile]

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
    rw [StateTransitionSpec.clientResult_bind, hstate, hresult cnt hcnt]
    rcases lt_or_eq_of_le hcnt with hlt | rfl
    · rw [hfull cnt hlt]
      simp only [Bool.toNat_true, one_ne_zero, ↓reduceIte]
      exact ih (cnt + 1) (rem - 1) (by omega) (by omega) (by omega)
    · rw [hempty]
      simp only [Bool.toNat_false, ↓reduceIte]
      exact clientResult_boundedWhile_zero_snd _ _ _ _ _

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
      simp only [mkClusterInput_0, mkClusterInput_3, clientResult_readFull_mk,
        maskedSlot_backSlot q (a := cnt + 1) (by omega)])
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
  rw [mkClusterInput_3]
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
      simp only [mkClusterInput_0, clientResult_readFull_mk, maskedSlot_probeSlot q cnt])
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
  simp only [mkClusterInput_3]
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
  rw [StateTransitionSpec.clientResult_bind, clientState_backLen,
    clientResult_backLen_mk _ _ _ _ _ _ _ _ _ hinv hS_lt,
    StateTransitionSpec.clientResult_bind, clientState_fwdLen,
    clientResult_fwdLen_mk _ _ _ _ _ _ _ _ _ hinv hS_lt, clientResult_pure]
  simp only [mkClusterInput_0, mkClusterInput_3, mkClusterInput_4,
    add_sub_and_eq_backSlot_val q ha_le]
  rfl

theorem calcRunStart_zero {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a : ℕ) :
    calcRunStart st o a 0 = 0 := rfl

theorem calcRunStart_succ {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a m : ℕ) :
    calcRunStart st o a (m + 1) =
      calcRunStart st o a m + (decide (runsBefore st o (m + 1) ≤ occBefore st o a)).toNat := by
  simp only [calcRunStart, List.range_succ, List.filter_append, List.length_append,
    List.filter_cons, List.filter_nil]
  cases decide (runsBefore st o (m + 1) ≤ occBefore st o a) <;> rfl

theorem calcTargetSlot_zero {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a : ℕ)
    (r : Fin (2 ^ f)) :
    calcTargetSlot st o a 0 r = 0 := rfl

theorem calcTargetSlot_succ {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a m : ℕ)
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

theorem calcDeleteStopPrefix_zero {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a ℓ : ℕ) :
    calcDeleteStopPrefix st o a ℓ 0 = ℓ := rfl

theorem calcDeleteStopPrefix_succ {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b))
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

theorem queryAnyPrefix_zero {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a : ℕ)
    (r : Fin (2 ^ f)) :
    queryAnyPrefix st o a 0 r = false := rfl

theorem queryAnyPrefix_succ {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a m : ℕ)
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
  have h := iterate_invariant occBeforeStep (mkClusterInput base w w₀ n k q r opTag, o.val)
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
  have h := iterate_invariant scanLoopStep env
    (fun j m t => t = s ∧ j ≤ ℓ ∧ m = snap (ℓ - j))
    (fun j m t ⟨ht, hj, hm⟩ => by
      subst ht hm
      set i := ℓ - (j + 1)
      rw [clientState_scanLoopStep, show ℓ - j = i + 1 by omega]
      refine ⟨rfl, by omega, ?_⟩
      unfold scanLoopStep
      rw [StateTransitionSpec.clientResult_bind, clientState_scanStepReads,
        StateTransitionSpec.clientResult_bind, clientResult_pure, clientState_pure,
        StateTransitionSpec.clientResult_bind, clientState_scanStepTarget,
        StateTransitionSpec.clientResult_bind, clientState_scanStepStop,
        StateTransitionSpec.clientResult_bind, clientState_scanStepQuery, clientResult_pure,
        clientResult_scanStepTarget, clientResult_scanStepStop, clientResult_scanStepQuery,
        clientResult_scanStepReads]
      simp only [snap, env, d, mkClusterInput_1, clientResult_readOcc_mk,
        clientResult_readRunStart_mk, clientResult_readRem_mk, maskedSlot_probeSlot o i]
      have hruns : runsBefore st o i +
          (st.isRunStart (probeSlot (quotBits w₀ n) o i)).toNat = runsBefore st o (i + 1) := by
        rw [runsBefore_succ]; cases st.isRunStart _ <;> simp
      have hocc : occBefore st o i +
          (st.isOcc (probeSlot (quotBits w₀ n) o i)).toNat = occBefore st o (i + 1) := by
        rw [occBefore_succ]; cases st.isOcc _ <;> simp
      rw [hruns, hocc]
      ext
      · rfl
      · rfl
      · rfl
      · rw [calcRunStart_succ]
        by_cases h1 : runsBefore st o (i + 1) ≤ occBefore st o a <;> simp [h1]
      · rw [calcTargetSlot_succ]
        dsimp only [snap]
        change (if runsBefore st o (i + 1) ≤ occBefore st o a ∨
            runsBefore st o (i + 1) ≤ occBefore st o (a + 1) ∧
              st.remAt (probeSlot (quotBits w₀ n) o i) < r then
            calcTargetSlot st o a i r + 1 else calcTargetSlot st o a i r) = _
        by_cases h1 : runsBefore st o (i + 1) ≤ occBefore st o a <;>
          by_cases h2 : runsBefore st o (i + 1) ≤ occBefore st o (a + 1) <;>
          by_cases h3 : st.remAt (probeSlot (quotBits w₀ n) o i) < r <;> simp [h1, h2, h3]
      · rw [calcDeleteStopPrefix_succ st o a ℓ (by omega)]
        by_cases h1 : a < i <;>
          by_cases h2 : occBefore st o i < runsBefore st o (i + 1) <;>
          by_cases h3 : calcDeleteStopPrefix st o a ℓ i = ℓ <;> simp [h1, h2, h3]
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
  rw [StateTransitionSpec.clientResult_bind, clientState_occBefore, clientResult_occBefore_mk,
    StateTransitionSpec.clientResult_bind, clientState_readOcc,
    StateTransitionSpec.clientResult_bind, clientResult_pure, clientState_pure,
    StateTransitionSpec.clientResult_bind, clientState_scanLoop, clientResult_pure]
  dsimp only [d]
  rw [mkClusterInput_0, clientResult_readOcc_mk, maskedSlot_fin q]
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
  rw [StateTransitionSpec.clientState_bind, clientState_readRunStart,
    StateTransitionSpec.clientState_bind, clientState_readRem,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind, clientState_pure,
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
      dsimp only [shiftRightStep, copySlotProg, pure_bind_prog]
      rw [show s_idx + (rem + 1) - 1 = s_idx + rem by omega,
        show s_idx + (rem + 1) = s_idx + rem + 1 by omega]
    rw [StateTransitionSpec.clientState_bind, clientResult_shiftRightStep,
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
  simp only [insertClearOldProg, pure_bind_prog]
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
  dsimp only [pure_bind_prog]
  rw [StateTransitionSpec.clientResult_bind, clientState_cmpEq, clientResult_cmpEq,
    StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
    StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind, clientResult_pure,
    StateTransitionSpec.clientState_bind, clientState_cmpEq, clientResult_cmpEq,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind, clientState_pure]
  dsimp only [d]
  rw [mkClusterInput_0, mkClusterInput_1]
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
  rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
    clientResult_pure, clientState_pure, StateTransitionSpec.clientResult_bind,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
    clientResult_pure, clientState_pure, StateTransitionSpec.clientState_bind]
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
  unfold deleteHasMoreProg; dsimp only [pure_bind_prog]
  rw [StateTransitionSpec.clientResult_bind, clientState_cmpLt, clientResult_cmpLt,
    StateTransitionSpec.clientResult_bind, clientState_readRunStart,
    StateTransitionSpec.clientResult_bind, clientState_cmpZero, clientResult_cmpZero,
    clientResult_pure]
  dsimp only [d]
  by_cases hlt : s₀ + 1 < e
  · simp only [hlt, decide_true, Bool.toNat_true, one_mul, Bool.true_and,
      clientResult_readRunStart_mk, maskedSlot_probeSlot o (s₀ + 1)]
    cases st.isRunStart (probeSlot (quotBits w₀ n) o (s₀ + 1)) <;> rfl
  · simp [hlt]

private theorem clientState_deleteHasMore (s : Memory.State)
    (x : (ClusterInput × ℕ) × (ℕ × ℕ)) :
    (Memory.spec 0).clientState s (deleteHasMoreProg x) = s := by
  unfold deleteHasMoreProg; dsimp only [pure_bind_prog]
  rw [StateTransitionSpec.clientState_bind, clientState_cmpLt,
    StateTransitionSpec.clientState_bind, clientState_readRunStart,
    StateTransitionSpec.clientState_bind, clientState_cmpZero, clientState_pure]

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
    rw [StateTransitionSpec.clientState_bind, clientResult_shiftLeftStep]
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
  simp only [deleteUpdateRunProg, pure_bind_prog]
  cases hasMore
  · simp only [Bool.toNat_false, ↓reduceIte, Bool.not_false]
    have hz : writeOccProg (mkClusterInput base w w₀ n k q r opTag, q.val, 0) =
        writeOccProg (mkClusterInput base w w₀ n k q r opTag, q.val, false.toNat) := rfl
    rw [show d 0 = q.val from rfl, hz, extractFilterState_writeOcc_mk, maskedSlot_fin q]
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
  rw [StateTransitionSpec.clientState_bind, clientResult_pure, clientState_pure,
    StateTransitionSpec.clientState_bind, clientResult_pure, clientState_pure,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
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
  unfold deleteAfterScanProg; simp only [hlt, ↓reduceIte, pure_bind_prog]
  rw [StateTransitionSpec.clientResult_bind, clientState_deleteHasMore,
    clientResult_deleteHasMore_mk, StateTransitionSpec.clientResult_bind,
    StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind, clientResult_pure,
    StateTransitionSpec.clientState_bind, clientState_deleteHasMore,
    clientResult_deleteHasMore_mk, StateTransitionSpec.clientState_bind,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind, clientState_pure]
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

theorem slotFrame_deleteAfterScan_mk (base w w₀ n k : ℕ)
    (q o : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (s : Memory.State) (s₀ s_idx e : ℕ) :
    SlotFrame base w w₀ n k s
      ((Memory.spec 0).clientState s
        (deleteAfterScanProg
          ((mkClusterInput base w w₀ n k q r opTag, o.val), ((s₀, s_idx), e)))) := by
  by_cases hlt : s_idx < e
  · exact (deleteAfterScan_spec_of_lt base w w₀ n k q o r opTag s s₀ s_idx e hlt).2.2
  · simp only [deleteAfterScanProg, hlt, ↓reduceIte]
    exact SlotFrame.refl _ _ _ _ _ _

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
  rw [StateTransitionSpec.clientResult_bind, clientState_findCluster,
    clientResult_findCluster_mk _ _ _ _ _ _ _ _ _ hinv hS_lt,
    StateTransitionSpec.clientResult_bind, clientState_scanCluster,
    clientResult_scanCluster_mk _ _ _ _ _ _ _ _ _ _ _ _ hq,
    StateTransitionSpec.clientState_bind, clientState_findCluster,
    clientResult_findCluster_mk _ _ _ _ _ _ _ _ _ hinv hS_lt,
    StateTransitionSpec.clientState_bind, clientState_scanCluster,
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
  simp only [mkClusterInput_2, ↓reduceIte]
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
  simp only [mkClusterInput_2, one_ne_zero, ↓reduceIte]
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
  simp only [clusterDispatchProg, mkClusterInput_2, OfNat.ofNat_ne_zero, Nat.reduceEqDiff,
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

/-! ## Section 8C: Register Layout (`rQF`), Remainder Hash Code, and Realized `clusterCode` -/

open Cslib.Probability

/-- Register count for the Word-RAM quotient filter: `0..239` shared with `ReducedKWise`,
`240..247` dedicated to `SubroutineCode` control and operation tags, and
`248 .. 248 + realizes_clusterOp.scratchSize` dedicated to the realized `Memory.Prog` scratch
registers. -/
@[expose] noncomputable def rQF : ℕ :=
  248 + (realizes_clusterOp.scratchSize + 1)

theorem le_rQF : 248 ≤ rQF := by
  dsimp only [rQF]
  omega

/-- Canonical embedding `Fin 248 → Fin rQF` for fixed control and hash registers. -/
@[expose] noncomputable def qfReg : Fin 248 → Fin rQF :=
  Fin.castLE le_rQF

theorem injective_qfReg : Function.Injective qfReg :=
  Fin.castLE_injective le_rQF

@[simp]
theorem qfReg_inj {i j : Fin 248} : qfReg i = qfReg j ↔ i = j :=
  injective_qfReg.eq_iff

@[simp]
theorem val_qfReg (i : Fin 248) : (qfReg i).val = i.val := rfl

/-- Embedding `Fin 240 → Fin rQF` for `ReducedKWise` subroutines. -/
@[expose] noncomputable def kwiseMap : Fin 240 → Fin rQF :=
  Fin.castLE (by dsimp only [rQF]; omega)

theorem injective_kwiseMap : Function.Injective kwiseMap :=
  Fin.castLE_injective _

@[simp]
theorem kwiseMap_eq_qfReg (i : Fin 240) :
    kwiseMap i = qfReg (Fin.castLE (by decide) i) := rfl

theorem extend_kwiseMap_regs {y : Data 240} {x : Data rQF} {j : Fin rQF} (hj : 240 ≤ j.val) :
    (y.extend kwiseMap x).regs j = x.regs j := by
  change Function.extend kwiseMap y.regs x.regs j = x.regs j
  apply Function.extend_apply'
  rintro ⟨i, rfl⟩
  have := i.isLt
  dsimp only [kwiseMap, Fin.val_castLE] at hj
  omega

/-- Sample the remainder seed `γ : RemSeed w₀` uniformly and store it at `remSeedAddr base w w₀ n`
using `5` instructions (`1` `rand` call). -/
@[expose] noncomputable def remInitCode (w w₀ n : ℕ) : Code .exact rQF :=
  .seq (.op (.const (qfReg 30) (remSeedOff w w₀ n)))
  (.seq (.op (.exactBin .add (qfReg 30) (qfReg 0) (qfReg 30)))
  (.seq (.op (.const (qfReg 31) (2 ^ (w₀ - 1) - 1)))
  (.seq (.rand (qfReg 32) (qfReg 31))
        (.op (.store (qfReg 30) (qfReg 32))))))

/-- Closed-form machine state after `remInitCode w w₀ n` samples `γ`. -/
@[expose] noncomputable def remInitData (base w w₀ n : ℕ) (x : Data rQF) (γ : ℕ) : Data rQF :=
  (((x.set (qfReg 30) (remSeedOff w w₀ n)).set (qfReg 30) (remSeedAddr base w w₀ n)).set
    (qfReg 31) (2 ^ (w₀ - 1) - 1)).set (qfReg 32) γ |>.write (remSeedAddr base w w₀ n) γ

/-- Exact `ProbComp` semantics of `remInitCode w w₀ n`. -/
@[expose] noncomputable def remInitComp (base w w₀ n : ℕ) (x : Data rQF) :
    ProbComp (Data rQF × ℕ) := do
  let γ ← ProbComp.unifFin (2 ^ (w₀ - 1) - 1)
  pure (remInitData base w w₀ n x γ.val, 5)

theorem remInitCode_execRand {base w w₀ n k : ℕ} (hw₀ : w₀ ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k))
    {x : Data rQF} (h0 : x.regs (qfReg 0) = base) :
    ExecRand w (remInitCode w w₀ n) x (remInitComp base w w₀ n x) := by
  have hfit_addr : Fits w (base + remSeedOff w w₀ n) := by
    have : remSeedOff w w₀ n ≤ space w w₀ n k := by dsimp only [remSeedOff, space]; omega
    fits [this]
  have hfit_addr' : Fits w (remSeedAddr base w w₀ n) := hfit_addr
  have hfit_bound : Fits w (2 ^ (w₀ - 1) - 1) := by
    fits [Nat.pow_le_pow_right two_pos (by omega : w₀ - 1 ≤ w)]
  set s1 := x.set (qfReg 30) (remSeedOff w w₀ n)
  set s2 := s1.set (qfReg 30) (remSeedAddr base w w₀ n)
  set s3 := s2.set (qfReg 31) (2 ^ (w₀ - 1) - 1)
  have e2 : Exec w (.op (.exactBin .add (qfReg 30) (qfReg 0) (qfReg 30)) : Code .exact rQF)
      s1 s2 1 := by wram_exec [s1, h0, base_add_remSeedOff]
  have e4 := ExecRand.rand (B := .exact) (w := w) (dst := qfReg 32) (src := qfReg 31)
    (x := s3) (by simp [s3, hfit_bound])
  rw [show s3.regs (qfReg 31) = 2 ^ (w₀ - 1) - 1 by simp [s3]] at e4
  have e45 := ExecRand.seq
    (m₂ := fun d : Data rQF => pure (d.write (remSeedAddr base w w₀ n) (d.regs (qfReg 32)), 1))
    e4 fun z hz => by
      supp_cases hz with ⟨γ, rfl⟩
      have h1 := Exec.store (B := .exact) (w := w) (a := qfReg 30) (s := qfReg 32)
        (x := s3.set (qfReg 32) γ.val)
      rw [show (s3.set (qfReg 32) γ.val).regs (qfReg 30) = remSeedAddr base w w₀ n by
        simp +decide [s3, s2]] at h1
      exact h1.execRand
  have hall := (Exec.const (by fits)).seqRand (e2.seqRand ((Exec.const hfit_bound).seqRand e45))
  simpa only [remInitCode, remInitComp, remInitData, s3, s2, s1, bind_assoc, pure_bind,
    map_eq_bind_pure_comp, Function.comp_def, Data.set_regs, Function.update_self] using hall

theorem map_extractRemSeed_eval_remInitComp (base w w₀ n : ℕ) (x : Data rQF) :
    ((ProbComp.eval (remInitComp base w w₀ n x)).map fun z =>
      extractRemSeed base w w₀ n z.1.mem) =
      PMF.uniformOfFintype (RemSeed w₀) := by
  let e : Fin (2 ^ (w₀ - 1) - 1 + 1) ≃ RemSeed w₀ :=
    finCongr (Nat.sub_add_cancel Nat.one_le_two_pow)
  have hcomp :
      ((ProbComp.eval (remInitComp base w w₀ n x)).map fun z =>
        extractRemSeed base w w₀ n z.1.mem) =
        (ProbComp.eval (ProbComp.unifFin (2 ^ (w₀ - 1) - 1))).map e := by
    dsimp only [remInitComp]
    rw [ProbComp.eval_bind, PMF.map_bind]
    congr 1 with γ : 1
    simp only [ProbComp.eval_pure, PMF.pure_map, Function.comp_apply]
    congr 1
    apply Fin.ext
    have hlt : γ.val < 2 ^ (w₀ - 1) := by
      have := Nat.one_le_two_pow (n := w₀ - 1)
      have := γ.isLt
      omega
    dsimp only [extractRemSeed, remInitData, Data.write, Cslib.WordRAM.wordOfNat, e]
    simp [hlt]
  rw [hcomp, ProbComp.eval_unifFin, PMF.uniformOfFintype_map_equiv]

/-- Word-RAM snippet computing `(remHash U w₀ k γ u).val` into register `qfReg 3` from
`qfReg 0 = base` and `qfReg 1 = u.val`, using `ReducedKWise.reduceKeyCode w₀ w₀` in `45`
deterministic instructions. -/
@[expose] noncomputable def remEvalCode (w w₀ n k : ℕ) : Code .exact rQF :=
  .seq (.op (.const (qfReg 30) (remSeedOff w w₀ n)))
  (.seq (.op (.exactBin .add (qfReg 0) (qfReg 0) (qfReg 30)))
  (.seq ((ReducedKWise.reduceKeyCode w₀ w₀).rename kwiseMap)
  (.seq (.op (.const (qfReg 30) (remSeedOff w w₀ n)))
  (.seq (.op (.exactBin .sub (qfReg 0) (qfReg 0) (qfReg 30)))
  (.seq (.op (.const (qfReg 30) (w₀ - remBits w₀ k)))
        (.op (.exactBin .shiftRight (qfReg 3) (qfReg 3) (qfReg 30))))))))

theorem remEvalCode_exec {base w U w₀ n k : ℕ}
    (hw₀_pos : 0 < w₀) (hw₀ : w₀ ≤ w) (hU : U ≤ 2 ^ w₀)
    (hfit_space : Fits w (base + space w w₀ n k))
    (γ : RemSeed w₀) (u : Fin U) {x : Data rQF}
    (h0 : x.regs (qfReg 0) = base) (h1 : x.regs (qfReg 1) = u.val)
    (hseed : x.mem (remSeedAddr base w w₀ n) = γ.val) :
    ∃ y : Data rQF,
      Exec w (remEvalCode w w₀ n k) x y 45 ∧
      y.mem = x.mem ∧
      y.regs (qfReg 0) = base ∧
      y.regs (qfReg 3) = (remHash U w₀ k γ u).val ∧
      ∀ j : Fin rQF, 240 ≤ j.val → y.regs j = x.regs j := by
  have hfit_addr : Fits w (base + remSeedOff w w₀ n) := by
    have : remSeedOff w w₀ n ≤ space w w₀ n k := by dsimp only [remSeedOff, space]; omega
    fits [this]
  have hfit_addr' : Fits w (remSeedAddr base w w₀ n) := hfit_addr
  have hfit_sh : Fits w (w₀ - remBits w₀ k) := by
    fits [hw₀, @Nat.lt_two_pow_self w]
  have hrem_eq : oddMulModWord w₀ γ.val u.val >>> (w₀ - remBits w₀ k) =
      (remHash U w₀ k γ u).val := by
    have hsh : w₀ - remBits w₀ k = w₀ - (k + 1) := by dsimp only [remBits]; omega
    rw [hsh]
    exact oddMulModWord_shiftRight_eq_multiplyShiftReduced (R := k + 1) hw₀_pos γ u
  have hfit_rem : Fits w (remHash U w₀ k γ u).val := by
    fits [(remHash U w₀ k γ u).isLt, Nat.pow_le_pow_right two_pos ((remBits_le_w₀ w₀ k).trans hw₀)]
  have hmin : min w₀ (3 * w₀) = w₀ := min_eq_left (by omega)
  have hle : remSeedOff w w₀ n ≤ remSeedAddr base w w₀ n := by simp [remSeedAddr, remSeedOff]
  have hsub : remSeedAddr base w w₀ n - remSeedOff w w₀ n = base := by
    simp [remSeedAddr, remSeedOff]
  have hk1 : kwiseMap 1 = qfReg 1 := rfl
  unfold remEvalCode
  wram_exec [h0, show base + remSeedOff w w₀ n = remSeedAddr base w w₀ n from rfl]
  wram_call (ReducedKWise.reduceKeyCode_exec (b := w₀) hw₀_pos hw₀
    (((x.set (qfReg 30) (remSeedOff w w₀ n)).set (qfReg 0) (remSeedAddr base w w₀ n)).comap
      kwiseMap)
    (by simp only [Data.comap_mem, Data.comap_regs]; wram_simp [hseed]; exact γ.isLt)
    (by simp only [Data.comap_regs]; wram_simp [hk1, h1]; exact u.isLt.trans_le hU))
    renamed injective_kwiseMap with y₀ ⟨⟨hy₀_0, hy₀_3, hy₀_mem⟩, hframe⟩
  have hy0 : y₀.regs (qfReg 0) = remSeedAddr base w w₀ n := by
    rw [show qfReg 0 = kwiseMap 0 from rfl, hy₀_0]
    wram_simp
  have hy3 : y₀.regs (qfReg 3) = oddMulModWord w₀ γ.val u.val := by
    rw [show qfReg 3 = kwiseMap 3 from rfl, hy₀_3]
    wram_simp [hseed, hk1, h1, hmin, Nat.shiftRight_zero]
  wram_exec [hy0, hy3, hsub, hrem_eq]
  refine ⟨by wram_simp [hy₀_mem], by wram_simp, by wram_simp, fun j hj => ?_⟩
  have hj0 : j ≠ qfReg 0 := by fin_index [val_qfReg]
  have hj3 : j ≠ qfReg 3 := by fin_index [val_qfReg]
  have hj30 : j ≠ qfReg 30 := by fin_index [val_qfReg]
  wram_simp
  rw [hframe j fun i h => by subst h; simp at hj; omega]
  wram_simp

/-- Load `base + off` into `qfReg d` (for `d ≠ 0`) from `qfReg 0 = base` in `2` instructions. -/
@[expose] noncomputable def loadOffCode (d : Fin 248) (off : ℕ) : Code .exact rQF :=
  .seq (.op (.const (qfReg d) off))
       (.op (.exactBin .add (qfReg d) (qfReg 0) (qfReg d)))

private theorem loadOffCode_exec {base w off : ℕ} {d : Fin 248} (hd : d ≠ 0)
    (hfit : Fits w (base + off)) {x : Data rQF} (h0 : x.regs (qfReg 0) = base) :
    Exec w (loadOffCode d off) x (x.set (qfReg d) (base + off)) 2 := by
  have hd' : qfReg 0 ≠ qfReg d := by simp [qfReg_inj, hd.symm]
  unfold loadOffCode
  wram_exec [h0]
  cases x
  simp [Data.set]

/-- Source register map `Fin 15 → Fin rQF` (`qfReg 10 .. qfReg 24`) for `clusterOpProg`. -/
@[expose] noncomputable def clusterSrcRegs (i : Fin (WordEncoding.width ClusterInput)) : Fin rQF :=
  qfReg ⟨10 + i.val, by have hi : i.val < 15 := i.isLt; omega⟩

/-- Load the 15 words of `mkClusterInput base w w₀ n k q r opTag` into `qfReg 10 .. qfReg 24`
from `qfReg 0 = base`, `qfReg 2 = q.val`, `qfReg 3 = r.val`, `qfReg 247 = opTag` in `19`
instructions. -/
@[expose] noncomputable def loadClusterInputCode (w w₀ n k : ℕ) : Code .exact rQF :=
  let b := quotBits w₀ n
  let f := remBits w₀ k
  let pBit := slotPackShift b 1 w
  let pRem := slotPackShift b f w
  .seq (.op (.copy (qfReg 10) (qfReg 2)))
  (.seq (.op (.copy (qfReg 11) (qfReg 3)))
  (.seq (.op (.copy (qfReg 12) (qfReg 247)))
  (.seq (.op (.const (qfReg 13) (2 ^ b)))
  (.seq (.op (.const (qfReg 14) (2 ^ b - 1)))
  (.seq (loadOffCode 15 (fullOff w w₀ n))
  (.seq (loadOffCode 16 (occOff w w₀ n))
  (.seq (loadOffCode 17 (runOff w w₀ n))
  (.seq (loadOffCode 18 (remOff w w₀ n))
  (.seq (.op (.const (qfReg 19) pBit))
  (.seq (.op (.const (qfReg 20) (2 ^ pBit - 1)))
  (.seq (.op (.const (qfReg 21) pRem))
  (.seq (.op (.const (qfReg 22) (2 ^ pRem - 1)))
  (.seq (.op (.const (qfReg 23) f))
        (.op (.const (qfReg 24) (2 ^ f - 1))))))))))))))))

/-- Closed-form machine state after `loadClusterInputCode w w₀ n k`. -/
private noncomputable def loadClusterInputData (base w w₀ n k : ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) (opTag : ℕ)
    (x : Data rQF) : Data rQF :=
  let d := mkClusterInput base w w₀ n k q r opTag
  (((((((((((((((x.set (qfReg 10) (d 0)).set (qfReg 11) (d 1)).set (qfReg 12) (d 2)).set
    (qfReg 13) (d 3)).set (qfReg 14) (d 4)).set (qfReg 15) (d 5)).set
    (qfReg 16) (d 6)).set (qfReg 17) (d 7)).set (qfReg 18) (d 8)).set
    (qfReg 19) (d 9)).set (qfReg 20) (d 10)).set (qfReg 21) (d 11)).set
    (qfReg 22) (d 12)).set (qfReg 23) (d 13)).set (qfReg 24) (d 14))

private theorem loadClusterInputCode_exec {base w w₀ n k : ℕ}
    (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k))
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k))
    {opTag : ℕ} (hop : opTag < 4)
    {x : Data rQF}
    (h0 : x.regs (qfReg 0) = base)
    (h2 : x.regs (qfReg 2) = q.val)
    (h3 : x.regs (qfReg 3) = r.val)
    (h247 : x.regs (qfReg 247) = opTag)
    (hfr : x.regs (qfReg 240) = base + space w w₀ n k) :
    let d := mkClusterInput base w w₀ n k q r opTag
    let x₁ := loadClusterInputData base w w₀ n k q r opTag x
    Exec w (loadClusterInputCode w w₀ n k) x x₁ 19 ∧
    x₁.mem = x.mem ∧
    x₁.regs (qfReg 0) = base ∧
    x₁.regs (qfReg 240) = base + space w w₀ n k ∧
    x₁.regs ∘ clusterSrcRegs = WordEncoding.encode d := by
  intro d x₁
  have hfit_i (i : Fin (WordEncoding.width ClusterInput)) : Fits w (d i) :=
    encode_mkClusterInput_lt hw₀_pos hw hfit_space q r hop i
  have hf3 := hfit_i 3; have hf4 := hfit_i 4; have hf9 := hfit_i 9; have hf10 := hfit_i 10
  have hf11 := hfit_i 11; have hf12 := hfit_i 12; have hf13 := hfit_i 13; have hf14 := hfit_i 14
  simp only [d, mkClusterInput, Matrix.cons_val] at hf3 hf4 hf9 hf10 hf11 hf12 hf13 hf14
  refine ⟨?_, rfl, by simp +decide [x₁, loadClusterInputData, h0],
    by simp +decide [x₁, loadClusterInputData, hfr], ?_⟩
  · unfold loadClusterInputCode
    wram_exec [h2, h3, h247]
    refine WP.Exact.of_exec (loadOffCode_exec (d := 15) (by decide)
      (by rw [base_add_fullOff]; exact hfit_i 5) (by wram_simp [h0])) ?_
    wram_exec
    refine WP.Exact.of_exec (loadOffCode_exec (d := 16) (by decide)
      (by rw [base_add_occOff]; exact hfit_i 6) (by wram_simp [h0])) ?_
    wram_exec
    refine WP.Exact.of_exec (loadOffCode_exec (d := 17) (by decide)
      (by rw [base_add_runOff]; exact hfit_i 7) (by wram_simp [h0])) ?_
    wram_exec
    refine WP.Exact.of_exec (loadOffCode_exec (d := 18) (by decide)
      (by rw [base_add_remOff]; exact hfit_i 8) (by wram_simp [h0])) ?_
    wram_exec
    simp only [x₁, loadClusterInputData, mkClusterInput, base_add_fullOff, base_add_occOff,
      base_add_runOff, base_add_remOff]
    rfl
  funext i
  change x₁.regs (clusterSrcRegs i) = d i
  fin_cases i <;> simp +decide [x₁, loadClusterInputData, clusterSrcRegs, d, mkClusterInput]

/-- Output and scratch register map `Fin (1 + scratchSize + 1) → Fin rQF` for `clusterOpProg`:
coordinate `0` is `qfReg 1` (the operation output register), and coordinates `j > 0` are
`248 + (j - 1)`. -/
@[expose] noncomputable def clusterTmpRegs
    (j : Fin (WordEncoding.width ℕ + realizes_clusterOp.scratchSize + 1)) : Fin rQF :=
  if j.val = 0 then qfReg 1
  else ⟨248 + (j.val - 1), by
    have hj : j.val < 1 + realizes_clusterOp.scratchSize + 1 := j.isLt
    dsimp only [rQF]
    omega⟩

@[simp]
private theorem val_clusterTmpRegs
    (j : Fin (WordEncoding.width ℕ + realizes_clusterOp.scratchSize + 1)) :
    (clusterTmpRegs j).val = if j.val = 0 then 1 else 248 + (j.val - 1) := by
  dsimp only [clusterTmpRegs]
  split_ifs <;> rfl

private theorem injective_clusterTmpRegs : Function.Injective clusterTmpRegs := by
  fin_index [val_clusterTmpRegs]

private theorem clusterSrcRegs_ne_clusterTmpRegs (i : Fin (WordEncoding.width ClusterInput))
    (j : Fin (WordEncoding.width ℕ + realizes_clusterOp.scratchSize + 1)) :
    clusterSrcRegs i ≠ clusterTmpRegs j := by
  have hi : i.val < 15 := i.isLt
  fin_index [clusterSrcRegs, val_clusterTmpRegs, val_qfReg]

private theorem clusterTmpRegs_ne_qfReg {k : Fin 248} (hk : k.val ≠ 1)
    (j : Fin (WordEncoding.width ℕ + realizes_clusterOp.scratchSize + 1)) :
    clusterTmpRegs j ≠ qfReg k := by
  fin_index [val_clusterTmpRegs, val_qfReg]

private theorem clusterSrcRegs_ne_frontier (i : Fin (WordEncoding.width ClusterInput)) :
    clusterSrcRegs i ≠ qfReg 240 := by
  have hi : i.val < 15 := i.isLt
  fin_index [clusterSrcRegs, val_qfReg]

/-- Combined Word-RAM code loading `mkClusterInput` into registers `qfReg 10 .. qfReg 24` and
running the realized `clusterOpProg` code with frontier `qfReg 240` and output in `qfReg 1`. -/
@[expose] noncomputable def clusterCode (w w₀ n k : ℕ) : Code .exact rQF :=
  .seq (loadClusterInputCode w w₀ n k)
    (realizes_clusterOp.code (qfReg 240) clusterSrcRegs clusterTmpRegs)

/-- Exchange factor of the realized cluster `Memory.Prog` program. -/
@[expose] noncomputable def clusterFactor : ℕ :=
  realizes_clusterOp.factor

theorem clusterCode_execWithin {U base w w₀ n k : ℕ}
    (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k))
    {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ quotBits w₀ n)} {rem : Fin U → Fin (2 ^ remBits w₀ k)}
    (u : Fin U) {opTag : ℕ} (hop : opTag < 4)
    {x : Data rQF}
    (hx : x.Bounded w)
    (h0 : x.regs (qfReg 0) = base)
    (hfr : x.regs (qfReg 240) = base + space w w₀ n k)
    (h2 : x.regs (qfReg 2) = (quot u).val)
    (h3 : x.regs (qfReg 3) = (rem u).val)
    (h247 : x.regs (qfReg 247) = opTag)
    (hinv : FilterInv n S quot rem (extractFilterState base w w₀ n k x.mem))
    (hS_lt : #S < 2 ^ quotBits w₀ n) :
    let d := mkClusterInput base w w₀ n k (quot u) (rem u) opTag
    let s₀ : Memory.State := ⟨x.mem, base + space w w₀ n k⟩
    ∃ y : Data rQF,
      ExecWithin w (clusterCode w w₀ n k) x y
        (19 + clusterFactor * (11 * hinv.clusterLen hS_lt (quot u) + 14)) ∧
      y.Bounded w ∧
      y.regs (qfReg 0) = base ∧
      y.regs (qfReg 240) = ((Memory.spec 0).clientState s₀ (clusterOpProg d)).frontier ∧
      y.regs (qfReg 1) = (Memory.spec 0).clientResult s₀ (clusterOpProg d) ∧
      y.mem = ((Memory.spec 0).clientState s₀ (clusterOpProg d)).mem := by
  intro d s₀
  obtain ⟨he₁, hx₁_mem, hx₁_0, hx₁_fr, hx₁_src⟩ :=
    loadClusterInputCode_exec hw₀_pos hw hfit_space (quot u) (rem u) hop h0 h2 h3 h247 hfr
  set x₁ := loadClusterInputData base w w₀ n k (quot u) (rem u) opTag x
  have hms_eq : memoryState (qfReg 240) x₁ = s₀ := by
    dsimp only [memoryState, s₀]; rw [hx₁_mem, hx₁_fr]
  have hsafe := clusterSafe_mkClusterInput hw₀_pos hw hfit_space (quot u) (rem u) hop
  have hmemsafe := clusterMemSafe_mkClusterInput (wellFormed_memoryState (he₁.within.bounded hx))
    (by rw [hms_eq]) (quot u) (rem u) opTag
  obtain ⟨y, hy_exec, hy_ms, hy_out, hy_frame⟩ :=
    (realizes_clusterOp.code_spec (qfReg 240) clusterSrcRegs clusterTmpRegs
      injective_clusterTmpRegs clusterSrcRegs_ne_clusterTmpRegs
      (clusterTmpRegs_ne_qfReg (k := 240) (by decide)) clusterSrcRegs_ne_frontier).2
      w d x₁ (he₁.within.bounded hx) hx₁_src hsafe (validHistory_clusterOp hsafe hmemsafe)
  rw [hms_eq, clientState_width w (clusterOpProg d) s₀] at hy_ms
  have hcost_le :
      realizes_clusterOp.factor *
        (memoryCost (clusterOpProg d) (memoryState (qfReg 240) x₁) + 0 + 1) ≤
      clusterFactor * (11 * hinv.clusterLen hS_lt (quot u) + 14) := by
    rw [hms_eq]; apply Nat.mul_le_mul_left
    have hmc := memoryCost_clusterOp_le d s₀
    have hfc := clientResult_findCluster_mk base w w₀ n k (quot u) (rem u) opTag s₀ hinv hS_lt
    rw [show (Memory.spec 0).clientResult s₀ (findClusterProg d) = _ from hfc] at hmc
    dsimp only at hmc; omega
  exact ⟨y, he₁.within.seq (hy_exec.mono hcost_le), hy_exec.bounded (he₁.within.bounded hx),
    by rw [hy_frame (qfReg 0) (by decide) (clusterTmpRegs_ne_qfReg (k := 0) (by decide)), hx₁_0],
    congrArg Memory.State.frontier hy_ms,
    by have h := hy_out 0; rw [hms_eq, clientResult_width w (clusterOpProg d) s₀] at h; exact h,
    congrArg Memory.State.mem hy_ms⟩

end Cslib.DataStructure.ApproximateMembership.QuotientFilter
