/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Basic
public import CslibFrontier.Computability.WordRAM.Signed.Arithmetic
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Internal register layout, domain buffer predicate, and signed arithmetic wrappers

Internal register indices across the `47` algorithm registers above the `9`-register
`WordRAM.Signed` bank, the interleaved `(mask, size)` domain buffer invariant `HoldsDom`, and
width-fit wrappers around `WordRAM.Signed` (`add`, `subtract`, `multiply`) at physical word width
`w`.

## Main definitions

* `Cslib.Algorithms.WordRAM.TrimmedYates.HoldsDom`: interleaved `(setMask, card)` domain array
  layout in flat word memory.

## Main results

* `Cslib.Algorithms.WordRAM.TrimmedYates.mask_fits_of_valueEnvelope`: `Fits w (valueEnvelope d W)`
  implies `Fits w (2 ^ d)`.
* `Cslib.Algorithms.WordRAM.TrimmedYates.exec_signedAdd`, `exec_signedSub`, `exec_signedMul`:
  physical-width `ExecWithin` wrappers for `WordRAM.Signed` preserving registers `9 .. 55`.
-/

public section

namespace Cslib.Algorithms.WordRAM.TrimmedYates

open Finset Cslib.WordRAM

/-! ### Internal scratch register bank -/

/-- Scratch register holding constant `0`. -/
abbrev rZero : Fin numRegs := ⟨9, by decide⟩
/-- Scratch register holding constant `1`. -/
abbrev rOne : Fin numRegs := ⟨10, by decide⟩
/-- Saved post-preprocessing bump-allocator high-water mark (`qWorkStart`). -/
abbrev rPreFree : Fin numRegs := ⟨14, by decide⟩

/-- Current trie root pointer for trie operations. -/
abbrev rTrieRoot : Fin numRegs := ⟨16, by decide⟩
/-- Bitmask key argument for trie lookup/insert/add. -/
abbrev rTrieKey : Fin numRegs := ⟨17, by decide⟩
/-- Encoded payload value read from or written to a trie leaf. -/
abbrev rTrieVal : Fin numRegs := ⟨18, by decide⟩
/-- Current trie node pointer while descending bits. -/
abbrev rTrieCur : Fin numRegs := ⟨19, by decide⟩
/-- Remaining trie depth counter during descent. -/
abbrev rTrieRem : Fin numRegs := ⟨20, by decide⟩
/-- Extracted low bit (`0` or `1`) during trie descent. -/
abbrev rTrieBit : Fin numRegs := ⟨21, by decide⟩
/-- Scratch register for trie node address arithmetic. -/
abbrev rTrieTmp : Fin numRegs := ⟨22, by decide⟩

/-- Base address of the active coordinate array. -/
abbrev rCoordsPtr : Fin numRegs := ⟨23, by decide⟩
/-- Length of the active coordinate array (`d` or `#C`). -/
abbrev rCoordsLen : Fin numRegs := ⟨24, by decide⟩
/-- Maximum subset cardinality bound for `genBounded`. -/
abbrev rMaxCard : Fin numRegs := ⟨25, by decide⟩
/-- Base address of the enumerated `(mask, size)` domain buffer. -/
abbrev rDomPtr : Fin numRegs := ⟨26, by decide⟩
/-- Current number of `(mask, size)` pairs in `rDomPtr`. -/
abbrev rDomLen : Fin numRegs := ⟨27, by decide⟩
/-- Outer coordinate loop index in subset enumeration and extraction. -/
abbrev rGenIdx : Fin numRegs := ⟨28, by decide⟩
/-- Inner domain scan index in `genBounded`. -/
abbrev rGenPos : Fin numRegs := ⟨29, by decide⟩
/-- Snapshot of `rDomLen` at the start of a `genBounded` coordinate pass. -/
abbrev rGenOldLen : Fin numRegs := ⟨30, by decide⟩
/-- Single-bit mask `1 <<< coord` for the active coordinate. -/
abbrev rGenBitMask : Fin numRegs := ⟨31, by decide⟩
/-- General-purpose address and arithmetic scratch register. -/
abbrev rGenTmp : Fin numRegs := ⟨32, by decide⟩

/-- Fallback cardinality cutoff (`0` in preprocessing, `s + 1` in high queries). -/
abbrev rStageCutoff : Fin numRegs := ⟨35, by decide⟩
/-- Yates pass sign selector (`0` for `+1` zeta, `1` for `-1` Möbius). -/
abbrev rSignMode : Fin numRegs := ⟨36, by decide⟩
/-- Output base address for an array of `d + 1` stage trie roots. -/
abbrev rRootsOut : Fin numRegs := ⟨37, by decide⟩
/-- Base address of preprocessed fallback stage trie roots. -/
abbrev rFbRoots : Fin numRegs := ⟨38, by decide⟩
/-- Current Yates coordinate stage index `k ∈ [0, d)`. -/
abbrev rStageIdx : Fin numRegs := ⟨39, by decide⟩
/-- Current domain cell index `p ∈ [0, L)` during tabulation. -/
abbrev rCellIdx : Fin numRegs := ⟨40, by decide⟩
/-- Trie root of stage `k` read by stage `k + 1` (or left factor in `tabulateMul`). -/
abbrev rStageCurRoot : Fin numRegs := ⟨41, by decide⟩
/-- Fallback trie root for stage `k` (or right factor in `tabulateMul`). -/
abbrev rStageFbRoot : Fin numRegs := ⟨42, by decide⟩

/-- Current query loop index `q ∈ [0, |Cs|)`. -/
abbrev rQueryIdx : Fin numRegs := ⟨48, by decide⟩
/-- Current cell bitmask `setMask Y` (or active query mask `setMask C`). -/
abbrev rCellKey : Fin numRegs := ⟨49, by decide⟩
/-- Current cell cardinality `#Y`. -/
abbrev rCellCard : Fin numRegs := ⟨50, by decide⟩
/-- Base address of the `d + 1` preprocessed `f`-stage trie roots. -/
abbrev rPreFsBase : Fin numRegs := ⟨51, by decide⟩
/-- Base address of the `d + 1` preprocessed `g`-stage trie roots. -/
abbrev rPreGsBase : Fin numRegs := ⟨52, by decide⟩
/-- Base address of the `d + 1` preprocessed `h`-stage trie roots. -/
abbrev rPreHsBase : Fin numRegs := ⟨53, by decide⟩
/-- Base address of the `d + 1` per-query high `f`-stage trie roots. -/
abbrev rQFsBase : Fin numRegs := ⟨54, by decide⟩
/-- Base address of the `d + 1` per-query high `g`-stage trie roots. -/
abbrev rQGsBase : Fin numRegs := ⟨55, by decide⟩

/-! ### Domain buffer layout and width envelope helper -/

/-- Interleaved `(mask, size)` domain layout at `base`: entry `p` stores `setMask xs[p]` at
`base + 2 * p` and `#xs[p]` at `base + 2 * p + 1`. -/
@[expose] def HoldsDom {d : ℕ} (mem : ℕ → ℕ) (base : ℕ) (xs : List (Finset (Fin d))) : Prop :=
  ∀ p (hp : p < xs.length),
    mem (base + 2 * p) = setMask xs[p] ∧ mem (base + 2 * p + 1) = #xs[p]

theorem mask_fits_of_valueEnvelope {w d W : ℕ} (h : Fits w (valueEnvelope d W)) :
    Fits w (2 ^ d) := by
  refine h.of_le ?_
  have hmul : 2 ^ d ≤ 8 ^ d * (W + 1) ^ 2 :=
    (Nat.pow_le_pow_left (by decide) d).trans
      (Nat.le_mul_of_pos_right _ (Nat.one_le_pow 2 (W + 1) (Nat.succ_pos W)))
  dsimp only [valueEnvelope]
  omega

/-! ### Signed integer wrappers at physical width `w` -/

private theorem width_ge_three_of_fits {w B : ℕ} (hfit : Fits w (8 * B + 4)) : 3 ≤ w := by
  by_contra h
  have hw : w = 0 ∨ w = 1 ∨ w = 2 := by omega
  rcases hw with rfl | rfl | rfl <;> { simp only [Fits] at hfit; omega }

private theorem signedFits_of_natAbs_le {w B : ℕ} (hfit : Fits w (8 * B + 4)) {z : ℤ}
    (hz : z.natAbs ≤ B) : GenericRAM.Signed.Fits (w - 2) z := by
  have hw3 := width_ge_three_of_fits hfit
  have hpow : 2 ^ w = 8 * 2 ^ (w - 3) := by
    conv_lhs => rw [show w = (w - 3) + 3 by omega, pow_add]
    ring
  have hB : B < 2 ^ ((w - 2) - 1) := by
    rw [show (w - 2) - 1 = w - 3 by omega]
    simp only [Fits] at hfit
    omega
  have hcast : ((2 ^ ((w - 2) - 1) : ℕ) : ℤ) = (2 : ℤ) ^ ((w - 2) - 1) := by norm_cast
  exact ⟨by omega, by omega, by omega⟩

theorem signedAdd_preserves (i : Fin numRegs) :
    9 ≤ i.val → (Signed.add (r := 47)).Preserves i := by
  decide +kernel +revert

theorem signedSub_preserves (i : Fin numRegs) :
    9 ≤ i.val → (Signed.subtract (r := 47)).Preserves i := by
  decide +kernel +revert

theorem signedMul_preserves (i : Fin numRegs) :
    9 ≤ i.val → (Signed.multiply (r := 47)).Preserves i := by
  decide +kernel +revert

theorem exec_signedAdd {w B : ℕ} {a b : ℤ} (hfit : Fits w (8 * B + 4))
    (ha : a.natAbs ≤ B) (hb : b.natAbs ≤ B) (x : Data numRegs)
    (hxa : x.regs (Signed.left (r := 47)) = Signed.encode a)
    (hxb : x.regs (Signed.right (r := 47)) = Signed.encode b) :
    ∃ y, ExecWithin w (Signed.add (r := 47)) x y 15 ∧
      y.regs (Signed.result (r := 47)) = Signed.encode (a + b) ∧
      y.mem = x.mem ∧ ∀ i : Fin numRegs, 9 ≤ i.val → y.regs i = x.regs i := by
  have hw3 := width_ge_three_of_fits hfit
  obtain ⟨y, he, hyr, hym, hyf⟩ := Signed.exec_add (r := 47)
    (signedFits_of_natAbs_le hfit ha) (signedFits_of_natAbs_le hfit hb) x hxa hxb
  rw [show (w - 2) + 2 = w by omega] at he
  exact ⟨y, he, hyr, hym, fun i hi => hyf i (Or.inr hi)⟩

theorem exec_signedSub {w B : ℕ} {a b : ℤ} (hfit : Fits w (8 * B + 4))
    (ha : a.natAbs ≤ B) (hb : b.natAbs ≤ B) (x : Data numRegs)
    (hxa : x.regs (Signed.left (r := 47)) = Signed.encode a)
    (hxb : x.regs (Signed.right (r := 47)) = Signed.encode b) :
    ∃ y, ExecWithin w (Signed.subtract (r := 47)) x y 17 ∧
      y.regs (Signed.result (r := 47)) = Signed.encode (a - b) ∧
      y.mem = x.mem ∧ ∀ i : Fin numRegs, 9 ≤ i.val → y.regs i = x.regs i := by
  have hw3 := width_ge_three_of_fits hfit
  obtain ⟨y, he, hyr, hym, hyf⟩ := Signed.exec_subtract (r := 47)
    (signedFits_of_natAbs_le hfit ha) (signedFits_of_natAbs_le hfit hb) x hxa hxb
  rw [show (w - 2) + 2 = w by omega] at he
  exact ⟨y, he, hyr, hym, fun i hi => hyf i (Or.inr hi)⟩

theorem exec_signedMul {w B : ℕ} {a b : ℤ} (hfit : Fits w (8 * B + 4))
    (ha : a.natAbs ≤ B) (hb : b.natAbs ≤ B) (hab : (a * b).natAbs ≤ B) (x : Data numRegs)
    (hxa : x.regs (Signed.left (r := 47)) = Signed.encode a)
    (hxb : x.regs (Signed.right (r := 47)) = Signed.encode b) :
    ∃ y, ExecWithin w (Signed.multiply (r := 47)) x y 14 ∧
      y.regs (Signed.result (r := 47)) = Signed.encode (a * b) ∧
      y.mem = x.mem ∧ ∀ i : Fin numRegs, 9 ≤ i.val → y.regs i = x.regs i := by
  have hw3 := width_ge_three_of_fits hfit
  obtain ⟨y, he, hyr, hym, hyf⟩ := Signed.exec_multiply (r := 47)
    (signedFits_of_natAbs_le hfit ha) (signedFits_of_natAbs_le hfit hb)
    (signedFits_of_natAbs_le hfit hab) x hxa hxb
  rw [show (w - 2) + 2 = w by omega] at he
  exact ⟨y, he, hyr, hym, fun i hi => hyf i (Or.inr hi)⟩

end Cslib.Algorithms.WordRAM.TrimmedYates
