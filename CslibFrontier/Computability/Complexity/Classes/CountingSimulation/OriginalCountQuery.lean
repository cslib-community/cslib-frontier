/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.PaddedCountBits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import CslibFrontier.Foundations.Data.Nat.SqrtLog

/-!
# Original accepting-count queries and the padded machine

The native terminal count has one fixed finite binary table and a constant clock expansion.
For a fair-coin table with an ordinary pathwise running-time bound, the queried padded index
is computable in polynomial time from the binary clock and binary original index.
-/

public section

namespace Cslib.Complexity.CountingSimulation

open _root_.Turing _root_.Turing.MultiTapeTM ComputableInPolyTime

/-- The request index offset by the unused fair-coin suffix. -/
@[expose] def originalCountBit (p : ℕ × ℕ) : ℕ := p.2 + (paddedTime p.1 - p.1)

/-- Reindexing a padded fair-coin count uses only binary arithmetic on the short challenge. -/
theorem computableInPolyTime_originalCountBit :
    ComputableInPolyTime originalCountBit (encPair encNat encNat) encNat := by
  have ht := fst encNat encNat
  have hb := binary_clog_two_nat.comp (binary_add' ht (const 2))
  have hq : ComputableInPolyTime (fun p : ℕ × ℕ => numBlocks p.1) (encPair encNat encNat)
      encNat := by
    have h := binary_div' (binary_sub' (binary_add' ht hb) (const 1)) hb
    simpa only [numBlocks, blockLength, Nat.ceilDiv_eq_add_pred_div, Function.comp_apply] using h
  exact binary_add' (snd encNat encNat) (binary_sub' (binary_mul' hq hb) ht)

/-- Every bit of the original count fits after the fair-coin offset. -/
theorem originalCountBit_lt (t : ℕ) (bit : Fin (t + 1)) :
    originalCountBit (t, bit.val) < paddedTime t + 1 := by
  have := le_paddedTime t
  have := bit.isLt
  dsimp [originalCountBit]
  omega

/-- Under the ordinary machine running-time bound the selected physical bit is the original
bit. The condition is the native NTM pathwise running time of the two-action transition table. -/
theorem originalCountBit_eq_of_runsInTime {k : ℕ} {S : Type} (M : MultiTapePTM k Bool S)
    (x : List Bool) (t bit : ℕ) (ht : M.toNTM.RunsInTime x t) :
    (M.acceptCount x (paddedTime t)).testBit (originalCountBit (t, bit)) =
      (M.acceptCount x t).testBit bit := by
  let atm : MultiTapeATM k Bool S := ⟨M, fun _ => false⟩
  exact padded_acceptCount_testBit M x t bit ((atm.runsInTime_iff_stepCoins).1 ht)

/-- Encoding each transition occurrence with a fixed positive width preserves the time scale. -/
theorem width_clock_le (t width : ℕ) (hw : 0 < width) :
    t * width / (Nat.log 2 (t * width + 2)).sqrt + 2 ≤
      width * (t / (Nat.log 2 (t + 2)).sqrt + 2) := by
  by_cases hw₁ : width = 1
  · simp [hw₁]
  have hpos : 0 < (Nat.log 2 (t + 2)).sqrt :=
    Nat.sqrt_pos.mpr (Nat.log_pos one_lt_two (by omega))
  have hle := Nat.le_mul_of_pos_right t hw
  have hd : (Nat.log 2 (t + 2)).sqrt ≤ (Nat.log 2 (t * width + 2)).sqrt :=
    Nat.sqrt_le_sqrt (Nat.log_mono_right (by omega))
  have h := (Nat.div_le_div_left (a := t * width) hd hpos).trans
    (by simpa only [Nat.mul_comm t width] using
      Nat.mul_div_le_mul_div_add width t ((Nat.log 2 (t + 2)).sqrt))
  rw [Nat.mul_add]
  omega

/-- One binary fair-coin table and numbering realize every specified bit of the original
occurrence-labelled CTM count. The finite table is chosen before the input and clock. -/
theorem exists_original_count_table {k : ℕ} {S : Type} [Finite S] (M : MultiTapeCTM k Bool S) :
    ∃ (width states : ℕ) (Q : Type) (_ : Finite Q) (table : MultiTapePTM k Bool Q)
      (_ : Q ≃ Fin states), 0 < width ∧
      ∀ (input : List Bool) (t bit : ℕ), M.HaltsWithin t (Cfg.init M.initial input) →
        (table.acceptCount input (paddedTime (t * width))).testBit bit =
          (M.acceptCount t (Cfg.init M.initial input)).testBit bit := by
  classical
  obtain ⟨width, hw, hbound⟩ := M.exists_branchWidth
  let Q := MultiTapeCTM.CountingChoice.ScanState width S
  let := Fintype.ofFinite Q
  exact ⟨width, Fintype.card Q, Q, inferInstance, MultiTapeCTM.CountingChoice.table hw M,
    Fintype.equivFin Q, hw, fun x t b ht => padded_terminalCount_testBit hw M x t b (hbound x) ht⟩

end Cslib.Complexity.CountingSimulation
