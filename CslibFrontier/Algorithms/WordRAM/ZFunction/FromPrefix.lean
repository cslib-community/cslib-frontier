/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.ZFunction.FromPrefix
public import CslibFrontier.Algorithms.WordRAM.ZFunction
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.InputArray
import CslibFrontier.Computability.WordRAM.SymbolicExec
import Mathlib.Data.List.GetD

/-!
# Converting a prefix table into a Z-table on the word RAM

The program overwrites its input table with the canonical representative word, scanning left to
right. At position `i`, an entry `k` with `0 < k ≤ i` copies the representative at position
`k - 1`. Every other entry assigns the fresh symbol `i`. This pointed read uses address `k`
directly because the representative word starts at address one. Clearing the scan's registers
restores the full initial-state layout for the certified Z-algorithm.

The program takes at most `50 * n + 19` instructions, including halt, at any width fitting
`2 * n + 1` and the input entries. Its length-prefixed Z-table starts at address `n + 1`.
For an actual KMP prefix table, `fromPrefix_computePrefix` identifies the output with the Z-table
of the original word.
-/

public section

namespace Cslib.Algorithms.WordRAM.ZFunction

open Cslib.WordRAM
open Cslib.Algorithms.Lean.ZFunction

private abbrev zeroR : Fin 16 := 0
private abbrev oneR : Fin 16 := 1
private abbrev lengthR : Fin 16 := 2
private abbrev indexR : Fin 16 := 3
private abbrev addressR : Fin 16 := 4
private abbrev entryR : Fin 16 := 5

private def scanSetup : Code .standard 16 := ram[
  oneR ← #1;
  lengthR ← *zeroR ]

private def scanBody : Code .standard 16 := ram[
  addressR ← indexR + oneR;
  entryR ← *addressR;
  if entryR = zeroR then [
    entryR ← indexR
  ] else [
    if indexR < entryR then [entryR ← indexR] else [entryR ← *entryR]
  ];
  *addressR ← entryR;
  indexR ← indexR + oneR ]

private def clearScan : Code .standard 16 := ram[
  oneR ← zeroR;
  lengthR ← zeroR;
  indexR ← zeroR;
  addressR ← zeroR;
  entryR ← zeroR ]

private def scanCode : Code .standard 16 :=
  .seq (.seq scanSetup (.loop (.lt indexR lengthR) scanBody)) clearScan

/-- Convert the input prefix table in place to a representative word and run the Z-algorithm. -/
def fromPrefixCode : Code .standard 16 := .seq scanCode zCode

/-- Prefix-table to Z-table conversion with the result pointer returned in `Reg.out`. -/
def fromPrefixProgram : Program .standard 16 := fromPrefixCode.program Reg.out

private structure ScanState (pi : Array ℕ) (i : ℕ) (s : Data 16) : Prop where
  zero_eq : s.regs zeroR = 0
  one_eq : s.regs oneR = 1
  length_eq : s.regs lengthR = pi.size
  prefix_eq : ∀ j < i, s.mem (1 + j) = (prefixWord pi).toList.getD j 0
  frame : ∀ a, ¬(1 ≤ a ∧ a < 1 + i) → s.mem a = (Data.init pi.toList : Data 16).mem a

private theorem scanBody_exec {w : ℕ} (pi : Array ℕ) (hw : Fits w (2 * pi.size + 1))
    (s : Data 16) (hs : ScanState pi (s.regs indexR) s) (hlt : s.regs indexR < pi.size) :
    ∃ z, ExecWithin w scanBody s z 9 ∧ ScanState pi (s.regs indexR + 1) z ∧
      z.regs indexR = s.regs indexR + 1 := by
  let i := s.regs indexR
  let k := pi[i]
  have haddr : Fits w (i + 1) := hw.of_le (by omega)
  have hread : s.mem (s.regs indexR + 1) = k := by
    rw [hs.frame _ (by omega), Data.init_mem_succ,
      List.getD_eq_getElem _ 0 (by simpa using hlt)]
    rfl
  have hv : (prefixWord pi).toList.getD i 0 =
      if 0 < k ∧ k ≤ i then (prefixWord pi).toList.getD (k - 1) 0 else i := by
    have hword := getElem_prefixWord pi i hlt
    rw [List.getD_eq_getElem _ 0 (by simpa using hlt)]
    split <;> rename_i h
    · rw [List.getD_eq_getElem _ 0 (by simp only [Array.length_toList, size_prefixWord]; omega)]
      simpa only [Array.getElem_toList, k, h, true_and, ↓reduceDIte] using hword
    · simpa only [Array.getElem_toList, k, h, true_and, ↓reduceDIte] using hword
  have hstep : ∃ z, ExecWithin w scanBody s z 9 ∧ z.regs indexR = i + 1 ∧
      z.mem = Function.update s.mem (i + 1) ((prefixWord pi).toList.getD i 0) := by
    refine WP.exists_execWithin ?_
    unfold scanBody
    by_cases hcopy : 0 < k ∧ k ≤ i
    · have hprev : s.mem k = (prefixWord pi).toList.getD (k - 1) 0 := by
        simpa only [show 1 + (k - 1) = k by omega] using hs.prefix_eq (k - 1) (by omega)
      rw [ite_eq_left hcopy] at hv
      wram_exec [hs.one_eq, hs.zero_eq, hread, haddr, hprev,
        show k ≠ 0 by omega, show ¬i < k by omega]
      exact ⟨by wram_simp [i], by wram_simp [i, hv, hread, hprev]⟩
    · rw [ite_eq_right hcopy] at hv
      have hlarge : k ≠ 0 → i < k := by omega
      by_cases hz : k = 0 <;> wram_exec [hs.one_eq, hs.zero_eq, hread, haddr, hz, hlarge] <;>
        exact ⟨by wram_simp [i], by wram_simp [i, hv]⟩
  obtain ⟨z, hexec, hindex, hmem⟩ := hstep
  rw [Nat.add_comm i 1] at hmem
  obtain ⟨hprefix, hframe⟩ := prefix_write_step hs.prefix_eq hs.frame hmem
  exact ⟨z, hexec, ⟨(hexec.regs_eq (by decide)).trans hs.zero_eq,
    (hexec.regs_eq (by decide)).trans hs.one_eq,
    (hexec.regs_eq (by decide)).trans hs.length_eq, hprefix, hframe⟩, hindex⟩

private theorem scanCode_exec {w : ℕ} (pi : Array ℕ) (hw : Fits w (2 * pi.size + 1)) :
    ExecWithin w scanCode (Data.init pi.toList) (Data.init (prefixWord pi).toList)
      (11 * pi.size + 9) := by
  have hf : Fits w 1 := hw.of_le (by omega)
  have hsetup : ∃ x, ExecWithin w scanSetup (Data.init pi.toList) x 2 ∧
      x.regs indexR = 0 ∧ ScanState pi 0 x := by
    refine WP.exists_execWithin ?_
    unfold scanSetup
    wram_exec [Data.init_regs, Data.init_mem_zero, hf]
    exact ⟨by wram_simp [Data.init_regs], ⟨by wram_simp [Data.init_regs], by wram_simp,
      by wram_simp [Array.length_toList], fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ => rfl⟩⟩
  obtain ⟨x, hsetup, hi, hs⟩ := hsetup
  obtain ⟨y, hloop, hy, _⟩ := ExecWithin.loop_count (ScanState pi) (fun _ h => h.length_eq)
    (scanBody_exec pi hw) (by rw [hi]; omega) (hi ▸ hs)
  rw [hi] at hloop
  have hscan := hsetup.seq hloop
  have hm : y.mem = (Data.init (prefixWord pi).toList : Data 16).mem := by
    funext a
    cases a with
    | zero => rw [hy.frame 0 (by omega), Data.init_mem_zero, Data.init_mem_zero]; simp
    | succ j =>
      by_cases hj : j < pi.size
      · rw [Data.init_mem_succ, Nat.add_comm j 1, hy.prefix_eq j hj]
      · rw [hy.frame _ (by omega),
          Data.init_mem_of_length_lt (by simp only [Array.length_toList]; omega),
          Data.init_mem_of_length_lt (by simp only [Array.length_toList, size_prefixWord]; omega)]
  have hrest (r : Fin 16) (hr : 5 < r.val) : y.regs r = 0 := by
    have hpres : ∀ q : Fin 16, 5 < q.val →
        (Code.seq scanSetup (.loop (.lt indexR lengthR) scanBody)).Preserves q := by decide
    exact (hscan.regs_eq (hpres r hr)).trans (Data.init_regs _ _)
  have hclear : ∃ z, ExecWithin w clearScan y z 5 ∧ z = Data.init (prefixWord pi).toList := by
    refine WP.exists_execWithin ?_
    unfold clearScan
    wram_exec [hy.zero_eq]
    apply Data.ext
    · funext r
      fin_cases r <;> wram_simp [Data.init_regs, hrest]
      exact hy.zero_eq
    · exact hm
  obtain ⟨_, hclear, rfl⟩ := hclear
  exact (hscan.seq hclear).mono (by omega)

/-- On an array of `n` prefix lengths, the program writes the length-prefixed Z-table at
address `n + 1`, leaving the representative word in the input block. The bound charges both
the in-place conversion and the Z-algorithm. -/
theorem fromPrefixCode_exec {w : ℕ} (pi : Array ℕ) (hw : Fits w (2 * pi.size + 1)) :
    ∃ y, ExecWithin w fromPrefixCode (Data.init pi.toList) y (50 * pi.size + 18) ∧
      outputList y.mem (y.regs Reg.out) = (fromPrefix pi).toList ∧
      y.regs Reg.out = pi.size + 1 ∧ Fits w (y.regs Reg.out + (fromPrefix pi).size) ∧
      Block.HoldsList 1 (prefixWord pi).toList y.mem := by
  obtain ⟨y, hz, hout, hbase, hf, hword⟩ :=
    zCode_exec (prefixWord pi).toList (by simpa using hw)
  have hresult : (fromPrefix pi).toList = zFunction (prefixWord pi).toList :=
    zArray_toList (prefixWord pi)
  refine ⟨y, ((scanCode_exec pi hw).seq hz).mono ?_, hout.trans hresult.symm,
    by simpa using hbase, ?_, hword⟩
  · simp only [Array.length_toList, size_prefixWord]
    omega
  · simpa only [← hresult, Array.length_toList] using hf

/-- The uniform 16-register word-RAM program converts a length-prefixed prefix table of size
`n` within `50 * n + 19` instructions, including halt, when the width fits `2 * n + 1`
and the input words. -/
theorem fromPrefixProgram_computesListInTime :
    fromPrefixProgram.ComputesListInTime (fun _ (pi : Array ℕ) => pi.toList)
      (fun pi _ => 50 * pi.size + 19) (fun pi w => Fits w (2 * pi.size + 1))
      (fun pi => (fromPrefix pi).toList) :=
  fromPrefixCode.computesListInTime_program Reg.out fun pi _ hw _ => by
    obtain ⟨y, hexec, hout, _, hf, _⟩ := fromPrefixCode_exec pi hw
    exact ⟨y, hexec, hout, by simpa only [Array.length_toList] using hf⟩

end Cslib.Algorithms.WordRAM.ZFunction
