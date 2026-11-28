/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.ZFunction.ToPrefix
public import CslibFrontier.Computability.WordRAM.ListOutput
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Converting Z-values to the KMP prefix table on the Word-RAM

The input is the length-prefixed Z-table alone. At prefix length `t`, the earliest start `j ≥ 1`
whose Z-box reaches `t` gives the longest proper border, of length `t - j`. A box that falls
short can be discarded for every later prefix. Each iteration either discards a start or writes
one answer. Both pointers move only to the right.

`toPrefixProgram_computesListInTime` counts the reads, writes, pointer updates, tests and final
halt on the standard Word-RAM. For `n` input words the output occupies addresses `n+1` through
`2n+1`, including its length header, and words must fit these addresses.
-/

public section

namespace Cslib.Algorithms.WordRAM.ZFunction

open Cslib.WordRAM
open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.ZFunction

private abbrev zero : Fin 8 := 0
private abbrev one : Fin 8 := 1
private abbrev target : Fin 8 := 2
private abbrev start : Fin 8 := 3
private abbrev output : Fin 8 := 4
private abbrev width : Fin 8 := 5
private abbrev addr : Fin 8 := 6
private abbrev value : Fin 8 := 7

private def setup : Code .standard 8 := ram[
  one ← #1;
  value ← *zero;
  output ← value + one;
  *output ← value;
  target ← one;
  start ← one ]

private def stepCode : Code .standard 8 := ram[
  width ← target - start;
  addr ← one + start;
  value ← *addr;
  if value < width then [
    start ← start + one
  ] else [
    addr ← output + target;
    *addr ← width;
    target ← target + one
  ] ]

private def convert : Code .standard 8 :=
  .seq setup (.loop (.lt target output) stepCode)

/-- Convert the length-prefixed Z-table at address zero into the length-prefixed KMP table
immediately following it. -/
def toPrefixProgram : Program .standard 8 := convert.program output

private structure Scan (z : Array ℕ) (t j : ℕ) (acc : Array ℕ) (x : Data 8) : Prop where
  one_eq : x.regs one = 1
  out_eq : x.regs output = z.size + 1
  target_eq : x.regs target = t
  start_eq : x.regs start = j
  input : Block.HoldsList 1 z.toList x.mem
  header : x.mem (z.size + 1) = z.size
  written : Block.HoldsList (z.size + 2) acc.toList x.mem

private theorem setup_spec {w : ℕ} (z : Array ℕ) (hw : Fits w (2 * z.size + 1)) :
    ∃ x, ExecWithin w setup (.init z.toList) x 6 ∧ Scan z 1 1 #[] x := by
  have h1 : Fits w 1 := hw.of_le (by omega)
  have hout : Fits w (z.size + 1) := hw.of_le (by omega)
  refine WP.exists_execWithin ?_
  wram_exec [setup, Data.init_regs, Data.init_mem_zero, Array.length_toList, h1, hout]
  refine ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, ?_,
    by wram_simp, Block.holdsList_nil _ _⟩
  exact (Block.holdsList_init (r := 8) z.toList).frame fun a _ ha => by
    simp only [Data.set_mem, Data.write_mem, Function.update_of_ne (show a ≠ z.size + 1 by
      simp only [Array.length_toList] at ha; omega)]

private theorem step_spec {w : ℕ} {z : Array ℕ} {t j : ℕ} {acc : Array ℕ} {x : Data 8}
    (hw : Fits w (2 * z.size + 1)) (ht : t ≤ z.size) (hj : j ≤ t) (hsize : acc.size + 1 = t)
    (h : Scan z t j acc x) :
    ∃ y, ExecWithin w stepCode x y 8 ∧
      if z.getD j 0 < t - j then Scan z t (j + 1) acc y
      else Scan z (t + 1) j (acc.push (t - j)) y := by
  have hcmp : x.mem (1 + j) < t - j ↔ z.getD j 0 < t - j := by
    by_cases hjn : j < z.size
    · rw [h.input.get j (by simpa using hjn), Array.getElem_toList,
        Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hjn, Option.getD_some]
    · have heq : t = j := by omega
      simp [heq]
  have haddr : Fits w (1 + j) := hw.of_le (by omega)
  have hwidth : Fits w (t - j) := hw.of_le (by omega)
  by_cases hskip : z.getD j 0 < t - j
  · simp only [ite_eq_left hskip]
    have htest := hcmp.mpr hskip
    have hincr : Fits w (j + 1) := hw.of_le (by omega)
    refine WP.exists_execWithin ?_
    wram_exec [stepCode, h.one_eq, h.start_eq, h.target_eq, haddr, hwidth, htest, hincr]
    exact ⟨by wram_simp [h.one_eq], by wram_simp [h.out_eq], by wram_simp [h.target_eq],
      by wram_simp, h.input, h.header, h.written⟩
  · simp only [ite_eq_right hskip]
    have htest : ¬x.mem (1 + j) < t - j := fun hh => hskip (hcmp.mp hh)
    have hout : Fits w (z.size + 1 + t) := hw.of_le (by omega)
    have hincr : Fits w (t + 1) := hw.of_le (by omega)
    refine WP.exists_execWithin ?_
    wram_exec [stepCode, h.one_eq, h.out_eq, h.start_eq, h.target_eq, haddr, hwidth, htest,
      hout, hincr]
    refine ⟨by wram_simp [h.one_eq], by wram_simp [h.out_eq], by wram_simp,
      by wram_simp [h.start_eq], ?_, ?_, ?_⟩
    · exact h.input.frame fun a _ ha => by
        simp only [Data.set_mem, Data.write_mem, Function.update_of_ne (show a ≠ z.size + 1 + t by
          simp only [Array.length_toList] at ha; omega)]
    · wram_simp [Function.update_of_ne (show z.size + 1 ≠ z.size + 1 + t by omega), h.header]
    · simpa only [Array.toList_push, Array.length_toList, Data.set_mem, Data.write_mem,
        show z.size + 2 + acc.size = z.size + 1 + t by omega] using h.written.append_one (t - j)

private def remaining (n t j : ℕ) : ℕ := 10 * ((n + 1 - t) + (n + 1 - j)) + 2

private theorem loop_spec {w : ℕ} (z : Array ℕ) (t j : ℕ) (acc : Array ℕ) (x : Data 8)
    (hw : Fits w (2 * z.size + 1)) (ht : t ≤ z.size + 1) (hj : j ≤ t)
    (hsize : acc.size + 1 = t) (h : Scan z t j acc x) :
    ∃ y, ExecWithin w (.loop (.lt target output) stepCode) x y (remaining z.size t j) ∧
      outputList y.mem (y.regs output) = (zToPrefixLoop z t j acc).toList ∧
      Fits w (y.regs output + (zToPrefixLoop z t j acc).size) := by
  by_cases hactive : t ≤ z.size
  · have hc : (Cond.lt target output).Holds x := by
      simp only [Cond.holds_lt, h.target_eq, h.out_eq]; omega
    obtain ⟨y, he, hy⟩ := step_spec hw hactive hj hsize h
    rw [zToPrefixLoop, ite_eq_left hactive]
    split_ifs at hy ⊢ with hskip
    · have hj' : j + 1 ≤ t := by omega
      obtain ⟨f, hf, hout, hfit⟩ := loop_spec z t (j + 1) acc y hw ht hj' hsize hy
      exact ⟨f, (ExecWithin.loop_iter hc he hf).mono (by unfold remaining; omega), hout, hfit⟩
    · obtain ⟨f, hf, hout, hfit⟩ := loop_spec z (t + 1) j (acc.push (t - j)) y
        hw (by omega) (by omega) (by rw [Array.size_push, hsize]) hy
      exact ⟨f, (ExecWithin.loop_iter hc he hf).mono (by unfold remaining; omega), hout, hfit⟩
  · rw [zToPrefixLoop, ite_eq_right hactive]
    have hc : ¬(Cond.lt target output).Holds x := by
      simp only [Cond.holds_lt, h.target_eq, h.out_eq]; omega
    refine ⟨x, (ExecWithin.loop_exit hc).mono (by unfold remaining; omega), ?_, ?_⟩
    · rw [h.out_eq, outputList_eq_iff]
      exact ⟨by rw [h.header, Array.length_toList]; omega, h.written⟩
    · rw [h.out_eq]
      exact hw.of_le (by omega)
termination_by (z.size + 1 - t) + (z.size + 1 - j)
decreasing_by all_goals omega

/-- From the Z-table alone, compute the prefix-table conversion in at most `20n + 9`
standard Word-RAM instructions, including the final halt, at any width fitting `2n + 1`.
On realizable input tables the result is KMP's prefix table by `zToPrefix_zArray`. -/
theorem toPrefixProgram_computesListInTime :
    toPrefixProgram.ComputesListInTime (fun _ (z : Array ℕ) => z.toList)
      (fun z _ => 20 * z.size + 9) (fun z w => Fits w (2 * z.size + 1))
      (fun z => (zToPrefix z).toList) := by
  apply convert.computesListInTime_program output
  intro z w hw _
  obtain ⟨x, hsetup, hx⟩ := setup_spec z hw
  obtain ⟨y, hloop, hout, hfit⟩ := loop_spec z 1 1 #[] x hw (by omega) (by omega) rfl hx
  refine ⟨y, (hsetup.seq hloop).mono (by unfold remaining; omega), hout, ?_⟩
  simpa only [Array.length_toList, zToPrefix] using hfit

/-- On the Z-table of any word, the program outputs that word's KMP table. Fitting the last
output address suffices for the width, since each input Z-value is at most the word length. -/
theorem toPrefixProgram_executes_zArray {α : Type*} [DecidableEq α] (p : Array α) {w : ℕ}
    (hw : Fits w (2 * p.size + 1)) :
    ∃ steps, ExecutesList w toPrefixProgram (.init (zArray p).toList)
      (KMP.computePrefix p).toList steps ∧ steps ≤ 20 * p.size + 9 := by
  have hn : Fits w p.size := hw.of_le (by omega)
  have hi : InputFits w (zArray p).toList := by
    refine ⟨by simpa using hn, fun v hv => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
    rw [Array.getElem_toList, getElem_zArray]
    exact hn.of_le (List.lcpLen_le_length_left _ _)
  simpa only [zToPrefix_zArray, size_zArray] using
    toPrefixProgram_computesListInTime (zArray p) w (by simpa using hw) hi

end Cslib.Algorithms.WordRAM.ZFunction
