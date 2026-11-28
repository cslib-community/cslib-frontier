/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.RadixSort.Model
public import CslibFrontier.Computability.WordRAM.ListArray
import CslibFrontier.Computability.WordRAM.MemoryView

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# Native stable digit-selection scan

The scan appends a stable digit-selected subsequence to a disjoint destination array. Both
orders of the two disjoint blocks are allowed, so consecutive radix passes can swap pointers.
All loads, address calculations, stores and loop control are native instructions.

## Main definitions

* `Scan.body`: read, test, conditionally append, and advance.
* `Scan.code`: reset the input cursor and scan the array.

## Main results

* `Scan.exec`: stable selection with a linear instruction bound and memory frame.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.RadixSort

open Cslib.WordRAM

/-- Array length. -/
abbrev len : Fin 16 := 0
/-- Source pointer; the sorter returns the final sorted pointer here. -/
abbrev src : Fin 16 := 1
/-- Scratch pointer. -/
abbrev dst : Fin 16 := 2
/-- Current bit index. -/
abbrev bit : Fin 16 := 3
/-- Digit selected by the current scan. -/
abbrev tag : Fin 16 := 4
/-- Constant one. -/
abbrev one : Fin 16 := 5
/-- Constant two. -/
abbrev two : Fin 16 := 6
/-- Input cursor. -/
abbrev idx : Fin 16 := 7
/-- Output cursor. -/
abbrev out : Fin 16 := 8
/-- Address temporary. -/
abbrev addr : Fin 16 := 9
/-- Loaded key. -/
abbrev value : Fin 16 := 10
/-- Current key digit. -/
abbrev keyDigit : Fin 16 := 11
/-- Number of key bits, supplied by the caller. -/
abbrev bits : Fin 16 := 12
/-- Temporary used to swap the two pointers. -/
abbrev swap : Fin 16 := 13

namespace Scan

/-- One stable-selection iteration, with every address and counter operation charged. -/
def body : Code .standard 16 := ram[
  addr ← src + idx; value ← *addr;
  keyDigit ← value >>> bit; keyDigit ← keyDigit % two;
  if keyDigit = tag then [ addr ← dst + out; *addr ← value; out ← out + one ]
    else [ addr ← addr ];
  idx ← idx + one ]

/-- Reset the input cursor, then perform one stable-selection scan. -/
def code : Code .standard 16 := ram[ idx ← #0; while idx < len do [ ⟪body⟫ ] ]

/-- Append a stable digit-selected subsequence in `11n+3` instructions. The destination has
capacity `n`; source and destination blocks are disjoint, in either order. The caller's existing
destination prefix is retained. Only destination cells may change. -/
theorem exec {w s d b t : ℕ} (xs acc : List ℕ) (x : Data 16)
    (hn : x.regs len = xs.length) (hs : x.regs src = s) (hd : x.regs dst = d)
    (hb : x.regs bit = b) (ht : x.regs tag = t)
    (ho : x.regs one = 1) (h2 : x.regs two = 2) (hout : x.regs out = acc.length)
    (hsrc : Block.HoldsList s xs x.mem) (hacc : Block.HoldsList d acc x.mem)
    (hwords : ∀ v ∈ xs, Fits w v)
    (hcap : (acc ++ select b t xs).length ≤ xs.length)
    (hdisj : s + xs.length ≤ d ∨ d + xs.length ≤ s)
    (hsfit : Fits w (s + xs.length)) (hdfit : Fits w (d + xs.length)) :
    ∃ y, ExecWithin w code x y (11 * xs.length + 3) ∧
      Block.HoldsList d (acc ++ select b t xs) y.mem ∧
      Block.HoldsList s xs y.mem ∧
      y.regs out = (acc ++ select b t xs).length ∧
      Modifies (Block.mk d xs.length).footprint x.mem y.mem := by
  let selected (i : ℕ) := acc ++ select b t (xs.take i)
  have hselected (i : ℕ) : (selected i).length ≤ xs.length := by
    have hsub : (select b t (xs.take i)).Sublist (select b t xs) :=
      (List.take_sublist i xs).filter _
    simp only [selected, List.length_append] at hcap ⊢
    have := hsub.length_le
    omega
  let P (j : ℕ) (y : Data 16) : Prop :=
    (∀ j : Fin 16, j.val ≤ 6 → y.regs j = x.regs j) ∧
    y.regs out = (selected j).length ∧
    Block.HoldsList s xs y.mem ∧ Block.HoldsList d (selected j) y.mem ∧
    Modifies (Block.mk d xs.length).footprint x.mem y.mem
  have hbody (y : Data 16) (hy : P (y.regs idx) y) (hi : y.regs idx < xs.length) :
      ∃ z, ExecWithin w body y z 9 ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, hu, hm, ha, hf⟩ := hy
    have hread : y.mem (s + y.regs idx) = xs[y.regs idx] := hm.get _ hi
    have hv : Fits w xs[y.regs idx] := hwords _ (List.getElem_mem hi)
    have hshift : Fits w (xs[y.regs idx] >>> b) := hv.of_le (Nat.shiftRight_le _ _)
    have hmod : Fits w ((xs[y.regs idx] >>> b) % 2) := hshift.of_le (Nat.mod_le _ _)
    have hcur := hselected (y.regs idx)
    have hsuc : selected (y.regs idx + 1) = selected (y.regs idx) ++
        (if digit b xs[y.regs idx] = t then [xs[y.regs idx]] else []) := by
      dsimp only [selected]
      rw [List.take_succ_eq_append_getElem hi, select_append]
      simp only [select, List.filter_cons, List.filter_nil, decide_eq_true_eq]
      split_ifs <;> simp only [List.append_assoc, List.append_nil]
    have hjne (j : Fin 16) (hj : j.val ≤ 6) :
        j ≠ idx ∧ j ≠ out ∧ j ≠ addr ∧ j ≠ value ∧ j ≠ keyDigit := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> exact absurd hj (by decide)
    apply WP.exists_execWithin
    unfold body
    by_cases heq : digit b xs[y.regs idx] = t
    · have hlt : (selected (y.regs idx)).length < xs.length := by
        have hlim := hselected (y.regs idx + 1)
        rw [hsuc, ite_eq_left heq, List.length_append, List.length_singleton] at hlim
        omega
      have hdig : (xs[y.regs idx] >>> b) % 2 = t := (digit_eq_shift _ _).symm.trans heq
      wram_exec * [hread]
      wram_simp * [P, hsuc, heq, List.length_append, List.length_singleton]
      refine ⟨fun j hj => ?_, ?_, ha.append_one _, ?_⟩
      · obtain ⟨_, _, _, _, _⟩ := hjne j hj
        wram_simp; exact hr j hj
      · rcases hdisj with h | h <;> ram_keep hm
      · intro a hnot
        have hne : a ≠ d + (selected (y.regs idx)).length := fun heqa =>
          hnot (Block.mem_footprint.mpr (by dsimp only [Block.Owns]; omega))
        exact (Function.update_of_ne hne ..).trans (hf a hnot)
    · have hdig : (xs[y.regs idx] >>> b) % 2 ≠ t := by rwa [← digit_eq_shift]
      wram_exec * [hread]
      wram_simp * [P, hsuc, heq, List.append_nil]
      refine ⟨fun j hj => ?_, hm, ha, hf⟩
      obtain ⟨_, _, _, _, _⟩ := hjne j hj
      wram_simp; exact hr j hj
  let x₀ := x.set idx 0
  have hx₀ : P (x₀.regs idx) x₀ := by
    refine ⟨fun j hj => Function.update_of_ne (Fin.ne_of_val_ne (by change j.val ≠ 7; omega)) _ _,
      ?_, hsrc, ?_, Modifies.refl _ _⟩
    · simpa +decide [x₀, selected, select] using hout
    · simpa [x₀, selected, select] using hacc
  obtain ⟨y, he, ⟨hr, hu, hm, ha, hf⟩, _⟩ := ExecWithin.loop_count P
    (fun y hy => (hy.1 len (by decide)).trans hn) hbody (by simp [x₀]) hx₀
  have hi := (ExecWithin.const (d := idx) (x := x) (fits_zero w)).seq he
  refine ⟨y, hi.mono (by simp [x₀]; omega), ?_, hm, ?_, hf⟩
  · simpa only [selected, List.take_length] using ha
  · simpa only [selected, List.take_length] using hu

end Scan
end Cslib.Algorithms.WordRAM.RadixSort
