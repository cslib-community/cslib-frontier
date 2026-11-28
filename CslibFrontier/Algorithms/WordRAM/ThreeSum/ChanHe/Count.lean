/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.Collisions
public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.Residues
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import CslibFrontier.Computability.WordRAM.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.CanonicalCall
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# Native Chan–He collision counting

This fixed native program first decodes signed Euclidean residue keys, then builds a
histogram and counts ordered collisions. Register setup between the two loops is charged.
For injective input arrays its counter is exactly the existing Chan–He `coll`.

## Main definitions

* `Count.program`: the composed native residue/histogram program.
* `Count.memory`: the complete output memory, including the residue scratch array.

## Main results

* `Count.exec`: execution in at most `34n + 5M + 18` native instructions.
* `Count.exec_coll`: the counter equals the existing mathematical collision count.
* `Count.memory_before`: cells below the two workspace blocks retain their contents.

## References

* [T. M. Chan and Q. He, *Reducing 3SUM to Convolution-3SUM*][ChanHe2020]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Count

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Residue routine registers occupy the first sixteen registers. -/
def residuesRegisters (i : Fin 16) : Fin 28 := ⟨i.val, by omega⟩

/-- Histogram registers occupy registers sixteen through twenty-six. -/
def histogramRegisters (i : Fin 11) : Fin 28 := ⟨16 + i.val, by omega⟩

private theorem residues_injective : Function.Injective residuesRegisters :=
  fun _ _ h => Fin.ext (congrArg (Fin.val : Fin 28 → ℕ) h)

private theorem histogram_injective : Function.Injective histogramRegisters :=
  fun _ _ h => Fin.ext (Nat.add_left_cancel (congrArg (Fin.val : Fin 28 → ℕ) h))

/-- Encoded integer input base. -/
abbrev src : Fin 28 := 9
/-- Residue scratch base. -/
abbrev scratch : Fin 28 := 10
/-- Number of input values. -/
abbrev len : Fin 28 := 11
/-- Encoded positive modulus. -/
abbrev modulus : Fin 28 := 12
/-- Histogram destination base. -/
abbrev dst : Fin 28 := 27
/-- Output collision count, an ordinary unsigned word. -/
abbrev total : Fin 28 := 24

/-- Histogram input base register. -/
abbrev hsrc : Fin 28 := histogramRegisters Histogram.src
/-- Histogram output base register. -/
abbrev hdst : Fin 28 := histogramRegisters Histogram.dst
/-- Histogram length register. -/
abbrev hlen : Fin 28 := histogramRegisters Histogram.len
/-- Histogram modulus register. -/
abbrev hbins : Fin 28 := histogramRegisters Histogram.bins
/-- Histogram constant register, also used to decode the encoded modulus. -/
abbrev hone : Fin 28 := histogramRegisters Histogram.one

/-- Set up the histogram parameters, explicitly decoding the positive modulus. -/
def prepare : Code .standard 28 := ram[
  hsrc ← scratch; hdst ← dst; hlen ← len; hone ← #2; hbins ← modulus / hone ]

/-- A single finite native program, independent of input length, modulus and word width. -/
def program : Code .standard 28 :=
  .seq (Residues.program.rename residuesRegisters)
    (.seq prepare (Histogram.program.rename histogramRegisters))

/-- The complete counting program preserves its input base, scratch base, length,
encoded modulus and histogram base registers. -/
theorem preserves_parameters (i : Fin 28)
    (hi : (9 ≤ i.val ∧ i.val ≤ 12) ∨ i = dst) : program.Preserves i := by
  fin_cases i <;> norm_num [dst] at hi <;> decide

/-- The residue scratch array and the complete histogram, framed by the original memory. -/
def memory (mem : ℕ → ℕ) (values : ℕ → ℤ) (n M scratch dst : ℕ) : ℕ → ℕ :=
  Histogram.memory (Residues.memory mem values M scratch n)
    (fun i => (values i % (M : ℤ)).toNat) dst M n

/-- Neither the residue array nor the histogram modifies an earlier memory cell. -/
theorem memory_before (mem : ℕ → ℕ) (values : ℕ → ℤ) (n M scratch dst a : ℕ)
    (hs : a < scratch) (hd : a < dst) : memory mem values n M scratch dst a = mem a := by
  simp [memory, Histogram.memory, Residues.memory, show ¬(dst ≤ a ∧ a < dst + M) by omega,
    show ¬(scratch ≤ a ∧ a < scratch + n) by omega]

/-- Complete native collision counting, including residue computation, clearing the histogram
and register setup. Input, scratch and histogram blocks occur in that order and are disjoint.
The final halt is excluded. Fit hypotheses are local; a caller must derive them from its
input and width contract. -/
theorem exec {w M : ℕ} (x : Data 28) (values : ℕ → ℤ) (hM : 0 < M)
    (hmod : GenericRAM.Signed.Fits w (M : ℤ))
    (hmodreg : x.regs modulus = encode (M : ℤ))
    (hfit : ∀ i < x.regs len, GenericRAM.Signed.Fits w (values i))
    (hs : Fits (w + 2) (x.regs src + x.regs len))
    (hk : Fits (w + 2) (x.regs scratch + x.regs len))
    (hd : Fits (w + 2) (x.regs dst + M))
    (ht : Fits (w + 2) (x.regs len * x.regs len + x.regs len + 1))
    (hsk : x.regs src + x.regs len ≤ x.regs scratch)
    (hkd : x.regs scratch + x.regs len ≤ x.regs dst)
    (hinput : ∀ i < x.regs len, x.mem (x.regs src + i) = encode (values i)) :
    ∃ y, ExecWithin (w + 2) program x y (34 * x.regs len + 5 * M + 18) ∧
      y.mem = memory x.mem values (x.regs len) M (x.regs scratch) (x.regs dst) ∧
      y.regs total = Histogram.pairs (fun i => (values i % (M : ℤ)).toNat) (x.regs len) ∧
      ∀ i, ((9 ≤ i.val ∧ i.val ≤ 12) ∨ i = dst) → y.regs i = x.regs i := by
  have htwo : Fits (w + 2) 2 := (show Fits 2 2 from by decide).mono (by omega)
  have h1 : Fits (w + 2) 1 := htwo.of_le (by decide)
  have hraw : Fits (w + 2) M :=
    ((encode_fits hmod).mono (by omega)).of_le (by simp only [encode, Int.natAbs_natCast]; omega)
  obtain ⟨y, he, hym, hyt⟩ : ∃ y,
      ExecWithin (w + 2) program x y (34 * x.regs len + 5 * M + 18) ∧
      y.mem = memory x.mem values (x.regs len) M (x.regs scratch) (x.regs dst) ∧
      y.regs total = Histogram.pairs (fun i => (values i % (M : ℤ)).toNat) (x.regs len) := by
    refine WP.exists_execWithin ?_
    unfold program prepare
    wram_exec
    wram_call (Residues.exec _ values hM hmod hmodreg hfit hs hk hsk hinput)
      canonical residues_injective with a ⟨ham, har⟩
    change a.mem = Residues.memory x.mem values M (x.regs scratch) (x.regs len) at ham
    have has : a.regs Residues.dst = x.regs scratch := har Residues.dst (by decide)
    have hal : a.regs Residues.len = x.regs len := har Residues.len (by decide)
    have hamod : a.regs Residues.modulus = encode (M : ℤ) :=
      (har Residues.modulus (by decide)).trans hmodreg
    wram_exec [has, hal, hamod, encode_div_two, Int.natAbs_natCast]
    wram_call (Histogram.exec _ (fun i => (values i % (M : ℤ)).toNat) h1
      (by wram_simp [histogramRegisters, hsrc, hdst, hlen, hone, hbins]; exact hk)
      (by wram_simp [histogramRegisters, hsrc, hdst, hlen, hone, hbins]; exact hd)
      (by wram_simp [histogramRegisters, hsrc, hdst, hlen, hone, hbins]; exact ht)
      (by wram_simp [histogramRegisters, hsrc, hdst, hlen, hone, hbins]; exact hkd)
      (fun i _ => by
        wram_simp [histogramRegisters, hsrc, hdst, hlen, hone, hbins]
        have := Int.emod_nonneg (values i) (show (M : ℤ) ≠ 0 by omega)
        have := Int.emod_lt_of_pos (values i) (show (0 : ℤ) < M by omega)
        omega)
      (fun i hi => by
        have hi' : i < x.regs len := by
          wram_simp [histogramRegisters, hsrc, hdst, hlen, hone, hbins] at hi
          exact hi
        wram_simp [histogramRegisters, hsrc, hdst, hlen, hone, hbins, ham]
        simp [Residues.memory, hi']))
      canonical histogram_injective with b ⟨hbm, hbt, _⟩
    have hres_len : residuesRegisters Residues.len = len := rfl
    refine ⟨by wram_simp [histogramRegisters, hres_len,
      hsrc, hdst, hlen, hone, hbins]; omega, ?_, ?_⟩
    · wram_simp [histogramRegisters, hsrc, hdst, hlen, hone, hbins, hbm, ham]
      rfl
    · wram_simp [total, histogramRegisters, hsrc, hdst, hlen, hone, hbins, hbt]
  exact ⟨y, he, hym, hyt, fun i hi => he.regs_eq (preserves_parameters i hi)⟩

/-- For an injective integer array, the composed program returns exactly the collision
count used by the existing Chan–He prime searches. -/
theorem exec_coll {w M : ℕ} (x : Data 28) (values : ℕ → ℤ) (hM : 0 < M)
    (hmod : GenericRAM.Signed.Fits w (M : ℤ))
    (hmodreg : x.regs modulus = encode (M : ℤ))
    (hfit : ∀ i < x.regs len, GenericRAM.Signed.Fits w (values i))
    (hs : Fits (w + 2) (x.regs src + x.regs len))
    (hk : Fits (w + 2) (x.regs scratch + x.regs len))
    (hd : Fits (w + 2) (x.regs dst + M))
    (ht : Fits (w + 2) (x.regs len * x.regs len + x.regs len + 1))
    (hsk : x.regs src + x.regs len ≤ x.regs scratch)
    (hkd : x.regs scratch + x.regs len ≤ x.regs dst)
    (hinput : ∀ i < x.regs len, x.mem (x.regs src + i) = encode (values i))
    (hinj : Set.InjOn values (↑(Finset.range (x.regs len)) : Set ℕ)) :
    ∃ y, ExecWithin (w + 2) program x y (34 * x.regs len + 5 * M + 18) ∧
      y.mem = memory x.mem values (x.regs len) M (x.regs scratch) (x.regs dst) ∧
      y.regs total = Cslib.Algorithms.ThreeSum.ChanHe.coll
        ((Finset.range (x.regs len)).image values) M ∧
      ∀ i, ((9 ≤ i.val ∧ i.val ≤ 12) ∨ i = dst) → y.regs i = x.regs i := by
  obtain ⟨y, hy, hm, ht, hr⟩ := exec x values hM hmod hmodreg hfit hs hk hd ht hsk hkd hinput
  exact ⟨y, hy, hm, ht.trans (coll_eq_histogramPairs values _ M hM hinj).symm, hr⟩

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Count
