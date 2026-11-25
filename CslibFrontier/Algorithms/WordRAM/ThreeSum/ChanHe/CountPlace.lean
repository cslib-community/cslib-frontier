/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.CountCall
public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.PlaceExec
public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.PlaceMemory
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# A complete native counting and placement call

This routine actually computes the residues and histogram before extracting a heavy array and
placing the corresponding packed column. The histogram is not a premise of the execution
contract. It also writes the compact output count to its caller-supplied descriptor cell.

## Main definitions

* `CountPlace.program`: modulus encoding, complete `CountCall.program 2`, runtime argument
  delivery, complete `Place.program`, and the count store.

## References

This native composition is original and reuses the existing Chan–He mathematical definitions.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.CountPlace

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Input length (the selected third argument of the existing counting call). -/
abbrev len : Fin 64 := 32
/-- Signed input base. -/
abbrev src : Fin 64 := 33
/-- Unsigned residue workspace base. -/
abbrev scratch : Fin 64 := 34
/-- Histogram workspace base. -/
abbrev hist : Fin 64 := 35
/-- Compact heavy output base. -/
abbrev heavy : Fin 64 := 37
/-- Packed node array base. -/
abbrev packed : Fin 64 := 38
/-- Positive modulus, decoded unsigned. -/
abbrev modulus : Fin 64 := 40
/-- Encoded positive tag. -/
abbrev tag : Fin 64 := 41
/-- Packed column. -/
abbrev column : Fin 64 := 42
/-- Distance between the two stores. -/
abbrev distance : Fin 64 := 43
/-- Zero for X/Y, one for Z. -/
abbrev negative : Fin 64 := 44
/-- Cell in which the exact heavy count is stored. -/
abbrev descriptor : Fin 64 := 45

/-- Fixed embedding of the placement workspace below all caller parameters. -/
def registers (i : Fin 32) : Fin 64 := ⟨i.val, by omega⟩

private theorem registers_injective : Function.Injective registers := by
  intro i j he
  apply Fin.ext
  exact congrArg (fun k : Fin 64 => k.val) he

@[inherit_doc Place.src]
abbrev psrc : Fin 64 := registers Place.src
@[inherit_doc Place.keys]
abbrev pkeys : Fin 64 := registers Place.keys
@[inherit_doc Place.len]
abbrev plen : Fin 64 := registers Place.len
@[inherit_doc Place.hist]
abbrev phist : Fin 64 := registers Place.hist
@[inherit_doc Place.heavy]
abbrev pheavy : Fin 64 := registers Place.heavy
@[inherit_doc Place.packed]
abbrev ppacked : Fin 64 := registers Place.packed
@[inherit_doc Place.modulus]
abbrev pmodulus : Fin 64 := registers Place.modulus
@[inherit_doc Place.tag]
abbrev ptag : Fin 64 := registers Place.tag
@[inherit_doc Place.column]
abbrev pcolumn : Fin 64 := registers Place.column
@[inherit_doc Place.distance]
abbrev pdistance : Fin 64 := registers Place.distance
@[inherit_doc Place.negative]
abbrev pnegative : Fin 64 := registers Place.negative
@[inherit_doc Place.count]
abbrev pcount : Fin 64 := registers Place.count

/-- All eleven runtime argument copies are real instructions. -/
def prepare : Code .standard 64 := ram[
  psrc ← src; pkeys ← scratch; plen ← len; phist ← hist; pheavy ← heavy;
  ppacked ← packed; pmodulus ← modulus; ptag ← tag; pcolumn ← column;
  pdistance ← distance; pnegative ← negative ]

/-- Complete fixed native routine: no host histogram, heavy filter or output constructor. -/
def program : Code .standard 64 :=
  .seq (.op (.bin .add CountCall.modulus modulus modulus))
    (.seq (CountCall.program 2) (.seq prepare
      (.seq (Place.program.rename registers) (.op (.store descriptor pcount)))))

/-- Only the counting/placement workspace, the encoded modulus, and the discarded collision
counter can change. All caller registers at least 46 are included in this frame. -/
theorem preserves (i : Fin 64) (hi : 32 ≤ i.val) (hm : i ≠ CountCall.modulus)
    (hc : i ≠ CountCall.result 2) : program.Preserves i := by
  have h : ∀ i : Fin 64, 32 ≤ i.val → i ≠ CountCall.modulus → i ≠ CountCall.result 2 →
      program.Preserves i := by decide +kernel
  exact h i hi hm hc

/-- Polynomial envelope for addresses, counters, encoded magnitudes and every scan intermediate. -/
def budget (x : Data 64) (M N U t : ℕ) : ℕ :=
  x.regs src + x.regs scratch + x.regs hist + x.regs heavy + x.regs packed +
    x.regs len * x.regs len + 2 * x.regs len + M + 4 * N + 2 * t + 2 * U + 64

/-- Exact memory, including actual residue/histogram construction and the descriptor write. -/
def memory (mem : ℕ → ℕ) (values : ℕ → ℤ)
    (n M out dst col dist t scratch hist descriptor : ℕ) (neg : Bool) : ℕ → ℕ :=
  Function.update
    (Place.memory (Count.memory mem values n M scratch hist) values n M out dst col dist t neg n)
    descriptor (Place.heavyList values n M n).length

/-- Complete native count/extract/place execution, charging modulus encoding, all subroutine
argument/result copies and the final count write. The caller supplies actual signed input words;
no histogram or light/heavy-output contract is assumed. -/
theorem exec {w M N U t : ℕ} (x : Data 64) (values : ℕ → ℤ) (neg : Bool)
    (hM : 0 < M) (hmod : GenericRAM.Signed.Fits w (M : ℤ))
    (hmreg : x.regs modulus = M) (hN : 2 * M ≤ N) (ht : U ≤ t)
    (htag : x.regs tag = 2 * t) (hneg : x.regs negative = if neg then 1 else 0)
    (hc : x.regs column < 4) (hd : x.regs distance ≤ 4 * M)
    (hbdd : ∀ i < x.regs len, (values i).natAbs ≤ U)
    (hsigned : ∀ i < x.regs len, GenericRAM.Signed.Fits w (values i))
    (hfit : Fits (w + 2) (budget x M N U t))
    (hsh : x.regs src + x.regs len ≤ x.regs heavy)
    (hhp : x.regs heavy + x.regs len ≤ x.regs packed)
    (hpk : x.regs packed + 4 * N ≤ x.regs scratch)
    (hkh : x.regs scratch + x.regs len ≤ x.regs hist)
    (hinput : ∀ i < x.regs len, x.mem (x.regs src + i) = encode (values i))
    (hinj : Set.InjOn values (↑(Finset.range (x.regs len)) : Set ℕ)) :
    ∃ y, ExecWithin (w + 2) program x y (66 * x.regs len + 5 * M + 45) ∧
      y.mem = memory x.mem values (x.regs len) M (x.regs heavy) (x.regs packed)
        (x.regs column) (x.regs distance) t (x.regs scratch) (x.regs hist)
        (x.regs descriptor) neg ∧
      ∀ i, 32 ≤ i.val → i ≠ CountCall.modulus → i ≠ CountCall.result 2 →
        y.regs i = x.regs i := by
  have hemod : encode (M : ℤ) = M + M := by simp [encode, two_mul]
  have hf : Fits (w + 2) (encode (M : ℤ)) := (encode_fits hmod).mono (by omega)
  have fs : Fits (w + 2) (x.regs src + x.regs len) := hfit.of_le (by dsimp only [budget]; omega)
  have fk : Fits (w + 2) (x.regs scratch + x.regs len) := hfit.of_le (by dsimp only [budget]; omega)
  have fh : Fits (w + 2) (x.regs hist + M) := hfit.of_le (by dsimp only [budget]; omega)
  have fn : Fits (w + 2) (x.regs len * x.regs len + x.regs len + 1) :=
    hfit.of_le (by dsimp only [budget]; omega)
  have hsk : x.regs src + x.regs len ≤ x.regs scratch := by omega
  unfold program prepare
  refine WP.exists_execWithin ?_
  wram_exec [hmreg, ← hemod, hf]
  wram_call (CountCall.exec 2 _ values hM hmod ..) [CountCall.length, CountCall.source,
    CountCall.scratch, CountCall.histogram, hsigned, fs, fk, fh, fn, hsk, hkh, hinput, hinj]
    with a ⟨ham, _, har⟩
  replace ham :
      a.mem = Count.memory x.mem values (x.regs len) M (x.regs scratch) (x.regs hist) := by
    wram_simp [CountCall.length, CountCall.scratch, CountCall.histogram] at ham
    exact ham
  have ar (i : Fin 64) (hi : 32 ≤ i.val := by decide) (hm : i ≠ CountCall.modulus := by decide)
      (hc : i ≠ CountCall.result 2 := by decide) : a.regs i = x.regs i := by
    rw [har i (by omega) hc]
    wram_simp [hm]
  wram_exec [ar src, ar scratch, ar len, ar hist, ar heavy, ar packed, ar modulus, ar tag,
    ar column, ar distance, ar negative]
  wram_call (Place.exec _ values neg hM hN _ _ ht _ _ _ _
      (by
        rw [Place.budget]
        wram_simp [Data.comap_regs]
        exact hfit.of_le (by dsimp only [budget]; omega))
      _ _ _ _
      (by
        wram_simp [Data.comap_regs, Data.comap_mem]
        intro i hi
        rw [ham, Count.memory_before _ _ _ _ _ _ _ (by omega) (by omega)]
        exact hinput i hi)
      (by
        wram_simp [Data.comap_regs, Data.comap_mem]
        intro i hi
        rw [ham, Count.memory, Histogram.memory, ite_eq_right (by omega)]
        simp [Residues.memory, hi, residueKey])
      (by
        wram_simp [Data.comap_regs, Data.comap_mem]
        intro r hr
        rw [ham, Count.memory, Histogram.memory_read _ _ _ _ _ _ hr]
        rfl)) renamed registers_injective
      [Data.comap_regs, hc, hd, hmreg, htag, hneg, hbdd, hsh, hhp, hpk, hkh]
    with y ⟨⟨hbm, hbc, _⟩, hframe⟩
  have hb (i : Fin 64) (hi : 32 ≤ i.val) (k : Fin 32) : registers k ≠ i :=
    Fin.ne_of_val_ne (by dsimp only [registers]; omega)
  have yd : y.regs descriptor = x.regs descriptor := by
    rw [hframe descriptor (hb descriptor (by decide))]
    wram_simp
    exact ar descriptor
  wram_exec [yd]
  have hlen : CountCall.length 2 = len := rfl
  wram_simp [hlen, Data.comap_regs, Data.comap_mem] at hbm hbc ⊢
  refine ⟨by omega, ?_, fun i hi hm hc => ?_⟩
  · rw [hbc, hbm, ham]
    rfl
  · rw [hframe i (hb i hi)]
    wram_simp [hb i hi]
    exact ar i hi hm hc

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.CountPlace
