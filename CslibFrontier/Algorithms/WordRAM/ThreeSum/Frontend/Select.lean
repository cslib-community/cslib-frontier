/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Frontend.Model
public import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame
import CslibFrontier.Computability.WordRAM.SymbolicExec.Havoc

/-!
# Native selection of canonical signed keys

All arithmetic is unsigned. The sign bit and magnitude are decoded explicitly, the label
is formed by addition or subtraction, and its two digits are computed with native shifts and
remainders. The repeated-value case doubles the key and subtracts its original sign bit.

## Main definitions

* `Select.program`: concrete selection and transformation instructions.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Frontend

open Cslib.WordRAM

namespace Select

/-- Magnitude bound, followed by two bit positions, selected digit and scan mode. -/
abbrev magnitude : Fin 48 := 0
@[inherit_doc magnitude] abbrev beta : Fin 48 := 1
@[inherit_doc magnitude] abbrev beta' : Fin 48 := 2
@[inherit_doc magnitude] abbrev digit : Fin 48 := 3
@[inherit_doc magnitude] abbrev mode : Fin 48 := 4
/-- Input key; replaced by its selected output value. -/
abbrev key : Fin 48 := 5
/-- Full input multiplicity, read without truncation. -/
abbrev count : Fin 48 := 6
/-- Small constants installed by the scan. -/
abbrev zero : Fin 48 := 7
@[inherit_doc zero] abbrev one : Fin 48 := 8
@[inherit_doc zero] abbrev two : Fin 48 := 9
@[inherit_doc zero] abbrev three : Fin 48 := 10
@[inherit_doc zero] abbrev four : Fin 48 := 11
@[inherit_doc zero] abbrev five : Fin 48 := 12
/-- Scratch registers for decoding and label digits. -/
abbrev sign : Fin 48 := 13
@[inherit_doc sign] abbrev label : Fin 48 := 14
@[inherit_doc sign] abbrev bitA : Fin 48 := 15
@[inherit_doc sign] abbrev bitB : Fin 48 := 16
/-- Selection flag, either zero or one. -/
abbrev take : Fin 48 := 17
/-- Magnitude temporary. -/
abbrev absolute : Fin 48 := 18

/-- Explicit native sign/magnitude decoding, shifted label and binary digit computation. -/
def labels : Code .standard 48 := ram[
  sign ← key % two; absolute ← key / two; label ← magnitude + magnitude;
  if sign = zero then [ label ← label + absolute ] else [ label ← label - absolute ];
  bitA ← label >>> beta; bitA ← bitA % two;
  bitB ← label >>> beta'; bitB ← bitB % two ]

/-- A no-op used by unsuccessful selections. -/
def skip : Code .standard 48 := ram[ take ← take ]

/-- Select one of the six finite scan modes and perform the repeated-value transformation. -/
def choose : Code .standard 48 := ram[
  take ← #0;
  if mode = zero then [
    if bitA = digit then [ take ← one ] else [ ⟪skip⟫ ]
  ] else [ if mode = one then [
    if bitA = digit then [ ⟪skip⟫ ] else [
      if bitB = zero then [ take ← one ] else [ ⟪skip⟫ ] ]
  ] else [ if mode = two then [
    if bitA = digit then [ ⟪skip⟫ ] else [
      if bitB = one then [ take ← one ] else [ ⟪skip⟫ ] ]
  ] else [ if mode = three then [
    if key = zero then [ ⟪skip⟫ ] else [
      if count < two then [ ⟪skip⟫ ] else [ take ← one ] ];
    key ← key + key; key ← key - sign
  ] else [ if mode = four then [
    if key = zero then [
      if count < three then [ ⟪skip⟫ ] else [ take ← one ]
    ] else [ ⟪skip⟫ ]
  ] else [ if mode = five then [ take ← one ] else [ ⟪skip⟫ ] ] ] ] ] ] ]

/-- Every decoding, arithmetic, branch and selection instruction is part of this code. -/
def program : Code .standard 48 := .seq labels choose

/-- This scalar program never reads the physical word width. -/
theorem not_readsWidth : ¬program.ReadsWidth := by decide

/-- Registers below the decoding scratch are preserved by label calculation. -/
theorem labels_preserves (j : Fin 48) (hj : j.val ≤ 12) : labels.Preserves j := by
  have hne (k : Fin 48) (hk : 13 ≤ k.val) : (some k : Option (Fin 48)) ≠ some j := by
    intro h
    have := congrArg Fin.val (Option.some.inj h)
    omega
  simp only [labels, Code.Preserves, Op.dest]
  exact ⟨hne sign (by decide), hne absolute (by decide), hne label (by decide),
    ⟨hne label (by decide), hne label (by decide)⟩, hne bitA (by decide),
    hne bitA (by decide), hne bitB (by decide), hne bitB (by decide)⟩

/-- Selection preserves all caller parameters, constants and scan registers. -/
theorem preserves (j : Fin 48) (hj : (j.val ≤ 12 ∧ j.val ≠ 5) ∨ 19 ≤ j.val) :
    program.Preserves j := by
  have hne (k : Fin 48) (hk : k.val = 5 ∨ 13 ≤ k.val ∧ k.val ≤ 18) :
      (some k : Option (Fin 48)) ≠ some j := by
    intro h
    have := congrArg Fin.val (Option.some.inj h)
    omega
  simp only [program, labels, choose, skip, Code.Preserves, Op.bin, Op.dest]
  repeat' constructor
  all_goals exact hne _ (by decide)

/-- Decoding and both binary digits cost at most eleven native instructions. -/
theorem labels_exec {w : ℕ} (x : Data 48)
    (hz : x.regs zero = 0) (h2 : x.regs two = 2)
    (hkey : Fits w (x.regs key))
    (habs : x.regs key / 2 ≤ 2 * x.regs magnitude)
    (hfit : Fits w (4 * x.regs magnitude + 2)) :
    ∃ y, ExecWithin w labels x y 11 ∧
      y.regs sign = x.regs key % 2 ∧
      y.regs label = Math.label (x.regs magnitude) (x.regs key) ∧
      y.regs bitA = (Math.label (x.regs magnitude) (x.regs key) >>> x.regs beta) % 2 ∧
      y.regs bitB = (Math.label (x.regs magnitude) (x.regs key) >>> x.regs beta') % 2 ∧
      y.mem = x.mem := by
  wram_exec (disch := first | fits | exact Fits.of_le (by fits) (Nat.shiftRight_le _ _) | omega)
    [labels, hz, h2] <;>
  · wram_simp
    simp [Math.label, *, two_mul]

/-- Selection from already computed digits, with the full repeated-value count. -/
theorem choose_exec {w : ℕ} (x : Data 48)
    (hz : x.regs zero = 0) (h1 : x.regs one = 1) (h2 : x.regs two = 2)
    (h3 : x.regs three = 3) (h4 : x.regs four = 4) (h5 : x.regs five = 5)
    (hs : x.regs sign = x.regs key % 2)
    (hfit : Fits w (2 * x.regs key)) (hsmall : Fits w 5) :
    ∃ y, ExecWithin w choose x y 20 ∧
      y.regs take = (Math.flag (x.regs bitA) (x.regs bitB) (x.regs digit)
        (x.regs mode) (x.regs key, x.regs count)).toNat ∧
      y.regs key = Math.value (x.regs mode) (x.regs key) ∧ y.mem = x.mem := by
  wram_exec [choose, skip, hz, h1, h2, h3, h4, h5, hs] <;>
  · wram_simp
    simp [Math.flag, Math.value, Math.twice, two_mul, Bool.toNat, *]

/-- Complete native scalar selection. Its cost includes decoding, both label bits and doubling. -/
theorem exec {w : ℕ} (x : Data 48)
    (hz : x.regs zero = 0) (h1 : x.regs one = 1) (h2 : x.regs two = 2)
    (h3 : x.regs three = 3) (h4 : x.regs four = 4) (h5 : x.regs five = 5)
    (hkey : Fits w (x.regs key)) (habs : x.regs key / 2 ≤ 2 * x.regs magnitude)
    (hfit : Fits w (4 * x.regs magnitude + 2))
    (hdouble : Fits w (2 * x.regs key)) (hsmall : Fits w 5) :
    ∃ y, ExecWithin w program x y 31 ∧
      y.regs take = (Math.keep (x.regs magnitude) (x.regs beta) (x.regs beta')
        (x.regs digit) (x.regs mode) (x.regs key, x.regs count)).toNat ∧
      y.regs key = Math.value (x.regs mode) (x.regs key) ∧ y.mem = x.mem := by
  refine WP.exists_execWithin ?_
  wram_exec [program]
  wram_call (labels_exec x hz h2 hkey habs hfit) framed with v m ⟨hus, _, hua, hub, hum⟩
  wram_call (choose_exec _ ..) framed [hz, h1, h2, h3, h4, h5, hus] with v₁ m₁ ⟨hyt, hyk, hym⟩
  exact ⟨by simpa only [Math.keep, hua, hub] using hyt, hyk, hym.trans hum⟩

end Select
end Cslib.Algorithms.WordRAM.ThreeSum.Frontend
