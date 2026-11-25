/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

-- upstream: candidate
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import CslibFrontier.Foundations.Data.Matrix.Binary

/-!
# Printing an indexed binary matrix

A polynomial-time bit lookup and polynomial-time unary dimensions suffice to print the whole
matrix in the library's fixed-width row-major representation.
-/

public section

open Cslib

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Print every bit of a rectangular matrix in row-major order by enumerating the unary row
and column indices. The output is the canonical width-one matrix encoding. -/
theorem matrixToBinary_one {α : Type} {input : α ↪ List Bool} {rows cols : α → ℕ}
    (M : (a : α) → Matrix (Fin (rows a)) (Fin (cols a)) (ZMod 2))
    {entry : α → ℕ → ℕ → Bool}
    (hr : ComputableInPolyTime rows input encUnary)
    (hc : ComputableInPolyTime cols input encUnary)
    (he : ComputableInPolyTime (fun p : (α × ℕ) × ℕ => entry p.1.1 p.1.2 p.2)
      (encPair (encPair input encUnary) encUnary) encBool)
    (hentry : ∀ a (i : Fin (rows a)) (j : Fin (cols a)),
      entry a i.val j.val = (M a i j).val.testBit 0) :
    ComputableInPolyTime (fun a => Cslib.Matrix.toBinary (w := 1) (M a)) input encBits := by
  have ht : ComputableInPolyTime (fun a =>
      (List.range (rows a)).flatMap (fun i => (List.range (cols a)).map (entry a i)))
      input encBits :=
    flatMapToBitsWithInput (unary_range' hr)
      (mapToBitsWithInput (unary_range' (hc.comp (fst input encUnary))) he)
  convert ht using 1
  funext a
  rw [Cslib.Matrix.toBinary_eq]
  simp only [List.ofFn_succ, List.ofFn_zero, Fin.val_zero]
  simp_rw [← hentry]
  simp only [List.ofFn_eq_map, ← List.flatMap_def, ← List.map_eq_flatMap]
  simp only [← List.map_coe_finRange_eq_range, List.flatMap_map, List.map_map, Function.comp_def]

end Turing.MultiTapeTM.ComputableInPolyTime
