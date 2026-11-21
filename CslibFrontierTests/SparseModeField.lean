/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.SparseModeField

open Cslib.BitString Cslib.SparseModeTuple Turing Turing.MultiTapeTM

private def x : Entry := ⟨1, 0⟩
private def y : Entry := ⟨0, 4⟩
private def r : Row := ⟨0, x, [y]⟩
private def old : Row := ⟨1, ⟨0, 0⟩, []⟩
private def rows : List Row := [old, r]

-- Read either field of the second entry of the second row, through earlier rows and entries.
-- A hundred cells of trailing padding never increase the promised clock.
example {input : List Bool} (ip : Fin (input.length + 2)) (out : List Bool) (side : Bool) :
    let px := SparseModeField.prefixFields side rows [old] r [x] y
    let tally := List.replicate px.length true
    let cursor := if side then 23 else 18
    let bits := if side then [true, false, true] else [true]
    RunsBetween GammaOffset.machine (GammaOffset.storage ip out (padded 123 rows) 0 tally 0)
      (GammaOffset.storage ip ((out ++ tally) ++ bits) (padded 123 rows) cursor tally px.length)
      94 285 := by
  have hlen : (encode rows).length = 23 := by decide
  have hcursor (b : Bool) :
      ((SparseModeField.prefixFields b rows [old] r [x] y).flatMap eliasGamma).length +
        (eliasGamma (SparseModeField.value b y)).length = if b then 23 else 18 := by
    cases b <;> decide
  have hout (b : Bool) : GammaStream.tokenOutput true (SparseModeField.value b y) =
      if b then [true, false, true] else [true] := by cases b <;> decide
  have h := SparseModeField.runsBetween side ip out 123 [old] [] r [x] [] y rfl
  simpa only [show [old] ++ r :: [] = rows from rfl, hcursor, hout, hlen,
    Nat.reduceMul, Nat.reduceAdd] using h
