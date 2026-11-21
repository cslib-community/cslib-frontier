/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.GammaStream

open Cslib.BitString Cslib.SparseModeTuple Turing Turing.MultiTapeTM Turing.MultiTapeTM.GammaStream

-- The empty sequence halts after its first blank check without changing the prepared tapes.
example {input : List Bool} (ip : Fin (input.length + 2)) (out pre : List Bool) :
    RunsBetween (machine false) (storage ip out pre pre.length) (storage ip out pre pre.length)
      1 4 := by simpa using runsBetween false ip out pre []

-- One scanner skips an entire row containing two occupied weights, across all seven tokens.
private def sparse : List Row := [⟨1, ⟨1, 2⟩, [⟨1, 0⟩]⟩]

example {input : List Bool} (ip : Fin (input.length + 2)) (out pre : List Bool) :
    RunsBetween (machine false) (storage ip out (pre ++ encode sparse) pre.length)
      (storage ip (out ++ List.replicate 7 true) (pre ++ encode sparse) (pre.length + 19))
      58 118 := by
  have hf : (fields sparse).length = 7 := by decide
  have he : (encode sparse).length = 19 := by decide
  simpa only [hf, he] using runsBetween_sparse ip out pre sparse
