/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import CslibFrontier.Foundations.Data.BitString.CyclicDifference.BoundaryKernel

/-! The pure quotient kernel needs no ordered-incidence or embedding imports. Its minimal
two-port case and wrap edge use the same theorem and literal coordinate maps.
-/

open Cslib.BitString

example : zeroPort (0 : Fin 2) 0 = zeroPort (0 : Fin 2) 1 :=
  (zeroPort_kernel 0 0 1).mpr (by decide +kernel)

example : zeroPort (1 : Fin 2) 0 = zeroPort (1 : Fin 2) 1 :=
  (zeroPort_kernel 1 0 1).mpr (by decide +kernel)

example : List.ofFn (zeroPort (1 : Fin 2)) = [0, 0] := by decide +kernel
example : List.ofFn (zeroPort (5 : Fin 6)) = [0, 1, 2, 3, 4, 0] := by decide +kernel
example : zeroPort (5 : Fin 6) 1 ≠ zeroPort (5 : Fin 6) 2 := by decide +kernel

-- No pair away from the selected merged endpoint is accidentally identified.
example {n : ℕ} (i a b : Fin (n + 2))
    (ha : a ≠ finRotate (n + 2) i) (hb : b ≠ finRotate (n + 2) i)
    (h : zeroPort i a = zeroPort i b) : a = b := by
  have he := (zeroPort_kernel i a b).mp h
  simpa only [Function.update_of_ne ha, Function.update_of_ne hb, id_eq] using he

open Lean Elab Command in
run_cmd do
  for name in (← getEnv).header.moduleNames do
    if (`CslibFrontier.Computability.Complexity.Problems.CSP).isPrefixOf name ||
        (`CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem).isPrefixOf name ||
        (`CslibFrontier.Logics.Propositional.CSP.Planar.Embedding).isPrefixOf name then
      throwError "pure boundary kernel imported ordered graph infrastructure {name}"
