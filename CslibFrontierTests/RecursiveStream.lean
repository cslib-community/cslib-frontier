/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Recursive
meta import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Recursive

/-! Flat recursive-stream splitting, including higher arities and native certificates. -/

open Turing.MultiTapeTM Turing.MultiTapeTM.RecursiveEncoding

example : splitTree id ([] : List ℕ) = none := rfl

example : splitTree id [0, 3, 0, 0, 0] = some ([0], [3, 0, 0, 0]) := rfl

example : splitTree id [3, 0, 1, 0, 0, 0] = some ([3, 0, 1, 0, 0], [0]) := rfl

example : splitTree id [3, 0, 1, 0] = none := rfl

example : isTree id [3, 0, 1, 0, 0] = true := rfl

example : isTree id [3, 0, 1, 0] = false := rfl

example : isTree id [0, 0] = false := rfl

example : Forest id 1 [3, 0, 1, 0, 0] :=
  (splitTree_eq_some_iff.mp (show splitTree id [3, 0, 1, 0, 0] =
    some ([3, 0, 1, 0, 0], []) from rfl)).1

-- Finite arity recognition suffices; no decoder or inhabitant of a semantic tree is supplied.
example : ComputableInPolyTime
    (splitTree (fun b : Bool => if b then 3 else 0)) (encList encBool)
    (encOption (encPair (encList encBool) (encList encBool))) :=
  splitTree_polyTime (ComputableInPolyTime.of_finite _)
    (maximum := 3) (by intro b; cases b <;> decide)

example : ComputableInPolyTime
    (isTree (fun b : Bool => if b then 3 else 0)) (encList encBool) encBool :=
  isTree_polyTime (ComputableInPolyTime.of_finite _)
    (maximum := 3) (by intro b; cases b <;> decide)

set_option linter.hashCommand false in
#guard splitTree id (List.replicate 256 1 ++ [0, 3, 0, 0, 0]) ==
  some (List.replicate 256 1 ++ [0], [3, 0, 0, 0])
