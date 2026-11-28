/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.RecursiveChild
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
meta import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.RecursiveChild

open Turing.MultiTapeTM Turing.MultiTapeTM.RecursiveEncoding

-- Unary, empty, and binary children retain their exact flat streams.
set_option linter.hashCommand false in
#guard child? id 0 [3, 1, 0, 0, 2, 0, 0] == some [1, 0]
set_option linter.hashCommand false in
#guard child? id 1 [3, 1, 0, 0, 2, 0, 0] == some [0]
set_option linter.hashCommand false in
#guard child? id 2 [3, 1, 0, 0, 2, 0, 0] == some [2, 0, 0]
set_option linter.hashCommand false in
#guard child? id 3 [3, 1, 0, 0, 2, 0, 0] == none
set_option linter.hashCommand false in
#guard child? id 2 [3, 1, 0, 0, 2, 0] == none
set_option linter.hashCommand false in
#guard child? id 0 ([] : List ℕ) == none

-- A following value does not alter a selected child.
set_option linter.hashCommand false in
#guard child? id 2 [3, 1, 0, 0, 2, 0, 0, 1, 0] == some [2, 0, 0]

-- The native certificate needs no token decoder or default token.
example : ComputableInPolyTime (child? Fin.val 2) (encList (encFinEnum (Fin 4)))
    (encOption (encList (encFinEnum (Fin 4)))) :=
  child?_polyTime (ComputableInPolyTime.of_finite _) (maximum := 3)
    (fun token => by have := token.isLt; omega) 2
