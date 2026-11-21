/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootPortFinish

open Turing.MultiTapeTM.RootPortFinish
open Cslib.SeededPredecessor (Context)

-- A column port reads the column key of the same edge even when its row label differs.
example (c : Context) (i r v : ℕ) (hc : c.candidate < c.edge)
    (hv : symbol c i r ≠ symbol c i v) :
    run ⟨⟨true, i, symbol c i v⟩, c, some (r, v)⟩ = true ∧
    run ⟨⟨false, i, symbol c i v⟩, c, some (r, v)⟩ = false := by
  simp [hc, hv]

-- At the prefix bound, even membership in the correct group does not contribute to the rank.
example (c : Context) (i r v : ℕ) (hc : c.candidate = c.edge) :
    run ⟨⟨false, i, symbol c i r⟩, c, some (r, v)⟩ = false := by simp [hc]
