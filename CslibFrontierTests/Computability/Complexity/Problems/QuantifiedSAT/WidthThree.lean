/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Complexity.Problems.QuantifiedSAT.WidthThree

set_option linter.privateModule false

open Cslib.Complexity Cslib.Complexity.QuantifiedSAT.WidthThree
open Cslib.Logic.PL

example : SigmaPComplete 1 encoding (SigmaWidthThree 1) := sigmaWidthThree_complete (by decide)
example : SigmaPComplete 2 encoding (SigmaWidthThree 2) := sigmaWidthThree_complete (by decide)
example : SigmaPComplete 3 encoding (SigmaWidthThree 3) := sigmaWidthThree_complete (by decide)
example : PiPComplete 3 encoding (PiWidthThree 3) := piWidthThree_complete (by decide)
example : PiPComplete 4 encoding (PiWidthThree 4) := piWidthThree_complete (by decide)

-- These checks distinguish the signs without allowing quantifier choices to mask a reversal.
example : (prenexAt true ⟨[[0]], [[(0, true)]]⟩).matrix.eval (fun _ => true) = true := by decide
example : (prenexAt true ⟨[[0]], [[(0, false)]]⟩).matrix.eval (fun _ => true) = false := by decide
example : (prenexAt false ⟨[[0]], [[(0, true)]]⟩).matrix.eval (fun _ => true) = true := by decide
example : (prenexAt false ⟨[[0]], [[(0, false)]]⟩).matrix.eval (fun _ => true) = false := by decide

-- A unit literal is existentially satisfiable. Two opposite unit clauses are inconsistent.
example : (⟨[[0]], [[(0, true)]]⟩ : Instance) ∈ SigmaWidthThree 1 := by decide
example : (⟨[[0]], [[(0, true)], [(0, false)]]⟩ : Instance) ∉ SigmaWidthThree 1 := by decide

-- The disjunction of opposite signs is universally true. A single literal is not.
example : (⟨[[0]], [[(0, true)], [(0, false)]]⟩ : Instance) ∈ PiWidthThree 1 := by decide
example : (⟨[[0]], [[(0, true)]]⟩ : Instance) ∉ PiWidthThree 1 := by decide

-- CNF and DNF have opposite truth values on empty matrices and empty rows.
example : (⟨[[]], []⟩ : Instance) ∈ SigmaWidthThree 1 := by decide
example : (⟨[[]], [[]]⟩ : Instance) ∉ SigmaWidthThree 1 := by decide
example : (⟨[[], []], []⟩ : Instance) ∉ SigmaWidthThree 2 := by decide
example : (⟨[[], []], [[]]⟩ : Instance) ∈ SigmaWidthThree 2 := by decide

-- Out-of-range widths, an unbound variable and the wrong number of blocks are rejected.
example : (⟨[[0]], [[(0, true), (0, true), (0, true), (0, true)]]⟩ : Instance) ∉
    SigmaWidthThree 1 := by decide
example : (⟨[[0]], [[], [(0, true), (0, true), (0, true), (0, true)]]⟩ : Instance) ∉
    PiWidthThree 1 := by decide
example : (⟨[[0]], [[(1, true)]]⟩ : Instance) ∉ SigmaWidthThree 1 := by decide
example : (⟨[[], []], []⟩ : Instance) ∉ SigmaWidthThree 1 := by decide
