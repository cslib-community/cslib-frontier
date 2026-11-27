/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Logic/Equiv/Fin/Basic.lean`)

public import CslibFrontier.Init
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Coordinates of a flattened finite product

Dividing the row-major index by the column count recovers the first coordinate, and taking
its remainder recovers the second coordinate.
-/

public section

variable {m n : ℕ}

/-- Division by the column count recovers the first coordinate of a flattened index. -/
theorem finProdFinEquiv_val_div (x : Fin m × Fin n) :
    (finProdFinEquiv x : ℕ) / n = x.1 :=
  congrArg (fun p => (p.1 : ℕ)) (finProdFinEquiv.symm_apply_apply x)

/-- Remainder modulo the column count recovers the second coordinate of a flattened index. -/
theorem finProdFinEquiv_val_mod (x : Fin m × Fin n) :
    (finProdFinEquiv x : ℕ) % n = x.2 :=
  congrArg (fun p => (p.2 : ℕ)) (finProdFinEquiv.symm_apply_apply x)
