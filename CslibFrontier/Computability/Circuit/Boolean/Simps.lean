/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Formula
public import CslibFrontier.Computability.Circuit.Simps

/-!
# Normalizing and bounding Boolean circuits

Adds the connectives of Boolean formulas to the simp set `circuit_simps` and to the rules of
`circuit_bound`.
-/

public section

open Cslib.Circuits

attribute [circuit_simps]
  Formula.eval_const Formula.eval_not Formula.eval_and Formula.eval_or Formula.eval_xor
  Formula.size_not Formula.size_and Formula.size_or
  Formula.depth_const Formula.depth_not Formula.depth_and Formula.depth_or

attribute [circuit_bound] Formula.depth_xor_le

end
