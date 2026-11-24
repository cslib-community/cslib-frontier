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

namespace Cslib.Circuits.Formula

open Boolean

variable {n : ℕ} {F G : Formula signature n}

/-- The weighted cost of `const c` is `cost (.const c)`. -/
@[simp, circuit_simps] theorem cost_const (cost : signature.Op → ℕ) (c : Bool) :
    (const c : Formula signature n).cost cost = cost (.const c) := by
  simp [const]

/-- The weighted cost of `F.not` adds `cost .not` to the weighted cost of `F`. -/
@[simp, circuit_simps] theorem cost_not (cost : signature.Op → ℕ) :
    F.not.cost cost = F.cost cost + cost .not := by
  simp [not]

/-- The weighted cost of `F.and G` adds `cost .and` to the weighted costs of `F` and `G`. -/
@[simp, circuit_simps] theorem cost_and (cost : signature.Op → ℕ) :
    (F.and G).cost cost = F.cost cost + G.cost cost + cost .and := by
  simp [and, Fin.sum_univ_two]

/-- The weighted cost of `F.or G` adds `cost .or` to the weighted costs of `F` and `G`. -/
@[simp, circuit_simps] theorem cost_or (cost : signature.Op → ℕ) :
    (F.or G).cost cost = F.cost cost + G.cost cost + cost .or := by
  simp [or, Fin.sum_univ_two]

end Cslib.Circuits.Formula

open Cslib.Circuits

attribute [circuit_simps]
  Formula.eval_const Formula.eval_not Formula.eval_and Formula.eval_or Formula.eval_xor
  Formula.size_const Formula.size_not Formula.size_and Formula.size_or Formula.size_xor
  Formula.leafSize_const Formula.leafSize_not Formula.leafSize_and Formula.leafSize_or
  Formula.leafSize_xor
  Formula.depth_const Formula.depth_not Formula.depth_and Formula.depth_or

attribute [circuit_bound] Formula.depth_xor_le

end
