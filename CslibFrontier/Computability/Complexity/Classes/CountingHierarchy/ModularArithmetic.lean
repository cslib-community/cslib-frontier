/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Arithmetic
public import Mathlib.Data.ZMod.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryOrder
import Mathlib.Tactic.Ring

/-!
# Same-level total modular subtraction

`modularSub` subtracts binary residues without constructing a negative natural number.
Its polynomial-time certificate is total, including modulus zero, and its counting-function
certificate preserves the common level of all three inputs. At every positive modulus the
output casts to the actual difference in `ZMod p`.

Ported from `LeanCanny.CountingHierarchy.ModularArithmetic` at lean-canny commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`. This shared arithmetic supports modular evaluators
without importing the real-arithmetic applications.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- Total modular subtraction; modulus zero returns the natural value `x`. -/
@[expose] def modularSub (p x y : ℕ) : ℕ := (x + (p - y % p)) % p

/-- Binary modular subtraction is polynomial-time on every input. -/
@[fun_prop]
theorem modularSub_polyTime {α : Type} {enc : α ↪ List Bool} {p x y : α → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hx : ComputableInPolyTime x enc encNat)
    (hy : ComputableInPolyTime y enc encNat) :
    ComputableInPolyTime (fun w => modularSub (p w) (x w) (y w)) enc encNat :=
  ComputableInPolyTime.binary_mod.comp
    ((ComputableInPolyTime.binary_add' hx (ComputableInPolyTime.binary_sub' hp
      (ComputableInPolyTime.binary_mod.comp (hy.prod hp)))).prod hp)

/-- Binary modular subtraction preserves a common counting-function level. -/
theorem modularSub_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ} {p x y : α → ℕ}
    (hp : p ∈ CountingFunction a enc encNat)
    (hx : x ∈ CountingFunction a enc encNat)
    (hy : y ∈ CountingFunction a enc encNat) :
    (fun w => modularSub (p w) (x w) (y w)) ∈ CountingFunction a enc encNat := by
  have hfp : ComputableInPolyTime
      (fun q : ℕ × (ℕ × ℕ) => modularSub q.1 q.2.1 q.2.2)
      (encPair encNat (encPair encNat encNat)) encNat :=
    modularSub_polyTime (by fun_prop) (by fun_prop) (by fun_prop)
  exact CountingFunction.map (CountingFunction.prod hp (CountingFunction.prod hx hy)) hfp

/-- At a positive modulus, the evaluator represents subtraction in `ZMod p`. -/
theorem modularSub_cast {p : ℕ} (hp : 0 < p) (x y : ℕ) :
    (modularSub p x y : ZMod p) = (x : ZMod p) - (y : ZMod p) := by
  rw [modularSub, ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub (Nat.mod_lt _ hp).le,
    ZMod.natCast_self, ZMod.natCast_mod]
  ring

end Cslib.Complexity
