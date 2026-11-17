/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Tactic.PolyTime.Init
public import Mathlib.Data.Nat.Sqrt
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.NthRoot
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-!
# Polynomial-time integer square roots on binary naturals

`Nat.sqrt m` (`⌊√m⌋`) is the integer square root `Nat.nthRoot 2 m`, so it is computable in
polynomial time over `Turing.MultiTapeTM.encNat` by the integer root
`Turing.MultiTapeTM.ComputableInPolyTime.binary_nthRoot'` at exponent `2`.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.binary_sqrt`, `.binary_sqrt'`: plain polynomial-time
  floor square root `Nat.sqrt` over `encNat`.
* `Turing.MultiTapeTM.ComputableInPolyTime.binary_ceilSqrt`, `.binary_ceilSqrt'`: plain
  polynomial-time integer ceiling square root `if m = 0 then 0 else (m - 1).sqrt + 1` over `encNat`.
-/

public section

namespace Turing.MultiTapeTM

namespace ComputableInPolyTime

/-- Integer floor square root `Nat.sqrt` is polynomial-time on binary naturals. -/
@[fun_prop, program_certificate]
theorem binary_sqrt : ComputableInPolyTime Nat.sqrt encNat encNat := by
  refine (binary_nthRoot' (const 2) id').of_enc_eq fun m => congrArg encNat ?_
  exact (Nat.nthRoot_eq_of_le_of_lt (Nat.sqrt_le' m) (Nat.lt_succ_sqrt' m)).symm

/-- Integer ceiling square root is polynomial-time on binary naturals. -/
theorem binary_ceilSqrt :
    ComputableInPolyTime (fun m : ℕ => if m = 0 then 0 else (m - 1).sqrt + 1)
      encNat encNat := by
  have hcond : ComputableInPolyTime
      (fun m : ℕ => if decide (m ≤ 0) then 0 else (m - 1).sqrt + 1) encNat encNat :=
    (binary_le' id' (const 0)).ite' (const 0)
      (binary_add' (binary_sqrt.comp (binary_sub' id' (const 1))) (const 1))
  refine hcond.of_enc_eq fun m => congrArg encNat ?_
  simp only [Nat.le_zero, decide_eq_true_eq]

/-- Integer floor square root of a computed binary natural. -/
theorem binary_sqrt' {α : Type} {input : α ↪ List Bool} {f : α → ℕ}
    (hf : ComputableInPolyTime f input encNat) :
    ComputableInPolyTime (fun a => (f a).sqrt) input encNat :=
  binary_sqrt.comp hf

/-- Integer ceiling square root of a computed binary natural. -/
theorem binary_ceilSqrt' {α : Type} {input : α ↪ List Bool} {f : α → ℕ}
    (hf : ComputableInPolyTime f input encNat) :
    ComputableInPolyTime (fun a => if f a = 0 then 0 else (f a - 1).sqrt + 1) input encNat :=
  binary_ceilSqrt.comp hf

end ComputableInPolyTime

end Turing.MultiTapeTM
