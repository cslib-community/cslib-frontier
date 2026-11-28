/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module

public import CslibFrontier.Computability.BranchingProgram.ReadOnceParity
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Pi

/-! Concrete `module` clients for syntactic read-once parity branching programs: wire counts,
routes, the read-once condition, and cancelling parallel wires (`NBP.reduce`). -/

public section

namespace CslibFrontierTests.ReadOnceParityBranchingProgram

open Cslib.BranchingPrograms

/-! ### 1. Exclusive disjunction -/

/-- Two parallel contacts `x 0` and `x 1` from the source to the target. -/
def xorProgram : NBP (Fin 2) Bool 2 :=
  .node .target [⟨0, some (0, true)⟩, ⟨0, some (1, true)⟩]

example : xorProgram.wireCount = 2 := by
  decide

/-- Each of its two routes tests one coordinate. -/
example : xorProgram.routes = [[(0, true)], [(1, true)]] := by
  decide

example : xorProgram.IsReadOnce := by
  decide

example : ∀ x : Fin 2 → Bool, xorProgram.AcceptsParity x ↔ (x 0 ^^ x 1) = true := by
  decide

/-! ### 2. Inner product modulo two -/

/-- `x 0 * x 1 + x 2 * x 3` over `F₂`: two routes through the middle nodes `2` and `1`, which test
disjoint pairs of coordinates. Node `3` is the source and node `0` the target. -/
def innerProduct : NBP (Fin 4) Bool 4 :=
  NBP.target
    |>.node [⟨0, some (3, true)⟩]
    |>.node [⟨0, some (1, true)⟩]
    |>.node [⟨2, some (0, true)⟩, ⟨1, some (2, true)⟩]

example : innerProduct.IsReadOnce := by
  decide

example : innerProduct.wireCount = 4 := by
  decide

example : ∀ x : Fin 4 → Bool,
    innerProduct.AcceptsParity x ↔ ((x 0 && x 1) ^^ (x 2 && x 3)) = true := by
  decide

/-! ### 3. A program that is not read-once -/

/-- A rectifier and a negated contact in parallel, followed by a contact: `x 0` on both layers.
It computes `x 0 && x 0`, but its route through the negated contact tests `x 0` twice. -/
def twice : NBP (Fin 1) Bool 3 :=
  NBP.target
    |>.node [⟨0, some (0, true)⟩]
    |>.node [⟨1, none⟩, ⟨1, some (0, false)⟩]

/-- The read-once condition is syntactic: the route testing `x 0 = false` and then `x 0 = true` is
switched on by no input, but it still tests `x 0` twice. -/
example : ¬ twice.IsReadOnce := by
  decide

example : ∀ x : Fin 1 → Bool, twice.AcceptsParity x ↔ x 0 = true := by
  decide

/-! ### 4. Cancelling parallel wires -/

/-- Three copies of the contact `x 0` and two of the contact `x 1`. -/
def parallel : NBP (Fin 2) Bool 2 :=
  .node .target [⟨0, some (0, true)⟩, ⟨0, some (1, true)⟩, ⟨0, some (0, true)⟩,
    ⟨0, some (0, true)⟩, ⟨0, some (1, true)⟩]

/-- Pairs of parallel copies cancel: one copy of `x 0` remains. -/
example : parallel.reduce.wireCount = 1 := by
  decide

example : ∀ x : Fin 2 → Bool, parallel.AcceptsParity x ↔ x 0 = true := by
  decide

example (x : Fin 2 → Bool) : parallel.reduce.AcceptsParity x ↔ parallel.AcceptsParity x :=
  parallel.acceptsParity_reduce_iff x

example : parallel.IsReadOnce := by
  decide

example : parallel.reduce.IsReadOnce :=
  NBP.IsReadOnce.reduce (by decide)

/-- On two nodes with two Boolean coordinates at most `2 ^ 2 * (2 * 2 + 1) = 20` wires remain. -/
example : parallel.reduce.wireCount ≤ 2 ^ 2 * (Fintype.card (Fin 2) * Fintype.card Bool + 1) :=
  NBP.wireCount_reduce_le parallel

end CslibFrontierTests.ReadOnceParityBranchingProgram
