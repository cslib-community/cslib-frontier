/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Time
public import Mathlib.Computability.Primrec.Basic
public import Mathlib.Logic.Function.Iterate

/-!
# Ackermann time

`Cslib.Complexity.Ack` is the class of problems decidable in time bounded by the diagonal
fast-growing function applied to a primitive-recursive function of the input length
[Schmitz, Sections 2.2 and 2.3][Schmitz2016].
-/

public section

namespace Cslib.Complexity

/-- The finite levels of Schmitz's fast-growing hierarchy. Level zero is successor, and level
`k + 1` at input `n` iterates level `k` exactly `n + 1` times starting at `n`. -/
def fastGrowing : ℕ → ℕ → ℕ
  | 0 => Nat.succ
  | k + 1 => fun n => (fastGrowing k)^[n + 1] n

/-- Ackermann time uses the limit level `ω` with fundamental sequence `ω[n] = n + 1`,
composed with a primitive-recursive bound on the encoded input length. -/
def Ack {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ p : ℕ → ℕ, Nat.Primrec p ∧ A ∈ DTIME enc (fun n => fastGrowing (p n + 1) (p n))}

end Cslib.Complexity
