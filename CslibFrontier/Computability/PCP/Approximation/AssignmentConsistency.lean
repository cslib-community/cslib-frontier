/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership

/-!
# Consistency of finite partial Boolean assignments

A partial assignment is represented as a list of variable indices and their Boolean values.
`Cslib.Complexity.SAT.consistentLits` checks whether two such lists agree wherever they both
assign a value. Testing a list against itself detects conflicting repetitions. The check is
polynomial-time with binary indices.
-/

public section

namespace Cslib.Complexity.SAT

open Turing.MultiTapeTM

/-- Two partial assignments, given as lists of literals `(x, b)` read as `x := b`, are
**consistent** when they give no variable two different values. -/
@[expose]
def consistentLits (ρ ρ' : List (ℕ × Bool)) : Bool :=
  ρ.all fun l => ρ'.all fun l' => !(l.1 == l'.1) || l.2 == l'.2

/-- The checker succeeds exactly when shared variables have the same value. -/
theorem consistentLits_eq_true_iff {ρ ρ' : List (ℕ × Bool)} :
    consistentLits ρ ρ' = true ↔ ∀ l ∈ ρ, ∀ l' ∈ ρ', l.1 = l'.1 → l.2 = l'.2 := by
  simp only [consistentLits, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, beq_iff_eq]
  exact forall₂_congr fun _ _ => forall₂_congr fun _ _ => Decidable.imp_iff_not_or.symm

/-- Consistency is decidable in polynomial time in the encoded lists, using binary variable
indices. -/
@[fun_prop]
theorem computableInPolyTime_consistentLits :
    ComputableInPolyTime (fun p : List (ℕ × Bool) × List (ℕ × Bool) => consistentLits p.1 p.2)
      (encPair (encList (encPair encNat encBool)) (encList (encPair encNat encBool))) encBool := by
  unfold consistentLits
  fun_prop

end Cslib.Complexity.SAT
