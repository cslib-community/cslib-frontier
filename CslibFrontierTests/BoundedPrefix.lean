/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.BoundedPrefix
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Tactic.PolyTime

/-!
# Tests for bounded-prefix multi-tape Turing computation

Non-vacuous checked regression test exercising
`Turing.MultiTapeTM.computableInTimeAndSpace_boundedPrefix`: a function inspecting only a
polynomially capped prefix of a second binary argument runs on a single fixed machine whose
worst-case time and space depend solely on `|enc a|`, even against arbitrarily oversized inputs.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.BoundedPrefix

open Cslib Turing.MultiTapeTM

def boundedPrefixMatch (p : List Bool × List Bool) : Bool :=
  decide (p.2.length ≤ p.1.length) && (p.2.take p.1.length == p.1)

theorem polyTime_boundedPrefixMatch :
    ComputableInPolyTime boundedPrefixMatch (encPair encBits encBits) encBool := by
  unfold boundedPrefixMatch
  fun_prop

theorem boundedPrefixMatch_take (a raw : List Bool) :
    boundedPrefixMatch (a, raw) = boundedPrefixMatch (a, raw.take (a.length + 1)) := by
  by_cases hle : raw.length ≤ a.length
  · rw [List.take_of_length_le (hle.trans (Nat.le_succ _))]
  · have hgt : a.length < raw.length := Nat.lt_of_not_ge hle
    have htakeLen : (raw.take (a.length + 1)).length = a.length + 1 := by
      simp [List.length_take, hgt]
    simp [boundedPrefixMatch, hle, htakeLen]

example :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : Turing.MultiTapeTM k Bool State)
      (t s : ℕ → ℕ),
      PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
      (∀ (a : List Bool) (N : ℕ),
        tm.ComputesInTimeAndSpace
          (encPair encBits encBits (a, List.replicate N true))
          (encBool (boundedPrefixMatch (a, List.replicate N true)))
          (t a.length) (s a.length)) ∧
      tm.ComputesInTimeAndSpace
        (encPair encBits encBits ([true, false], List.replicate 1000 true))
        (encBool false) (t 2) (s 2) := by
  obtain ⟨k, State, hfin, tm, t, s, ht, hs, hrun⟩ :=
    computableInTimeAndSpace_boundedPrefix
      (encA := encBits) (encB := encBool) (cap := List.length)
      ComputableInPolyTime.length_bits polyTime_boundedPrefixMatch boundedPrefixMatch_take
  refine ⟨k, State, hfin, tm, t, s, ht, hs, fun a N => hrun (a, List.replicate N true), ?_⟩
  have hfalse : boundedPrefixMatch ([true, false], List.replicate 1000 true) = false := by
    unfold boundedPrefixMatch
    rw [show decide ((List.replicate 1000 true).length ≤ [true, false].length) = false by
      rw [List.length_replicate]; decide]
    rfl
  have hgoal := hrun ([true, false], List.replicate 1000 true)
  rwa [hfalse] at hgoal

end CslibFrontierTests.BoundedPrefix
