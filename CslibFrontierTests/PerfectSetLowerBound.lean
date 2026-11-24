/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.SetLowerBound
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! The perfectly complete set lower bound protocol
([Arora and Barak, Exercise 8 §3][AroraBarak07]) on one family with threshold `K = 4` whose
certified sets have sizes `4`, `2` and `3`. The test `R (a, x) = a₀ ∨ x₀ ∨ (a₁ ∧ x₁)` on two-bit
strings `x` certifies all four strings when `a₀` holds, the two strings with `x₀` when neither
`a₀` nor `a₁` holds, and the three strings with `x₀ ∨ x₁` when only `a₁` holds. One verifier is
perfectly complete on the first input, sound on the second, and has no obligation on the third. -/

set_option linter.privateModule false

namespace CslibFrontierTests.PerfectSetLowerBound

open Cslib Cslib.Complexity Finset Turing.MultiTapeTM

/-- The test: `a₀ ∨ x₀ ∨ (a₁ ∧ x₁)`. -/
def test (x : List Bool × List Bool) : Bool :=
  x.1.getD 0 false || x.2.getD 0 false || (x.1.getD 1 false && x.2.getD 1 false)

theorem computableInPolyTime_test :
    ComputableInPolyTime test (encPair encBits encBits) encBool :=
  have h₁ (i : ℕ) := ComputableInPolyTime.bitsGetDWithInput
    (ComputableInPolyTime.fst encBits encBits) (ComputableInPolyTime.const (encOut := encUnary) i)
    false
  have h₂ (i : ℕ) := ComputableInPolyTime.bitsGetDWithInput
    (ComputableInPolyTime.snd encBits encBits) (ComputableInPolyTime.const (encOut := encUnary) i)
    false
  ComputableInPolyTime.bool_or' (ComputableInPolyTime.bool_or' (h₁ 0) (h₂ 0))
    (ComputableInPolyTime.bool_and' (h₁ 1) (h₂ 1))

/-- The certified set of `test` at `a`: the two-bit strings `x` with `test (a, x)`. -/
theorem card_certifiedSet_test (a : List Bool) :
    #(certifiedSet encBits 2 0 test a) = #{x : BitString 2 | test (a, List.ofFn x) = true} := by
  unfold certifiedSet
  generalize hk : (2 : Polynomial ℕ).eval (encBits a).length = k
  generalize hj : (0 : Polynomial ℕ).eval (encBits a).length = j
  obtain rfl : k = 2 := by simp [← hk]
  obtain rfl : j = 0 := by simp [← hj]
  congr 1
  refine filter_congr fun x _ => ?_
  simp

theorem card_S_true : #(certifiedSet encBits 2 0 test [true]) = 4 := by
  rw [card_certifiedSet_test]; decide

theorem card_S_false : #(certifiedSet encBits 2 0 test [false, false]) = 2 := by
  rw [card_certifiedSet_test]; decide

theorem card_S_middle : #(certifiedSet encBits 2 0 test [false, true]) = 3 := by
  rw [card_certifiedSet_test]; decide

/-- One verifier for the whole family: complete on `[true]` (`4 ≤ 4`), sound on
`[false, false]` (`2 · 2 ≤ 4`), and unconstrained on `[false, true]` (`2 < 3 < 4`). -/
example : ∃ (p q : Polynomial ℕ) (V : List Bool × List Bool → Bool),
    ComputableInPolyTime V (encPair encBits encBits) encBool ∧
    (∀ r : Fin (p.eval (encBits [true]).length) → Bool,
      ∃ y : Fin (q.eval (encBits [true]).length) → Bool,
        V ([true], List.ofFn r ++ List.ofFn y) = true) ∧
    2 * 2 ^ p.eval (encBits [false, false]).length ≤
      3 * #{r : Fin (p.eval (encBits [false, false]).length) → Bool |
        ∀ y : Fin (q.eval (encBits [false, false]).length) → Bool,
          V ([false, false], List.ofFn r ++ List.ofFn y) = false} := by
  obtain ⟨p, q, V, hV, h⟩ := exists_perfectlyComplete_verifier_of_card_certifiedSet
    (K := fun _ => 4) computableInPolyTime_test (.const _) fun _ => by norm_num
  refine ⟨p, q, V, hV, (h [true]).1 card_S_true.ge, (h [false, false]).2 ?_⟩
  rw [card_S_false]

/-- The middle input is neither complete nor sound for `K = 4`: `3 < 4` and `4 < 2 · 3`. -/
example : ¬ 4 ≤ #(certifiedSet encBits 2 0 test [false, true]) ∧
    ¬ 2 * #(certifiedSet encBits 2 0 test [false, true]) ≤ 4 := by
  rw [card_S_middle]
  decide

end CslibFrontierTests.PerfectSetLowerBound
