/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.OneTimeSignature.ContainmentFree
import Mathlib.Tactic.FinCases

/-!
# Tests for containment-free encodings

Concrete checks and hypothesis counterexamples for
`CslibFrontier.Crypto.Computational.OneTimeSignature.ContainmentFree`:
- The book's `w = 1 + Nat.clog 2 v` satisfies `v < 2 ^ w`, yielding containment freeness of
  `optSet v (1 + Nat.clog 2 v)` via `optSet_containmentFree`.
- Positive instantiations of `card_le_choose_half_of_containmentFree`,
  `exists_containmentFree_of_card_le`, `horsSet_containmentFree`, `optWord_polyTime`, and
  `horsWord_polyTime`.
- Counterexamples for each added hypothesis: `hinj` and `hcard` in
  `containmentFree_of_injective_of_card_eq`, `v < 2 ^ w` in `optSet_containmentFree`, and
  `2 ^ v ≤ n.choose ℓ` in `horsSet_containmentFree`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.

open Cslib.BitString
open Cslib.Crypto.OneTimeSignature
open Turing.MultiTapeTM

section ContainmentFreeTests

/-- The book's `w = 1 + ⌈log₂ v⌉` satisfies `v < 2 ^ w`. -/
example (v : ℕ) : v < 2 ^ (1 + Nat.clog 2 v) := by
  rw [Nat.add_comm]
  exact (Nat.le_pow_clog (by decide) v).trans_lt
    (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))

/-- Hence `P_opt` with `w = 1 + Nat.clog 2 v` is containment free for every `v`. -/
example (v : ℕ) : ContainmentFree (optSet v (1 + Nat.clog 2 v)) :=
  optSet_containmentFree <| by
    rw [Nat.add_comm]
    exact (Nat.le_pow_clog (by decide) v).trans_lt
      (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))

/-- Sperner's upper bound and its converse on concrete sizes (`6 = 4.choose 2`). -/
example : ∃ P : Fin 6 → Finset (Fin 4), ContainmentFree P :=
  exists_containmentFree_of_card_le (M := Fin 6) (n := 4) (by decide)

example {P : Fin 6 → Finset (Fin 4)} (hP : ContainmentFree P) :
    Fintype.card (Fin 6) ≤ (Fintype.card (Fin 4)).choose (Fintype.card (Fin 4) / 2) :=
  card_le_choose_half_of_containmentFree hP

/-- Fixed-size `horsSet` on 2-bit messages into 2-element subsets of `Fin 4`
(`2 ^ 2 ≤ 4.choose 2`). -/
example : ContainmentFree (horsSet 4 2 (v := 2)) :=
  horsSet_containmentFree (by decide)

/-- Efficiency certificates typecheck on the public encoders. -/
example : ComputableInPolyTime (fun p : ℕ × List Bool => optWord p.1 p.2)
    (encPair encUnary encBits) encBits :=
  optWord_polyTime

example : ComputableInPolyTime (fun p : (ℕ × ℕ) × List Bool => horsWord p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary encUnary) encBits) encBits :=
  horsWord_polyTime

/-- Dropping `hinj` from `containmentFree_of_injective_of_card_eq` fails even with
constant size. -/
example : ¬ ContainmentFree (fun _ : Fin 2 => (Finset.univ : Finset (Fin 1))) := by
  intro h
  exact h (by decide : (0 : Fin 2) ≠ 1) (by decide)

/-- Dropping constant cardinality from `containmentFree_of_injective_of_card_eq` fails even if
injective. -/
example :
    ¬ ContainmentFree (fun m : Fin 2 => if m = 0 then (∅ : Finset (Fin 1)) else Finset.univ) := by
  intro h
  exact h (by decide : (0 : Fin 2) ≠ 1) (by decide)

/-- `optSet_containmentFree` fails when `¬ v < 2 ^ w` (`v = 2`, `w = 1`: `count false` wraps
mod `2`). -/
example : ¬ ContainmentFree (optSet 2 1) := by
  intro h
  have hne : (![false, false] : Cslib.BitString 2) ≠ ![true, false] := by
    intro heq
    have := congrFun heq 0
    simp at this
  apply h hne
  intro x hx
  fin_cases x
  · change Fin.castAdd 1 (0 : Fin 2) ∈ optSet 2 1 ![true, false]
    change Fin.castAdd 1 (0 : Fin 2) ∈ optSet 2 1 ![false, false] at hx
    rw [mem_optSet_castAdd] at hx
    simp at hx
  · change Fin.castAdd 1 (1 : Fin 2) ∈ optSet 2 1 ![true, false]
    change Fin.castAdd 1 (1 : Fin 2) ∈ optSet 2 1 ![false, false] at hx
    rw [mem_optSet_castAdd] at hx
    simp at hx
  · change Fin.natAdd 2 (0 : Fin 1) ∈ optSet 2 1 ![true, false]
    rw [mem_optSet_natAdd]
    decide

/-- `horsSet_containmentFree` fails when `¬ 2 ^ v ≤ n.choose ℓ` (`n = 2`, `ℓ = 1`, `v = 2`). -/
example : ¬ ContainmentFree (horsSet 2 1 (v := 2)) := by
  intro h
  have hne : (![true, false] : Cslib.BitString 2) ≠ ![true, true] := by
    intro heq
    have := congrFun heq 1
    simp at this
  exact h hne (by decide)

end ContainmentFreeTests
