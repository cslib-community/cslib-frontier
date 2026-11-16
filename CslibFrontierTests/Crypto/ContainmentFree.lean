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
  `optSet v (1 + Nat.clog 2 v)` via `optSet_containmentFree`, plus the concrete Figure 14.2
  instance on `01001100` (with LSB-first checksum bits).
- Tightness and converse of the finite Sperner bound (`6 = 4.choose 2` fits, `7` cannot) via
  `exists_containmentFree_of_card_le` and `card_le_choose_half_of_containmentFree`.
- Concrete `horsSet 4 2` values, constant subset size via `card_horsSet`, containment freeness via
  `horsSet_containmentFree`, and cardinality failure when `2 ^ v > n.choose ℓ`.
- Counterexamples for each added hypothesis: `hinj` and `hcard` in
  `containmentFree_of_injective_of_card_eq`, `v < 2 ^ w` in `optSet_containmentFree`, and
  `2 ^ v ≤ n.choose ℓ` in `horsSet_containmentFree`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.

open Cslib.BitString
open Cslib.Crypto.OneTimeSignature

section ContainmentFreeTests

/-- `P_opt` with the book's `w = 1 + ⌈log₂ v⌉` satisfies `v < 2 ^ w` and is containment free for
every `v`. -/
example (v : ℕ) : ContainmentFree (optSet v (1 + Nat.clog 2 v)) :=
  optSet_containmentFree <| by
    rw [Nat.add_comm]
    exact (Nat.le_pow_clog (by decide) v).trans_lt
      (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))

/-- Concrete `P_opt` instance on the 8-bit message `01001100` from Figure 14.2 (p. 589). Because
`optWord` appends the 4-bit checksum `5 = 0101` LSB-first rather than MSB-first as drawn there, the
checksum indices are `{8, 10}` (`0`-indexed) rather than `{9, 11}`. -/
example :
    optSet 8 4 ![false, true, false, false, true, true, false, false] = {1, 4, 5, 8, 10} := by
  let m : Cslib.BitString 8 := ![false, true, false, false, true, true, false, false]
  have hcast : ∀ i : Fin 8, Fin.castAdd 4 i ∈ optSet 8 4 m ↔
      Fin.castAdd 4 i ∈ ({1, 4, 5, 8, 10} : Finset (Fin 12)) := by
    intro i
    rw [mem_optSet_castAdd]
    fin_cases i <;> decide
  have hnat : ∀ j : Fin 4, Fin.natAdd 8 j ∈ optSet 8 4 m ↔
      Fin.natAdd 8 j ∈ ({1, 4, 5, 8, 10} : Finset (Fin 12)) := by
    intro j
    rw [mem_optSet_natAdd]
    fin_cases j <;> decide
  ext k
  exact Fin.addCases hcast hnat k

/-- Sperner's upper bound is tight (`6 = 4.choose 2 < 7`): 6 messages fit, 7 cannot. -/
example : ∃ P : Fin 6 → Finset (Fin 4), ContainmentFree P :=
  exists_containmentFree_of_card_le (M := Fin 6) (n := 4) (by decide)

example : ¬ ∃ P : Fin 7 → Finset (Fin 4), ContainmentFree P :=
  fun ⟨P, hP⟩ => absurd (card_le_choose_half_of_containmentFree hP) (by decide)

/-- Fixed-size `horsSet` on 2-bit messages into 2-element subsets of `Fin 4`
(`2 ^ 2 ≤ 4.choose 2`), checking all four subsets, constant cardinality, and containment
freeness. -/
example : horsSet 4 2 (v := 2) ![false, false] = {2, 3} := by decide
example : horsSet 4 2 (v := 2) ![false, true] = {1, 3} := by decide
example : horsSet 4 2 (v := 2) ![true, false] = {1, 2} := by decide
example : horsSet 4 2 (v := 2) ![true, true] = {0, 3} := by decide

example (m : Cslib.BitString 2) : (horsSet 4 2 m).card = 2 :=
  card_horsSet (v := 2) (by decide) m

example : ContainmentFree (horsSet 4 2 (v := 2)) :=
  horsSet_containmentFree (by decide)

/-- Dropping `2 ^ v ≤ n.choose ℓ` breaks the constant-cardinality property of `horsSet` as well as
containment freeness (`2 ^ 2 > 2.choose 1`). -/
example : (horsSet 2 1 (v := 2) ![true, true]).card ≠ 1 := by decide

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
