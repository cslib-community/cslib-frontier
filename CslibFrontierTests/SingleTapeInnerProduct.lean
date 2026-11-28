/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Machines.Turing.SingleTape.InnerProduct
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum

/-!
# Native single-tape inner-product lower bound clients

These ordinary module clients check the unmarked binary language at empty, odd and even lengths,
the parity and position of common one-bits, zero padding on both halves, and the explicit native
time lower bound. The average-bound client uses individual native halting times even when
the hypothetical correctness certificate supplies an arbitrary global time bound.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.SingleTapeInnerProduct

open Cslib Cslib.Turing SingleTapeTM Matrix

example : ([] : List Bool) ∉ Cslib.Language.innerProduct := by decide

example : [true, true] ∈ Cslib.Language.innerProduct := by decide

example : [true, false] ∉ Cslib.Language.innerProduct := by decide

/-- An odd-length input is rejected even if the two inspected bits would agree. -/
example : [true, true, true] ∉ Cslib.Language.innerProduct := by decide

/-- Two common one-bits cancel modulo two. -/
example : [true, true, true, true] ∉ Cslib.Language.innerProduct := by decide

example : [true, false, true, false] ∈ Cslib.Language.innerProduct := by decide

/-- Equal Hamming weights do not replace coordinatewise alignment. -/
example : [true, false, false, true] ∉ Cslib.Language.innerProduct := by decide

/-- Zero padding on both halves preserves a nonzero inner product. -/
example : [true] ++ List.replicate 3 false ++ ([true] ++ List.replicate 3 false) ∈
    Cslib.Language.innerProduct := by decide

/-- With empty active blocks, padding alone cannot produce inner product one. -/
example : List.replicate 3 false ++ List.replicate 3 false ∉
    Cslib.Language.innerProduct := by decide

/-- Fixing odd-product suffixes complements, rather than preserves, the active inner product. -/
example (x y : BitString 3) :
    List.ofFn x ++ [true] ++ (List.ofFn y ++ [true]) ∈ Cslib.Language.innerProduct ↔
      x ⬝ᵥ y = false := by
  simpa [dotProduct, Fin.sum_univ_one, Bool.mul_eq_and] using
    Cslib.Language.ofFn_blocks_mem_innerProduct_iff x (fun _ : Fin 1 => true) y
      (fun _ : Fin 1 => true)

/-- A concrete native machine lets the client evaluate the state-dependent constant. -/
private def haltMachine : SingleTapeTM Bool where
  State := Unit
  q₀ := ()
  tr _ s := (⟨s, none⟩, none)

/-- The native theorem rules out a linear-time certificate using the computed state constant. -/
example : ¬ haltMachine.DecidesByHeadInTime id Cslib.Language.innerProduct true
    (fun n => n + 1) := by
  intro hdec
  have hd : Nat.clog 2 (Fintype.card haltMachine.State + 2) = 2 := by decide
  have h := innerProduct_lower_bound hdec (n := 128) (by rw [hd]; decide)
  rw [hd] at h
  norm_num at h

/-- The average ranges over the full input space, including nonzero suffixes and both verdicts. -/
example : (∑ p : BitString 2 × BitString 2, if p.1 ⬝ᵥ p.2 then (1 : ℕ) else 0) = 6 := by
  decide +kernel

private def alwaysYes : SingleTapeTM Bool where
  State := Unit
  q₀ := ()
  tr _ _ := (⟨true, none⟩, none)

/-- Individual native halting times remain informative even with an arbitrary global clock. -/
example (T : ℕ → ℕ) :
    ¬ alwaysYes.DecidesByHeadInTime id Cslib.Language.innerProduct true T := by
  intro hdec
  have hd : Nat.clog 2 (Fintype.card alwaysYes.State + 2) = 2 := by decide
  have hlarge (n : ℕ) (hn : 12 ≤ n) : (2 * n) ^ 2 ≤ 128 := by
    have h := innerProduct_average_lower_bound hdec (n := n) (by rw [hd]; exact hn)
      (fun _ => 1) (fun _ => rfl)
    rw [hd] at h
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin, Nat.nsmul_eq_mul, mul_one, ← pow_add,
      ← two_mul] at h
    apply Nat.le_of_mul_le_mul_left (c := 2 ^ (2 * n)) ?_ (by positivity)
    simpa only [show 64 * 2 = 128 from rfl, Nat.mul_comm] using h
  have h := hlarge 12 le_rfl
  norm_num at h

end CslibFrontierTests.SingleTapeInnerProduct
