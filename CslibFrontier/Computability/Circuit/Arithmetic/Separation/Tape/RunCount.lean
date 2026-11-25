/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Tape.RunSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# The sizes of the clause sum of a run

If the alphabet, the tapes, the states, the inputs, the steps and the places are at most `B`, then
the letters are at most `4 B²` (`card_letter_le`), the hidden variables at most `6 B²`
(`RunVar.card_le`), their one-hot bits at most `9 B³` (`card_sigma_dom_le`), the weighted clauses at
most `4 B⁵` (`RunStep.card_le`) and the forbidding clauses at most `25 B⁵` (`RunRule.card_le`).

## Main results

* `Tape.Ch.card`, `Tape.card_letter_le`, `Tape.RunVar.card_le`, `Tape.card_sigma_dom_le`,
  `Tape.RunStep.card_le`, `Tape.RunRule.card_le`, `Tape.length_wordOf_ofFn`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  module `Nc.RunPerm`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Tape

open Finset

theorem Ch.card (S : Type) [Fintype S] (n : ℕ) :
    Fintype.card (Ch S (Fin n)) = 2 * Fintype.card S + n := by
  rw [Fintype.card_congr (chSumEquiv S (Fin n)), Fintype.card_sum, Fintype.card_prod,
    Fintype.card_bool, Fintype.card_fin]
  ring

variable {Γ S Q : Type} [Fintype Γ] [Fintype S] [Fintype Q] {n t M B : ℕ}

theorem card_letter_le (hΓ : Fintype.card Γ ≤ B) (hS : Fintype.card S ≤ B) (hn : n ≤ B)
    (hB : 1 ≤ B) : Fintype.card (Letter S (Fin n) Γ) ≤ 4 * B ^ 2 := by
  rw [Fintype.card_option, Fintype.card_prod, Ch.card]
  calc (2 * Fintype.card S + n) * Fintype.card Γ + 1 ≤ (2 * B + B) * B + 1 * 1 := by gcongr
    _ ≤ (2 * B + B) * B + B * B := by gcongr
    _ = 4 * B ^ 2 := by ring

theorem RunVar.card_le (hS : Fintype.card S ≤ B) (hn : n ≤ B) (ht : t + 1 ≤ B)
    (hM : M ≤ B) : Fintype.card (RunVar S n t M) ≤ 6 * B ^ 2 := by
  rw [RunVar.card]
  calc t + (t + 1) + (2 * Fintype.card S + n) * (t + 1) + Fintype.card S * M
      ≤ B * 1 + B * 1 + (2 * B + B) * B + B * B := by
        have : 1 ≤ B := by omega
        gcongr <;> omega
    _ ≤ B * B + B * B + (2 * B + B) * B + B * B := by
        have : 1 ≤ B := by omega
        gcongr
    _ = 6 * B ^ 2 := by ring

/-- The one-hot bits as a sum of products. -/
private def RunVar.equivSigma (Γ S Q : Type) (n t M : ℕ) :
    (Σ d : RunVar S n t M, d.Dom Γ Q) ≃ (Fin t × Letter S (Fin n) Γ) ⊕ (Fin (t + 1) × Q) ⊕
      ((Ch S (Fin n) × Fin (t + 1)) × Fin M) ⊕ ((S × Fin M) × Option Γ) where
  toFun
    | ⟨.letter τ, a⟩ => .inl (τ, a)
    | ⟨.state τ, q⟩ => .inr (.inl (τ, q))
    | ⟨.place z τ, m⟩ => .inr (.inr (.inl ((z, τ), m)))
    | ⟨.content s p, y⟩ => .inr (.inr (.inr ((s, p), y)))
  invFun
    | .inl (τ, a) => ⟨.letter τ, a⟩
    | .inr (.inl (τ, q)) => ⟨.state τ, q⟩
    | .inr (.inr (.inl ((z, τ), m))) => ⟨.place z τ, m⟩
    | .inr (.inr (.inr ((s, p), y))) => ⟨.content s p, y⟩
  left_inv := by rintro ⟨_ | _ | _ | _, _⟩ <;> rfl
  right_inv := by rintro (⟨_, _⟩ | ⟨_, _⟩ | ⟨⟨_, _⟩, _⟩ | ⟨⟨_, _⟩, _⟩) <;> rfl

theorem card_sigma_dom_le
    (hΓ : Fintype.card Γ + 1 ≤ B) (hS : Fintype.card S ≤ B) (hQ : Fintype.card Q ≤ B)
    (hn : n ≤ B) (ht : t + 1 ≤ B) (hM : M ≤ B) :
    Fintype.card (Σ d : RunVar S n t M, d.Dom Γ Q) ≤ 9 * B ^ 3 := by
  have hB : 1 ≤ B := by omega
  have hL := card_letter_le (Γ := Γ) (S := S) (n := n) (by omega) hS hn (by omega)
  have h : Fintype.card (Σ d : RunVar S n t M, d.Dom Γ Q) =
      t * Fintype.card (Letter S (Fin n) Γ) + ((t + 1) * Fintype.card Q +
        (((2 * Fintype.card S + n) * (t + 1)) * M +
          (Fintype.card S * M) * (Fintype.card Γ + 1))) := by
    rw [Fintype.card_congr (RunVar.equivSigma Γ S Q n t M)]
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_option, Ch.card]
  rw [h]
  calc _ ≤ B * (4 * B ^ 2) + (B * B * 1 + (((2 * B + B) * B) * B + (B * B) * B)) := by
        rw [mul_one]
        gcongr
        omega
    _ ≤ B * (4 * B ^ 2) + (B * B * B + (((2 * B + B) * B) * B + (B * B) * B)) := by gcongr
    _ = 9 * B ^ 3 := by ring

theorem RunStep.card_le (hΓ : Fintype.card Γ + 1 ≤ B) (hS : Fintype.card S ≤ B)
    (hQ : Fintype.card Q ≤ B) (hn : n ≤ B) (ht : t ≤ B) :
    Fintype.card (RunStep Γ S Q n t) ≤ 4 * B ^ 5 := by
  have hL := card_letter_le (Γ := Γ) (S := S) (n := n) (by omega) hS hn (by omega)
  rw [RunStep.card]
  calc _ ≤ B * (4 * B ^ 2 * (B * B)) := by gcongr
    _ = 4 * B ^ 5 := by ring

theorem RunRule.card_le (hΓ : Fintype.card Γ + 1 ≤ B) (hS : Fintype.card S ≤ B) (hn : n ≤ B)
    (ht : t ≤ B) (hM : M ≤ B) : Fintype.card (RunRule Γ S n t M) ≤ 25 * B ^ 5 := by
  have hB : 1 ≤ B := by omega
  have hL := card_letter_le (Γ := Γ) (S := S) (n := n) (by omega) hS hn (by omega)
  have hΓ' : Fintype.card Γ ≤ B := by omega
  have h (k : ℕ) (hk : k ≤ 5) : B ^ k ≤ B ^ 5 := Nat.pow_le_pow_right hB hk
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  have h3 := h 3 (by omega)
  have h4 := h 4 (by omega)
  rw [RunRule.card]
  calc _ ≤ 2 + (2 * B + B) + (2 * B + B) * (B * (B * (4 * B ^ 2))) + B * (B * B) +
        B * (2 * (B * (B * B))) + B * (2 * (B * B)) + B * (B * (B * B)) + B * B := by gcongr
    _ = 2 * B ^ 0 + 3 * B ^ 1 + 12 * B ^ 5 + 3 * B ^ 3 + 3 * B ^ 4 + B ^ 2 := by ring
    _ ≤ 25 * B ^ 5 := by omega

omit [Fintype Γ] in
/-- The total length of the words with their separators. -/
theorem length_wordOf_ofFn (u : Fin n → List Γ) :
    (wordOf (List.ofFn u)).length = (∑ j, (u j).length) + n := by
  rw [length_wordOf, List.map_ofFn, List.sum_ofFn, List.length_ofFn]
  rfl

end Cslib.Circuits.Arithmetic.Separation.Tape
