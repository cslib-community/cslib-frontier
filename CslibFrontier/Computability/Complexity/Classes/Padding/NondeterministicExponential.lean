/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Padding.Language
public import CslibFrontier.Computability.Complexity.Classes.Padding.NondeterministicPolynomial
public import CslibFrontier.Computability.Complexity.Classes.Time
import CslibFrontier.Computability.Complexity.Classes.Time.Verifier
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolynomialPadding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.TwoPow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential
import Mathlib.Tactic.Linarith

/-!
# Polynomial padding into nondeterministic exponential time

If `A` is in `NTIME (2 ^ (n ^ k))` with `1 ≤ k`, its polynomially padded language with exponent
`k + 1` (`Cslib.Complexity.polynomialPadded`) is in `NTIME (2 ^ n)`: on a word `x`, decode
`y = unframe x`, test the padding in quadratic time, then guess a certificate for
`y` of length `2 ^ (|y| ^ k + O(1))`, which is at most a constant times `2 ^ (|x| / 2)` once
`|x| ≥ (|y| + 1) ^ (k + 1)`. The proof guesses and verifies with the linear-time verifier of `A`
(`Cslib.Complexity.setOf_exists_mem_NTIME`, `Cslib.Complexity.exists_verifier_of_mem_NTIME`), as
for the polynomial padding in
`CslibFrontier.Computability.Complexity.Classes.Padding.NondeterministicPolynomial`.

## Main results

* `Cslib.Complexity.polynomialPadded_mem_NTIME_two_pow`: padding into `NTIME (2 ^ n)`.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- **Padding into nondeterministic time `2 ^ n`.** If `A` is in nondeterministic time
`O(2 ^ (n ^ k))`, with `1 ≤ k`, then its padded language with exponent `k + 1` is in
nondeterministic time `O(2 ^ n)`. Membership is decided through the total decoder `unframe`, which
reads pairs `true, b` from the start of a word and stops at the first other symbol or at the end,
so every word decodes: `x` is in the padded language exactly when `unframe x ∈ A` and
`((unframe x).length + 1) ^ (k + 1) ≤ x.length`. A word `frame y ++ 1 ^ L` is one such word; a
word with no terminating frame bit is another, e.g. `[true]` decodes to `[]` and lies in
`polynomialPadded Set.univ 2`. -/
theorem polynomialPadded_mem_NTIME_two_pow {A : Set (List Bool)} {k : ℕ} (hk : 1 ≤ k)
    (hA : A ∈ NTIME encBits (fun n => 2 ^ n ^ k)) :
    polynomialPadded A (k + 1) ∈ NTIME encBits (fun n => 2 ^ n) := by
  classical
  obtain ⟨V, c, hV, hc⟩ := exists_verifier_of_mem_NTIME hA
  let guard (x : List Bool) : Bool := decide (((unframe x).length + 1) ^ (k + 1) ≤ x.length)
  let e (x : List Bool) : ℕ := (unframe x).length ^ k + (c + 1)
  let ℓ (x : List Bool) : ℕ := if guard x then 2 ^ e x else 0
  let V' (p : List Bool × List Bool) : Bool := if guard p.1 then V (unframe p.1, p.2) else false
  have hL (m : ℕ) : c * 2 ^ m ^ k + c ≤ 2 ^ (m ^ k + (c + 1)) := by
    have hc' : c ≤ 2 ^ c := Nat.lt_two_pow_self.le
    have h1 : 1 ≤ 2 ^ m ^ k := Nat.one_le_two_pow
    calc c * 2 ^ m ^ k + c
        ≤ 2 ^ c * 2 ^ m ^ k + 2 ^ c * 2 ^ m ^ k :=
          Nat.add_le_add (Nat.mul_le_mul_right _ hc') (hc'.trans (Nat.le_mul_of_pos_right _ h1))
      _ = 2 ^ (m ^ k + (c + 1)) := by ring
  have hset : polynomialPadded A (k + 1) =
      {x | ∃ w : List Bool, w.length = ℓ x ∧ V' (x, w) = true} :=
    polynomialPadded_eq_setOf_exists (t := fun n => 2 ^ n ^ k)
      (Lc := fun m => 2 ^ (m ^ k + (c + 1))) hc hL
  rw [hset]
  have hepoly : ComputableInPolyTime e encBits encUnary := by
    simp only [e]
    fun_prop
  obtain ⟨C₂, hexp⟩ := hepoly.exists_computableInO_unary_two_pow
  have hguard := computableInO_polynomialPaddingGuard (k + 1)
  have hℓ := hguard.ite hexp (ComputableInO.const (encIn := encBits) (encMid := encUnary) 0)
  have hpair := (ComputableInO.unframe.comp (ComputableInO.fst encBits encBits)).prod
    (ComputableInO.snd encBits encBits)
  have hV' := (hguard.comp (ComputableInO.fst encBits encBits)).ite (hV.comp hpair)
    (ComputableInO.const (encIn := encPair encBits encBits) (encMid := encBool) false)
  obtain ⟨CQ, hCQ⟩ := Cslib.PolynomiallyBounded.exists_le_mul_two_pow
    (p := fun n => 14 * (n + 1) ^ 2) (by fun_prop)
  refine setOf_exists_mem_NTIME (ℓ := ℓ) (V := V') hℓ hV'
    (C := CQ + C₂ + 4 ^ (c + 1) + 4 * 2 ^ (c + 1)) fun x w hw => ?_
  simp only [Function.comp_apply, encBits_apply, length_encPair] at hw ⊢
  set n := x.length with hn
  set m := (unframe x).length with hm
  have hmn : m ≤ n := length_unframe_le x
  have hQ : 14 * (n + 1) ^ 2 ≤ CQ * 2 ^ n := hCQ n
  by_cases hg : (m + 1) ^ (k + 1) ≤ n
  · simp only [ℓ, guard, ← hn, ← hm, decide_eq_true_eq, hg, ↓reduceIte] at hw ⊢
    -- the padding pays for the certificate: `2 * m ^ k ≤ n`
    have hmk : 2 * m ^ k ≤ n := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · simp [h0, Nat.zero_pow (by omega : 0 < k)]
      · calc 2 * m ^ k ≤ (m + 1) * (m + 1) ^ k :=
            Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) k)
          _ = (m + 1) ^ (k + 1) := (pow_succ' _ _).symm
          _ ≤ n := hg
    have hs : m ^ k ≤ n := by omega
    have hex : e x = m ^ k + (c + 1) := rfl
    have h2e : 2 ^ e x ≤ 2 ^ (c + 1) * 2 ^ n := by
      rw [hex, pow_add, Nat.mul_comm]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hs)
    have h4e : 4 ^ e x ≤ 4 ^ (c + 1) * 2 ^ n := by
      rw [hex, pow_add, Nat.mul_comm]
      refine Nat.mul_le_mul_left _ ?_
      calc 4 ^ m ^ k = 2 ^ (2 * m ^ k) := by rw [pow_mul]; norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hmk
    have hsq : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    nlinarith [Nat.zero_le (CQ + C₂ + 4 ^ (c + 1) + 4 * 2 ^ (c + 1))]
  · simp only [ℓ, guard, ← hn, ← hm, decide_eq_true_eq, hg, ↓reduceIte] at hw ⊢
    rw [hw]
    have hsq : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    nlinarith [Nat.zero_le ((C₂ + 4 ^ (c + 1) + 4 * 2 ^ (c + 1)) * 2 ^ n),
      Nat.zero_le (CQ + C₂ + 4 ^ (c + 1) + 4 * 2 ^ (c + 1))]

end Cslib.Complexity
