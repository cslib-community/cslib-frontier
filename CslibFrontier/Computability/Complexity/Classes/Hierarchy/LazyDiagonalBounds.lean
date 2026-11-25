/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
import Mathlib.Tactic.Ring

/-!
# Shared arithmetic bounds for lazy diagonalization

This module provides the shared arithmetic estimates used by the polynomial and exponential
nondeterministic time hierarchy proofs (`NondeterministicTime` and
`NondeterministicExponentialTime`) to bound the universal simulation and the verifier branch
tests.

## Main results

* `Cslib.Complexity.LazyDiagonal.accBound_aux`: bounds the universal simulation time and space
  by `K * (X ^ 4 * Y ^ 2)`.
* `Cslib.Complexity.LazyDiagonal.cheap_aux`: bounds the verifier branch-test overhead by a
  multiple of `(N + 1) ^ 2 * Y ^ 2`.
* `Cslib.Complexity.LazyDiagonal.acceptance_input_bound`: control the simulation input
  factor from a linear description bound and certificate length.
* `Cslib.Complexity.LazyDiagonal.verifier_branch_bound`: combine branch-sensitive costs
  with the independently established certificate, test, simulation and search estimates.
* `Cslib.Complexity.LazyDiagonal.brute_bound_aux`: bound the exponential brute-force search
  step in the exponential nondeterministic time hierarchies.
-/

public section

namespace Cslib.Complexity.LazyDiagonal

/-- The numeric core of the resources of the simulation: for an encoded input of length `N`, a
decoding time `A`, a word `W = frame y ++ v`, a decoded description of encoded length `Dl`, encoded
symbols of length `Nl`, a clock `Y` of `Ll` binary digits and a result of encoded length `E`,
everything is within `K * X ^ 4 * Y ^ 2`. -/
theorem accBound_aux (d cD cO : ℕ) : ∃ K, ∀ {N A W Dl Nl Ll X Y E : ℕ},
    N ≤ 2 * X → A ≤ X → W ≤ 2 * X → Dl ≤ cD * (N + A + 1) → Nl ≤ 3 * W →
    Ll ≤ (d + 4) * X → 1 ≤ X → 1 ≤ Y →
    E ≤ cO * (N + A + (N + W + (N + Y)) + (2 * Dl + 1 + (2 * Nl + 1 + Ll) + 1) ^ 2 * (Y + 1) + 1) →
    N + A + (N + W + (N + Y)) + (2 * Dl + 1 + (2 * Nl + 1 + Ll) + 1) ^ 4 * (Y + 1) ^ 2 +
        (E + 1) ^ 2 + 1 ≤ K * (X ^ 4 * Y ^ 2) ∧
      N + A + (N + W + (N + Y)) + (2 * Dl + 1 + (2 * Nl + 1 + Ll) + 1) ^ 2 * (Y + 1) + E + 1 ≤
        K * (X ^ 4 * Y ^ 2) := by
  set C₁ := 8 * cD + d + 19
  set C₂ := 11 + 2 * C₁ ^ 2
  refine ⟨10 + 4 * C₁ ^ 4 + (cO * C₂ + 1) ^ 2 + 1 + C₂ * (cO + 1),
    fun {N A W Dl Nl Ll X Y E} hN hA hW hD hNl hLl hX hY hE => ?_⟩
  have hIn : 2 * Dl + 1 + (2 * Nl + 1 + Ll) + 1 ≤ C₁ * X := by
    have h1 := (Nat.mul_le_mul_left cD (by omega : N + A + 1 ≤ 4 * X)).trans
      (le_of_eq (show cD * (4 * X) = 4 * (cD * X) by ring))
    have h2 : C₁ * X = 8 * (cD * X) + (d + 4) * X + 15 * X := by simp only [C₁]; ring
    omega
  have hXY : X * Y ≤ X ^ 2 * Y := Nat.mul_le_mul_right _ (Nat.le_self_pow two_ne_zero _)
  have hX2Y : X ^ 2 * Y ≤ X ^ 4 * Y ^ 2 :=
    Nat.mul_le_mul (Nat.pow_le_pow_right hX (by decide)) (Nat.le_self_pow two_ne_zero _)
  have hpre : N + A + (N + W + (N + Y)) ≤ 10 * (X * Y) := by
    have h1 := Nat.le_mul_of_pos_right X hY
    have h2 := Nat.le_mul_of_pos_left Y hX; omega
  have hU₂ : (2 * Dl + 1 + (2 * Nl + 1 + Ll) + 1) ^ 2 * (Y + 1) ≤ 2 * C₁ ^ 2 * (X ^ 2 * Y) :=
    (Nat.mul_le_mul (Nat.pow_le_pow_left hIn 2) (by omega : Y + 1 ≤ 2 * Y)).trans
      (le_of_eq (by ring))
  have hU₄ : (2 * Dl + 1 + (2 * Nl + 1 + Ll) + 1) ^ 4 * (Y + 1) ^ 2 ≤
      4 * C₁ ^ 4 * (X ^ 4 * Y ^ 2) :=
    (Nat.mul_le_mul (Nat.pow_le_pow_left hIn 4)
      (Nat.pow_le_pow_left (by omega : Y + 1 ≤ 2 * Y) 2)).trans (le_of_eq (by ring))
  have h12 : 1 ≤ X ^ 2 * Y := Nat.mul_pos (Nat.pow_pos hX) hY
  have hS : N + A + (N + W + (N + Y)) + (2 * Dl + 1 + (2 * Nl + 1 + Ll) + 1) ^ 2 * (Y + 1) + 1 ≤
      C₂ * (X ^ 2 * Y) := by
    have : C₂ * (X ^ 2 * Y) = 11 * (X ^ 2 * Y) + 2 * C₁ ^ 2 * (X ^ 2 * Y) := by
      simp only [C₂]; ring
    omega
  have hE' : E ≤ cO * C₂ * (X ^ 2 * Y) :=
    hE.trans ((Nat.mul_le_mul_left cO hS).trans (le_of_eq (by ring)))
  have hE2 : (E + 1) ^ 2 ≤ (cO * C₂ + 1) ^ 2 * (X ^ 4 * Y ^ 2) := by
    have h₂ : E + 1 ≤ (cO * C₂ + 1) * (X ^ 2 * Y) := by
      have : (cO * C₂ + 1) * (X ^ 2 * Y) = cO * C₂ * (X ^ 2 * Y) + X ^ 2 * Y := by ring
      omega
    exact (Nat.pow_le_pow_left h₂ 2).trans (le_of_eq (by ring))
  have h1 : 1 ≤ X ^ 4 * Y ^ 2 := Nat.mul_pos (Nat.pow_pos hX) (Nat.pow_pos hY)
  have := Nat.mul_le_mul_left 10 (hXY.trans hX2Y)
  have := hU₂.trans (Nat.mul_le_mul_left (2 * C₁ ^ 2) hX2Y)
  have := Nat.mul_le_mul_left C₂ hX2Y; have := Nat.mul_le_mul_left (cO * C₂) hX2Y
  have : (10 + 4 * C₁ ^ 4 + (cO * C₂ + 1) ^ 2 + 1 + C₂ * (cO + 1)) * (X ^ 4 * Y ^ 2) =
      10 * (X ^ 4 * Y ^ 2) + 4 * C₁ ^ 4 * (X ^ 4 * Y ^ 2) +
        (cO * C₂ + 1) ^ 2 * (X ^ 4 * Y ^ 2) + X ^ 4 * Y ^ 2 +
          (C₂ * (X ^ 4 * Y ^ 2) + cO * C₂ * (X ^ 4 * Y ^ 2)) := by ring
  exact ⟨by omega, by omega⟩

/-- The numeric facts behind `cheap`, for an encoded input of length `N`, an input of length `n`
and a clock `Z` of at most `G * Y`. -/
theorem cheap_aux (G : ℕ) {N n Z Y : ℕ} (hn : n ≤ N) (hY : 1 ≤ Y) (hZ : Z ≤ G * Y) :
    N + 1 ≤ (N + 1) ^ 2 * Y ^ 2 ∧ (Z + 1) ^ 2 ≤ (G + 4) ^ 2 * ((N + 1) ^ 2 * Y ^ 2) ∧
      (2 * N + 4 + Z) ^ 2 ≤ (G + 4) ^ 2 * ((N + 1) ^ 2 * Y ^ 2) := by
  have hY2 : 1 ≤ Y ^ 2 := Nat.one_le_pow _ _ hY
  have hN2 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow two_ne_zero _
  have h₁ : N + 1 ≤ (N + 1) * Y := Nat.le_mul_of_pos_right _ hY
  have h₂ := Nat.mul_le_mul_left G (Nat.le_mul_of_pos_left Y (by omega : 0 < N + 1))
  have e : (G + 4) * ((N + 1) * Y) = G * ((N + 1) * Y) + 4 * ((N + 1) * Y) := by ring
  have hsq : (2 * N + 4 + Z) ^ 2 ≤ (G + 4) ^ 2 * ((N + 1) ^ 2 * Y ^ 2) :=
    (Nat.pow_le_pow_left (by omega : 2 * N + 4 + Z ≤ (G + 4) * ((N + 1) * Y)) 2).trans
      (le_of_eq (by ring))
  exact ⟨hN2.trans (Nat.le_mul_of_pos_right _ hY2),
    (Nat.pow_le_pow_left (by omega) 2).trans hsq, hsq⟩


/-- A linear description bound and a certificate covering the input control the common
fourth-power input factor in the acceptance simulation. -/
theorem acceptance_input_bound {description n certificate C : ℕ}
    (hd : description ≤ C * n) (hn : n + 2 ≤ certificate) :
    description + (n + 1) + certificate + 1 ≤ (C + 3) * certificate := by
  have h := Nat.mul_le_mul_left C (by omega : n ≤ certificate)
  have e : (C + 3) * certificate = C * certificate + 3 * certificate := by ring
  omega

/-- Bound the complete lazy-verifier branch tree after charging certificate construction.
Simulation is charged only for a short description, and search only when the first horizon
comparison fails. The last comparison changes the branch but needs no further estimate. -/
theorem verifier_branch_bound {n t c a b M A₁ A₂ A₃ B : ℕ}
    {short : Bool} {q r : Prop} [Decidable q] [Decidable r]
    (hn : n + 1 ≤ M) (ht : t ≤ A₃ * M) (hc : c ≤ A₁ * M)
    (ha : short = true → a ≤ A₂ * M) (hb : ¬q → b ≤ n + 1 + B) :
    n + t + (c + if short then
      (c + if q then c + a else (c + if r then c + b else c)) else c) ≤
      (2 + A₃ + 4 * A₁ + A₂ + B) * M + (2 + A₃ + 4 * A₁ + A₂ + B) := by
  have e : (2 + A₃ + 4 * A₁ + A₂ + B) * M =
      2 * M + A₃ * M + 4 * (A₁ * M) + A₂ * M + B * M := by ring
  have hB : B ≤ B * M := Nat.le_mul_of_pos_right _ (by omega)
  generalize 2 + A₃ + 4 * A₁ + A₂ + B = C at *
  split_ifs with h₀ h₁ h₂
  · have := ha h₀; omega
  · have := hb h₁; omega
  all_goals omega

/-- The numeric facts behind the bound of the exponential brute-force search: the encoded pair of
length `N`, the certificate length `c`, the unary certificate length and the search. -/
theorem brute_bound_aux (C K₀ N c : ℕ) (hc : 1 ≤ c) :
    N + (C * 2 ^ N + c * c) + 2 ^ (K₀ * (2 * N + 1 + c + c)) ≤
      (C + 3) * (2 ^ ((3 * K₀ + 4) * (N + c)) + 1) := by
  set B := 2 ^ ((3 * K₀ + 4) * (N + c))
  have hN : 2 ^ N ≤ B := Nat.pow_le_pow_right Nat.one_lt_two.le
    ((Nat.le_add_right N c).trans (Nat.le_mul_of_pos_left _ (by omega)))
  have hcc : c * c ≤ B :=
    ((Nat.mul_le_mul Nat.lt_two_pow_self.le Nat.lt_two_pow_self.le).trans_eq
      (pow_add 2 c c).symm).trans (Nat.pow_le_pow_right Nat.one_lt_two.le
        ((by omega : c + c ≤ 4 * (N + c)).trans
          (Nat.mul_le_mul_right _ (by omega : 4 ≤ 3 * K₀ + 4))))
  have hs : 2 ^ (K₀ * (2 * N + 1 + c + c)) ≤ B := Nat.pow_le_pow_right Nat.one_lt_two.le
    ((Nat.mul_le_mul_left K₀ (by omega : 2 * N + 1 + c + c ≤ 3 * (N + c))).trans
      ((le_of_eq (by ring : K₀ * (3 * (N + c)) = 3 * K₀ * (N + c))).trans
        (Nat.mul_le_mul_right _ (by omega : 3 * K₀ ≤ 3 * K₀ + 4))))
  have hN' : N < 2 ^ N := Nat.lt_two_pow_self
  have hC : C * 2 ^ N ≤ C * B := Nat.mul_le_mul_left _ hN
  have e : (C + 3) * (B + 1) = C * B + 3 * B + (C + 3) := by ring
  omega

end Cslib.Complexity.LazyDiagonal
