/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.TransitiveSymmetric
public import CslibFrontier.Foundations.BooleanAnalysis.Tribes

/-! # Tests for transitive-symmetric functions

Relabelling carries a dictator on one coordinate to a dictator on another, with its derivative,
influence and Fourier coefficient. The transposition of two bits is an automorphism of their
conjunction, so both bits have the same influence and degree-one coefficient. Majority is
symmetric, so every permutation is an automorphism of it, it is transitive-symmetric, and its
influences are at most `1 / √n`; a real function of the weight is also transitive-symmetric.
`Tribes_{2,2}` is transitive-symmetric but not symmetric, and a dictator on two bits is not
transitive-symmetric.
-/

public section

namespace CslibFrontierTests.BooleanAnalysisTransitiveSymmetric

open Cslib Cslib.BitString

/-! ### Relabelling a dictator -/

/-- The transposition of the two coordinates of `Fin 2`. -/
abbrev σ : Equiv.Perm (Fin 2) := Equiv.swap 0 1

-- The derivative of the dictator on bit `1` in bit `1` is that of the dictator on bit `0` in
-- bit `0`, at the relabelled point.
example (x : Fin 2 → Bool) :
    derivative 1 (fun y : Fin 2 → Bool => signVal (y 1)) x =
      derivative 0 (fun z : Fin 2 → Bool => signVal (z 0)) fun j => x (σ j) := by
  simpa using derivative_comp_arrowCongr σ 1 (fun z : Fin 2 → Bool => signVal (z 0)) x

-- The two dictators have the same influence.
example : influence 1 (fun y : Fin 2 → Bool => signVal (y 1)) =
    influence 0 (fun z : Fin 2 → Bool => signVal (z 0)) := by
  simpa using influence_comp_arrowCongr σ 1 (fun z : Fin 2 → Bool => signVal (z 0))

-- The coefficient of the dictator on bit `1` at `{1}` is that of the dictator on bit `0` at `{0}`.
example : fourierCoeff (fun y : Fin 2 → Bool => signVal (y 1)) {1} =
    fourierCoeff (fun z : Fin 2 → Bool => signVal (z 0)) {0} := by
  simpa using fourierCoeff_comp_arrowCongr σ (fun z : Fin 2 → Bool => signVal (z 0)) {1}

/-! ### Automorphisms of a conjunction -/

/-- The conjunction of two bits. -/
abbrev and₂ (x : Fin 2 → Bool) : Bool := x 0 && x 1

theorem swap_mem_aut_and₂ : σ ∈ aut and₂ := by decide

-- The transposition is not an automorphism of the dictator on bit `0`.
example : σ ∉ aut fun x : Fin 2 → Bool => x 0 := by decide

-- Both bits of the conjunction have the same influence ...
example : influence 1 (fun x => signVal (and₂ x)) = influence 0 (fun x => signVal (and₂ x)) := by
  simpa using influence_apply_of_mem_aut (aut_le_aut_comp signVal and₂ swap_mem_aut_and₂) 0

-- ... and the same degree-one coefficient.
example : fourierCoeff (fun x => signVal (and₂ x)) {1} =
    fourierCoeff (fun x => signVal (and₂ x)) {0} := by
  simpa using fourierCoeff_map_of_mem_aut (aut_le_aut_comp signVal and₂ swap_mem_aut_and₂) {0}

/-! ### Majority -/

-- Each voter of majority on `n` bits has influence at most `1 / √n` (Proposition 2.22).
example (n : ℕ) (i : Fin n) : influence i (fun x => signVal (majority n x)) ≤ 1 / √n := by
  have := (isSymmetric_majority (n := n)).isPretransitive_aut
  simpa using influence_signVal_le_one_div_sqrt_card_of_monotone_of_isPretransitive
    (f := majority n) (monotone_threshold _) i

-- The first and last voters of majority on three bits have the same degree-one coefficient.
example : fourierCoeff (fun x => signVal (majority 3 x)) {0} =
    fourierCoeff (fun x => signVal (majority 3 x)) {2} :=
  have := (isSymmetric_majority (n := 3)).isPretransitive_aut
  fourierCoeff_singleton_signVal_eq_of_isPretransitive _ 0 2

-- Rotating three bits keeps the weight of `(true, false, true)`, which is `2`.
example : weight (![true, false, true] ∘ finRotate 3) = 2 := by
  rw [weight_comp_equiv]
  decide

-- Every permutation is an automorphism of majority, and so of majority read as signs.
example (π : Equiv.Perm (Fin 5)) : π ∈ aut fun x => signVal (majority 5 x) :=
  aut_le_aut_comp signVal _ (isSymmetric_majority.aut_eq_top ▸ Subgroup.mem_top π)

-- A real function of the weight, the number of `true` bits minus two, is unchanged by every
-- permutation, so its coordinates are transitive-symmetric.
example : MulAction.IsPretransitive (aut fun x : Fin 3 → Bool => (weight x : ℝ) - 2) (Fin 3) :=
  isPretransitive_aut_of_eq_top <|
    aut_eq_top_of_forall_weight_eq fun x y h => by simp only [h]

/-! ### Tribes -/

/-- `Tribes_{2,2}` is transitive-symmetric, the book's motivating example. -/
instance : MulAction.IsPretransitive (aut (tribes 2 2)) (Fin (2 * 2)) :=
  isPretransitive_aut_iff.2 (by decide)

-- It is not symmetric: inputs of the same weight can get different values.
example : ¬BooleanFunction.IsSymmetric (tribes 2 2) := by
  intro h
  have := h ![true, true, false, false] ![true, false, true, false] (by decide)
  revert this
  decide

-- So its first and last bits have the same influence ...
example : influence 0 (fun x => signVal (tribes 2 2 x)) =
    influence 3 (fun x => signVal (tribes 2 2 x)) :=
  influence_signVal_eq_of_isPretransitive _ 0 3

-- ... and every bit has influence at most `1 / √4`.
example (i : Fin (2 * 2)) :
    influence i (fun x => signVal (tribes 2 2 x)) ≤ 1 / √(2 * 2 : ℕ) := by
  simpa using influence_signVal_le_one_div_sqrt_card_of_monotone_of_isPretransitive
    (monotone_tribes 2 2) i

/-! ### A dictator -/

-- A dictator on two bits is not transitive-symmetric: no automorphism carries the dictating
-- coordinate to the other.
example : ¬MulAction.IsPretransitive (aut fun x : Fin 2 → Bool => x 0) (Fin 2) := by
  rw [isPretransitive_aut_iff]
  decide

end CslibFrontierTests.BooleanAnalysisTransitiveSymmetric
