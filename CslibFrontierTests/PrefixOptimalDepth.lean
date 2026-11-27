/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Circuit.Prefix.OptimalDepth

/-! # Tests for optimal fanout-bounded prefix circuits (Sergeev 2025) -/

set_option linter.privateModule false

open Cslib.Circuits Cslib.Circuits.Prefix

/-! ## Concrete `w_2(d, h)` and `w_2*(D)` values and `k = 2` optimal depths -/

private theorem w2_star_zero : maxCircuitWidthUpper 2 0 = 1 := by
  rw [maxCircuitWidthUpper, Finset.sum_range_one, maxConsistentWidth_two]
  decide

private theorem w2_star_one : maxCircuitWidthUpper 2 1 = 2 := by
  rw [maxCircuitWidthUpper, Finset.sum_range_succ, Finset.sum_range_one,
    maxConsistentWidth_two, maxConsistentWidth_two]
  decide

private theorem w2_star_two : maxCircuitWidthUpper 2 2 = 4 := by
  have h := maxCircuitWidthUpper_recurrence (k := 2) (D := 2) le_rfl le_rfl
  simpa only [Finset.Ico_self, Finset.sum_empty, zero_add, Nat.sub_self, w2_star_zero] using h

private theorem w2_star_three : maxCircuitWidthUpper 2 3 = 6 := by
  have h := maxCircuitWidthUpper_recurrence (k := 2) (D := 3) le_rfl (by decide)
  simpa only [Finset.Ico_self, Finset.sum_empty, zero_add, show 3 - 2 = 1 by rfl,
    w2_star_one] using h

-- Exact maximum input widths `1 + w_2*(D - 1) = 2, 3, 5, 7` for `D = 1, 2, 3, 4`.
example : 1 + maxCircuitWidthUpper 2 0 = 2 ∧
    1 + maxCircuitWidthUpper 2 1 = 3 ∧
    1 + maxCircuitWidthUpper 2 2 = 5 ∧
    1 + maxCircuitWidthUpper 2 3 = 7 := by
  rw [w2_star_zero, w2_star_one, w2_star_two, w2_star_three]
  decide

-- Exact optimal depths `D(N, 2)` for `N = 1 .. 8` matching `⌊log₂ N⌋ + ⌊log₂(2N / 3)⌋`.
example : optimalPrefixDepth 1 2 = 0 :=
  optimalPrefixDepth_one le_rfl

example : optimalPrefixDepth 2 2 = 1 := by
  have hle : optimalPrefixDepth 2 2 ≤ 1 :=
    (optimalPrefixDepth_two_le_iff (by decide) (by decide)).mpr (by rw [w2_star_zero])
  have hgt : ¬ optimalPrefixDepth 2 2 = 0 := by
    intro h0
    obtain ⟨c, hopt, hfan, hd⟩ := exists_optimalPrefixCircuit_depth_eq (N := 2) (k := 2)
      le_rfl (by decide)
    have hw := width_le_maxCircuitWidthUpper_two (by decide) hopt hfan
    rw [hd, h0, w2_star_zero] at hw
    omega
  omega

example : optimalPrefixDepth 3 2 = 2 := by
  have hle : optimalPrefixDepth 3 2 ≤ 2 :=
    (optimalPrefixDepth_two_le_iff (by decide) (by decide)).mpr (by rw [w2_star_one])
  have hgt : ¬ optimalPrefixDepth 3 2 ≤ 1 := by
    rw [optimalPrefixDepth_two_le_iff (by decide) (by decide), w2_star_zero]
    decide
  omega

example : optimalPrefixDepth 4 2 = 3 ∧ optimalPrefixDepth 5 2 = 3 := by
  have h4_le : optimalPrefixDepth 4 2 ≤ 3 :=
    (optimalPrefixDepth_two_le_iff (by decide) (by decide)).mpr (by rw [w2_star_two]; decide)
  have h4_gt : ¬ optimalPrefixDepth 4 2 ≤ 2 := by
    rw [optimalPrefixDepth_two_le_iff (by decide) (by decide), w2_star_one]
    decide
  have h5_le : optimalPrefixDepth 5 2 ≤ 3 :=
    (optimalPrefixDepth_two_le_iff (by decide) (by decide)).mpr (by rw [w2_star_two])
  have h5_gt : ¬ optimalPrefixDepth 5 2 ≤ 2 := by
    rw [optimalPrefixDepth_two_le_iff (by decide) (by decide), w2_star_one]
    decide
  omega

example : optimalPrefixDepth 6 2 = 4 ∧ optimalPrefixDepth 7 2 = 4 ∧
    optimalPrefixDepth 8 2 ≥ 5 := by
  have h6_le : optimalPrefixDepth 6 2 ≤ 4 :=
    (optimalPrefixDepth_two_le_iff (by decide) (by decide)).mpr (by rw [w2_star_three]; decide)
  have h6_gt : ¬ optimalPrefixDepth 6 2 ≤ 3 := by
    rw [optimalPrefixDepth_two_le_iff (by decide) (by decide), w2_star_two]
    decide
  have h7_le : optimalPrefixDepth 7 2 ≤ 4 :=
    (optimalPrefixDepth_two_le_iff (by decide) (by decide)).mpr (by rw [w2_star_three])
  have h7_gt : ¬ optimalPrefixDepth 7 2 ≤ 3 := by
    rw [optimalPrefixDepth_two_le_iff (by decide) (by decide), w2_star_two]
    decide
  have h8_gt : ¬ optimalPrefixDepth 8 2 ≤ 4 := by
    rw [optimalPrefixDepth_two_le_iff (by decide) (by decide), w2_star_three]
    decide
  omega

/-! ## Concrete `w_3(d, h)` and `w_3*(0..4)` values -/

private theorem w3_1_h {h : ℕ} (hh : 1 ≤ h) : maxConsistentWidth 3 1 h = 2 := by
  have hrec := maxConsistentWidth_eq (k := 3) (d := 1) (h := h) (by decide) (by decide) hh
  simpa only [show min 1 (3 - 1) = 1 by rfl, Finset.Ico_self, Finset.sum_empty, zero_add,
    Nat.sub_self, maxConsistentWidth_zero_left (k := 3) (by decide)] using hrec

private theorem w3_2_1 : maxConsistentWidth 3 2 1 = 3 := by
  have hrec := maxConsistentWidth_eq (k := 3) (d := 2) (h := 1) (by decide) (by decide) (by decide)
  simpa only [show min 2 (3 - 1) = 2 by rfl, show Finset.Ico 1 2 = {1} by decide,
    Finset.sum_singleton, Nat.sub_self,
    maxConsistentWidth_zero_right (k := 3) (by decide)] using hrec

private theorem w3_star_0_to_4 :
    maxCircuitWidthUpper 3 0 = 1 ∧
    maxCircuitWidthUpper 3 1 = 2 ∧
    maxCircuitWidthUpper 3 2 = 4 ∧
    maxCircuitWidthUpper 3 3 = 7 ∧
    maxCircuitWidthUpper 3 4 = 11 := by
  have hw0 : maxCircuitWidthUpper 3 0 = 1 := by
    rw [maxCircuitWidthUpper, Finset.sum_range_one, Nat.sub_zero,
      maxConsistentWidth_zero_left (k := 3) (by decide)]
  have hw1 : maxCircuitWidthUpper 3 1 = 2 := by
    rw [maxCircuitWidthUpper, Finset.sum_range_succ, Finset.sum_range_one, Nat.sub_zero,
      Nat.sub_self, maxConsistentWidth_zero_left (k := 3) (by decide),
      maxConsistentWidth_zero_right (k := 3) (by decide)]
  have hw2 : maxCircuitWidthUpper 3 2 = 4 := by
    rw [maxCircuitWidthUpper, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      Nat.sub_zero, Nat.sub_self, maxConsistentWidth_zero_left (k := 3) (by decide),
      maxConsistentWidth_zero_right (k := 3) (by decide), w3_1_h (by decide)]
  have hw3 : maxCircuitWidthUpper 3 3 = 7 := by
    have hrec := maxCircuitWidthUpper_recurrence (k := 3) (D := 3) (by decide) le_rfl
    simpa only [show Finset.Ico 2 3 = {2} by decide, Finset.sum_singleton,
      show 3 - 2 = 1 by rfl, Nat.sub_self, hw1, hw0] using hrec
  have hw4 : maxCircuitWidthUpper 3 4 = 11 := by
    have hrec := maxCircuitWidthUpper_recurrence (k := 3) (D := 4) (by decide) (by decide)
    simpa only [show Finset.Ico 2 3 = {2} by decide, Finset.sum_singleton,
      show 4 - 2 = 2 by rfl, show 4 - 3 = 1 by rfl, hw2, hw1] using hrec
  exact ⟨hw0, hw1, hw2, hw3, hw4⟩

example : maxCircuitWidthUpper 3 4 = 11 := w3_star_0_to_4.2.2.2.2

/-! ## Non-vacuity witness for `ConsistentTreePair` at `k = 3, d = 2, h = 1` (width `3`) -/

private def pair_k3_d2_h1 : ConsistentTreePair 3 2 1 where
  a := 0
  b := 3
  tree := .split (.snoc (.two (.leaf 0) (.leaf 1)) (.leaf 2))
  inDepth_le := by decide
  outDepth_le := by decide
  fanout_le := by
    simp only [ConsistentTree.FanoutAtMost, ConsistentChain.FanoutAtMost, ConsistentChain.arity]
    decide

example : pair_k3_d2_h1.width = 3 := rfl

/-! ## Concrete optimal fanout-2 prefix circuits on `N = 1, 2, 3, 5` (including required `id`) -/

private def mulLine {N g : ℕ} (w₀ w₁ : Wire N g) : Line prefixSignature N g :=
  ⟨.mul, fun i => if i.val = 0 then w₀ else w₁⟩

private def idLine {N g : ℕ} (w₀ : Wire N g) : Line prefixSignature N g :=
  ⟨.id, fun _ => w₀⟩

-- `N = 1`: 0 gates, depth 0, complexity 0 (`0 + 0 = 2 * 1 - 2`).
private def circuit1 : PrefixCircuit 1 :=
  ⟨Program.empty, fun _ => .input 0⟩

example : IsUniversalPrefixCircuit circuit1 ∧ IsOptimalPrefixCircuit circuit1 ∧
    FanoutAtMost circuit1 2 ∧ circuit1.depth = 0 ∧ binaryComplexity circuit1 = 0 := by
  refine ⟨by decide, ⟨by decide, by decide⟩, by decide, by decide, by decide⟩

-- `N = 2`: 1 `mul` gate, depth 1, complexity 1 (`1 + 1 = 2 * 2 - 2`), fanout 2 (NOT fanout 1).
private def circuit2 : PrefixCircuit 2 :=
  ⟨Program.empty.gate (mulLine (.input 0) (.input 1)),
    ![.input 0, .gate 0]⟩

example : IsUniversalPrefixCircuit circuit2 ∧ IsOptimalPrefixCircuit circuit2 ∧
    FanoutAtMost circuit2 2 ∧ ¬ FanoutAtMost circuit2 1 := by
  refine ⟨by decide, ⟨by decide, by decide⟩, by decide, by decide⟩

-- `N = 3`: 2 `mul` gates, depth 2, complexity 2 (`2 + 2 = 2 * 3 - 2`), fanout 2.
private def circuit3 : PrefixCircuit 3 :=
  let p1 := Program.empty.gate (mulLine (.input 0) (.input 1))
  let p2 := p1.gate (mulLine (.gate 0) (.input 2))
  ⟨p2, ![.input 0, .gate 0, .gate 1]⟩

example : IsUniversalPrefixCircuit circuit3 ∧ IsOptimalPrefixCircuit circuit3 ∧
    FanoutAtMost circuit3 2 ∧ circuit3.depth = 2 ∧ binaryComplexity circuit3 = 2 := by
  refine ⟨by decide, ⟨by decide, by decide⟩, by decide, by decide, by decide⟩

-- `N = 5` at optimal depth `D = 3`: 5 `mul` gates + 1 `id` buffer (6 total gates),
-- demonstrating that unary `id` replication is genuinely required to achieve `N = 5` at `D = 3`
-- under `FanoutAtMost _ 2` (`binaryComplexity + depth = 5 + 3 = 8 = 2 * 5 - 2`).
private def circuit5 : PrefixCircuit 5 :=
  -- gate 0: x0 * x1 (depth 1, fanout 2: feeds gate 2 and id buffer gate 3)
  let p1 := Program.empty.gate (mulLine (.input 0) (.input 1))
  -- gate 1: x2 * x3 (depth 1, fanout 1: feeds gate 2)
  let p2 := p1.gate (mulLine (.input 2) (.input 3))
  -- gate 2: gate 0 * gate 1 = [0, 4) (depth 2, fanout 2: feeds out 3 and gate 5)
  let p3 := p2.gate (mulLine (.gate 0) (.gate 1))
  -- gate 3: id(gate 0) = [0, 2) (depth 2, fanout 2: feeds out 1 and gate 4)
  let p4 := p3.gate (idLine (.gate 0))
  -- gate 4: gate 3 * x2 = [0, 3) (depth 3, fanout 1: feeds out 2)
  let p5 := p4.gate (mulLine (.gate 3) (.input 2))
  -- gate 5: gate 2 * x4 = [0, 5) (depth 3, fanout 1: feeds out 4)
  let p6 := p5.gate (mulLine (.gate 2) (.input 4))
  ⟨p6, ![.input 0, .gate 3, .gate 4, .gate 2, .gate 5]⟩

example : IsUniversalPrefixCircuit circuit5 ∧ IsOptimalPrefixCircuit circuit5 ∧
    FanoutAtMost circuit5 2 ∧ circuit5.size = 6 ∧
    binaryComplexity circuit5 = 5 ∧ circuit5.depth = 3 := by
  refine ⟨by decide, ⟨by decide, by decide⟩, by decide, rfl, by decide, by decide⟩

/-! ## Boundary witness: reversed multiplication works in commutative semigroups, not universally -/

private def reversedCircuit2 : PrefixCircuit 2 :=
  ⟨Program.empty.gate (mulLine (.input 1) (.input 0)),
    ![.input 0, .gate 0]⟩

-- Correct on commutative `(ℕ, *)`, yet rejected by `IsUniversalPrefixCircuit`.
example (x : Fin 2 → ℕ) :
    reversedCircuit2.eval (semigroupInterp ℕ) x = prefixProd x := by
  funext j
  fin_cases j
  · rfl
  · change x 1 * x 0 = x 0 * x 1
    exact Nat.mul_comm (x 1) (x 0)

example : ¬ IsUniversalPrefixCircuit reversedCircuit2 := by decide

/-! ## Characteristic root `alphaRoot` and main asymptotic depth bound -/

-- `α_2 = √2 < α_3 < α_4 < φ` and `3 / 2 < α_3`.
example : alphaRoot 2 = Real.sqrt 2 ∧
    (3 / 2 : ℝ) < alphaRoot 3 ∧
    alphaRoot 2 < alphaRoot 3 ∧
    alphaRoot 3 < alphaRoot 4 ∧
    alphaRoot 4 < Real.goldenRatio :=
  ⟨alphaRoot_two,
    three_halves_lt_alphaRoot (by decide),
    alphaRoot_strictMonoOn (by decide : (2 : ℕ) ∈ Set.Ici 2) (by decide) (by decide),
    alphaRoot_strictMonoOn (by decide : (3 : ℕ) ∈ Set.Ici 2) (by decide) (by decide),
    alphaRoot_lt_goldenRatio (by decide)⟩

-- Concrete instantiation of Sergeev's main theorem at `k = 3`.
example : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
    |(optimalPrefixDepth N 3 : ℝ) - Real.logb (alphaRoot 3) N| ≤ C :=
  abs_optimalPrefixDepth_sub_logb_le (by decide)
