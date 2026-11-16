/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Circuit.Boolean.FanInTwo
import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification.Samples
import CslibFrontier.Foundations.Combinatorics.Expander.AffineTower
import CslibFrontier.Foundations.Combinatorics.Expander.Connected
import CslibFrontier.Foundations.Combinatorics.SetFamily.PairwiseIntersection
import CslibFrontier.Foundations.Data.Code.Varshamov

/-! # Satisfying instances for the Arora–Barak short steps

Each hypothesis of the theorems for Arora–Barak Theorem 16.35, Lemma 17.9, Claim 18.34 and
Exercises 13.2, 16.11, 17.6 and 17.10(b) holds in a concrete case. The file is a `module`
client with ordinary imports, so it checks the public API as downstream modules see it.
-/

set_option linter.privateModule false

open Finset Cslib
open scoped Cslib.Probability.PMF

/-- Theorem 16.35 applies to the base of the affine-plane zig-zag tower, whose spectral expansion
is at most `1 / 5` over a field with at least 256 elements. -/
example (K : Type*) [Field K] [Fintype K] [DecidableEq K] (hK : 256 ≤ Fintype.card K)
    (u v : Cslib.RotationMap.AffinePlaneTowerBaseVertex K) :
    ∃ w : (Cslib.RotationMap.affinePlaneTowerBase K).toSimpleGraph.Walk u v,
      w.length ≤ Nat.clog 4 (Fintype.card (Cslib.RotationMap.AffinePlaneTowerBaseVertex K)) :=
  Cslib.RotationMap.exists_walk_length_le_clog_of_spectralExpansion_lt _
    ((Cslib.RotationMap.spectralExpansion_affinePlaneTowerBase_le_one_div_five K hK).trans_lt
      (by norm_num)) u v

/-- Claim 18.34 on two overlapping sets with `C = 1`: `|{0,1}| + |{1,2}| ≤ 4 · |{0,1,2}|`. -/
example : ∑ i, #(![({0, 1} : Finset ℕ), {1, 2}] i) ≤
    4 * 1 * #(univ.biUnion ![({0, 1} : Finset ℕ), {1, 2}]) :=
  sum_card_le_four_mul_card_biUnion _ one_pos (by decide)

/-- Lemma 17.9 and Exercises 17.6 and 17.10(b) at `δ = 1 / 4`. -/
example (n : ℕ) : True := by
  obtain ⟨-, -, -⟩ :=
    Cslib.Code.exists_linearMap_two_mul (δ := 1 / 4) (by norm_num) (by norm_num) n
  obtain ⟨-, -, -⟩ :=
    Cslib.Code.exists_linearMap_ceil_div (δ := 1 / 4) (by norm_num) (by norm_num) n
  obtain ⟨-, -, -⟩ :=
    Cslib.Code.exists_linearMap_ceil_mul_div (δ := 1 / 4) (by norm_num) (by norm_num) n
  trivial

/-- Exercise 16.11 with `ε = 1 / 2`: every agreement fraction is at most `1`. -/
example (n m : ℕ) (f : BooleanFunction n) :
    dist (Cslib.Probability.PMF.iid
        ((Cslib.Probability.PMF.uniformOfFintype (BitString n)).map f) m)
      (Cslib.Probability.PMF.iid (Cslib.Probability.PMF.uniformOfFintype Bool) m) ≤ 1 / 2 * m := by
  refine Cslib.Circuits.Boolean.dist_iid_map_uniformOfFintype_le (S := 1) le_rfl
    (fun g _ => ?_) m
  rw [div_le_iff₀ (by positivity)]
  have : (#{x : BitString n | g x = f x} : ℝ) ≤ 2 ^ n := by
    exact_mod_cast (card_le_univ _).trans_eq (by simp)
  linarith

/-- Exercise 16.11 from average-case hardness: with `ε = 1 / S`, `IsAverageCaseHard f S` is the
premise. -/
example (n S m : ℕ) (f : BooleanFunction n) (hS : 1 ≤ S)
    (hf : Cslib.Circuits.Boolean.IsAverageCaseHard f S) :
    dist (Cslib.Probability.PMF.iid
        ((Cslib.Probability.PMF.uniformOfFintype (BitString n)).map f) m)
      (Cslib.Probability.PMF.iid (Cslib.Probability.PMF.uniformOfFintype Bool) m) ≤ 1 / S * m :=
  Cslib.Circuits.Boolean.dist_iid_map_uniformOfFintype_le hS hf m

/-- The shared incidence count on two overlapping sets inside `{0,1,2}`:
`(2 + 2)² ≤ 3 · (2 + 1 + 1 + 2)`. -/
example : (∑ c ∈ univ, #(![({0, 1} : Finset ℕ), {1, 2}] c)) ^ 2 ≤
    #({0, 1, 2} : Finset ℕ) * ∑ c ∈ univ, ∑ c' ∈ univ,
      #(![({0, 1} : Finset ℕ), {1, 2}] c ∩ ![({0, 1} : Finset ℕ), {1, 2}] c') :=
  sq_sum_card_le_card_mul_sum_sum_card_inter _ _ (by decide)

/-- Exercise 13.2 for every circuit of unbounded fan-in. -/
example {n m : ℕ} (C : Cslib.Circuits.Circuit Cslib.Circuits.Boolean.Unbounded.signature n m)
    (j : Fin m) :
    ∃ F : Cslib.Circuits.Formula Cslib.Circuits.Boolean.Unbounded.signature n,
      F.depth ≤ C.depth ∧ F.size + F.leafSize ≤ (10 * (n + C.size)) ^ C.depth := by
  obtain ⟨F, -, hd, hs⟩ := Cslib.Circuits.Boolean.Unbounded.exists_formula_size_add_leafSize_le C j
  exact ⟨F, hd, hs⟩
