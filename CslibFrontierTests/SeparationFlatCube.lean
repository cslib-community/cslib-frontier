/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flat.Convexity
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flat.CubePoints
import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Price.Random
import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.UnitExponent
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Tests of the cube points and of the unit exponents of a spectral point, as a client: a vertex
of the square and its distance to the opposite vertex; the support point, whose unit exponents at
legs on two parties are at most `0`; the unit exponent of a pull-back; an extension of a spectral
point to a new party that keeps the wire exponents and the value at a tensor; and Proposition E.9
on the line, at both facet centres. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SeparationFlatCube

open Cslib.PartyTensor Cslib.Circuits.Arithmetic.Separation.Flat

/-- The vertex `(1/2, -1/2)` of the square. -/
example : cubePoint (fun x : Fin 2 => boolSign (x = 0)) 1 = -1 / 2 := by
  rw [cubePoint_apply]
  norm_num [boolSign]

/-- Opposite vertices of the square are at distance `√2`. -/
example : dist (cubePoint fun x : Fin 2 => boolSign (x = 0))
    (cubePoint fun x : Fin 2 => -boolSign (x = 0)) = √2 := by
  simpa using dist_cubePoint_neg (k := 2) fun x => decide (x = 0)

/-- At the support point, legs on two parties have unit exponent at most `0`. -/
example (π : Fin 3 → Bool) (h : ∀ a, π a = true ∨ π a = false) :
    (SpectralPoint.support ℚ Bool).unitExponent π ≤ 0 :=
  ((SpectralPoint.support ℚ Bool).unitExponent_le_of_two π true false h).trans_eq
    (SpectralPoint.wireExponent_support true false)

/-- The unit exponents of a pull-back along `Bool.not`. -/
example (F : SpectralPoint ℚ Bool) (π : Fin 2 → Bool) :
    (F.pull not).unitExponent π = F.unitExponent (not ∘ π) :=
  F.pull_unitExponent not π

/-- A spectral point on `Bool` extends to one new party moved to `true`, with the same wire
exponents and the same value at `C` on `Bool`. -/
example (F : SpectralPoint ℚ Bool) (C : Cslib.PartyTensor ℚ Bool) (hC : 0 < F C) :
    ∃ F' : SpectralPoint ℚ (Bool ⊕ Unit),
      (∀ p p', F'.wireExponent (Sum.inl p) (Sum.inl p') = F.wireExponent p p') ∧
        F' (push Sum.inl C) = F C := by
  obtain ⟨F', -, -, he, hv⟩ := F.exists_extend_keep (Q := Unit) (fun _ : Fin 1 => (1 : ℝ))
    (fun _ => zero_le_one) (by simp) (fun _ _ => true) C hC
  exact ⟨F', he, hv⟩

/-- The centres `±½ e₀` of the two facets of the segment `[-½, ½]`. -/
private noncomputable def centre (b : Bool) : EuclideanSpace ℝ (Fin 1) :=
  (if b then (1 / 2 : ℝ) else -(1 / 2)) • EuclideanSpace.single 0 1

/-- Both facet centres of the segment. -/
private noncomputable def centres : Finset (EuclideanSpace ℝ (Fin 1)) :=
  {centre true, centre false}

private theorem mem_centres (b : Bool) : centre b ∈ centres := by
  cases b <;> simp [centres]

/-- Proposition E.9 on the line: in the flat case the two facet centres `±½ e₀` have a spectral
point whose scaled wire exponent between them is their distance `1` up to `ε`, and whose scaled
unit exponent at both is at most `1 + ε`. -/
example {K : Type} [Field K] (hK : Cslib.Circuits.Arithmetic.Separation.TwoCases.FlatCase K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (F : SpectralPoint K centres) (c : ℝ), 0 ≤ c ∧
      |c * F.wireExponent ⟨_, mem_centres true⟩ ⟨_, mem_centres false⟩ - 1| < ε ∧
      c * F.unitExponent (fun x : centres => x) ≤ 1 + ε := by
  obtain ⟨F, c, hc, hw, h⟩ := exists_spectralPoint_cube hK centres centres subset_rfl
    ⟨_, mem_centres true⟩ (fun x hx => by
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact ⟨0, true, rfl⟩
      · exact ⟨0, false, Finset.mem_singleton.1 hx⟩) hε
  have hd : dist (centre true) (centre false) = 1 := by
    rw [EuclideanSpace.dist_eq]
    norm_num [centre, Real.dist_eq]
  have hw' := hw ⟨_, mem_centres true⟩ ⟨_, mem_centres false⟩
  rw [Subtype.dist_eq, hd] at hw'
  exact ⟨F, c, hc, hw', by simpa using h⟩

end CslibFrontierTests.SeparationFlatCube
