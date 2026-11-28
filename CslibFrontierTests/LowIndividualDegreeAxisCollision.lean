/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.AxisCollision
import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.OneCoordinate
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Algebra.Field.ZMod

/-! # A sharp collision bound for two distinct lines over the three-element field -/

set_option linter.privateModule false

open Cslib.PCP Cslib.PCP.LowIndividualDegree Cslib.Quantum Finset Function MvPolynomial
open scoped BigOperators ComplexOrder

private abbrev F := ZMod 3

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private noncomputable def identityPoly : BoundedPolynomial F 1 1 :=
  ⟨X 0, by intro i; fin_cases i; simp⟩

private noncomputable abbrev zeroPoly : MvPolynomial (Fin 1) F := 0

private noncomputable def strategy (φ : AlgState ℂ) :
    CommutingStrategy (Question F 1) (Question F 1) (Answer F 1) (Answer F 1) ℂ where
  state := φ
  alice q := Measurement.const (honest zeroPoly q)
  bob q := Measurement.const (honest zeroPoly q)
  commute _ _ _ _ := Commute.all _ _

private noncomputable def zeroAnswer : PolynomialFunction F 1 :=
  .ofPolynomial 0 (by simp)

private theorem zeroAnswer_value (t : F) : zeroAnswer.value t = 0 := by
  rw [PolynomialFunction.value_eq_eval]
  exact (PolynomialFunction.eval_ofPolynomial (0 : Polynomial F) _ _).trans
    Polynomial.eval_zero

private theorem coordinateLine_eq_univ (u : Point F 1) : coordinateLine u 0 = univ :=
  (coordinateLine_eq u 0).trans (linePoints_single_eq_univ u 0)

private theorem decodeCoordinate_honest_zero (u : Point F 1) :
    decodeCoordinate 1 u 0 (honest zeroPoly (.axis (coordinateLine u 0))) = zeroAnswer := by
  apply PolynomialFunction.value_injective
  funext t
  let v := update u 0 t
  have hq : ((.axis (coordinateLine v 0), .point v) : Question F 1 × Question F 1) ∈
      (branchQuestions 0 .axis).support := by
    simp only [branchQuestions_axis, axisQuestions_one, coordinateLine_eq_univ,
      PMF.mem_support_bind_iff, assignLineRoles, PMF.support_map, Set.mem_image,
      Cslib.Probability.PMF.mem_support_uniformOfFintype, true_and]
    exact ⟨v, true, rfl⟩
  have h := decodeCoordinate_agrees v 0
    (accepts_honest_of_mem_branch (d := 1) zeroPoly (fun _ => by simp) .axis hq)
  simpa only [v, decodeCoordinate_update, update_self, coordinateLine_eq_univ, zeroAnswer_value,
    honest_point, decodePoint_inl, zeroPoly, map_zero] using h

private theorem measurement_map_const {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (f : α → β) (a : α) :
    (Measurement.const (A := ℂ) a).map f = Measurement.const (f a) := by
  apply Measurement.ext
  intro b
  rw [Measurement.map_effect, sum_filter, sum_eq_single_of_mem a (mem_univ a)]
  · simp [Measurement.const, eq_comm]
  · intro a' _ hne
    simp [Measurement.const, hne]

private theorem decoded_zero (φ : AlgState ℂ) (u : Point F 1) :
    decodedCoordinate (strategy φ).bob 1 u 0 = Measurement.const zeroAnswer := by
  rw [decodedCoordinate]
  change (Measurement.const (honest zeroPoly (.axis (coordinateLine u 0)))).map
    (decodeCoordinate 1 u 0) = _
  rw [measurement_map_const, decodeCoordinate_honest_zero]

private noncomputable def weight : Measurement (BoundedPolynomial F 1 1) ℂ :=
  Measurement.const identityPoly

private noncomputable def collisionMass (φ : AlgState ℂ) : ℝ :=
  𝔼 u : Point F 1, ∑ g,
    let B := decodedCoordinate (strategy φ).bob 1 u 0
    let D := (B.map (fun f => f.value (u 0))).effect (eval u g.val) -
      B.effect (axisRestriction u 0 g)
    ((strategy φ).state (star D * weight.effect g * D)).re

private theorem collisionMass_eq (φ : AlgState ℂ) : collisionMass φ = 1 / 3 := by
  classical
  have heval (u : Point F 1) : eval u identityPoly.val = u 0 := eval_X _
  have hpoint (u : Point F 1) : (∑ g,
      let B := decodedCoordinate (strategy φ).bob 1 u 0
      let D := (B.map (fun f => f.value (u 0))).effect (eval u g.val) -
        B.effect (axisRestriction u 0 g)
      ((strategy φ).state (star D * weight.effect g * D)).re) = if u 0 = 0 then (1 : ℝ) else 0 := by
    have hne : axisRestriction u 0 identityPoly ≠ zeroAnswer := by
      intro h
      have hv := congrArg (fun f : PolynomialFunction F 1 => f.value 1) h
      simp [value_axisRestriction, identityPoly, zeroAnswer_value] at hv
    rw [sum_eq_single_of_mem identityPoly (mem_univ _)]
    · dsimp only
      rw [decoded_zero, measurement_map_const, zeroAnswer_value]
      by_cases h : u 0 = 0 <;>
        simp [weight, Measurement.const, heval, hne, h, strategy, AlgState.map_one]
    · intro g _ hne
      simp [weight, Measurement.const, hne]
  unfold collisionMass
  simp only [hpoint]
  rw [Fintype.expect_eq_sum_div_card, sum_boole]
  have hz : (univ.filter fun u : Point F 1 => u 0 = 0) = {0} := by
    ext u
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨fun hu => funext fun i => (congrArg u (Subsingleton.elim i 0)).trans hu,
      fun hu => congrFun hu 0⟩
  rw [hz]
  simp [ZMod.card]

/-- The projective collision theorem is sharp for the zero line and the identity polynomial. -/
example (φ : AlgState ℂ) : collisionMass φ = 1 / 3 ∧ collisionMass φ ≤ 1 / 3 := by
  have h := average_axisCollision_le (strategy φ) 1 weight
    (fun L => Measurement.isProjective_const (honest zeroPoly (.axis L)))
    (fun _ _ _ _ => Commute.all _ _) 0
  change collisionMass φ ≤ ((1 : ℕ) : ℝ) / Fintype.card F at h
  exact ⟨collisionMass_eq φ, by simpa only [ZMod.card, Nat.cast_ofNat, Nat.cast_one] using h⟩
