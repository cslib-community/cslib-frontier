/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.Pasting
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Ring.Idempotent

/-! # Pasting on three slices over the field with three elements -/

set_option linter.privateModule false

open Cslib.PCP.LowIndividualDegree Cslib.Quantum MvPolynomial Finset
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private abbrev F := ZMod 3

private def nodes : Fin 3 ↪ F := (ZMod.finEquiv 3).toEquiv.toEmbedding

private noncomputable def zeroSlice : BoundedPolynomial F 1 1 := ⟨0, by simp⟩

private noncomputable def linearSlice : BoundedPolynomial F 1 1 := ⟨X 0, by
  intro i
  simp [Subsingleton.elim i 0]⟩

private noncomputable def productPoly : BoundedPolynomial F 2 1 :=
  ⟨X (Fin.last 1) * X (Fin.castSucc (0 : Fin 1)), fun i => by
    apply (degreeOf_mul_le _ _ _).trans
    fin_cases i <;> simp [degreeOf_X]⟩

private noncomputable def partialSlices (i : Fin 3) : Option (BoundedPolynomial F 1 1) :=
  if i = 0 then some zeroSlice else if i = 1 then some linearSlice else none

/-- Two compatible slices and one failure recover the bivariate product. -/
example : pasteOutcome nodes partialSlices = some productPoly := by
  apply (pasteOutcome_eq_some_iff _ _ _).mpr
  constructor
  · have hs : successfulSlices partialSlices = {0, 1} := by
      ext i
      fin_cases i <;> simp [partialSlices]
    rw [hs]
    decide
  · unfold FitsSlices
    intro i q h
    fin_cases i
    · have hq : q = zeroSlice := by simpa [partialSlices, eq_comm] using h
      subst q
      apply Subtype.ext
      change specializeLast (0 : F) productPoly.val = _
      change specializeLast (0 : F) (X (Fin.last 1) * X (Fin.castSucc (0 : Fin 1))) = 0
      rw [map_mul, specializeLast_X_last, specializeLast_X_castSucc, map_zero, zero_mul]
    · have hq : q = linearSlice := by simpa [partialSlices, eq_comm] using h
      subst q
      apply Subtype.ext
      change specializeLast (1 : F) productPoly.val = _
      change specializeLast (1 : F) (X (Fin.last 1) * X (Fin.castSucc (0 : Fin 1))) = X 0
      rw [map_mul, specializeLast_X_last, specializeLast_X_castSucc, map_one, one_mul]
    · simp [partialSlices] at h

private noncomputable def inconsistentSlices (i : Fin 3) :
    Option (BoundedPolynomial F 1 1) :=
  if i = 2 then some linearSlice else some zeroSlice

/-- Once two zero slices force the zero polynomial, an incompatible third slice fails. -/
example : pasteOutcome nodes inconsistentSlices = none := by
  cases h : pasteOutcome nodes inconsistentSlices with
  | none => rfl
  | some p =>
    exfalso
    have hf := (pasteOutcome_eq_some_iff _ _ _).mp h
    have hzero : p.val = 0 := by
      apply eq_of_specializeLast_eq (s := ({0, 1} : Finset (Fin 3))) nodes.injective.injOn
      · exact (p.prop (Fin.last 1)).trans_lt (by decide)
      · simp
      · intro j hj
        have hne : j ≠ 2 := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hj
          rcases hj with rfl | rfl <;> decide
        have hv := hf.2 j zeroSlice (by simp [inconsistentSlices, hne])
        change specializeLast (nodes j) p.val = specializeLast (nodes j) (0 : MvPolynomial _ _)
        rw [map_zero]
        exact congrArg Subtype.val hv
    have hv := hf.2 (2 : Fin 3) linearSlice (by simp [inconsistentSlices])
    have hv' : specializeLast (nodes (2 : Fin 3)) p.val = X 0 := congrArg Subtype.val hv
    rw [hzero, map_zero] at hv'
    exact (X_ne_zero (R := F) (0 : Fin 1)) hv'.symm


private noncomputable def zeroConstant : BoundedPolynomial F 0 0 := ⟨0, fun i => Fin.elim0 i⟩
private noncomputable def zeroPaste : BoundedPolynomial F 1 0 := ⟨0, by simp⟩

private noncomputable def singleSlice (x : F) :
    Measurement (Option (BoundedPolynomial F 0 0)) ℂ := by
  classical
  exact Measurement.const (if x = 0 then some zeroConstant else none)

private theorem singleSlice_projective (x : F) : (singleSlice x).IsProjective := by
  classical
  exact Measurement.isProjective_const _

private def singletonEmbedding (x : F) : Fin 1 ↪ F :=
  ⟨fun _ => x, fun _ _ _ => Subsingleton.elim _ _⟩

private def singletonEquiv : (Fin 1 ↪ F) ≃ F where
  toFun x := x 0
  invFun := singletonEmbedding
  left_inv x := by
    ext i
    rw [Subsingleton.elim i 0]
    rfl
  right_inv _ := rfl

private theorem fixed_single_slice_effect (x : Fin 1 ↪ F) (p : BoundedPolynomial F 1 0) :
    (pasteProjectiveSlices x singleSlice singleSlice_projective).effect (some p) =
      if p = zeroPaste ∧ x 0 = 0 then 1 else 0 := by
  classical
  let g (_ : Fin 1) := some zeroConstant
  have hg : pasteOutcome x g = some zeroPaste := by
    apply (pasteOutcome_eq_some_iff _ _ _).mpr
    refine ⟨Finset.card_pos.mpr ⟨0, by simp [g]⟩, ?_⟩
    intro i q h
    have hq := Option.some.inj h
    subst q
    apply Subtype.ext
    change specializeLast (x i) (0 : MvPolynomial (Fin 1) F) = 0
    exact map_zero _
  have hread : (0 < (successfulSlices g).card ∧ FitsSlices x g p) ↔ p = zeroPaste := by
    rw [← pasteOutcome_eq_some_iff, hg, Option.some.injEq, eq_comm]
  rw [pasteProjectiveSlices_effect_some]
  simp only [Measurement.sequentialProjective_effect_one, sum_filter]
  by_cases hx : x 0 = 0
  · rw [sum_eq_single_of_mem g (mem_univ g)]
    · by_cases hp : p = zeroPaste
      · rw [ite_eq_left (hread.mpr hp), ite_eq_left ⟨hp, hx⟩]
        simp [singleSlice, Measurement.const, g, hx]
      · rw [ite_eq_right (fun h => hp (hread.mp h))]
        simp [hp]
    · intro w _ hne
      have hw : w 0 ≠ some zeroConstant := fun he => hne (by
        funext i
        simpa only [Subsingleton.elim i (0 : Fin 1), g] using he)
      simp [singleSlice, Measurement.const, hx, hw]
  · simp only [hx, and_false, ite_false]
    refine sum_eq_zero fun w _ => ?_
    by_cases hw : w 0 = none
    · have hnone : successfulSlices w = ∅ := by
        ext i
        simp [Subsingleton.elim i (0 : Fin 1), hw]
      simp [hnone]
    · simp [singleSlice, Measurement.const, hx, hw]

private instance : Nonempty (Fin 1 ↪ F) := ⟨singletonEmbedding 0⟩

private theorem averaged_single_slice_effect (p : BoundedPolynomial F 1 0) :
    (pasteSlices 1 singleSlice singleSlice_projective).effect (some p) =
      if p = zeroPaste then 1 / 3 else 0 := by
  classical
  let _ : Fintype (Fin 1 ↪ F) := Fintype.ofFinite _
  rw [pasteSlices_effect]
  have hcard : Fintype.card (Fin 1 ↪ F) = 3 :=
    (Fintype.card_congr singletonEquiv).trans (ZMod.card 3)
  simp only [fixed_single_slice_effect, Cslib.Probability.PMF.uniformOfFintype_apply, hcard,
    ENNReal.toReal_inv]
  let term (t : F) : ℂ := (3 : ℝ)⁻¹ • (if p = zeroPaste ∧ t = 0 then 1 else 0)
  change (∑ x : Fin 1 ↪ F, term (singletonEquiv x)) = _
  rw [Equiv.sum_comp]
  by_cases hp : p = zeroPaste
  · simp [term, hp, one_div, Algebra.smul_def]
  · simp [term, hp]

/-- The average samples each singleton slice uniformly. Only the slice at zero
can produce the zero polynomial, and the remaining mass is failure. -/
example :
    (pasteSlices 1 singleSlice singleSlice_projective).effect (some zeroPaste) = 1 / 3 ∧
    (pasteSlices 1 singleSlice singleSlice_projective).effect none = 2 / 3 := by
  classical
  refine ⟨by simp [averaged_single_slice_effect], ?_⟩
  have h := (pasteSlices 1 singleSlice singleSlice_projective).sum_effect
  rw [Fintype.sum_option] at h
  simp only [averaged_single_slice_effect, sum_ite_eq', mem_univ, ite_true] at h
  linear_combination h

private abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
private def diagonalProjection : Mat := !![1, 0; 0, 0]
private noncomputable def uniformProjection : Mat := !![1 / 2, 1 / 2; 1 / 2, 1 / 2]

private theorem diagonalProjection_star : star diagonalProjection = diagonalProjection := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonalProjection, Matrix.star_apply]

private theorem uniformProjection_star : star uniformProjection = uniformProjection := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uniformProjection, Matrix.star_apply]

private theorem diagonalProjection_sq :
    diagonalProjection * diagonalProjection = diagonalProjection := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [diagonalProjection, Matrix.mul_apply, Fin.sum_univ_two]

private theorem uniformProjection_sq :
    uniformProjection * uniformProjection = uniformProjection := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [uniformProjection, Matrix.mul_apply, Fin.sum_univ_two]

private def binary (e : Mat) (he : star e = e) (he₂ : e * e = e) : Measurement Bool Mat where
  effect b := if b then e else 1 - e
  nonneg b := by
    cases b
    · have hc : (1 - e) * (1 - e) = 1 - e := (show IsIdempotentElem e from he₂).one_sub
      simpa only [Bool.false_eq_true, ite_false, star_sub, star_one, he, hc]
        using star_mul_self_nonneg (1 - e)
    · simpa only [ite_true, he, he₂] using star_mul_self_nonneg e
  sum_effect := by simp

private theorem binary_projective (e : Mat) (he : star e = e) (he₂ : e * e = e) :
    (binary e he he₂).IsProjective := by
  intro b
  cases b
  · exact (show IsIdempotentElem e from he₂).one_sub
  · exact he₂

private theorem pair_projective (D U : Measurement Bool Mat)
    (hD : D.IsProjective) (hU : U.IsProjective) :
    ∀ i : Fin 2, (![D, U] i).IsProjective := by
  intro i
  fin_cases i
  · exact hD
  · exact hU

/-- The first measurement sandwiches the second, with distinct values for the
off-diagonal entry when the order is reversed. -/
example :
    let D := binary diagonalProjection diagonalProjection_star diagonalProjection_sq
    let U := binary uniformProjection uniformProjection_star uniformProjection_sq
    let hD := binary_projective _ diagonalProjection_star diagonalProjection_sq
    let hU := binary_projective _ uniformProjection_star uniformProjection_sq
    ((Measurement.sequentialProjective ![D, U] (pair_projective D U hD hU)).effect
      (fun _ => true)) 0 1 = 0 ∧
    ((Measurement.sequentialProjective ![U, D] (pair_projective U D hU hD)).effect
      (fun _ => true)) 0 1 = 1 / 4 := by
  intro D U hD hU
  constructor
  · rw [Measurement.sequentialProjective_effect_succ, Measurement.sequentialProjective_effect_one]
    change (diagonalProjection * uniformProjection * diagonalProjection) 0 1 = 0
    norm_num [diagonalProjection, uniformProjection, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [Measurement.sequentialProjective_effect_succ, Measurement.sequentialProjective_effect_one]
    change (uniformProjection * diagonalProjection * uniformProjection) 0 1 = 1 / 4
    norm_num [diagonalProjection, uniformProjection, Matrix.mul_apply, Fin.sum_univ_two]
