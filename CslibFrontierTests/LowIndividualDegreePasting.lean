/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.VerifierPasting
import CslibFrontierTests.QubitMeasurementFixture
import Mathlib.Algebra.Field.ZMod

/-! # Pasting on three slices over the field with three elements -/

set_option linter.privateModule false

open Cslib.PCP Cslib.PCP.LowIndividualDegree Cslib.Quantum MvPolynomial Finset
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator BigOperators Real
open Matrix CslibFrontierTests.QubitMeasurementFixture

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
private theorem inconsistentSlices_fail : pasteOutcome nodes inconsistentSlices = none := by
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


open scoped Classical in
/-- The three incompatible slices can agree with a line at at most one prefix. -/
example :
    (Finset.univ.filter fun u => LocallyInterpolable nodes inconsistentSlices u).card ≤ 1 := by
  have hcard : 1 < (successfulSlices inconsistentSlices).card := by
    have h : successfulSlices inconsistentSlices = Finset.univ := by
      ext i
      by_cases hi : i = 2 <;> simp [inconsistentSlices, hi]
    rw [h, Finset.card_univ]
    decide
  have h := card_locallyInterpolable_mul_card_le nodes inconsistentSlices hcard
    inconsistentSlices_fail
  simp only [ZMod.card, Nat.pow_one, Nat.one_mul] at h
  omega

private def twoNodes : Fin 2 ↪ F :=
  (Fin.castSuccEmb (n := 2)).trans nodes

private noncomputable def zeroTranscript (_ : Fin 2) : Option (BoundedPolynomial F 1 1) :=
  some zeroSlice

/-- A zero readout differs from the line `t ↦ t` at the unsampled coordinate two.
The mismatch bound charges the disagreement on the sampled coordinate one. -/
example :
    ((PMF.pure (zeroTranscript, ())).map (Prod.map (pasteOutcome twoNodes) id)).toOuterMeasure
        (pastedLineMismatch (d := 1) (m := 1) (0 : Fin 1 → F) 2 (fun (_ : Unit) t => t)) = 1 ∧
      (∑ i : Fin 2, ((PMF.pure (zeroTranscript, ())).toOuterMeasure
        (sliceLineMismatch (0 : Fin 1 → F) twoNodes (fun (_ : Unit) t => t) i)).toReal) = 1 := by
  classical
  let p : BoundedPolynomial F 2 1 := ⟨0, by simp⟩
  have hp : pasteOutcome twoNodes zeroTranscript = some p := by
    apply (pasteOutcome_eq_some_iff _ _ _).mpr
    constructor
    · have hs : successfulSlices zeroTranscript = Finset.univ := by
        ext i
        simp [zeroTranscript]
      rw [hs]
      decide
    · intro i q h
      have he : q = zeroSlice := (Option.some.inj h).symm
      subst q
      apply Subtype.ext
      change specializeLast _ (0 : MvPolynomial (Fin 2) F) = 0
      exact map_zero _
  constructor
  · rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_pure_apply]
    have hm : (Prod.map (pasteOutcome twoNodes) id (zeroTranscript, ())) ∈
        pastedLineMismatch (d := 1) (0 : Fin 1 → F) 2 (fun (_ : Unit) t => t) := by
      unfold pastedLineMismatch
      refine ⟨p, hp, ?_⟩
      change eval (Fin.snoc (0 : Fin 1 → F) (2 : F)) (0 : MvPolynomial (Fin 2) F) ≠ 2
      rw [map_zero]
      decide
    exact ite_eq_left hm
  · rw [Fin.sum_univ_two]
    have hzero :
        (zeroTranscript, ()) ∉ sliceLineMismatch (0 : Fin 1 → F) twoNodes
          (fun (_ : Unit) t => t) (0 : Fin 2) := by
      rintro ⟨q, he, hne⟩
      have hq : q = zeroSlice := (Option.some.inj he).symm
      subst q
      apply hne
      change eval (0 : Fin 1 → F) (0 : MvPolynomial (Fin 1) F) = 0
      exact map_zero _
    have hone :
        (zeroTranscript, ()) ∈ sliceLineMismatch (0 : Fin 1 → F) twoNodes
          (fun (_ : Unit) t => t) (1 : Fin 2) := by
      refine ⟨zeroSlice, rfl, ?_⟩
      change eval (0 : Fin 1 → F) (0 : MvPolynomial (Fin 1) F) ≠ 1
      rw [map_zero]
      exact zero_ne_one
    simp only [PMF.toOuterMeasure_pure_apply, hzero, hone, ↓reduceIte,
      ENNReal.toReal_zero, ENNReal.toReal_one, zero_add]
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

private theorem averaged_single_slice_failure :
    (pasteSlices 1 singleSlice singleSlice_projective).effect none = 2 / 3 := by
  classical
  have h := (pasteSlices 1 singleSlice singleSlice_projective).sum_effect
  rw [Fintype.sum_option] at h
  simp only [averaged_single_slice_effect, sum_ite_eq', mem_univ, ite_true] at h
  linear_combination h

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

private noncomputable def zeroVerifier (φ : AlgState ℂ) :
    CommutingStrategy (Question F 1) (Question F 1) (Answer F 1) (Answer F 1) ℂ := by
  classical
  exact {
    state := φ
    alice q := Measurement.const (honest zeroPaste.val q)
    bob q := Measurement.const (honest zeroPaste.val q)
    commute _ _ _ _ := Commute.all _ _ }

private theorem zeroVerifier_score (φ : AlgState ℂ) (b : Branch) :
    (branchGame (F := F) 0 0 b).commutingWinProb (zeroVerifier φ) = 1 := by
  classical
  let reply := honest zeroPaste.val
  have h (x y : Question F 1) :
      (zeroVerifier φ).answers x y = PMF.pure (reply x, reply y) := by
    ext ⟨a, c⟩
    rw [CommutingStrategy.answers_apply, PMF.pure_apply]
    by_cases ha : a = reply x <;> by_cases hc : c = reply y <;>
      simp [zeroVerifier, CommutingStrategy.prob, Measurement.const, reply, ha, hc]
  calc
    _ = (branchGame (F := F) 0 0 b).quantumWinProb
        (QuantumStrategy.ofDeterministic reply reply) := by
      rw [TwoProverGame.commutingWinProb, TwoProverGame.quantumWinProb]
      congr 1
      funext x y
      rw [h, QuantumStrategy.answers_ofDeterministic]
    _ = 1 := by
      rw [TwoProverGame.quantumWinProb_ofDeterministic]
      exact winProb_branch_honest zeroPaste.val zeroPaste.prop b

private theorem singleSlice_mismatch_zero (φ : AlgState ℂ) (u : Point F 0) (t : F) :
    Measurement.successfulMismatch φ (evaluatePolynomialMeasurement (singleSlice t) u)
      (decodedPoint (zeroVerifier φ).bob (Fin.snoc u t)) = 0 := by
  classical
  rw [evaluatePolynomialMeasurement, decodedPoint, Measurement.successfulMismatch_map_map]
  refine sum_eq_zero fun a _ => sum_eq_zero fun b _ => ?_
  by_cases ht : t = 0
  · have hv : honest zeroPaste.val (.point (Fin.snoc u 0)) = Sum.inl (0 : F) := by
      rw [honest_point]
      simp [zeroPaste]
    have hz : eval u zeroConstant.val = 0 := by simp [zeroConstant]
    by_cases ha : a = some zeroConstant <;> by_cases hb : b = Sum.inl (0 : F) <;>
      simp [singleSlice, zeroVerifier, Measurement.const, hv, hz, ht, ha, hb]
  · by_cases ha : a = none <;>
      simp [singleSlice, Measurement.const, ht, ha]

/-- A one-slice paste passes the degree-zero threshold. The successful effect has
mass one third and agrees with the honest point answer. The two thirds of failure
mass contribute zero to the verifier-pasting mismatch bound. -/
example (φ : AlgState ℂ) :
    (pasteSlices 1 singleSlice singleSlice_projective).effect (some zeroPaste) = 1 / 3 ∧
    (pasteSlices 1 singleSlice singleSlice_projective).effect none = 2 / 3 ∧
    (𝔼 u : Point F 0, 𝔼 t : F, Measurement.successfulMismatch φ
      (evaluatePolynomialMeasurement (pasteSlices 1 singleSlice singleSlice_projective)
        (Fin.snoc u t)) (decodedPoint (zeroVerifier φ).bob (Fin.snoc u t))) ≤ 0 := by
  classical
  refine ⟨by simp [averaged_single_slice_effect], averaged_single_slice_failure, ?_⟩
  have hpair : (𝔼 x : F, 𝔼 y : F,
      Measurement.successfulPairDefect φ (singleSlice x) (singleSlice y)) ≤ 0 := by
    simp [Measurement.successfulPairDefect, mul_comm]
  have hcopy : (𝔼 x : F, Measurement.successfulCopyDefect φ (singleSlice x) (singleSlice x)) ≤ 0 :=
    by simp [Measurement.successfulCopyDefect]
  have hp : (𝔼 u : Point F 0, 𝔼 t : F, Measurement.successfulMismatch φ
      (evaluatePolynomialMeasurement (singleSlice t) u)
      (decodedPoint (zeroVerifier φ).bob (Fin.snoc u t))) ≤ 0 := by
    simp [singleSlice_mismatch_zero]
  have h := average_pastedPointMismatch_le_of_verifier 1 (zeroVerifier φ)
    singleSlice singleSlice singleSlice_projective singleSlice_projective
    (fun _ _ _ _ => Commute.all _ _) (fun _ _ _ _ => Commute.all _ _)
    hpair hcopy hp
  norm_num [zeroVerifier_score] at h ⊢
  exact h

open scoped Classical in
/-- Even a successful slice cannot meet the degree-one threshold on a single
sample. Completion puts the resulting unit failure effect on the chosen polynomial. -/
example :
    let M (_ : F) : Measurement (Option (BoundedPolynomial F 1 1)) ℂ :=
      Measurement.const (some zeroSlice)
    let hp (_ : F) := Measurement.isProjective_const (A := ℂ) (some zeroSlice)
    (pasteSlices 1 M hp).effect none = 1 ∧
      (completedPaste 1 M hp productPoly).effect productPoly = 1 := by
  intro M hp
  have hs (p : BoundedPolynomial F 2 1) : (pasteSlices 1 M hp).effect (some p) = 0 := by
    rw [pasteSlices_effect]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [pasteProjectiveSlices_effect_some]
    suffices hempty : (Finset.univ.filter fun g : Fin 1 → Option (BoundedPolynomial F 1 1) =>
        1 < (successfulSlices g).card ∧ FitsSlices x g p) = ∅ by
      rw [hempty, Finset.sum_empty, smul_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro g hg
    have hcard := Finset.card_le_univ (successfulSlices g)
    simp only [Fintype.card_fin] at hcard
    exact (not_lt_of_ge hcard) (Finset.mem_filter.mp hg).2.1
  have hf : (pasteSlices 1 M hp).effect none = 1 := by
    rw [Measurement.effect_none_eq_one_sub_successfulEffect]
    simp [Measurement.successfulEffect, hs]
  exact ⟨hf, by rw [completedPaste_effect]; simp [hf, hs]⟩
