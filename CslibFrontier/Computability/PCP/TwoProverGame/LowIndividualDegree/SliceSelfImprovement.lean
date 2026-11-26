/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.ProjectiveSelfImprovement
public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.SliceRestriction
public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.VerifierPasting
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Foundations.Data.Finset.Holder
import CslibFrontier.Foundations.Quantum.Algebra.CStar
import CslibFrontier.Foundations.Quantum.Algebra.MaxEntangled

/-!
# Pasting self-improved coordinate slices

Apply projective self-improvement to each restricted strategy, then paste the
resulting projective submeasurements on the original local space. This
combines self-improvement and pasting in [JNVWY2020LowIndividualDegree, §6.2].

## Main results

* `Cslib.PCP.LowIndividualDegree.exists_paste_of_slice_agreement` constructs
  a complete ambient polynomial measurement from measurements on all slices.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Cslib.Quantum Matrix Finset
open scoped BigOperators Real MatrixOrder ComplexOrder Kronecker Matrix.Norms.L2Operator

variable {F ι : Type*} {n d : ℕ} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι]

local notation "Local" => Matrix ι ι ℂ
local notation "Joint" => Matrix (ι × ι) (ι × ι) ℂ
local notation "SlicePoly" => BoundedPolynomial F n d
local notation "AmbientPoly" => BoundedPolynomial F (n + 1) d

private theorem transcriptProduct_lift {α : Type*} [Fintype α] {k : ℕ}
    (e : Local →⋆ₐ[ℂ] Joint) (M : Fin k → Measurement α Local)
    (N : Fin k → Measurement α Joint) (he : ∀ j a, e ((M j).effect a) = (N j).effect a)
    (g : Fin k → α) :
    e (Measurement.transcriptProduct M g) = Measurement.transcriptProduct N g := by
  induction k with
  | zero => simp only [Measurement.transcriptProduct_zero, map_one]
  | succ k ih =>
    rw [Measurement.transcriptProduct_succ, Measurement.transcriptProduct_succ,
      map_mul, he, ih _ _ fun j a => he j.succ a]

private theorem completedPaste_effect_lift
    (e : Local →⋆ₐ[ℂ] Joint) (k : ℕ) [Nonempty (Fin k ↪ F)]
    (M : F → Measurement (Option SlicePoly) Local) (hM : ∀ t, (M t).IsProjective)
    (N : F → Measurement (Option SlicePoly) Joint) (hN : ∀ t, (N t).IsProjective)
    (he : ∀ t a, e ((M t).effect a) = (N t).effect a)
    (fallback p : AmbientPoly) :
    e ((completedPaste k M hM fallback).effect p) = (completedPaste k N hN fallback).effect p := by
  classical
  have hseq (x : Fin k ↪ F) (a : Option AmbientPoly) :
      e ((pasteProjectiveSlices x M hM).effect a) = (pasteProjectiveSlices x N hN).effect a := by
    simp only [pasteProjectiveSlices, pasteMeasurement, Measurement.map_effect, map_sum]
    refine sum_congr rfl fun g _ => ?_
    simp only [Measurement.sequentialProjective_effect, map_mul, map_star]
    rw [transcriptProduct_lift e _ _ (fun j a => he (x j) a)]
  have hpaste (a : Option AmbientPoly) :
      e ((pasteSlices k M hM).effect a) = (pasteSlices k N hN).effect a := by
    let _ : Fintype (Fin k ↪ F) := Fintype.ofFinite _
    rw [pasteSlices_effect, pasteSlices_effect]
    change (e.toAlgHom.restrictScalars ℝ) _ = _
    simp only [map_sum, map_smul, AlgHom.coe_restrictScalars', StarAlgHom.coe_toAlgHom, hseq]
  simp only [completedPaste_eq_map, Measurement.map_effect, map_sum, hpaste]

private theorem rightMeasurement_completedPaste
    (k : ℕ) [Nonempty (Fin k ↪ F)] (P : F → POVM (Option SlicePoly) ι)
    (hP : ∀ x, (P x).toMeasurement.IsProjective) (fallback : AmbientPoly) :
    QuantumStrategy.rightMeasurement (ι := ι)
      (completedPaste k (fun x => (P x).toMeasurement) hP fallback).toPOVM =
      completedPaste k (fun x => QuantumStrategy.rightMeasurement (ι := ι) (P x))
        (fun x => QuantumStrategy.rightMeasurement_isProjective (P x) (hP x)) fallback :=
  Measurement.ext fun a =>
    completedPaste_effect_lift oneKronecker k _ hP _ _ (fun _ _ => rfl) fallback a

omit [DecidableEq F] in
private theorem average_slice_budget
    (εs δs : F → ℝ) (ε δ r : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hr : 0 ≤ r) (he : ∀ x, 0 ≤ εs x) (hd : ∀ x, 0 ≤ δs x)
    (haxis : (n + 1 : ℝ) * (𝔼 x, εs x) ≤ (n + 2 : ℝ) * ε)
    (hcons : (𝔼 x, δs x) ≤ δ) :
    (𝔼 x, 3000 * (n + 1 : ℝ) *
      (εs x ^ (1 / 32 : ℝ) + δs x ^ (1 / 32 : ℝ) + r ^ (1 / 32 : ℝ))) ≤
    3000 * (n + 2 : ℝ) * (ε ^ (1 / 32 : ℝ) + δ ^ (1 / 32 : ℝ) + r ^ (1 / 32 : ℝ)) := by
  let m := (n + 1 : ℝ)
  let M := (n + 2 : ℝ)
  have hm : 0 < m := by dsimp [m]; positivity
  have hmM : m ≤ M := by dsimp [m, M]; linarith
  have hscale := Fintype.mul_expect_rpow_le_of_mul_expect_le he hm hmM hε
    (p := 1 / 32) (by norm_num) (by norm_num) haxis
  have hδ' := (mul_le_mul_of_nonneg_left hcons hm.le).trans
    (mul_le_mul_of_nonneg_right hmM hδ)
  have hscaleδ := Fintype.mul_expect_rpow_le_of_mul_expect_le hd hm hmM hδ
    (p := 1 / 32) (by norm_num) (by norm_num) hδ'
  have hscaler := mul_le_mul_of_nonneg_right hmM (Real.rpow_nonneg hr (1 / 32 : ℝ))
  change (𝔼 x, 3000 * m * (εs x ^ (1 / 32 : ℝ) + δs x ^ (1 / 32 : ℝ) +
    r ^ (1 / 32 : ℝ))) ≤ 3000 * M * _
  simp only [← mul_expect, expect_add_distrib, Fintype.expect_const]
  linarith only [hscale, hscaleδ, hscaler]

local notation "Q" => Question F (n + 2)
local notation "Ans" => Answer F (n + 2)
local notation "Poly" => BoundedPolynomial F (n + 1) d
local notation "Result" => BoundedPolynomial F (n + 2) d

/-- The disagreement bound for one paste in ambient dimension `m`.
Here `ε, δ, γ` are the branch losses, `r` is the degree divided by the field
size, `q` is the field size, and `σ` is the mean error of the input slices. -/
@[expose] noncomputable def slicePastingError
    (m : ℝ) (k : ℕ) (q ε δ γ r σ θ : ℝ) : ℝ :=
  let ζ := 3000 * m * (ε ^ (1 / 32 : ℝ) + δ ^ (1 / 32 : ℝ) + r ^ (1 / 32 : ℝ))
  let κ := σ + ζ
  let verticalError := √(8 * m * ε + 4 * δ)
  let commutatorError :=
    32 * (4 * √(2 * ζ) + 2 * √(64 * m * γ) + 2 * √ζ + 2 * √ζ) +
      30 * ζ + 20 * ((m - 1) * r)
  let sliceError := √(162 * commutatorError + 176 * ζ)
  κ / (1 - θ) + Real.exp (-(θ ^ 2 * k) / 2) +
  (1 + √2) * (k * √(2 * ζ) + (k : ℝ) ^ 2 * sliceError) +
  3 * ((k.choose 2 : ℝ) / q) + (m - 1) * r +
  2 * k * ζ + (2 * k + 1 : ℝ) * verticalError + 2 * k * ((k - 1 : ℕ) : ℝ) * sliceError

/-- One step of the symmetric low-individual-degree induction. From a polynomial
measurement agreeing with the points on each slice, construct one complete
polynomial POVM on the original local space. The diagonal cutoff is fixed for
the induction, and the quantitative estimate uses the actual ambient losses. -/
theorem exists_paste_of_slice_agreement
    (S : QuantumStrategy Q Q Ans Ans ι ι) (D k : ℕ)
    [Nonempty (Fin k ↪ F)] (hk : 0 < k)
    (hM : S.bob = S.alice)
    (hψ : ∀ a b, S.state.ofLp (a, b) = S.state.ofLp (b, a))
    (hprojective : ∀ q, ((S.alice q).toMeasurement).IsProjective)
    (G : F → POVM (Option Poly) ι) (σ : F → ℝ) (θ : ℝ)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hsize : 2 * (d : ℝ) ≤ θ * k)
    (hinput : ∀ x, 1 - σ x ≤ 𝔼 u : Point F (n + 1), ∑ g : Poly,
      (S.toCommuting.state ((QuantumStrategy.rightMeasurement (G x)).effect (some g) *
        (decodedPoint S.toCommuting.alice (Fin.snoc u x)).effect (MvPolynomial.eval u g.val))).re) :
    let C := S.toCommuting
    let ε := 1 - (branchGame (F := F) (n + 1) d .axis).commutingWinProb C
    let δ := 1 - (branchGame (F := F) (n + 1) d .consistency).commutingWinProb C
    let γ :=
      1 - (branchGameWithDiagonalCap (F := F) (n + 1) d D .diagonal).commutingWinProb C
    let r := (d : ℝ) / Fintype.card F
    ∃ H : POVM Result ι,
      (𝔼 w : Point F (n + 2), (1 - Measurement.agreement C.state
        ((QuantumStrategy.rightMeasurement H).map (fun p => MvPolynomial.eval w p.val))
        (decodedPoint C.alice w))) ≤
        slicePastingError (n + 2) k (Fintype.card F) ε δ γ r (𝔼 x, σ x) θ := by
  classical
  intro C ε δ γ r
  let ζ := 3000 * (n + 2 : ℝ) * (ε ^ (1 / 32 : ℝ) + δ ^ (1 / 32 : ℝ) + r ^ (1 / 32 : ℝ))
  let κ := (𝔼 x, σ x) + ζ
  let T (x : F) := restrictSliceTensor S x
  let εs (x : F) := 1 - (branchGame (F := F) n d .axis).commutingWinProb (T x).toCommuting
  let δs (x : F) := 1 - (branchGame (F := F) n d .consistency).commutingWinProb (T x).toCommuting
  let ζs (x : F) :=
    3000 * (n + 1 : ℝ) * (εs x ^ (1 / 32 : ℝ) + δs x ^ (1 / 32 : ℝ) + r ^ (1 / 32 : ℝ))
  have hstate (x : F) : (T x).toCommuting.state = C.state := restrictSliceTensor_joint_state S x
  have hpt (x : F) (u : Point F (n + 1)) :
      decodedPoint (T x).toCommuting.alice u = decodedPoint C.alice (Fin.snoc u x) := by
    simp only [T, C, restrictSliceTensor_toCommuting, decodedPoint_restrictSlice]
  have hex (x : F) :=
    exists_projectiveSymmetricSelfImprovement (T x) (G x) (σ x)
      (restrictSliceTensor_bob_eq_alice S x hM)
      (by simpa only [T, restrictSliceTensor_state] using hψ)
      (restrictSliceTensor_alice_isProjective S x hprojective)
      (by simpa only [hstate, hpt] using hinput x)
  choose P Z hP₀ hZ₀ hmajor₀ hmass₀ hpoint₀ hgap₀ hcopy₀ using hex
  let M (x : F) := QuantumStrategy.rightMeasurement (ι := ι) (P x)
  let R (x : F) := QuantumStrategy.leftMeasurement (κ := ι) (P x)
  let W (x : F) := Z x ⊗ₖ (1 : Local)
  have hMpr (x : F) : (M x).IsProjective :=
    QuantumStrategy.rightMeasurement_isProjective (P x) (hP₀ x)
  have hRpr (x : F) : (R x).IsProjective :=
    QuantumStrategy.leftMeasurement_isProjective (P x) (hP₀ x)
  have hComm (x : F) (q : Q) (a : Option Poly) (b : Ans) :
      Commute ((M x).effect a) ((C.alice q).effect b) :=
    (commute_kroneckerOne_oneKronecker ((S.alice q).effect b) ((P x).effect a)).symm
  have hCopies (x y : F) (a b : Option Poly) :
      Commute ((M x).effect a) ((R y).effect b) :=
    (commute_kroneckerOne_oneKronecker ((P y).effect b) ((P x).effect a)).symm
  have hMW (x y : F) (a : Option Poly) : Commute ((M x).effect a) (W y) :=
    (commute_kroneckerOne_oneKronecker (Z y) ((P x).effect a)).symm
  have hbudget : (𝔼 x, ζs x) ≤ ζ := by
    apply average_slice_budget εs δs ε δ r
      (sub_nonneg.mpr (TwoProverGame.commutingWinProb_le_one _ _))
      (sub_nonneg.mpr (TwoProverGame.commutingWinProb_le_one _ _))
      (by dsimp only [r]; positivity)
      (fun _ => sub_nonneg.mpr (TwoProverGame.commutingWinProb_le_one _ _))
      (fun _ => sub_nonneg.mpr (TwoProverGame.commutingWinProb_le_one _ _))
    · simpa only [εs, T, restrictSliceTensor_toCommuting, axisWinProbAtDegrees_eq] using
        average_slice_axis_loss_le C d D
    · simpa only [δs, T, restrictSliceTensor_toCommuting, consistencyWinProbAtDegrees_eq] using
        average_slice_consistency_loss_le C d D
  have hZ (x : F) : 0 ≤ W x :=
    ((hZ₀ x).posSemidef.kronecker PosSemidef.one).nonneg
  have hbound (x : F) (g : Poly) :
      averagePolynomialPointEffect (fun u => decodedPoint C.alice (Fin.snoc u x)) g ≤ W x := by
    simp_rw [← hpt x]
    change averagePolynomialPointEffect
      (decodedPoint fun q => QuantumStrategy.leftMeasurement (κ := ι) ((T x).alice q)) g ≤ W x
    rw [← averagePolynomialPointEffect_leftMeasurement]
    exact OrderHomClass.mono (kroneckerOne (κ := ι)) (hmajor₀ x g)
  have hmass : 1 - κ ≤ (C.state (Measurement.averageSuccessEffect R Option.isSome)).re := by
    rw [Measurement.averageSuccessEffect_eq, AlgState.re_apply_uniformAverage]
    have hm := expect_le_expect (s := univ) fun x _ =>
      (show 1 - σ x - ζs x ≤ (C.state (R x).successfulEffect).re from by
        simpa only [hstate] using hmass₀ x)
    simp only [expect_sub_distrib, Fintype.expect_const] at hm
    have hsum (x : F) : (∑ a with a.isSome, (R x).effect a) = (R x).successfulEffect := by
      simp [Measurement.successfulEffect, sum_filter, Fintype.sum_option]
    simp only [hsum, κ]
    linarith only [hm, hbudget]
  have hpoint : (𝔼 u : Point F (n + 1), 𝔼 x : F, Measurement.successfulMismatch C.state
      (evaluatePolynomialMeasurement (M x) u) (decodedPoint C.alice (Fin.snoc u x))) ≤ ζ := by
    rw [expect_comm]
    refine (expect_le_expect fun x _ => ?_).trans hbudget
    simpa only [hstate, hpt] using hpoint₀ x
  have hcopy : (𝔼 x : F, Measurement.successfulCopyDefect C.state (M x) (R x)) ≤ ζ := by
    refine (expect_le_expect fun x _ => ?_).trans hbudget
    dsimp only [Measurement.successfulCopyDefect]
    refine (sum_congr rfl fun g _ => congrArg (· ^ 2) (C.state.norm_sub_comm _ _)).trans_le ?_
    simpa only [Measurement.successfulCopyDefect, hstate] using hcopy₀ x
  have hgap : (𝔼 x : F, (C.state ((M x).effect none * W x)).re) ≤ ζ := by
    refine (expect_le_expect fun x _ => ?_).trans hbudget
    rw [(hMW x x none).eq]
    simpa only [hstate] using hgap₀ x
  let fallback : Result := ⟨0, by simp⟩
  let H := (completedPaste k (fun x => (P x).toMeasurement) hP₀ fallback).toPOVM
  have hpaste := average_completedPaste_disagreement_le_of_slice_majorants_atDegrees
    k hk C.swap D
    (fun u => QuantumStrategy.leftMeasurement_isProjective (S.alice (.point u))
      (hprojective (.point u)))
    (fun L => QuantumStrategy.rightMeasurement_isProjective (S.bob (.diagonal L))
      (by rw [hM]; exact hprojective _))
    M R hMpr hRpr hComm hCopies W hZ hbound hMW
    fallback hθ₀ hθ₁ hsize hmass hcopy hgap hpoint
  have haxis := TwoProverGame.commutingWinProb_swap_of_symmetric
    (branchGame (F := F) (n + 1) d .axis) S hM hψ
  have hcons := TwoProverGame.commutingWinProb_swap_of_symmetric
    (branchGame (F := F) (n + 1) d .consistency) S hM hψ
  change _ ≤ _ at hpaste
  have hswap : C.swap.swap = C := by
    cases C
    rfl
  rw [haxis, hcons, hswap] at hpaste
  refine ⟨H, ?_⟩
  rw [← Fintype.expect_fin_snoc]
  change (𝔼 u : Point F (n + 1), 𝔼 x : F, (1 - Measurement.agreement C.state
    ((QuantumStrategy.rightMeasurement H).map (fun p => MvPolynomial.eval (Fin.snoc u x) p.val))
    (decodedPoint C.alice (Fin.snoc u x)))) ≤ _
  rw [rightMeasurement_completedPaste k P hP₀ fallback]
  dsimp only [slicePastingError, ε, δ, γ, r]
  simp only [show (n + 2 : ℝ) - 1 = n + 1 by ring, ← mul_div_assoc (n + 1 : ℝ)]
  simpa only [Nat.cast_succ, show (n + 1 : ℝ) + 1 = n + 2 by ring, C, CommutingStrategy.swap]
    using hpaste

end Cslib.PCP.LowIndividualDegree
