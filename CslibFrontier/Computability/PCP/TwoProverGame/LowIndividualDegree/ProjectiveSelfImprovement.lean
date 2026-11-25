/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.TensorSelfImprovement
import CslibFrontier.Foundations.Quantum.Algebra.CompletionConsistency
import CslibFrontier.Foundations.Quantum.Algebra.CStar
import CslibFrontier.Foundations.Quantum.Algebra.MaxEntangled
import CslibFrontier.Foundations.Quantum.Algebra.TensorState
import CslibFrontier.Foundations.Quantum.Orthogonalization

/-!
# Projective self-improvement

Complete the nonprojective output with its failure outcome, and apply
same-space orthogonalization with the state's local marginal. The completed
agreement controls relabeling by polynomial evaluation, allowing the four
bounds to pass to the projective output.

## Main results

* `Cslib.PCP.LowIndividualDegree.exists_projectiveSymmetricSelfImprovement`
  proves the symmetric self-improvement theorem with projective output.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Cslib.Quantum Matrix Finset
open scoped BigOperators Kronecker MatrixOrder ComplexOrder Real Matrix.Norms.L2Operator

variable {F ι : Type*} {n d : ℕ} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι]

local notation "Q" => Question F (n + 1)
local notation "Ans" => Answer F (n + 1)
local notation "Poly" => BoundedPolynomial F (n + 1) d
local notation "Local" => Matrix ι ι ℂ

private theorem exists_projective_approx_of_symmetric_successfulGap
    {α : Type*} [Fintype α]
    (ψ : EuclideanSpace ℂ (ι × ι)) (hψ : ‖ψ‖ = 1)
    (hswap : ∀ a b, ψ.ofLp (a, b) = ψ.ofLp (b, a))
    (H : POVM (Option α) ι) (ζ : ℝ)
    (hgap : let φ := AlgState.vector ψ hψ
      let L := QuantumStrategy.leftMeasurement (κ := ι) H
      let R := QuantumStrategy.rightMeasurement (ι := ι) H
      (φ L.successfulEffect).re - ∑ a, (φ (L.effect (some a) * R.effect (some a))).re ≤ ζ) :
    ∃ P : POVM (Option α) ι, P.toMeasurement.IsProjective ∧
      let φ := AlgState.vector ψ hψ
      1 - 2 * ζ ≤ Measurement.agreement φ
        (QuantumStrategy.leftMeasurement H) (QuantumStrategy.rightMeasurement H) ∧
      (∑ a : Option α, φ.norm ((H.effect a - P.effect a) ⊗ₖ (1 : Local)) ^ 2) ≤ 18 * ζ ∧
      (∑ a : Option α, φ.norm ((1 : Local) ⊗ₖ (H.effect a - P.effect a)) ^ 2) ≤ 18 * ζ := by
  classical
  let φ := AlgState.vector ψ hψ
  let L := QuantumStrategy.leftMeasurement (κ := ι) H
  let R := QuantumStrategy.rightMeasurement (ι := ι) H
  have hφ (X Y : Local) : φ (X ⊗ₖ Y) = φ (Y ⊗ₖ X) :=
    AlgState.vector_kronecker_swap ψ hψ hswap X Y
  have hmass : (φ L.successfulEffect).re = (φ R.successfulEffect).re := by
    suffices φ L.successfulEffect = φ R.successfulEffect by rw [this]
    rw [Measurement.successfulEffect, Measurement.successfulEffect, map_sum, map_sum]
    exact sum_congr rfl fun a _ => hφ (H.effect (some a)) 1
  have hc (a b : Option α) : Commute (L.effect a) (R.effect b) :=
    commute_kroneckerOne_oneKronecker (H.effect a) (H.effect b)
  have hcomplete : 1 - 2 * ζ ≤ Measurement.agreement φ L R := by
    have h := Measurement.one_sub_agreement_le_two_mul_successfulGap φ L R hc hmass
    change (φ L.successfulEffect).re - ∑ a, (φ (L.effect (some a) * R.effect (some a))).re ≤
      ζ at hgap
    linarith only [h, hgap]
  have hsquare (a : Option α) : (φ (L.effect a * L.effect a)).re =
      (φ (R.effect a * R.effect a)).re := by
    change (φ ((H.effect a ⊗ₖ (1 : Local)) * (H.effect a ⊗ₖ (1 : Local)))).re =
      (φ (((1 : Local) ⊗ₖ H.effect a) * ((1 : Local) ⊗ₖ H.effect a))).re
    simpa only [← mul_kronecker_mul, Matrix.one_mul] using
      congrArg Complex.re (hφ (H.effect a * H.effect a) 1)
  have hlocal : 1 - 2 * ζ ≤ ∑ a, (φ (kroneckerOne (κ := ι)
      (H.toMeasurement.effect a * H.toMeasurement.effect a))).re := by
    refine hcomplete.trans ((Measurement.agreement_le_sum_effect_sq_of_equal φ L R
      (fun a => hc a a) hsquare).trans_eq ?_)
    refine sum_congr rfl fun a _ => ?_
    change (φ (kroneckerOne (H.effect a) * kroneckerOne (H.effect a))).re = _
    rw [map_mul (kroneckerOne (κ := ι)), POVM.toMeasurement_effect]
  obtain ⟨P, hP, hround⟩ := Measurement.exists_isProjective_sum_norm_map_sub_sq_le_of_le
    φ (kroneckerOne (κ := ι)) H.toMeasurement hlocal
  simp only [← map_sub (kroneckerOne (κ := ι))] at hround
  simp only [POVM.toMeasurement_effect, kroneckerOne_apply] at hround
  refine ⟨P.toPOVM, hP, hcomplete, ?_, ?_⟩
  · simpa only [Measurement.toPOVM_effect, show (9 : ℝ) * (2 * ζ) = 18 * ζ by ring] using hround
  · have he (a : Option α) :
        φ.norm ((H.effect a - P.effect a) ⊗ₖ (1 : Local)) ^ 2 =
          φ.norm ((1 : Local) ⊗ₖ (H.effect a - P.effect a)) ^ 2 := by
      let X := H.effect a - P.effect a
      change φ.norm (kroneckerOne X) ^ 2 = φ.norm (oneKronecker X) ^ 2
      rw [AlgState.norm_sq, AlgState.norm_sq, ← map_star (kroneckerOne (κ := ι)),
        ← map_star (oneKronecker (ι := ι)), ← map_mul (kroneckerOne (κ := ι)),
        ← map_mul (oneKronecker (ι := ι)), kroneckerOne_apply, oneKronecker_apply]
      exact congrArg Complex.re (hφ _ _)
    simpa only [he, Measurement.toPOVM_effect, show (9 : ℝ) * (2 * ζ) = 18 * ζ by ring] using
      hround

private theorem boundedness_le_evaluatedGap
    (φ : AlgState (Matrix (ι × ι) (ι × ι) ℂ))
    (A : Point F (n + 1) → Measurement F (Matrix (ι × ι) (ι × ι) ℂ))
    (P : Measurement (Option Poly) (Matrix (ι × ι) (ι × ι) ℂ))
    (Z : Matrix (ι × ι) (ι × ι) ℂ)
    (hmajor : ∀ g : Poly, averagePolynomialPointEffect A g ≤ Z)
    (hcomm : ∀ g u b, Commute (P.effect g) ((A u).effect b))
    (hZ : ∀ g, Commute (P.effect g) Z) :
    (φ (Z * P.effect none)).re ≤ (φ Z).re -
      𝔼 u : Point F (n + 1), ∑ b,
        (φ ((A u).effect b * (evaluatePolynomialMeasurement P u).effect (some b))).re := by
  have hscore (u : Point F (n + 1)) :
      (∑ b, (φ ((A u).effect b * (evaluatePolynomialMeasurement P u).effect (some b))).re) =
        ∑ g : Poly, (φ ((A u).effect (MvPolynomial.eval u g.val) * P.effect (some g))).re := by
    simp only [evaluatePolynomialMeasurement_effect_some, mul_sum, map_sum, Complex.re_sum]
    rw [← sum_fiberwise univ (fun g : Poly => MvPolynomial.eval u g.val)
      (fun g => (φ ((A u).effect (MvPolynomial.eval u g.val) * P.effect (some g))).re)]
    refine sum_congr rfl fun b _ => sum_congr rfl fun g hg => ?_
    rw [(mem_filter.mp hg).2]
  have hmean (g : Poly) :
      (𝔼 u : Point F (n + 1), (φ ((A u).effect (MvPolynomial.eval u g.val) *
        P.effect (some g))).re) =
        (φ (averagePolynomialPointEffect A g * P.effect (some g))).re := by
    rw [averagePolynomialPointEffect_eq, smul_mul_assoc, sum_mul,
      AlgState.re_apply_uniformAverage]
  simp only [hscore]
  rw [expect_sum_comm]
  simp only [hmean]
  have hle : (∑ g : Poly, (φ (averagePolynomialPointEffect A g * P.effect (some g))).re) ≤
      (φ (Z * P.successfulEffect)).re := by
    rw [Measurement.successfulEffect, mul_sum, map_sum, Complex.re_sum]
    refine sum_le_sum fun g _ => φ.re_apply_mono ?_
    rw [← sub_nonneg, ← sub_mul]
    have hc := (hZ (some g)).sub_right
      (commute_averagePolynomialPointEffect A g _ (hcomm (some g)))
    exact hc.symm.mul_nonneg (sub_nonneg.mpr (hmajor g)) (P.nonneg _)
  rw [P.effect_none_eq_one_sub_successfulEffect, mul_sub, mul_one, map_sub, Complex.sub_re]
  linarith only [hle]

private theorem exists_roundedSymmetricSelfImprovement
    (S : QuantumStrategy Q Q Ans Ans ι ι) (G : POVM (Option Poly) ι) (η : ℝ)
    (hM : S.bob = S.alice)
    (hψ : ∀ a b, S.state.ofLp (a, b) = S.state.ofLp (b, a))
    (hprojective : ∀ q, ((S.alice q).toMeasurement).IsProjective)
    (hinput : 1 - η ≤ 𝔼 u : Point F (n + 1), ∑ g : Poly,
      (S.toCommuting.state ((QuantumStrategy.rightMeasurement G).effect (some g) *
        (decodedPoint S.toCommuting.alice u).effect (MvPolynomial.eval u g.val))).re) :
    let C := S.toCommuting
    let δ := 1 - (branchGame (F := F) n d .consistency).commutingWinProb C
    let ε := 1 - (branchGame (F := F) n d .axis).commutingWinProb C
    let ζ := 100 * (n + 1 : ℝ) * (√ε + √δ + √((d : ℝ) / Fintype.card F))
    let s := √(18 * ζ)
    let t := √(16 * ζ + 4 * s)
    ∃ (P : POVM (Option Poly) ι) (Z : Local),
      let L := QuantumStrategy.leftMeasurement (κ := ι) P
      let R := QuantumStrategy.rightMeasurement (ι := ι) P
      let A := decodedPoint C.alice
      P.toMeasurement.IsProjective ∧ 0 ≤ Z ∧
      (∀ g : Poly, averagePolynomialPointEffect
        (decodedPoint fun q => (S.alice q).toMeasurement) g ≤ Z) ∧
      1 - η - (ζ + s) ≤ (C.state L.successfulEffect).re ∧
      (𝔼 u : Point F (n + 1), Measurement.successfulMismatch C.state
        (evaluatePolynomialMeasurement R u) (A u)) ≤ ζ + s + t ∧
      (C.state ((Z ⊗ₖ (1 : Local)) * R.effect none)).re ≤ ζ + t ∧
      Measurement.successfulCopyDefect C.state L R ≤ 4 * ζ + 4 * s := by
  classical
  intro C δ ε ζ s t
  obtain ⟨H, Z, hZ, hmajor, hmass, hpoint, hgap, hstrong⟩ :=
    exists_symmetricSelfImprovement S G η hM hψ hprojective hinput
  change (C.state (QuantumStrategy.leftMeasurement H).successfulEffect).re -
    ∑ g, (C.state ((QuantumStrategy.leftMeasurement H).effect (some g) *
      (QuantumStrategy.rightMeasurement H).effect (some g))).re ≤ ζ at hstrong
  obtain ⟨P, hP, hcomplete, hdistL, hdistR⟩ :=
    exists_projective_approx_of_symmetric_successfulGap S.state S.norm_state hψ H ζ hstrong
  let A := decodedPoint C.alice
  let HL := QuantumStrategy.leftMeasurement (κ := ι) H
  let HR := QuantumStrategy.rightMeasurement (ι := ι) H
  let PL := QuantumStrategy.leftMeasurement (κ := ι) P
  let PR := QuantumStrategy.rightMeasurement (ι := ι) P
  have haL : (∑ a, C.state.norm (HL.effect a - PL.effect a) ^ 2) ≤ 18 * ζ := by
    change (∑ a : Option Poly, C.state.norm (kroneckerOne (H.effect a) -
      kroneckerOne (P.effect a)) ^ 2) ≤ _
    simp only [← map_sub (kroneckerOne (κ := ι))]
    simp only [kroneckerOne_apply (κ := ι)]
    exact hdistL
  have haR : (∑ a, C.state.norm (HR.effect a - PR.effect a) ^ 2) ≤ 18 * ζ := by
    change (∑ a : Option Poly, C.state.norm (oneKronecker (H.effect a) -
      oneKronecker (P.effect a)) ^ 2) ≤ _
    simp only [← map_sub (oneKronecker (ι := ι))]
    simp only [oneKronecker_apply (ι := ι)]
    exact hdistR
  have hcomm (L R : POVM (Option Poly) ι) (a b : Option Poly) :
      Commute ((QuantumStrategy.leftMeasurement (κ := ι) L).effect a)
        ((QuantumStrategy.rightMeasurement (ι := ι) R).effect b) :=
    commute_kroneckerOne_oneKronecker (L.effect a) (R.effect b)
  have hmassClose (L R : Measurement (Option Poly) (Matrix (ι × ι) (ι × ι) ℂ))
      (h : (∑ a, C.state.norm (L.effect a - R.effect a) ^ 2) ≤ 18 * ζ) :
      |(C.state L.successfulEffect).re - (C.state R.successfulEffect).re| ≤ s := by
    refine (Measurement.abs_successfulMass_sub_le C.state L R).trans ?_
    rw [C.state.norm_sub_comm, ← Real.sqrt_sq (C.state.norm_nonneg _)]
    apply Real.sqrt_le_sqrt
    exact (single_le_sum (fun a _ => sq_nonneg (C.state.norm (L.effect a - R.effect a)))
      (mem_univ (none : Option Poly))).trans h
  have hmL := hmassClose HL PL haL
  have hmR := hmassClose HR PR haR
  have hcoarse (u : Point F (n + 1)) :
      (∑ b, C.state.norm ((evaluatePolynomialMeasurement HR u).effect b -
        (evaluatePolynomialMeasurement PR u).effect b) ^ 2) ≤ 16 * ζ + 4 * s := by
    have h := Measurement.sum_norm_sub_sq_map_le_of_agreement C.state HL HR PR
      (Option.map fun g => MvPolynomial.eval u g.val) (hcomm H H) (hcomm H P) hcomplete haR
    simpa only [evaluatePolynomialMeasurement, show (8 : ℝ) * (2 * ζ) = 16 * ζ by ring] using h
  have hscore (u : Point F (n + 1)) :
      |(∑ b, (C.state ((A u).effect b *
          (evaluatePolynomialMeasurement HR u).effect (some b))).re) -
        (∑ b, (C.state ((A u).effect b *
          (evaluatePolynomialMeasurement PR u).effect (some b))).re)| ≤ t := by
    have h := (Measurement.abs_agreement_sub_right_le C.state ((A u).map some)
      (evaluatePolynomialMeasurement HR u) (evaluatePolynomialMeasurement PR u)).trans
      (Real.sqrt_le_sqrt (hcoarse u))
    simpa only [Measurement.agreement_map_left] using h
  have hbad (N : Measurement (Option Poly) (Matrix (ι × ι) (ι × ι) ℂ))
      (hc : ∀ a u b, Commute ((A u).effect b) (N.effect a)) (u : Point F (n + 1)) :
      Measurement.successfulMismatch C.state (evaluatePolynomialMeasurement N u) (A u) =
        (C.state N.successfulEffect).re -
          ∑ b, (C.state ((A u).effect b *
            (evaluatePolynomialMeasurement N u).effect (some b))).re := by
    have hd (b : F) : Commute ((A u).effect b)
        ((evaluatePolynomialMeasurement N u).effect (some b)) := by
      rw [evaluatePolynomialMeasurement_effect_some]
      exact Commute.sum_right _ _ _ fun a _ => hc _ _ _
    unfold Measurement.successfulMismatch
    simp only [mul_sub, mul_one, map_sub, Complex.sub_re, sum_sub_distrib, ← (hd _).eq,
      ← Complex.re_sum, ← map_sum]
    rw [show (∑ b, (evaluatePolynomialMeasurement N u).effect (some b)) =
      (evaluatePolynomialMeasurement N u).successfulEffect from rfl,
      evaluatePolynomialMeasurement_successfulEffect]
  have hA (N : POVM (Option Poly) ι) (a : Option Poly) (u : Point F (n + 1)) (b : F) :
      Commute ((A u).effect b) ((QuantumStrategy.rightMeasurement (ι := ι) N).effect a) :=
    (Measurement.commute_map_right (C.alice (.point u)) decodePoint _ (fun c =>
      (commute_kroneckerOne_oneKronecker ((S.alice (.point u)).effect c) (N.effect a)).symm) b).symm
  have hmatch : 1 - (2 * ζ + 2 * s) ≤ Measurement.agreement C.state PL PR := by
    have h1 := (Measurement.abs_agreement_sub_right_le C.state HL HR PR).trans
      (Real.sqrt_le_sqrt haR)
    have h2 := (Measurement.abs_agreement_sub_right_le C.state PR HL PL).trans
      (Real.sqrt_le_sqrt haL)
    have hsw (N : POVM (Option Poly) ι) :
        Measurement.agreement C.state PR (QuantumStrategy.leftMeasurement (κ := ι) N) =
          Measurement.agreement C.state (QuantumStrategy.leftMeasurement (κ := ι) N) PR := by
      unfold Measurement.agreement
      exact sum_congr rfl fun a _ => by rw [(hcomm N P a a).eq]
    rw [hsw H, hsw P] at h2
    change 1 - 2 * ζ ≤ Measurement.agreement C.state HL HR at hcomplete
    linarith only [(abs_le.mp h1).2, (abs_le.mp h2).2, hcomplete]
  refine ⟨P, Z, hP, hZ, hmajor, ?_, ?_, ?_, ?_⟩
  · change 1 - η - ζ ≤ (C.state HL.successfulEffect).re at hmass
    change 1 - η - (ζ + s) ≤ (C.state PL.successfulEffect).re
    linarith only [hmass, (abs_le.mp hmL).2]
  · have hpt (u : Point F (n + 1)) :
        Measurement.successfulMismatch C.state (evaluatePolynomialMeasurement PR u) (A u) ≤
          Measurement.successfulMismatch C.state (evaluatePolynomialMeasurement HR u) (A u) +
            (s + t) := by
      rw [hbad PR (hA P), hbad HR (hA H)]
      linarith only [(abs_le.mp hmR).1, (abs_le.mp (hscore u)).2]
    have he := expect_le_expect (s := univ) fun u _ => hpt u
    rw [Finset.expect_add_distrib, Fintype.expect_const] at he
    change (𝔼 u : Point F (n + 1), Measurement.successfulMismatch C.state
      (evaluatePolynomialMeasurement HR u) (A u)) ≤ ζ at hpoint
    exact he.trans (by linarith only [hpoint])
  · have hlift (g : Poly) : averagePolynomialPointEffect A g ≤ Z ⊗ₖ (1 : Local) := by
      change averagePolynomialPointEffect
        (decodedPoint fun q => QuantumStrategy.leftMeasurement (κ := ι) (S.alice q)) g ≤ _
      rw [← averagePolynomialPointEffect_leftMeasurement]
      exact OrderHomClass.mono (kroneckerOne (κ := ι)) (hmajor g)
    have hb := boundedness_le_evaluatedGap C.state A PR (Z ⊗ₖ (1 : Local)) hlift
      (fun g u b => (hA P g u b).symm)
      (fun g => (commute_kroneckerOne_oneKronecker Z (P.effect g)).symm)
    have he := expect_le_expect (s := univ) fun u _ => sub_le_iff_le_add.mp (abs_le.mp (hscore u)).2
    rw [Finset.expect_add_distrib, Fintype.expect_const] at he
    change (C.state (Z ⊗ₖ (1 : Local))).re - (𝔼 u : Point F (n + 1), ∑ b,
      (C.state ((A u).effect b * (evaluatePolynomialMeasurement HR u).effect (some b))).re) ≤
        ζ at hgap
    exact hb.trans (by linarith only [hgap, he])
  · have h := Measurement.sum_norm_sub_sq_le_of_agreement C.state PL PR
      (fun a => hcomm P P a a) hmatch
    rw [Fintype.sum_option] at h
    change Measurement.successfulCopyDefect C.state PL PR ≤ _
    unfold Measurement.successfulCopyDefect
    linarith only [h, sq_nonneg (C.state.norm (PL.effect none - PR.effect none))]

private theorem projective_budget (m ε δ r : ℝ) (hm : 1 ≤ m)
    (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    let ζ := 100 * m * (√ε + √δ + √r)
    let s := √(18 * ζ)
    let t := √(16 * ζ + 4 * s)
    let κ := 3000 * m * (ε ^ (1 / 32 : ℝ) + δ ^ (1 / 32 : ℝ) + r ^ (1 / 32 : ℝ))
    ζ + s ≤ κ ∧ ζ + s + t ≤ κ ∧ ζ + t ≤ κ ∧ 4 * ζ + 4 * s ≤ κ := by
  intro ζ s t κ
  let v := max ε (max δ r)
  let x := √v
  let y := √x
  let u := √y
  have hv : 0 ≤ v := hε.1.trans (le_max_left _ _)
  have hv1 : v ≤ 1 := max_le hε.2 (max_le hδ.2 hr.2)
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hx1 : x ≤ 1 := Real.sqrt_le_one.mpr hv1
  have hy1 : y ≤ 1 := Real.sqrt_le_one.mpr hx1
  have hxy : x ≤ y := Real.le_sqrt_of_sq_le (by nlinarith only [mul_nonneg hx (sub_nonneg.mpr hx1)])
  have hyu : y ≤ u := Real.le_sqrt_of_sq_le (by nlinarith only [mul_nonneg hy (sub_nonneg.mpr hy1)])
  have hm₀ : 0 ≤ m := zero_le_one.trans hm
  have hζ : ζ ≤ 300 * m * x := by
    have he : √ε ≤ x := Real.sqrt_le_sqrt (le_max_left _ _)
    have hd : √δ ≤ x := Real.sqrt_le_sqrt ((le_max_left _ _).trans (le_max_right _ _))
    have hrr : √r ≤ x := Real.sqrt_le_sqrt ((le_max_right _ _).trans (le_max_right _ _))
    nlinarith only [he, hd, hrr, hm₀]
  have hs : s ≤ 74 * m * y := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    rw [mul_pow, mul_pow, Real.sq_sqrt hx]
    nlinarith only [hζ, mul_nonneg hm₀ hx, mul_nonneg (sub_nonneg.mpr hm) (mul_nonneg hm₀ hx)]
  have ht : t ≤ 72 * m * u := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    rw [mul_pow, mul_pow, Real.sq_sqrt hy]
    nlinarith only [hζ, hs, mul_le_mul_of_nonneg_left hxy hm₀, mul_nonneg hm₀ hy,
      mul_nonneg (sub_nonneg.mpr hm) (mul_nonneg hm₀ hy)]
  have hpow : u ≤ v ^ (1 / 32 : ℝ) := by
    change √(√(√v)) ≤ _
    simp only [Real.sqrt_eq_rpow, ← Real.rpow_mul hv]
    exact Real.rpow_le_rpow_of_exponent_ge' hv hv1 (by norm_num) (by norm_num)
  have hsum : v ^ (1 / 32 : ℝ) ≤
      ε ^ (1 / 32 : ℝ) + δ ^ (1 / 32 : ℝ) + r ^ (1 / 32 : ℝ) := by
    dsimp only [v]
    rw [Real.rpow_max hε.1 (hr.1.trans (le_max_right δ r)) (by norm_num),
      Real.rpow_max hδ.1 hr.1 (by norm_num)]
    have he : 0 ≤ ε ^ (1 / 32 : ℝ) := Real.rpow_nonneg hε.1 _
    have hd : 0 ≤ δ ^ (1 / 32 : ℝ) := Real.rpow_nonneg hδ.1 _
    have hrr : 0 ≤ r ^ (1 / 32 : ℝ) := Real.rpow_nonneg hr.1 _
    exact max_le (by linarith) (max_le (by linarith) (by linarith))
  have hκ : 3000 * (m * u) ≤ κ := by
    change _ ≤ 3000 * m * _
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left (hpow.trans hsum) (by positivity)
  have hxmu := mul_le_mul_of_nonneg_left (hxy.trans hyu) hm₀
  have hymu := mul_le_mul_of_nonneg_left hyu hm₀
  have hmu := mul_nonneg hm₀ hu
  exact ⟨by linarith only [hζ, hs, hκ, hxmu, hymu, hmu],
    by linarith only [hζ, hs, ht, hκ, hxmu, hymu, hmu],
    by linarith only [hζ, ht, hκ, hxmu, hmu],
    by linarith only [hζ, hs, hκ, hxmu, hymu, hmu]⟩

/-- Projective self-improvement for the symmetric low individual degree test
[JNVWY2020LowIndividualDegree, Theorem 9.4]. The failure outcome completes
the projective submeasurement. Strong self-consistency compares the successful
effects on opposite sides, and the majorant bounds the mass on failure. -/
theorem exists_projectiveSymmetricSelfImprovement
    (S : QuantumStrategy Q Q Ans Ans ι ι) (G : POVM (Option Poly) ι) (η : ℝ)
    (hM : S.bob = S.alice)
    (hψ : ∀ a b, S.state.ofLp (a, b) = S.state.ofLp (b, a))
    (hprojective : ∀ q, ((S.alice q).toMeasurement).IsProjective)
    (hinput : 1 - η ≤ 𝔼 u : Point F (n + 1), ∑ g : Poly,
      (S.toCommuting.state ((QuantumStrategy.rightMeasurement G).effect (some g) *
        (decodedPoint S.toCommuting.alice u).effect (MvPolynomial.eval u g.val))).re) :
    let C := S.toCommuting
    let δ := 1 - (branchGame (F := F) n d .consistency).commutingWinProb C
    let ε := 1 - (branchGame (F := F) n d .axis).commutingWinProb C
    let r := (d : ℝ) / Fintype.card F
    let κ := 3000 * (n + 1 : ℝ) * (ε ^ (1 / 32 : ℝ) + δ ^ (1 / 32 : ℝ) + r ^ (1 / 32 : ℝ))
    ∃ (P : POVM (Option Poly) ι) (Z : Local),
      let L := QuantumStrategy.leftMeasurement (κ := ι) P
      let R := QuantumStrategy.rightMeasurement (ι := ι) P
      let A := decodedPoint C.alice
      P.toMeasurement.IsProjective ∧ 0 ≤ Z ∧
      (∀ g : Poly, averagePolynomialPointEffect
        (decodedPoint fun q => (S.alice q).toMeasurement) g ≤ Z) ∧
      1 - η - κ ≤ (C.state L.successfulEffect).re ∧
      (𝔼 u : Point F (n + 1), Measurement.successfulMismatch C.state
        (evaluatePolynomialMeasurement R u) (A u)) ≤ κ ∧
      (C.state ((Z ⊗ₖ (1 : Local)) * R.effect none)).re ≤ κ ∧
      Measurement.successfulCopyDefect C.state L R ≤ κ := by
  classical
  intro C δ ε r κ
  have hε : ε ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨sub_nonneg.mpr (TwoProverGame.commutingWinProb_le_one _ _),
      sub_le_self _ (TwoProverGame.commutingWinProb_nonneg _ _)⟩
  have hδ : δ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨sub_nonneg.mpr (TwoProverGame.commutingWinProb_le_one _ _),
      sub_le_self _ (TwoProverGame.commutingWinProb_nonneg _ _)⟩
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hm : 1 ≤ (n + 1 : ℝ) := le_add_of_nonneg_left (Nat.cast_nonneg n)
  by_cases hr1 : r ≤ 1
  · obtain ⟨P, Z, hP, hZ, hmajor, hmass, hpoint, hgap, hcopy⟩ :=
      exists_roundedSymmetricSelfImprovement S G η hM hψ hprojective hinput
    obtain ⟨hmass', hpoint', hgap', hcopy'⟩ :=
      projective_budget (n + 1) ε δ r hm hε hδ ⟨hr, hr1⟩
    exact ⟨P, Z, hP, hZ, hmajor, (sub_le_sub_left hmass' _).trans hmass,
      hpoint.trans hpoint', hgap.trans hgap', hcopy.trans hcopy'⟩
  · let P : POVM (Option Poly) ι := POVM.const none
    have hP : P.toMeasurement.IsProjective := by
      intro a
      cases a <;> simp [P, POVM.const, POVM.toMeasurement_effect]
    have hκ : 1 ≤ κ := by
      have hpow : 1 ≤ r ^ (1 / 32 : ℝ) := Real.one_le_rpow (le_of_not_ge hr1) (by norm_num)
      have hsum : 1 ≤ ε ^ (1 / 32 : ℝ) + δ ^ (1 / 32 : ℝ) + r ^ (1 / 32 : ℝ) := by
        linarith only [hpow, Real.rpow_nonneg hε.1 (1 / 32 : ℝ), Real.rpow_nonneg hδ.1 (1 / 32 : ℝ)]
      calc (1 : ℝ) ≤ 3000 * (n + 1 : ℝ) * 1 := by linarith only [hm]
        _ ≤ κ := mul_le_mul_of_nonneg_left hsum (by positivity)
    have hscore : (𝔼 u : Point F (n + 1), ∑ g : Poly,
        (C.state ((QuantumStrategy.rightMeasurement G).effect (some g) *
          (decodedPoint C.alice u).effect (MvPolynomial.eval u g.val))).re) ≤ 1 := by
      rw [← Fintype.expect_const (ι := Point F (n + 1)) (1 : ℝ)]
      refine expect_le_expect (s := univ) fun u _ => ?_
      let G' := QuantumStrategy.rightMeasurement (ι := ι) G
      let A := decodedPoint C.alice u
      calc
        _ ≤ ∑ g : Poly, (C.state (G'.effect (some g))).re := by
          refine sum_le_sum fun g _ => C.state.re_apply_mono ?_
          have hc : Commute (G'.effect (some g)) (A.effect (MvPolynomial.eval u g.val)) :=
            Measurement.commute_map_right (C.alice (.point u)) decodePoint _ (fun a =>
              (commute_kroneckerOne_oneKronecker ((S.alice (.point u)).effect a)
                (G.effect (some g))).symm) _
          have h := ((Commute.one_right _).sub_right hc).mul_nonneg (G'.nonneg _)
            (sub_nonneg.mpr (A.effect_le_one _))
          simpa only [mul_sub, mul_one, sub_nonneg] using h
        _ ≤ ∑ a : Option Poly, (C.state (G'.effect a)).re := by
          rw [Fintype.sum_option]
          exact le_add_of_nonneg_left (C.state.re_apply_nonneg (G'.nonneg none))
        _ = 1 := G'.sum_prob C.state
    have ηnonneg : 0 ≤ η := by linarith only [hinput.trans hscore]
    have hvL (g : Poly) : (QuantumStrategy.leftMeasurement (κ := ι) P).effect (some g) = 0 := by
      change kroneckerOne (P.effect (some g)) = 0
      simp [P, POVM.const]
    have hvR (g : Poly) : (QuantumStrategy.rightMeasurement (ι := ι) P).effect (some g) = 0 := by
      change oneKronecker (P.effect (some g)) = 0
      simp [P, POVM.const]
    have hvnone : (QuantumStrategy.rightMeasurement (ι := ι) P).effect none = 1 := by
      change oneKronecker (P.effect none) = 1
      simp [P, POVM.const]
    refine ⟨P, 1, hP, zero_le_one, fun g => (averagePolynomialPointEffect_mem_Icc _ g).2,
      ?_, ?_, ?_, ?_⟩
    · simp only [Measurement.successfulEffect, hvL, sum_const_zero, map_zero, Complex.zero_re]
      linarith only [ηnonneg, hκ]
    · simp only [Measurement.successfulMismatch, evaluatePolynomialMeasurement_effect_some,
        hvR, sum_const_zero, zero_mul, map_zero, Complex.zero_re, Fintype.expect_const]
      exact zero_le_one.trans hκ
    · simpa only [hvnone, one_kronecker_one, mul_one, C.state.map_one, Complex.one_re] using hκ
    · simp only [Measurement.successfulCopyDefect, hvL, hvR, sub_zero, AlgState.norm_zero,
        zero_pow (by decide : (2 : ℕ) ≠ 0), sum_const_zero]
      exact zero_le_one.trans hκ

end Cslib.PCP.LowIndividualDegree
