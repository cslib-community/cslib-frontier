/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.SelfImprovementSDP
public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.VerifierSelfImprovement
import CslibFrontier.Foundations.Quantum.Algebra.CStar
import CslibFrontier.Foundations.Quantum.Algebra.MaxEntangled
import CslibFrontier.Foundations.Quantum.Algebra.TensorState

/-!
# Tensor-product self-improvement

The local self-improvement program supplies a polynomial POVM and a dual
majorant. Both embed in the two players' matrix algebras, where the verifier
bounds apply to the corresponding sandwiched measurements.

## Main results

* `Cslib.PCP.LowIndividualDegree.exists_tensorSelfImprovement` constructs the
  polynomial POVM and majorant and proves the four verifier bounds.
* `Cslib.PCP.LowIndividualDegree.exists_symmetricSelfImprovement` obtains
  one local polynomial submeasurement for a symmetric strategy.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Cslib.Quantum Matrix Finset
open scoped BigOperators Kronecker MatrixOrder ComplexOrder Real Matrix.Norms.L2Operator

variable {F ι κ : Type*} {n d : ℕ} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

local notation "Q" => Question F (n + 1)
local notation "Ans" => Answer F (n + 1)
local notation "Poly" => BoundedPolynomial F (n + 1) d
local notation "Local" => Matrix ι ι ℂ
local notation "Joint" => Matrix (ι × κ) (ι × κ) ℂ

private theorem kroneckerOne_decodedPoint (M : Q → POVM Ans ι) (u : Point F (n + 1)) (a : F) :
    (kroneckerOne ((decodedPoint (fun q => (M q).toMeasurement) u).effect a) : Joint) =
      (decodedPoint (fun q => QuantumStrategy.leftMeasurement (M q)) u).effect a := by
  simp only [decodedPoint, Measurement.map_effect, map_sum]; rfl

/-- The averaged point effect of a polynomial embeds into the joint algebra
by tensoring with the identity. -/
theorem averagePolynomialPointEffect_leftMeasurement
    (M : Q → POVM Ans ι) (g : Poly) :
    (averagePolynomialPointEffect (decodedPoint (fun q => (M q).toMeasurement)) g ⊗ₖ
      (1 : Matrix κ κ ℂ)) =
      averagePolynomialPointEffect (decodedPoint (fun q => QuantumStrategy.leftMeasurement
        (M q))) g := by
  rw [averagePolynomialPointEffect_eq, averagePolynomialPointEffect_eq]
  change ((kroneckerOne (κ := κ)).toAlgHom.restrictScalars ℝ) _ = _
  simp only [map_smul, map_sum, AlgHom.coe_restrictScalars', StarAlgHom.coe_toAlgHom,
    kroneckerOne_decodedPoint]

private theorem exists_leftSelfImprovementCertificate (M : Q → POVM Ans ι) :
    ∃ (T : POVM Poly ι) (Z : Local), 0 ≤ Z ∧
      (∀ g : Poly, averagePolynomialPointEffect
        (decodedPoint fun q => (M q).toMeasurement) g ≤ Z) ∧
      (∀ g : Poly, averagePolynomialPointEffect (decodedPoint
        (fun q => QuantumStrategy.leftMeasurement (κ := κ) (M q))) g ≤ Z ⊗ₖ (1 : Matrix κ κ ℂ)) ∧
      (∀ g, (QuantumStrategy.leftMeasurement (κ := κ) T).effect g * (Z ⊗ₖ (1 : Matrix κ κ ℂ)) =
        (QuantumStrategy.leftMeasurement (κ := κ) T).effect g *
          averagePolynomialPointEffect (decodedPoint
            (fun q => QuantumStrategy.leftMeasurement (κ := κ) (M q))) g) := by
  classical
  obtain ⟨T, Z, hZ, hle, hslack, _, _, _⟩ := exists_selfImprovement_trace_certificate (d := d)
    (decodedPoint (fun q => (M q).toMeasurement))
  refine ⟨T.toPOVM, Z, hZ, hle, fun g => ?_, fun g => ?_⟩ <;>
    rw [← averagePolynomialPointEffect_leftMeasurement]
  · exact OrderHomClass.mono (kroneckerOne (κ := κ)) (hle g)
  · change kroneckerOne (κ := κ) (T.effect g) * kroneckerOne Z =
      kroneckerOne (T.effect g) * kroneckerOne (averagePolynomialPointEffect
        (decodedPoint (fun q => (M q).toMeasurement)) g)
    rw [← map_mul, ← map_mul, hslack]

/-- For a finite-dimensional strategy with projective point and axis effects,
the local SDP constructs sandwiched polynomial measurements whose successful
mass, point disagreement, dual gap and strong self-consistency are controlled
by the input agreement and the verifier losses. -/
theorem exists_tensorSelfImprovement
    (S : QuantumStrategy Q Q Ans Ans ι ι) (G : POVM (Option Poly) ι) (η : ℝ)
    (hLpoint : ∀ u, (S.toCommuting.bob (.point u)).IsProjective)
    (hRpoint : ∀ u, (S.toCommuting.alice (.point u)).IsProjective)
    (hLaxis : ∀ L, (S.toCommuting.bob (.axis L)).IsProjective)
    (hRaxis : ∀ L, (S.toCommuting.alice (.axis L)).IsProjective)
    (hinput : 1 - η ≤ 𝔼 u : Point F (n + 1), ∑ g : Poly,
      (S.toCommuting.state ((QuantumStrategy.rightMeasurement G).effect (some g) *
        (decodedPoint S.toCommuting.alice u).effect (MvPolynomial.eval u g.val))).re) :
    let C := S.toCommuting
    let δ (C' : CommutingStrategy Q Q Ans Ans (Matrix (ι × ι) (ι × ι) ℂ)) :=
      1 - (branchGame (F := F) n d .consistency).commutingWinProb C'
    let ε (C' : CommutingStrategy Q Q Ans Ans (Matrix (ι × ι) (ι × ι) ℂ)) :=
      1 - (branchGame (F := F) n d .axis).commutingWinProb C'
    let ξ C' := (n + 1 : ℝ) * (6 * (2 * δ C' + 4 * ε C' + (d : ℝ) / Fintype.card F))
    ∃ (T : POVM Poly ι) (Z : Local),
      let L := decodedPoint C.bob
      let R := decodedPoint C.alice
      let P := sandwichedPolynomialMeasurement L (QuantumStrategy.rightMeasurement T)
      let H := sandwichedPolynomialMeasurement R (QuantumStrategy.leftMeasurement T)
      let W := Z ⊗ₖ (1 : Local)
      0 ≤ Z ∧
      (∀ g : Poly, averagePolynomialPointEffect
        (decodedPoint fun q => (S.alice q).toMeasurement) g ≤ Z) ∧
      1 - η - 3 * √(2 * δ C) ≤ (C.state H.successfulEffect).re ∧
      (𝔼 u : Point F (n + 1), Measurement.successfulMismatch C.state
        (evaluatePolynomialMeasurement H u) (L u)) ≤ 2 * √(2 * δ C) + 2 * √(ξ C) ∧
      (C.state W).re - (𝔼 u : Point F (n + 1), ∑ b,
        (C.state ((evaluatePolynomialMeasurement H u).effect (some b) * (L u).effect b)).re) ≤
          5 * √(2 * δ C) + 2 * √(ξ C) ∧
      (C.state P.successfulEffect).re -
        ∑ g, (C.state (P.effect (some g) * H.effect (some g))).re ≤
          5 * √(2 * δ C) + 5 * √(ξ C) + 2 * √(ξ C.swap) +
            (n + 1 : ℝ) * d / Fintype.card F := by
  classical
  intro C δ ε ξ
  obtain ⟨T, Z, hZ, hlocal, hle, hslack⟩ :=
    exists_leftSelfImprovementCertificate (κ := ι) (d := d) S.alice
  let R := decodedPoint C.alice
  let L := decodedPoint C.bob
  let U := QuantumStrategy.rightMeasurement (ι := ι) T
  let V := QuantumStrategy.leftMeasurement (κ := ι) T
  let W := Z ⊗ₖ (1 : Local)
  have hT (q g b) : Commute (V.effect g) ((C.bob q).effect b) :=
    commute_kroneckerOne_oneKronecker (T.effect g) ((S.bob q).effect b)
  have hU (q g a) : Commute (U.effect g) ((C.alice q).effect a) :=
    (commute_kroneckerOne_oneKronecker ((S.alice q).effect a) (T.effect g)).symm
  obtain ⟨hpoint, hgap⟩ := sandwichedPolynomial_point_bounds_of_verifier
    C d V W hLpoint hLaxis hT hslack
  have hstrong := successfulMass_sub_sandwichedAgreement_le_of_verifier
    C d U V W hLpoint hRpoint hLaxis hRaxis hT hU
    (fun h g => (commute_kroneckerOne_oneKronecker (T.effect g) (T.effect h)).symm)
    (fun q b => (commute_kroneckerOne_oneKronecker Z ((S.bob q).effect b)).symm)
    (fun g => (commute_kroneckerOne_oneKronecker Z (T.effect g)).symm) hle hslack
  have hcopy : (𝔼 u : Point F (n + 1), Measurement.copyDefect C.state (R u) (L u)) ≤
      2 * δ C := by
    simpa only [Measurement.copyDefect, R, L, δ, C.state.norm_sub_comm] using
      decodedPoint_stateDist_le C d
  have hmass := successfulMass_sandwichedPolynomial_lower_bound C.state L R V
    (fun u => (hLpoint u).map _) (fun u g b =>
      (Measurement.commute_map_right (C.bob (.point u)) decodePoint _ (hT (.point u) g) b).symm)
    (QuantumStrategy.rightMeasurement G) W hle hslack
    (fun g => (commute_kroneckerOne_oneKronecker Z (G.effect g)).symm)
    (fun g u b => Measurement.commute_map_right (C.alice (.point u)) decodePoint _
      (fun a =>
        (commute_kroneckerOne_oneKronecker ((S.alice (.point u)).effect a) (G.effect g)).symm) b)
  exact ⟨T, Z, hZ, hlocal, (sub_le_sub hinput (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcopy)
    (by norm_num))).trans hmass, hpoint, hgap, hstrong⟩

private theorem sandwichedPolynomial_effect_lift {J : Type*} [CStarAlgebra J]
    [PartialOrder J] [StarOrderedRing J]
    (e : Local →⋆ₐ[ℂ] J) (M : Q → POVM Ans ι) (T : POVM Poly ι)
    (M' : Q → Measurement Ans J) (T' : Measurement Poly J)
    (hM : ∀ q a, (M' q).effect a = e ((M q).effect a))
    (hT : ∀ g, T'.effect g = e (T.effect g)) (a : Option Poly) :
    (sandwichedPolynomialMeasurement (decodedPoint M') T').effect a =
      e ((sandwichedPolynomialMeasurement (decodedPoint fun q => (M q).toMeasurement)
        T.toMeasurement).effect a) := by
  let B := decodedPoint fun q => (M q).toMeasurement
  have hpoint (u : Point F (n + 1)) (b : F) :
      (decodedPoint M' u).effect b = e ((B u).effect b) := by
    simp only [B, decodedPoint, Measurement.map_effect, map_sum, hM, POVM.toMeasurement_effect]
  have hsome (g : Poly) :
      (sandwichedPolynomialMeasurement (decodedPoint M') T').effect (some g) =
        e ((sandwichedPolynomialMeasurement B T.toMeasurement).effect (some g)) := by
    rw [sandwichedPolynomialMeasurement_effect_some, sandwichedPolynomialMeasurement_effect_some]
    change _ = (e.toAlgHom.restrictScalars ℝ) _
    simp only [map_smul, map_sum, map_mul, StarAlgHom.coe_toAlgHom, AlgHom.coe_restrictScalars',
      hpoint, hT, POVM.toMeasurement_effect]
  cases a with
  | some g => exact hsome g
  | none =>
      simp only [Measurement.effect_none_eq_one_sub_successfulEffect,
        Measurement.successfulEffect, map_sub, map_one, map_sum, hsome, B]

private theorem sandwichedPolynomial_left (M : Q → POVM Ans ι) (T : POVM Poly ι) :
    sandwichedPolynomialMeasurement
        (decodedPoint fun q => QuantumStrategy.leftMeasurement (κ := κ) (M q))
        (QuantumStrategy.leftMeasurement T) =
      QuantumStrategy.leftMeasurement (sandwichedPolynomialMeasurement
        (decodedPoint fun q => (M q).toMeasurement) T.toMeasurement).toPOVM :=
  Measurement.ext fun a => sandwichedPolynomial_effect_lift (kroneckerOne (κ := κ)) M T
    (fun q => QuantumStrategy.leftMeasurement (M q)) (QuantumStrategy.leftMeasurement T)
    (fun _ _ => rfl) (fun _ => rfl) a

private theorem sandwichedPolynomial_right (M : Q → POVM Ans ι) (T : POVM Poly ι) :
    sandwichedPolynomialMeasurement
        (decodedPoint fun q => QuantumStrategy.rightMeasurement (ι := κ) (M q))
        (QuantumStrategy.rightMeasurement T) =
      QuantumStrategy.rightMeasurement (sandwichedPolynomialMeasurement
        (decodedPoint fun q => (M q).toMeasurement) T.toMeasurement).toPOVM :=
  Measurement.ext fun a => sandwichedPolynomial_effect_lift (oneKronecker (ι := κ)) M T
    (fun q => QuantumStrategy.rightMeasurement (M q)) (QuantumStrategy.rightMeasurement T)
    (fun _ _ => rfl) (fun _ => rfl) a

private theorem selfImprovement_budget (m δ ε r : ℝ) (hm : 1 ≤ m)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hr : 0 ≤ r) :
    let t := √ε + √δ + √r
    let ξ := m * (6 * (2 * δ + 4 * ε + r))
    √(2 * δ) ≤ 2 * √δ ∧ √ξ ≤ 6 * m * t := by
  intro t ξ
  have ht : 0 ≤ t := by dsimp [t]; positivity
  refine ⟨Real.sqrt_le_iff.2 ⟨by positivity,
    by nlinarith only [Real.sq_sqrt hδ, hδ]⟩, ?_⟩
  have hinner : 6 * (2 * δ + 4 * ε + r) ≤ (6 * t) ^ 2 := by
    dsimp only [t]
    nlinarith only [Real.sq_sqrt hδ, Real.sq_sqrt hε, Real.sq_sqrt hr, hδ, hε, hr,
      mul_nonneg (Real.sqrt_nonneg δ) (Real.sqrt_nonneg ε),
      mul_nonneg (Real.sqrt_nonneg δ) (Real.sqrt_nonneg r),
      mul_nonneg (Real.sqrt_nonneg ε) (Real.sqrt_nonneg r)]
  calc
    √ξ ≤ √(m * (6 * t) ^ 2) := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hinner (by linarith))
    _ = √m * (6 * t) := by rw [Real.sqrt_mul (by linarith), Real.sqrt_sq (by positivity)]
    _ ≤ m * (6 * t) := mul_le_mul_of_nonneg_right (Real.sqrt_le_self_iff.mpr (Or.inr hm))
      (by positivity)
    _ = 6 * m * t := by ring

/-- The four nonprojective self-improvement bounds for a symmetric strategy
[JNVWY2020LowIndividualDegree, Lemma 9.1]. Both players use the same local
submeasurement, with an extra outcome recording failure. The common error
bound uses the actual axis and point-consistency losses. -/
theorem exists_symmetricSelfImprovement
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
    ∃ (H : POVM (Option Poly) ι) (Z : Local),
      let L := QuantumStrategy.leftMeasurement (κ := ι) H
      let R := QuantumStrategy.rightMeasurement (ι := ι) H
      let A := decodedPoint C.alice
      0 ≤ Z ∧
      (∀ g : Poly, averagePolynomialPointEffect
        (decodedPoint fun q => (S.alice q).toMeasurement) g ≤ Z) ∧
      1 - η - ζ ≤ (C.state L.successfulEffect).re ∧
      (𝔼 u : Point F (n + 1), Measurement.successfulMismatch C.state
        (evaluatePolynomialMeasurement R u) (A u)) ≤ ζ ∧
      (C.state (Z ⊗ₖ (1 : Local))).re - (𝔼 u : Point F (n + 1), ∑ b,
        (C.state ((A u).effect b * (evaluatePolynomialMeasurement R u).effect (some b))).re) ≤ ζ ∧
      (C.state L.successfulEffect).re -
        ∑ g, (C.state (L.effect (some g) * R.effect (some g))).re ≤ ζ := by
  classical
  intro C δ ε ζ
  let m := (n + 1 : ℝ)
  let r := (d : ℝ) / Fintype.card F
  let t := √ε + √δ + √r
  let ξ := m * (6 * (2 * δ + 4 * ε + r))
  have hm : 1 ≤ m := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hδ : 0 ≤ δ := sub_nonneg.mpr (TwoProverGame.commutingWinProb_le_one _ _)
  have hε : 0 ≤ ε := sub_nonneg.mpr (TwoProverGame.commutingWinProb_le_one _ _)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  obtain ⟨hδsqrt, hξsqrt⟩ := selfImprovement_budget m δ ε r hm hδ hε hr
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hmt : t ≤ m * t := le_mul_of_one_le_left ht hm
  have hδt : √δ ≤ t := by dsimp only [t]; linarith only [Real.sqrt_nonneg ε, Real.sqrt_nonneg r]
  have hrt : √r ≤ t := by dsimp only [t]; linarith only [Real.sqrt_nonneg ε, Real.sqrt_nonneg δ]
  have hδmt := hδt.trans hmt
  have hrmt' := hrt.trans hmt
  have hz : ζ = 100 * (m * t) := mul_assoc _ _ _
  have hL (q : Q) : (C.alice q).IsProjective :=
    QuantumStrategy.leftMeasurement_isProjective (S.alice q) (hprojective q)
  have hR (q : Q) : (C.bob q).IsProjective := by
    dsimp only [C, QuantumStrategy.toCommuting]
    exact hM ▸ QuantumStrategy.rightMeasurement_isProjective (S.alice q) (hprojective q)
  obtain ⟨T, Z, hZ, hmajor, hmass, hpoint, hgap, hstrong⟩ :=
    exists_tensorSelfImprovement S G η (fun _ => hR _) (fun _ => hL _)
      (fun _ => hR _) (fun _ => hL _) hinput
  let H := sandwichedPolynomialMeasurement (decodedPoint fun q => (S.alice q).toMeasurement)
    T.toMeasurement
  let L := QuantumStrategy.leftMeasurement (κ := ι) H.toPOVM
  let R := QuantumStrategy.rightMeasurement (ι := ι) H.toPOVM
  have hleft : sandwichedPolynomialMeasurement (decodedPoint S.toCommuting.alice)
      (QuantumStrategy.leftMeasurement T) = L := sandwichedPolynomial_left S.alice T
  have hright : sandwichedPolynomialMeasurement (decodedPoint S.toCommuting.bob)
      (QuantumStrategy.rightMeasurement T) = R := by
    dsimp only [QuantumStrategy.toCommuting]
    rw [hM, sandwichedPolynomial_right]
  have hswap (X Y : Local) : C.state (X ⊗ₖ Y) = C.state (Y ⊗ₖ X) :=
    AlgState.vector_kronecker_swap S.state S.norm_state hψ X Y
  have htrace : C.state R.successfulEffect = C.state L.successfulEffect := by
    rw [Measurement.successfulEffect, Measurement.successfulEffect, map_sum, map_sum]
    exact sum_congr rfl fun g _ => hswap 1 (H.effect (some g))
  have hpointSwap (u : Point F (n + 1)) (g : Poly) (b : F) :
      C.state (L.effect (some g) * (decodedPoint C.bob u).effect b) =
        C.state ((decodedPoint C.alice u).effect b * R.effect (some g)) := by
    let B := decodedPoint fun q => (S.alice q).toMeasurement
    have hbob : (decodedPoint C.bob u).effect b = oneKronecker ((B u).effect b) := by
      simp only [C, QuantumStrategy.toCommuting, hM, B, decodedPoint, Measurement.map_effect,
        map_sum]
      rfl
    have halice : kroneckerOne ((B u).effect b) = (decodedPoint C.alice u).effect b :=
      kroneckerOne_decodedPoint S.alice u b
    rw [hbob, ← halice]
    change C.state ((H.effect (some g) ⊗ₖ (1 : Local)) * (1 ⊗ₖ (B u).effect b)) =
      C.state (((B u).effect b ⊗ₖ 1) * (1 ⊗ₖ H.effect (some g)))
    simpa only [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul] using
      hswap (H.effect (some g)) ((B u).effect b)
  have hcompare (u : Point F (n + 1)) (a b : F) :
      C.state ((evaluatePolynomialMeasurement L u).effect (some a) *
        (decodedPoint C.bob u).effect b) =
      C.state ((decodedPoint C.alice u).effect b *
        (evaluatePolynomialMeasurement R u).effect (some a)) := by
    simp only [evaluatePolynomialMeasurement_effect_some, sum_mul, mul_sum, map_sum, hpointSwap]
  have hevalMass (u : Point F (n + 1)) (a : F) :
      C.state ((evaluatePolynomialMeasurement L u).effect (some a)) =
        C.state ((evaluatePolynomialMeasurement R u).effect (some a)) := by
    rw [evaluatePolynomialMeasurement_effect_some, evaluatePolynomialMeasurement_effect_some,
      map_sum, map_sum]
    exact sum_congr rfl fun g _ => hswap (H.effect (some g)) 1
  have hcomm (u : Point F (n + 1)) (a b : F) :
      Commute ((evaluatePolynomialMeasurement R u).effect (some a))
        ((decodedPoint C.alice u).effect b) := by
    rw [evaluatePolynomialMeasurement_effect_some]
    exact Commute.sum_left _ _ _ fun g _ =>
      Measurement.commute_map_right (C.alice (.point u)) decodePoint _ (fun c =>
      (commute_kroneckerOne_oneKronecker
        ((S.alice (.point u)).effect c) (H.effect (some g))).symm) b
  rw [hleft] at hmass hpoint hgap
  rw [hleft, hright] at hstrong
  refine ⟨H.toPOVM, Z, hZ, hmajor, ?_, ?_, ?_, ?_⟩
  · exact le_trans (by rw [hz]; linarith only [hδsqrt, hδmt, hmt, ht]) hmass
  · change (𝔼 u : Point F (n + 1), Measurement.successfulMismatch C.state
        (evaluatePolynomialMeasurement L u) (decodedPoint C.bob u)) ≤
      2 * √(2 * δ) + 2 * √ξ at hpoint
    simp only [Measurement.successfulMismatch, mul_sub, mul_one, map_sub, hevalMass,
      hcompare, ← (hcomm _ _ _).eq] at hpoint
    simpa only [Measurement.successfulMismatch, mul_sub, mul_one, map_sub] using
      hpoint.trans (by rw [hz]; linarith only [hδsqrt, hξsqrt, hδmt, hmt, ht])
  · change _ - (𝔼 u : Point F (n + 1), ∑ b,
      (C.state ((evaluatePolynomialMeasurement L u).effect (some b) *
        (decodedPoint C.bob u).effect b)).re) ≤ 5 * √(2 * δ) + 2 * √ξ at hgap
    simpa only [hcompare] using
      hgap.trans (by rw [hz]; linarith only [hδsqrt, hξsqrt, hδmt, hmt, ht])
  · change (C.state R.successfulEffect).re -
      ∑ g, (C.state (R.effect (some g) * L.effect (some g))).re ≤ _ at hstrong
    rw [htrace] at hstrong
    have hxy (g : Poly) : Commute (L.effect (some g)) (R.effect (some g)) :=
      commute_kroneckerOne_oneKronecker (H.effect (some g)) (H.effect (some g))
    simp only [← (hxy _).eq, TwoProverGame.commutingWinProb_swap_of_symmetric _ S hM hψ] at hstrong
    by_cases hsmall : r ≤ 1
    · have hrs : r ≤ √r :=
        (Real.le_sqrt hr hr).2 (by nlinarith only [mul_nonneg hr (sub_nonneg.mpr hsmall)])
      have hrmt : m * r ≤ m * t := mul_le_mul_of_nonneg_left (hrs.trans hrt) (by linarith)
      refine hstrong.trans ?_
      change 5 * √(2 * δ) + 5 * √ξ + 2 * √ξ + m * d / Fintype.card F ≤ ζ
      rw [mul_div_assoc, hz]
      linarith only [hδsqrt, hξsqrt, hδmt, hrmt, hmt, ht]
    · have hmass_le : (C.state L.successfulEffect).re ≤ 1 :=
        C.state.re_apply_le_one (sub_nonneg.mp
          (L.effect_none_eq_one_sub_successfulEffect ▸ L.nonneg none))
      have hagree : 0 ≤ ∑ g, (C.state (L.effect (some g) * R.effect (some g))).re :=
        sum_nonneg fun g _ => C.state.re_apply_nonneg
          ((hxy g).mul_nonneg (L.nonneg _) (R.nonneg _))
      have hrone : 1 ≤ √r := Real.one_le_sqrt.mpr (le_of_not_ge hsmall)
      rw [hz]
      linarith only [hmass_le, hagree, hrone, hrmt']

end Cslib.PCP.LowIndividualDegree
