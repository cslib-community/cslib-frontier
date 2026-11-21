/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.SliceBoundedness
import CslibFrontier.Foundations.Data.Finset.Expect

/-!
# Commutation of evaluated slice effects

The evaluated slice commutator is controlled by agreement with the point
measurements, the diagonal test, the failures charged to the slice majorants,
and agreement with a commuting copy of the polynomial measurements. The product
replacements follow the proof of Lemma 11.1 in [JNVWY2020LowIndividualDegree].

## Main results

* `Cslib.PCP.LowIndividualDegree.evaluatedSlice_successfulPairDefect_le` bounds
  the averaged squared commutators of the successful evaluated effects.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Cslib.Quantum Finset MvPolynomial
open scoped BigOperators Real

variable {F A : Type*} {m d : ℕ} [Fintype F]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private theorem abs_mean_le_sqrt {X : Type*} [Fintype X]
    (f : X → ℝ) (defect : X → ℝ) (hdefect : ∀ x, 0 ≤ defect x)
    (h : ∀ x, |f x| ≤ √(defect x)) {ε : ℝ} (hε : (𝔼 x, defect x) ≤ ε) :
    |𝔼 x, f x| ≤ √ε :=
  ((abs_expect_le _ _).trans (expect_le_expect fun x _ => h x)).trans
    ((Fintype.expect_sqrt_le_sqrt_expect _ hdefect).trans (Real.sqrt_le_sqrt hε))

private theorem abs_sum_sandwich_replace_le (φ : AlgState A)
    (P N : Measurement (Option F) A) (hp : P.IsProjective) (C : F → A) :
    |(∑ a : F, ∑ b : F, (φ (P.effect (some a) * N.effect (some b) *
      P.effect (some a) * N.effect (some b))).re) -
      (∑ a : F, ∑ b : F, (φ (P.effect (some a) * N.effect (some b) *
        P.effect (some a) * C b)).re)| ≤
      √(∑ b : F, φ.norm (N.effect (some b) - C b) ^ 2) := by
  simpa only [mul_sub, map_sub, Complex.sub_re, sum_sub_distrib] using
    Measurement.abs_sum_successful_sandwich_mul_le φ P N hp (fun b => N.effect (some b) - C b)

private theorem abs_sum_matching_replace_le (φ : AlgState A)
    (P N : Measurement (Option F) A) (hp : P.IsProjective)
    (B C : Measurement F A)
    (hPC : ∀ a b, Commute (P.effect a) (C.effect b))
    (hNC : ∀ a b, Commute (N.effect a) (C.effect b)) :
    |(∑ a : F, ∑ b : F, (φ (P.effect (some a) * N.effect (some b) *
      P.effect (some a) * C.effect b)).re) -
      (∑ a : F, ∑ b : F, (φ (P.effect (some a) * N.effect (some b) *
        P.successfulEffect * (C.effect b * B.effect a))).re)| ≤
      √(∑ a : F, φ.norm (P.effect (some a) - P.successfulEffect * B.effect a) ^ 2) := by
  let J := ∑ b : F, N.effect (some b) * C.effect b
  have hJ := Measurement.sum_successful_matching_mem_Icc N C fun b => hNC _ b
  have hGC (b : F) : Commute P.successfulEffect (C.effect b) :=
    Commute.sum_left _ _ _ fun a _ => hPC _ b
  have h := φ.abs_sum_re_star_mul_le_of_normalized
    (fun a => J * P.effect (some a)) (fun a => P.effect (some a) - P.successfulEffect * B.effect a)
    (Measurement.sum_norm_mul_some_effect_sq_le_one φ P hp J hJ)
  have hs (a : F) : star (J * P.effect (some a)) = P.effect (some a) * J := by
    rw [star_mul, (P.nonneg (some a)).isSelfAdjoint.star_eq, hJ.1.isSelfAdjoint.star_eq]
  simp only [hs, mul_sub, map_sub, Complex.sub_re, sum_sub_distrib] at h
  simp only [J, mul_sum, sum_mul, map_sum, Complex.re_sum] at h
  simpa only [mul_assoc, (hPC _ _).eq, (hGC _).symm.left_comm] using h

private theorem abs_sum_matching_drop_le (φ : AlgState A)
    (P N : Measurement (Option F) A) (hp : P.IsProjective)
    (B C : Measurement F A)
    (hPB : ∀ a b, Commute (P.effect a) (B.effect b))
    (hNB : ∀ a b, Commute (N.effect a) (B.effect b))
    (hNC : ∀ a b, Commute (N.effect a) (C.effect b)) :
    |(∑ a : F, ∑ b : F, (φ (P.effect (some a) * N.effect (some b) *
      (B.effect a * C.effect b))).re) -
      (∑ a : F, ∑ b : F, (φ (P.effect (some a) * N.effect (some b) * C.effect b)).re)| ≤
      √(∑ a : F, φ.norm (P.effect (some a) - P.successfulEffect * B.effect a) ^ 2) := by
  let J := ∑ b : F, N.effect (some b) * C.effect b
  have hJ := Measurement.sum_successful_matching_mem_Icc N C fun b => hNC _ b
  have h := φ.abs_sum_re_star_mul_le_of_normalized_right
    (fun a => P.effect (some a) - P.successfulEffect * B.effect a) (fun a => P.effect (some a) * J)
    (Measurement.sum_norm_some_effect_mul_sq_le_one φ P hp J hJ)
  have hsa (a : F) :
      star (P.effect (some a) - P.successfulEffect * B.effect a) *
        P.effect (some a) = P.effect (some a) - P.effect (some a) * B.effect a := by
    rw [star_sub, star_mul, (P.nonneg _).isSelfAdjoint.star_eq,
      P.successfulEffect_mem_Icc.1.isSelfAdjoint.star_eq, (B.nonneg _).isSelfAdjoint.star_eq,
      sub_mul, hp, mul_assoc, hp.successfulEffect_mul_some, ← (hPB _ _).eq]
  have he (a : F) : star (P.effect (some a) - P.successfulEffect * B.effect a) *
      (P.effect (some a) * J) = (P.effect (some a) - P.effect (some a) * B.effect a) * J := by
    rw [← mul_assoc, hsa]
  simp only [he, sub_mul, map_sub, Complex.sub_re, sum_sub_distrib] at h
  simp only [J, mul_sum, map_sum, Complex.re_sum] at h
  rw [abs_sub_comm]
  simpa only [mul_assoc, (hNB _ _).symm.left_comm] using h

private theorem abs_sum_right_drop_le (φ : AlgState A)
    (P N : Measurement (Option F) A) (hn : N.IsProjective) (C : Measurement F A) :
    |(∑ a : F, ∑ b : F, (φ (P.effect (some a) * N.effect (some b) * C.effect b)).re) -
      (∑ a : F, ∑ b : F, (φ (P.effect (some a) * N.effect (some b))).re)| ≤
      √(∑ b : F, φ.norm (N.effect (some b) - N.successfulEffect * C.effect b) ^ 2) := by
  have h := φ.abs_sum_re_star_mul_le_of_normalized
    (fun b => N.effect (some b) * P.successfulEffect)
    (fun b => N.effect (some b) - N.successfulEffect * C.effect b)
    (Measurement.sum_norm_some_effect_mul_sq_le_one φ N hn _
      P.successfulEffect_mem_Icc)
  have hnG (b : F) : N.effect (some b) * N.successfulEffect = N.effect (some b) := by
    have hc : Commute N.successfulEffect (N.effect (some b)) :=
      Commute.sum_left _ _ _ fun a _ => hn.commute_effect (some a) (some b)
    rw [← hc.eq]
    exact hn.successfulEffect_mul_some N b
  have he (b : F) : star (N.effect (some b) * P.successfulEffect) *
      (N.effect (some b) - N.successfulEffect * C.effect b) =
      P.successfulEffect * N.effect (some b) -
        P.successfulEffect * (N.effect (some b) * C.effect b) := by
    rw [star_mul, (N.nonneg (some b)).isSelfAdjoint.star_eq,
      P.successfulEffect_mem_Icc.1.isSelfAdjoint.star_eq, mul_sub, mul_assoc,
      hn (some b), mul_assoc, ← mul_assoc (N.effect (some b)), hnG]
  rw [abs_sub_comm, sum_comm (f := fun a b : F =>
    (φ (P.effect (some a) * N.effect (some b) * C.effect b)).re),
    sum_comm (f := fun a b : F => (φ (P.effect (some a) * N.effect (some b))).re)]
  simp only [he, map_sub, Complex.sub_re, sum_sub_distrib] at h
  simpa only [Measurement.successfulEffect, sum_mul, map_sum, Complex.re_sum, mul_assoc] using h

private theorem abs_sum_sandwich_copy_le (φ : AlgState A)
    (P N R : Measurement (Option F) A) (hn : N.IsProjective)
    (hPR : ∀ a b, Commute (P.effect a) (R.effect b))
    (hNR : ∀ a b, Commute (N.effect a) (R.effect b)) :
    |(∑ a : F, ∑ b : F, (φ (P.effect (some a) * N.effect (some b))).re) -
      (∑ a : F, ∑ b : F, (φ (N.effect (some b) * P.effect (some a) * N.effect (some b))).re)| ≤
      2 * √(Measurement.successfulCopyDefect φ N R) := by
  let G := P.successfulEffect
  let q (b : F) := N.effect (some b)
  let r (b : F) := R.effect (some b)
  have hG := P.successfulEffect_mem_Icc
  have hqr (b : F) : Commute (G * q b) (r b) :=
    (Commute.sum_left _ _ _ fun a _ => hPR (some a) (some b)).mul_left (hNR (some b) (some b))
  have hd (b : F) : star (q b - r b) = q b - r b := by
    simp only [q, r, star_sub, (N.nonneg _).isSelfAdjoint.star_eq,
      (R.nonneg _).isSelfAdjoint.star_eq]
  have h1 : |(∑ b : F, (φ (G * q b)).re) - ∑ b : F, (φ (r b * (G * q b))).re| ≤
      √(Measurement.successfulCopyDefect φ N R) := by
    have h := φ.abs_sum_re_star_mul_le_of_normalized (fun b => q b * G)
      (fun b => q b - r b) (Measurement.sum_norm_some_effect_mul_sq_le_one φ N hn G hG)
    have hterm (b : F) : star (q b * G) * (q b - r b) = G * q b - r b * (G * q b) := by
      rw [star_mul, hG.1.isSelfAdjoint.star_eq, (N.nonneg (some b)).isSelfAdjoint.star_eq,
        mul_sub, mul_assoc G (q b) (q b), show q b * q b = q b from hn _, (hqr b).eq]
    simpa only [hterm, map_sub, Complex.sub_re, sum_sub_distrib,
      Measurement.successfulCopyDefect, q, r] using h
  have h2 : |(∑ b : F, (φ (r b * (G * q b))).re) - ∑ b : F, (φ (q b * (G * q b))).re| ≤
      √(Measurement.successfulCopyDefect φ N R) := by
    have h := φ.abs_sum_re_star_mul_le_of_normalized_right
      (fun b => q b - r b) (fun b => G * q b)
      (Measurement.sum_norm_mul_some_effect_sq_le_one φ N hn G hG)
    rw [abs_sub_comm]
    simpa only [hd, sub_mul, map_sub, Complex.sub_re, sum_sub_distrib,
      Measurement.successfulCopyDefect, q, r] using h
  have hh := (abs_sub_le (∑ b, (φ (G * q b)).re)
    (∑ b, (φ (r b * (G * q b))).re) (∑ b, (φ (q b * (G * q b))).re)).trans
      (add_le_add h1 h2)
  rw [← two_mul] at hh
  rw [sum_comm (f := fun a b : F => (φ (P.effect (some a) * N.effect (some b))).re),
    sum_comm (f := fun a b : F =>
      (φ (N.effect (some b) * P.effect (some a) * N.effect (some b))).re)]
  simpa only [G, q, Measurement.successfulEffect, mul_sum, sum_mul, map_sum,
    Complex.re_sum, mul_assoc] using hh

private theorem mean_successfulPairDefect_eq {X : Type*} [Fintype X]
    (φ : AlgState A) (P : X → Measurement (Option F) A) (hP : ∀ u, (P u).IsProjective) :
    (𝔼 u, 𝔼 v, Measurement.successfulPairDefect φ (P u) (P v)) =
      2 * ((𝔼 u, 𝔼 v, ∑ a : F, ∑ b : F, (φ
        ((P v).effect (some b) * (P u).effect (some a) * (P v).effect (some b))).re) -
       (𝔼 u, 𝔼 v, ∑ a : F, ∑ b : F, (φ
        ((P u).effect (some a) * (P v).effect (some b) *
          (P u).effect (some a) * (P v).effect (some b))).re)) := by
  let p (u : X) (a : F) := (P u).effect (some a)
  have hterm (u v : X) (a b : F) :
      φ.norm (p u a * p v b - p v b * p u a) ^ 2 =
        (φ (p v b * p u a * p v b)).re + (φ (p u a * p v b * p u a)).re -
          ((φ (p u a * p v b * p u a * p v b)).re +
            (φ (p v b * p u a * p v b * p u a)).re) := by
    have hs (w : X) (c : F) : star (p w c) = p w c :=
      ((P w).nonneg _).isSelfAdjoint.star_eq
    have hp (w : X) (c : F) : p w c * p w c = p w c := hP w _
    rw [AlgState.norm_sq, star_sub, star_mul, star_mul, hs, hs, sub_mul, mul_sub, mul_sub]
    simp only [mul_assoc, ← mul_assoc (p u a) (p u a), ← mul_assoc (p v b) (p v b),
      hp, map_sub, Complex.sub_re]
    simp only [← mul_assoc]
    ring
  let mean (f : X → X → F → F → ℝ) := 𝔼 u, 𝔼 v, ∑ a : F, ∑ b : F, f u v a b
  have hswap (f : X → X → F → F → ℝ) :
      mean (fun u v a b => f v u b a) = mean f := by
    unfold mean
    rw [expect_comm univ univ]
    congr with u
    congr with v
    exact sum_comm
  change mean (fun u v a b => φ.norm (p u a * p v b - p v b * p u a) ^ 2) = _
  simp only [hterm, mean, sum_add_distrib, sum_sub_distrib, expect_add_distrib,
    expect_sub_distrib]
  rw [show (𝔼 u, 𝔼 v, ∑ a : F, ∑ b : F, (φ (p u a * p v b * p u a)).re) =
      𝔼 u, 𝔼 v, ∑ a : F, ∑ b : F, (φ (p v b * p u a * p v b)).re from hswap _,
    show (𝔼 u, 𝔼 v, ∑ a : F, ∑ b : F, (φ (p v b * p u a * p v b * p u a)).re) =
      𝔼 u, 𝔼 v, ∑ a : F, ∑ b : F, (φ (p u a * p v b * p u a * p v b)).re from hswap _]
  change _ = 2 * (mean _ - mean _)
  unfold mean
  ring

variable [Field F] [DecidableEq F]

/-- Agreement with the point measurement, the diagonal loss, the failure charge and
the polynomial copy defect bound the commutators of the successful evaluated effects. -/
theorem evaluatedSlice_successfulPairDefect_le_atDegrees
    (S : CommutingStrategy (Question F (m + 1)) (Question F (m + 1))
      (Answer F (m + 1)) (Answer F (m + 1)) A)
    (hPoint : ∀ u, (S.alice (.point u)).IsProjective)
    (hLine : ∀ L, (S.bob (.diagonal L)).IsProjective) (degree D : ℕ)
    (M : F → Measurement (Option (BoundedPolynomial F m d)) A) (hM : ∀ x, (M x).IsProjective)
    (Z : F → A) (hZ : ∀ x, 0 ≤ Z x)
    (hbound : ∀ x (g : BoundedPolynomial F m d),
      averagePolynomialPointEffect (fun u => decodedPoint S.alice (Fin.snoc u x)) g ≤ Z x)
    (hMP : ∀ x w g a, Commute ((M x).effect g) ((decodedPoint S.alice w).effect a))
    (hMZ : ∀ x y g, Commute ((M x).effect g) (Z y))
    (N : F → Measurement (Option (BoundedPolynomial F m d)) A) (hN : ∀ x, (N x).IsProjective)
    (hMN : ∀ x y a b, Commute ((M x).effect a) ((N y).effect b))
    {η ζ ξ : ℝ}
    (hcopy : (𝔼 x, Measurement.successfulCopyDefect S.state (M x) (N x)) ≤ ξ)
    (hfail : (𝔼 x : F, (S.state ((M x).effect none * Z x)).re) ≤ ζ) :
    let P (w : Point F (m + 1)) :=
      evaluatePolynomialMeasurement (M (w (Fin.last m))) (Fin.init w)
    (𝔼 w, Measurement.successfulMismatch S.state (P w) (decodedPoint S.alice w)) ≤ η →
    (𝔼 u, 𝔼 v, Measurement.successfulPairDefect S.state (P u) (P v)) ≤
      2 * (4 * √(2 * η) + 2 * √(64 * (m + 1 : ℝ) *
        (1 - (branchGameWithDiagonalCap (F := F) m degree D .diagonal).commutingWinProb S)) +
          2 * √ζ + 2 * √ξ) := by
  intro P hη
  let R (w : Point F (m + 1)) :=
    evaluatePolynomialMeasurement (N (w (Fin.last m))) (Fin.init w)
  have hPR (u v : Point F (m + 1)) (a b : Option F) :
      Commute ((P u).effect a) ((R v).effect b) :=
    Measurement.commute_map_map (M _) (N _) (hMN _ _)
      (Option.map fun g => eval (Fin.init u) g.val)
      (Option.map fun g => eval (Fin.init v) g.val) a b
  have hξ : (𝔼 w, Measurement.successfulCopyDefect S.state (P w) (R w)) ≤ ξ := by
    refine (expect_le_expect (g := fun w : Point F (m + 1) =>
      Measurement.successfulCopyDefect S.state (M (w (Fin.last m))) (N (w (Fin.last m))))
      (fun w _ => ?_)).trans ?_
    · exact Measurement.successfulCopyDefect_map_le S.state (M _) (N _) (hM _) (hN _)
        (fun a b => hMN _ _ (some a) (some b)) (fun g => eval (Fin.init w) g.val)
    · rw [← Fintype.expect_fin_snoc]
      simpa only [Fin.snoc_last, Fintype.expect_const] using hcopy
  let Q (u : Point F (m + 1)) := decodedPoint S.alice u
  let p (u : Point F (m + 1)) (a : F) := (P u).effect (some a)
  let b (u : Point F (m + 1)) (a : F) := (Q u).effect a
  let G (u : Point F (m + 1)) := (P u).successfulEffect
  let δ := 64 * (m + 1 : ℝ) *
    (1 - (branchGameWithDiagonalCap (F := F) m degree D .diagonal).commutingWinProb S)
  let defect (u : Point F (m + 1)) := ∑ a : F, S.state.norm (p u a - G u * b u a) ^ 2
  let score (f : Point F (m + 1) → Point F (m + 1) → F → F → A) :=
    𝔼 u, 𝔼 v, ∑ a : F, ∑ c : F, (S.state (f u v a c)).re
  -- Expand the squared commutator into the first and last of these averaged products.
  let s0 := score fun u v a c => p u a * p v c * p u a * p v c
  let s1 := score fun u v a c => p u a * p v c * p u a * (G v * b v c)
  let s2 := score fun u v a c => p u a * p v c * p u a * b v c
  let s3 := score fun u v a c => p u a * p v c * G u * (b v c * b u a)
  let s4 := score fun u v a c => p u a * p v c * G u * (b u a * b v c)
  let s5 := score fun u v a c => p u a * p v c * (b u a * b v c)
  let s6 := score fun u v a c => p u a * p v c * b v c
  let s7 := score fun u v a c => p u a * p v c
  let s8 := score fun u v a c => p v c * p u a * p v c
  have hP (u : Point F (m + 1)) : (P u).IsProjective :=
    (hM _).map (Option.map fun g => eval (Fin.init u) g.val)
  have hQ (u : Point F (m + 1)) : (Q u).IsProjective := (hPoint u).map decodePoint
  have hPQ (u v : Point F (m + 1)) (a : Option F) (c : F) :
      Commute ((P u).effect a) ((Q v).effect c) :=
    (Measurement.commute_map_right (M (u (Fin.last m))) _ _
      (fun g => (hMP _ _ g c).symm) a).symm
  have hPZ (u : Point F (m + 1)) (x : F) (a : Option F) :
      Commute ((P u).effect a) (Z x) :=
    (Measurement.commute_map_right (M (u (Fin.last m))) _ _
      (fun g => (hMZ _ _ g).symm) a).symm
  have hdefect₀ (u : Point F (m + 1)) : 0 ≤ defect u :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hdefect : (𝔼 u, defect u) ≤ 2 * η := by
    have he (u : Point F (m + 1)) :
        defect u = 2 * Measurement.successfulMismatch S.state (P u) (Q u) := by
      simpa only [defect, p, G, b, P, evaluatePolynomialMeasurement_successfulEffect] using
        evaluatedSlice_gated_stateDist_eq S.state (M (u (Fin.last m))) (Q u)
          (hM _) (hQ u) (fun g a => hMP _ _ g a) (Fin.init u)
    simp only [he, ← mul_expect]
    exact mul_le_mul_of_nonneg_left hη (by norm_num)
  have hscore (f g : Point F (m + 1) → Point F (m + 1) → F → F → A) :
      score f - score g = 𝔼 z : Point F (m + 1) × Point F (m + 1),
        ∑ a : F, ∑ c : F, ((S.state (f z.1 z.2 a c)).re - (S.state (g z.1 z.2 a c)).re) := by
    simp only [score, Fintype.expect_prod_type, sum_sub_distrib, expect_sub_distrib]
  -- Replace each slice effect by its gated point effect, charging the omitted failure terms.
  have h01 : |s0 - s1| ≤ √(2 * η) := by
    change |score _ - score _| ≤ _
    rw [hscore]
    refine abs_mean_le_sqrt (X := Point F (m + 1) × Point F (m + 1))
      _ (fun z => defect z.2) (fun z => hdefect₀ z.2) ?_ (by
        simpa only [Fintype.expect_comp_snd] using hdefect)
    intro z
    simpa only [sum_sub_distrib] using abs_sum_sandwich_replace_le
      S.state (P z.1) (P z.2) (hP z.1) (fun c => G z.2 * b z.2 c)
  have h12 : |s1 - s2| ≤ √ζ := by
    let loss (u v : Point F (m + 1)) :=
      ∑ a : F, ∑ c : F, (S.state (p u a * p v c * p u a * (P v).effect none * b v c)).re
    have he : s2 - s1 = 𝔼 u, 𝔼 v, loss u v := by
      simp only [s2, s1, score, loss, Measurement.effect_none_eq_one_sub_successfulEffect,
        mul_sub, sub_mul, mul_one, map_sub, Complex.sub_re, sum_sub_distrib, expect_sub_distrib,
        mul_assoc, G]
    rw [abs_sub_comm, he]
    simp only [Fintype.expect_eq_expect_snoc (loss _)]
    have hfixed (u : Point F (m + 1)) :
        |𝔼 x : F, 𝔼 v : Point F m, loss u (Fin.snoc v x)| ≤ √ζ :=
      abs_mean_le_sqrt _ (fun x => (S.state ((M x).effect none * Z x)).re)
        (fun x => S.state.re_apply_nonneg ((hMZ x x none).mul_nonneg ((M x).nonneg none) (hZ x)))
        (fun x => by
          simpa only [loss, b, p, P, Fin.snoc_last, Fin.init_snoc,
            evaluatePolynomialMeasurement_effect_none] using
            abs_average_evaluated_sandwich_failure_le S.state (M x) (P u) (hM x) (hP u)
              (fun v => Q (Fin.snoc v x)) (Z x) (hZ x) (hbound x)
              (fun a v c => hMP x (Fin.snoc v x) a c) (fun a v c => hPQ u (Fin.snoc v x) a c)
              (fun a => hMZ x x a) (hPZ u x)) hfail
    refine (abs_expect_le _ _).trans ?_
    simpa only [Fintype.expect_const] using
      expect_le_expect (s := univ) (g := fun _ : Point F (m + 1) => √ζ) fun u _ => hfixed u
  have h23 : |s2 - s3| ≤ √(2 * η) := by
    change |score _ - score _| ≤ _
    rw [hscore]
    refine abs_mean_le_sqrt (X := Point F (m + 1) × Point F (m + 1))
      _ (fun z => defect z.1) (fun z => hdefect₀ z.1) ?_ (by
        simpa only [Fintype.expect_comp_fst] using hdefect)
    intro z
    simpa only [sum_sub_distrib] using abs_sum_matching_replace_le
      S.state (P z.1) (P z.2) (hP z.1) (Q z.1) (Q z.2) (hPQ z.1 z.2) (hPQ z.2 z.2)
  have h34 : |s3 - s4| ≤ √δ := by
    change |score _ - score _| ≤ _
    rw [hscore]
    let pointDefect (z : Point F (m + 1) × Point F (m + 1)) :=
      Measurement.pairCommutatorDefect S.state (Q z.1) (Q z.2)
    refine abs_mean_le_sqrt _ pointDefect
      (fun z => sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _) ?_ ?_
    · intro z
      simp only [sum_sub_distrib]
      rw [abs_sub_comm]
      exact Measurement.abs_sum_mul_pointOrder_sub_le S.state (P z.1) (P z.2)
        (hP z.1) (hP z.2) (Q z.1) (Q z.2) (G z.1) (P z.1).successfulEffect_mem_Icc
    · simpa only [pointDefect, Fintype.expect_prod_type] using
        decodedPoint_pairCommutatorDefect_le_atDegrees S hPoint hLine degree D
  have h45 : |s4 - s5| ≤ √δ + √ζ := by
    rw [abs_sub_comm]
    change |score _ - score _| ≤ _
    rw [hscore, Fintype.expect_prod_type]
    have he (u v : Point F (m + 1)) (a c : F) :
        p u a * p v c * (b u a * b v c) - p u a * p v c * G u * (b u a * b v c) =
        p u a * p v c * (P u).effect none * (b u a * b v c) := by
      rw [Measurement.effect_none_eq_one_sub_successfulEffect, ← show G u = _ from rfl]
      noncomm_ring
    simp only [← Complex.sub_re, ← map_sub, he]
    exact abs_average_evaluated_failure_pointProduct_le_atDegrees
      S hPoint hLine degree D M hM Z hZ hbound hMP hMZ hfail
  have h56 : |s5 - s6| ≤ √(2 * η) := by
    change |score _ - score _| ≤ _
    rw [hscore]
    refine abs_mean_le_sqrt (X := Point F (m + 1) × Point F (m + 1))
      _ (fun z => defect z.1) (fun z => hdefect₀ z.1) ?_ (by
        simpa only [Fintype.expect_comp_fst] using hdefect)
    intro z
    simpa only [sum_sub_distrib] using abs_sum_matching_drop_le S.state (P z.1) (P z.2)
      (hP z.1) (Q z.1) (Q z.2) (hPQ z.1 z.1) (hPQ z.2 z.1) (hPQ z.2 z.2)
  have h67 : |s6 - s7| ≤ √(2 * η) := by
    change |score _ - score _| ≤ _
    rw [hscore]
    refine abs_mean_le_sqrt (X := Point F (m + 1) × Point F (m + 1))
      _ (fun z => defect z.2) (fun z => hdefect₀ z.2) ?_ (by
        simpa only [Fintype.expect_comp_snd] using hdefect)
    intro z
    simpa only [sum_sub_distrib] using
      abs_sum_right_drop_le S.state (P z.1) (P z.2) (hP z.2) (Q z.2)
  -- Insert the commuting copy to move the final evaluated effect to the front.
  have h78 : |s7 - s8| ≤ 2 * √ξ := by
    change |score _ - score _| ≤ _
    rw [hscore]
    refine (abs_expect_le _ _).trans ((expect_le_expect
      (g := fun z => 2 * √(Measurement.successfulCopyDefect S.state (P z.2) (R z.2)))
      fun z _ => ?_).trans ?_)
    · simpa only [sum_sub_distrib] using abs_sum_sandwich_copy_le
        S.state (P z.1) (P z.2) (R z.2) (hP z.2) (hPR z.1 z.2) (hPR z.2 z.2)
    · rw [Fintype.expect_comp_snd
          (fun w => 2 * √(Measurement.successfulCopyDefect S.state (P w) (R w))), ← mul_expect]
      exact mul_le_mul_of_nonneg_left
        ((Fintype.expect_sqrt_le_sqrt_expect _ (fun z => sum_nonneg fun _ _ => sq_nonneg _)).trans
          (Real.sqrt_le_sqrt hξ)) (by norm_num)
  rw [mean_successfulPairDefect_eq S.state P hP]
  change 2 * (s8 - s0) ≤ 2 * (4 * √(2 * η) + 2 * √δ + 2 * √ζ + 2 * √ξ)
  linarith [neg_abs_le (s0 - s1), neg_abs_le (s1 - s2), neg_abs_le (s2 - s3),
    neg_abs_le (s3 - s4), neg_abs_le (s4 - s5), neg_abs_le (s5 - s6),
    neg_abs_le (s6 - s7), neg_abs_le (s7 - s8)]

/-- Agreement with the point measurement, the diagonal loss, the failure charge and
the polynomial copy defect bound the commutators of the successful evaluated effects. -/
theorem evaluatedSlice_successfulPairDefect_le
    (S : CommutingStrategy (Question F (m + 1)) (Question F (m + 1))
      (Answer F (m + 1)) (Answer F (m + 1)) A)
    (hPoint : ∀ u, (S.alice (.point u)).IsProjective)
    (hLine : ∀ L, (S.bob (.diagonal L)).IsProjective) (degree : ℕ)
    (M : F → Measurement (Option (BoundedPolynomial F m d)) A) (hM : ∀ x, (M x).IsProjective)
    (Z : F → A) (hZ : ∀ x, 0 ≤ Z x)
    (hbound : ∀ x (g : BoundedPolynomial F m d),
      averagePolynomialPointEffect (fun u => decodedPoint S.alice (Fin.snoc u x)) g ≤ Z x)
    (hMP : ∀ x w g a, Commute ((M x).effect g) ((decodedPoint S.alice w).effect a))
    (hMZ : ∀ x y g, Commute ((M x).effect g) (Z y))
    (N : F → Measurement (Option (BoundedPolynomial F m d)) A) (hN : ∀ x, (N x).IsProjective)
    (hMN : ∀ x y a b, Commute ((M x).effect a) ((N y).effect b))
    {η ζ ξ : ℝ}
    (hcopy : (𝔼 x, Measurement.successfulCopyDefect S.state (M x) (N x)) ≤ ξ)
    (hfail : (𝔼 x : F, (S.state ((M x).effect none * Z x)).re) ≤ ζ) :
    let P (w : Point F (m + 1)) :=
      evaluatePolynomialMeasurement (M (w (Fin.last m))) (Fin.init w)
    (𝔼 w, Measurement.successfulMismatch S.state (P w) (decodedPoint S.alice w)) ≤ η →
    (𝔼 u, 𝔼 v, Measurement.successfulPairDefect S.state (P u) (P v)) ≤
      2 * (4 * √(2 * η) + 2 * √(64 * (m + 1 : ℝ) *
        (1 - (branchGame (F := F) m degree .diagonal).commutingWinProb S)) +
          2 * √ζ + 2 * √ξ) := by
  rw [branchGame_eq_withDiagonalCap]
  exact evaluatedSlice_successfulPairDefect_le_atDegrees S hPoint hLine degree ((m + 1) * degree)
    M hM Z hZ hbound hMP hMZ N hN hMN hcopy hfail

end Cslib.PCP.LowIndividualDegree
