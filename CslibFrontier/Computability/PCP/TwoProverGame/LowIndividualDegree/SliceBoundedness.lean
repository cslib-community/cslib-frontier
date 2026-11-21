/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.PastingConsistency
public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.PointCommutativity
public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.PolynomialPointEffect
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Foundations.Quantum.Algebra.MeasurementMixture
public import CslibFrontier.Foundations.Quantum.Algebra.GatedAgreement

/-!
# Transferring point agreement and boundedness to evaluated slices

Evaluating a projective polynomial measurement preserves success and failure.
Its agreement with a point measurement controls state distance after multiplying
the point effects by the success projection. A positive operator dominating the
averaged point effects controls the term with the failure projection, as in
[Ji, Natarajan, Vidick, Wright and Yuen, Equation (95) and Claims 11.2–11.3]
[JNVWY2020LowIndividualDegree].

## Main results

* `Cslib.PCP.LowIndividualDegree.evaluatedSlice_gated_stateDist_eq` converts
  agreement on successful outcomes into a gated state-distance identity.
* `Cslib.PCP.LowIndividualDegree.abs_average_evaluated_sandwich_failure_le` bounds
  the failure term sandwiched by a second slice's effects.
* `Cslib.PCP.LowIndividualDegree.abs_average_evaluated_failure_pointProduct_le`
  bounds the failure term with two point measurements using the diagonal test.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Finset Cslib.Quantum MvPolynomial
open scoped BigOperators Real

variable {F A : Type*} {m d : ℕ} [Field F] [Fintype F] [DecidableEq F]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Agreement of the successful evaluated slice with the point measurement gives the
squared state distance from the point measurement multiplied by the slice success effect. -/
theorem evaluatedSlice_gated_stateDist_eq
    (φ : AlgState A) (P : Measurement (Option (BoundedPolynomial F m d)) A)
    (B : Measurement F A) (hp : P.IsProjective) (hb : B.IsProjective)
    (hc : ∀ a b, Commute (P.effect a) (B.effect b)) (u : (Fin m → F)) :
    (∑ a, φ.norm ((evaluatePolynomialMeasurement P u).effect (some a) -
      P.successfulEffect * B.effect a) ^ 2) =
        2 * Measurement.successfulMismatch φ (evaluatePolynomialMeasurement P u) B := by
  have hP : (evaluatePolynomialMeasurement P u).IsProjective :=
    hp.map (Option.map fun g => eval u g.val)
  have hc' (a : Option F) (b : F) : Commute ((evaluatePolynomialMeasurement P u).effect a)
      (B.effect b) :=
    (Measurement.commute_map_right P _ _ (fun g => (hc g b).symm) a).symm
  simpa only [evaluatePolynomialMeasurement_successfulEffect] using
    Measurement.sum_norm_sub_success_mul_sq_eq φ (evaluatePolynomialMeasurement P u) B hP hb hc'

/-- A positive common majorant of the averaged point effects controls the failure term
after sandwiching an evaluated slice by the successful effects of a second measurement.
This is the fixed-slice estimate underlying Claim 11.2. -/
theorem abs_average_evaluated_sandwich_failure_le {β : Type*} [Fintype β]
    (φ : AlgState A) (P : Measurement (Option (BoundedPolynomial F m d)) A)
    (N : Measurement (Option β) A) (hp : P.IsProjective) (hn : N.IsProjective)
    (B : (Fin m → F) → Measurement F A) (Z : A) (hZ : 0 ≤ Z)
    (hbound : ∀ g : BoundedPolynomial F m d, averagePolynomialPointEffect B g ≤ Z)
    (hpB : ∀ a u b, Commute (P.effect a) ((B u).effect b))
    (hnB : ∀ a u b, Commute (N.effect a) ((B u).effect b))
    (hpZ : ∀ a, Commute (P.effect a) Z) (hnZ : ∀ a, Commute (N.effect a) Z) :
    |𝔼 u : (Fin m → F), ∑ a : β, ∑ b : F, (φ
        (N.effect (some a) * (evaluatePolynomialMeasurement P u).effect (some b) *
          N.effect (some a) * P.effect none * (B u).effect b)).re| ≤
      √((φ (P.effect none * Z)).re) := by
  classical
  let K (p : β × BoundedPolynomial F m d) := P.effect (some p.2) * N.effect (some p.1)
  let H (p : β × BoundedPolynomial F m d) := averagePolynomialPointEffect B p.2
  have hKTerm (a : β) (g : BoundedPolynomial F m d) :
      star (K (a, g)) * K (a, g) =
        N.effect (some a) * P.effect (some g) * N.effect (some a) := by
    simp only [K, star_mul, (P.nonneg _).isSelfAdjoint.star_eq,
      (N.nonneg _).isSelfAdjoint.star_eq, ← mul_assoc]
    rw [mul_assoc (N.effect (some a)), hp]
  have hK : ∑ p, star (K p) * K p ≤ 1 := by
    rw [Fintype.sum_prod_type]
    exact Measurement.sum_successful_product_sq_le P N hp hn
  have h := φ.abs_sum_failure_mul_le K H (P.effect none) Z
    (P.nonneg none).isSelfAdjoint (hp none) hK
    (fun p => averagePolynomialPointEffect_mem_Icc B p.2) hZ (fun p => hbound p.2)
    (fun p => commute_averagePolynomialPointEffect B p.2 _ fun u b =>
      (hpB _ u b).mul_left (hnB _ u b))
    (fun p => (hpZ _).mul_left (hnZ _))
    (fun p => commute_averagePolynomialPointEffect B p.2 _ (hpB none)) (hpZ none)
  rw [Fintype.sum_prod_type] at h
  have hsum (u : (Fin m → F)) (a : β) :
      (∑ b : F, (φ (N.effect (some a) * (evaluatePolynomialMeasurement P u).effect (some b) *
          N.effect (some a) * P.effect none * (B u).effect b)).re) =
        ∑ g, (φ (star (K (a, g)) * K (a, g) * P.effect none *
          (B u).effect (eval u g.val))).re := by
    simp only [evaluatePolynomialMeasurement_effect_some, mul_sum, sum_mul, map_sum, Complex.re_sum]
    conv_rhs => rw [← sum_fiberwise univ (fun g : BoundedPolynomial F m d => eval u g.val)]
    refine sum_congr rfl fun b _ => sum_congr rfl fun g hg => ?_
    rw [hKTerm, (mem_filter.mp hg).2]
  have hmean (a : β) (g : BoundedPolynomial F m d) :
      (𝔼 u : (Fin m → F), (φ (star (K (a, g)) * K (a, g) * P.effect none *
        (B u).effect (eval u g.val))).re) =
        (φ (star (K (a, g)) * K (a, g) * P.effect none * H (a, g))).re := by
    rw [show H (a, g) = _ from averagePolynomialPointEffect_eq B g]
    rw [← φ.re_apply_uniformAverage, ← mul_sum, ← mul_smul_comm]
  simp_rw [hsum, expect_sum_comm, hmean]
  exact h

/-- After moving the varying point effect to the right, the same majorant controls
the failure term with a second fixed point measurement. -/
theorem abs_average_evaluated_failure_rightPoint_le {β : Type*} [Fintype β]
    (φ : AlgState A) (P : Measurement (Option (BoundedPolynomial F m d)) A)
    (N : Measurement (Option β) A) (hp : P.IsProjective) (hn : N.IsProjective)
    (B : (Fin m → F) → Measurement F A) (hB : ∀ u, (B u).IsProjective)
    (C : Measurement β A) (hC : C.IsProjective) (Z : A) (hZ : 0 ≤ Z)
    (hbound : ∀ g : BoundedPolynomial F m d, averagePolynomialPointEffect B g ≤ Z)
    (hpB : ∀ a u b, Commute (P.effect a) ((B u).effect b))
    (hnB : ∀ a u b, Commute (N.effect a) ((B u).effect b))
    (hpC : ∀ a b, Commute (P.effect a) (C.effect b))
    (hnC : ∀ a b, Commute (N.effect a) (C.effect b))
    (hpZ : ∀ a, Commute (P.effect a) Z) (hnZ : ∀ a, Commute (N.effect a) Z) :
    |𝔼 u : (Fin m → F), ∑ a : F, ∑ b : β, (φ
        ((evaluatePolynomialMeasurement P u).effect (some a) * N.effect (some b) *
          P.effect none * (C.effect b * (B u).effect a))).re| ≤
      √((φ (P.effect none * Z)).re) := by
  classical
  let K (p : β × BoundedPolynomial F m d) := P.effect (some p.2) * N.effect (some p.1)
  let L (p : β × BoundedPolynomial F m d) := P.effect (some p.2) * C.effect p.1
  let Y (u : Fin m → F) (p : β × BoundedPolynomial F m d) :=
    (K p * P.effect none) * (B u).effect (eval u p.2.val)
  have hK : ∑ p, star (K p) * K p ≤ 1 := by
    rw [Fintype.sum_prod_type]
    exact Measurement.sum_successful_product_sq_le P N hp hn
  have hL : (∑ p, φ.norm (L p) ^ 2) ≤ 1 := by
    rw [Fintype.sum_prod_type, sum_comm]
    simp only [L, (hpC _ _).eq, Measurement.sum_norm_effect_mul_sq φ C hC]
    simpa only [mul_one, AlgState.norm_one, one_pow] using
      Measurement.sum_norm_some_effect_mul_sq_le φ P hp 1
  have hsum (u : Fin m → F) :
      (∑ a : F, ∑ b : β, (φ
        ((evaluatePolynomialMeasurement P u).effect (some a) * N.effect (some b) *
          P.effect none * (C.effect b * (B u).effect a))).re) =
        ∑ p, (φ (star (L p) * Y u p)).re := by
    rw [sum_comm, Fintype.sum_prod_type]
    refine sum_congr rfl fun b _ => ?_
    simp only [evaluatePolynomialMeasurement_effect_some, sum_mul, map_sum, Complex.re_sum]
    conv_rhs => rw [← sum_fiberwise univ (fun g : BoundedPolynomial F m d => eval u g.val)]
    refine sum_congr rfl fun a _ => sum_congr rfl fun g hg => ?_
    have he := (mem_filter.mp hg).2
    simp only [L, Y, K, star_mul, (P.nonneg _).isSelfAdjoint.star_eq,
      (C.nonneg _).isSelfAdjoint.star_eq, he, mul_assoc]
    rw [← mul_assoc (P.effect (some g)) (P.effect (some g)), hp,
      (hpC (some g) b).symm.left_comm, (hnC (some b) b).symm.left_comm,
      (hpC none b).symm.left_comm]
  have hY (u : Fin m → F) (p : β × BoundedPolynomial F m d) :
      φ.norm (Y u p) ^ 2 = (φ (star (K p * P.effect none) *
        (B u).effect (eval u p.2.val) * (K p * P.effect none))).re := by
    let D := (B u).effect (eval u p.2.val)
    have hc : Commute (K p * P.effect none) D :=
      ((hpB _ _ _).mul_left (hnB _ _ _)).mul_left (hpB none _ _)
    change φ.norm ((K p * P.effect none) * D) ^ 2 = _
    rw [AlgState.norm_sq, hc.eq, star_mul, (B u).nonneg _ |>.isSelfAdjoint.star_eq,
      mul_assoc, ← mul_assoc D D, hB, ← mul_assoc]
  have hmean (p : β × BoundedPolynomial F m d) :
      (𝔼 u : Fin m → F, φ.norm (Y u p) ^ 2) =
        (φ (star (K p * P.effect none) * averagePolynomialPointEffect B p.2 *
          (K p * P.effect none))).re := by
    simp only [hY]
    rw [averagePolynomialPointEffect_eq]
    rw [← φ.re_apply_uniformAverage, ← sum_mul, ← mul_sum, ← smul_mul_assoc, ← mul_smul_comm]
  have hv : (𝔼 u : Fin m → F, ∑ p, φ.norm (Y u p) ^ 2) ≤ (φ (P.effect none * Z)).re := by
    simp only [expect_sum_comm, hmean, ← Complex.re_sum, ← map_sum]
    exact φ.re_apply_mono (sum_failure_conjugate_le K
      (fun p => averagePolynomialPointEffect B p.2) (P.effect none) Z
      (P.nonneg none).isSelfAdjoint (hp none) hK hZ (fun p => hbound p.2)
      (fun p => (hpZ _).mul_left (hnZ _)) (hpZ none))
  simp only [hsum]
  calc
    _ ≤ 𝔼 u : Fin m → F, √(∑ p, φ.norm (Y u p) ^ 2) := by
      refine (abs_expect_le _ _).trans (expect_le_expect fun u _ => ?_)
      exact φ.abs_sum_re_star_mul_le_of_normalized L (Y u) hL
    _ ≤ _ := (Fintype.expect_sqrt_le_sqrt_expect _ (fun u =>
      sum_nonneg fun p _ => sq_nonneg _)).trans (Real.sqrt_le_sqrt hv)

/-- Swapping two decoded point effects inside the evaluated-slice failure term is
controlled by the diagonal verifier's loss. The preceding projective effects may
depend on either of the independently sampled points. -/
theorem abs_average_failure_pointOrder_sub_le {n : ℕ}
    (S : CommutingStrategy (Question F (n + 1)) (Question F (n + 1))
      (Answer F (n + 1)) (Answer F (n + 1)) A)
    (hPoint : ∀ u, (S.alice (.point u)).IsProjective)
    (hLine : ∀ L, (S.bob (.diagonal L)).IsProjective) (degree : ℕ)
    (P : Point F (n + 1) → Measurement (Option F) A) (hP : ∀ u, (P u).IsProjective) :
    |𝔼 u : Point F (n + 1), 𝔼 v : Point F (n + 1),
        ((∑ a : F, ∑ b : F, (S.state ((P u).effect (some a) * (P v).effect (some b) *
            (P u).effect none *
              ((decodedPoint S.alice u).effect a * (decodedPoint S.alice v).effect b))).re) -
          (∑ a : F, ∑ b : F, (S.state ((P u).effect (some a) * (P v).effect (some b) *
            (P u).effect none *
              ((decodedPoint S.alice v).effect b * (decodedPoint S.alice u).effect a))).re))| ≤
      √(64 * (n + 1 : ℝ) * (1 - (branchGame (F := F) n degree .diagonal).commutingWinProb S)) :=
  let f (u v : Point F (n + 1)) :=
    Measurement.pairCommutatorDefect S.state (decodedPoint S.alice u) (decodedPoint S.alice v)
  calc
    _ ≤ 𝔼 u : Point F (n + 1), 𝔼 v : Point F (n + 1), √(f u v) := by
      refine (abs_expect_le _ _).trans (expect_le_expect fun u _ => ?_)
      refine (abs_expect_le _ _).trans (expect_le_expect fun v _ => ?_)
      exact Measurement.abs_sum_failure_pointOrder_sub_le S.state (P u) (P v)
        (hP u) (hP v) (decodedPoint S.alice u) (decodedPoint S.alice v)
    _ ≤ √(𝔼 u : Point F (n + 1), 𝔼 v : Point F (n + 1), f u v) := by
      simpa only [Fintype.expect_prod_type] using
        Fintype.expect_sqrt_le_sqrt_expect
          (fun z : Point F (n + 1) × Point F (n + 1) => f z.1 z.2) (fun z => by
            unfold f Measurement.pairCommutatorDefect
            exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _)
    _ ≤ _ := Real.sqrt_le_sqrt (decodedPoint_pairCommutatorDefect_le S hPoint hLine degree)

/-- The evaluated-slice term with a failure projection is bounded by the slice
majorants and the diagonal test, as in Claim 11.3. -/
theorem abs_average_evaluated_failure_pointProduct_le
    (S : CommutingStrategy (Question F (m + 1)) (Question F (m + 1))
      (Answer F (m + 1)) (Answer F (m + 1)) A)
    (hPoint : ∀ u, (S.alice (.point u)).IsProjective)
    (hLine : ∀ L, (S.bob (.diagonal L)).IsProjective) (degree : ℕ)
    (M : F → Measurement (Option (BoundedPolynomial F m d)) A) (hM : ∀ x, (M x).IsProjective)
    (Z : F → A) (hZ : ∀ x, 0 ≤ Z x)
    (hbound : ∀ x (g : BoundedPolynomial F m d),
      averagePolynomialPointEffect (fun u => decodedPoint S.alice (Fin.snoc u x)) g ≤ Z x)
    (hMP : ∀ x w g a, Commute ((M x).effect g) ((decodedPoint S.alice w).effect a))
    (hMZ : ∀ x y g, Commute ((M x).effect g) (Z y)) {ζ : ℝ}
    (hfail : (𝔼 x : F, (S.state ((M x).effect none * Z x)).re) ≤ ζ) :
    let P (w : Point F (m + 1)) :=
      evaluatePolynomialMeasurement (M (w (Fin.last m))) (Fin.init w)
    |𝔼 u : Point F (m + 1), 𝔼 v : Point F (m + 1), ∑ a : F, ∑ b : F,
      (S.state ((P u).effect (some a) * (P v).effect (some b) * (P u).effect none *
        ((decodedPoint S.alice u).effect a * (decodedPoint S.alice v).effect b))).re| ≤
      √(64 * (m + 1 : ℝ) * (1 - (branchGame (F := F) m degree .diagonal).commutingWinProb S)) +
        √ζ := by
  intro P
  let Q (u : Point F (m + 1)) := decodedPoint S.alice u
  let ordered (u v : Point F (m + 1)) :=
    ∑ a : F, ∑ b : F, (S.state ((P u).effect (some a) * (P v).effect (some b) *
      (P u).effect none * ((Q u).effect a * (Q v).effect b))).re
  let reordered (u v : Point F (m + 1)) :=
    ∑ a : F, ∑ b : F, (S.state ((P u).effect (some a) * (P v).effect (some b) *
      (P u).effect none * ((Q v).effect b * (Q u).effect a))).re
  have hP (u : Point F (m + 1)) : (P u).IsProjective :=
    (hM _).map (Option.map fun g => eval (Fin.init u) g.val)
  have hQ (u : Point F (m + 1)) : (Q u).IsProjective := (hPoint u).map decodePoint
  have hswap := abs_average_failure_pointOrder_sub_le S hPoint hLine degree P hP
  change |𝔼 u, 𝔼 v, (ordered u v - reordered u v)| ≤ _ at hswap
  simp only [expect_sub_distrib] at hswap
  have hfixed (x : F) (v : Point F (m + 1)) :
      |𝔼 u : Point F m, reordered (Fin.snoc u x) v| ≤
        √((S.state ((M x).effect none * Z x)).re) := by
    have hnQ (b : Option F) (w : Point F (m + 1)) (a : F) :
        Commute ((P v).effect b) ((Q w).effect a) :=
      (Measurement.commute_map_right (M (v (Fin.last m))) _ _
        (fun g => (hMP _ _ g a).symm) b).symm
    have hnZ (b : Option F) : Commute ((P v).effect b) (Z x) :=
      (Measurement.commute_map_right (M (v (Fin.last m))) _ _
        (fun g => (hMZ _ _ g).symm) b).symm
    have h := abs_average_evaluated_failure_rightPoint_le S.state (M x) (P v) (hM x) (hP v)
      (fun u => Q (Fin.snoc u x)) (fun _ => hQ _) (Q v) (hQ v) (Z x) (hZ x) (hbound x)
      (fun g u a => hMP x (Fin.snoc u x) g a) (fun b u a => hnQ b (Fin.snoc u x) a)
      (fun g b => hMP x v g b) (fun b a => hnQ b v a) (fun g => hMZ x x g) hnZ
    simpa only [reordered, P, Fin.snoc_last, Fin.init_snoc,
      evaluatePolynomialMeasurement_effect_none] using h
  have hremaining : |𝔼 u, 𝔼 v, reordered u v| ≤ √ζ := by
    rw [expect_comm univ univ]
    simp_rw [Fintype.expect_eq_expect_snoc (fun u => reordered u _)]
    refine (abs_expect_le _ _).trans ?_
    refine (expect_le_expect fun v _ => abs_expect_le _ _).trans ?_
    refine (expect_le_expect fun v _ => expect_le_expect fun x _ => hfixed x v).trans ?_
    rw [Fintype.expect_const]
    apply (Fintype.expect_sqrt_le_sqrt_expect _ ?_).trans (Real.sqrt_le_sqrt hfail)
    intro x
    exact S.state.re_apply_nonneg (Commute.mul_nonneg ((M x).nonneg none) (hZ x) (hMZ x x none))
  change |𝔼 u, 𝔼 v, ordered u v| ≤ _
  simpa only [sub_zero] using (abs_sub_le _ (𝔼 u, 𝔼 v, reordered u v) 0).trans
    (by simpa only [sub_zero] using add_le_add hswap hremaining)

end Cslib.PCP.LowIndividualDegree
