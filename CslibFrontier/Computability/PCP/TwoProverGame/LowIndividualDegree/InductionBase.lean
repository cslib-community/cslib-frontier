/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.BoundedPolynomial
public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.VerticalAxis
import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.AxisPolynomialAnswer
import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.OneCoordinate
import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.PolynomialMeasurement
import CslibFrontier.Foundations.Probability.InnerProductResampling
import CslibFrontier.Foundations.Quantum.Algebra.CStar
import CslibFrontier.Foundations.Quantum.Algebra.MaxEntangled
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Base cases for low individual degree soundness

With one coordinate, the measurement on the unique axis line gives the local polynomial
measurement used to start the induction in [JNVWY2020LowIndividualDegree, §6.2].
At degree zero, every decoded axis answer is constant along its line. The
product resampling inequality controls the variance of point effects by the
axis loss. The consistency branch then relates those effects to the other
player's point effects, so a measurement at one fixed point suffices.

## Main results

* `Cslib.PCP.LowIndividualDegree.exists_one_coordinate_polynomial_POVM`:
  the axis branch score bounds the matching mass of a local polynomial POVM.
* `Cslib.PCP.LowIndividualDegree.exists_degree_zero_polynomial_POVM`:
  the axis and consistency losses bound the disagreement with a constant-polynomial POVM.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Cslib.Quantum Finset Matrix Function
open scoped BigOperators MatrixOrder ComplexOrder Kronecker Matrix.Norms.L2Operator

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- A polynomial function on the whole line has a bounded multivariate representative. -/
theorem PolynomialFunction.exists_boundedPolynomial {d : ℕ} (f : PolynomialFunction F d) :
    ∃ p : BoundedPolynomial F 1 d, ∀ u, MvPolynomial.eval u p.val = f.eval u := by
  obtain ⟨p, hp, he⟩ := f.exists_polynomial
  let e := MvPolynomial.uniqueAlgEquiv F (Fin 1)
  refine ⟨⟨e.symm p, fun i => MvPolynomial.degreeOf_le_iff.mpr fun a ha => ?_⟩, fun u => ?_⟩
  · rw [Subsingleton.elim i default]
    exact not_lt.mp fun h => (MvPolynomial.mem_support_iff.mp ha)
      ((MvPolynomial.coeff_uniqueAlgEquiv_symm F p a).trans
        (Polynomial.coeff_eq_zero_of_natDegree_lt (hp.trans_lt h)))
  · change MvPolynomial.eval₂ (RingHom.id F) u (e.symm p) = _
    rw [MvPolynomial.eval₂_uniqueAlgEquiv_symm, he]; rfl

private theorem acceptScore_swap_of_symmetric {m : ℕ}
    (S : QuantumStrategy (Question F m) (Question F m) (Answer F m) (Answer F m) ι ι)
    (hM : S.bob = S.alice) (hψ : ∀ a b, S.state.ofLp (a, b) = S.state.ofLp (b, a))
    (d : ℕ) (x y : Question F m) :
    acceptScore S.toCommuting d y x = acceptScore S.toCommuting d x y := by
  classical
  rw [acceptScore_eq_sum, acceptScore_eq_sum, sum_comm]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  simp only [accepts_eq_withDiagonalCap, acceptsWithDiagonalCap_swap d (m * d) y x b a,
    S.prob_toCommuting_swap_of_symmetric hM hψ x y a b]
  split <;> simp_all

private theorem exists_polynomial_POVM_of_decoding {n d : ℕ}
    (S : QuantumStrategy (Question F (n + 1)) (Question F (n + 1))
      (Answer F (n + 1)) (Answer F (n + 1)) ι ι)
    (q : Question F (n + 1)) (f : Answer F (n + 1) → BoundedPolynomial F (n + 1) d)
    (s : ℝ)
    (h : s ≤ 𝔼 u : Point F (n + 1),
      Measurement.agreement S.toCommuting.state (decodedPoint S.toCommuting.alice u)
        ((S.toCommuting.bob q).map fun a => MvPolynomial.eval u (f a).val)) :
    ∃ G : POVM (Option (BoundedPolynomial F (n + 1) d)) ι,
      s ≤ 𝔼 u : Point F (n + 1), ∑ g : BoundedPolynomial F (n + 1) d,
        (S.toCommuting.state ((QuantumStrategy.rightMeasurement (ι := ι) G).effect (some g) *
          (decodedPoint S.toCommuting.alice u).effect (MvPolynomial.eval u g.val))).re := by
  classical
  let C := S.toCommuting
  let G := ((S.bob q).toMeasurement.map (some ∘ f)).toPOVM
  refine ⟨G, h.trans (expect_le_expect fun u _ => le_of_eq ?_)⟩
  have hlift : QuantumStrategy.rightMeasurement (ι := ι) G = (C.bob q).map (some ∘ f) :=
    Measurement.ext fun a => by
      simp only [G, QuantumStrategy.rightMeasurement, Measurement.toPOVM_effect,
        Measurement.map_effect, POVM.toMeasurement_effect, C, QuantumStrategy.toCommuting]
      exact map_sum (oneKronecker (ι := ι)) _ _
  rw [hlift, Measurement.agreement]
  have hread (b : F) :
      ((C.bob q).map (fun a => MvPolynomial.eval u (f a).val)).effect b =
        ∑ g with MvPolynomial.eval u g.val = b, ((C.bob q).map (some ∘ f)).effect (some g) := by
    rw [← evaluatePolynomialMeasurement_effect_some, evaluatePolynomialMeasurement,
      Measurement.map_map, Measurement.map_effect, Measurement.map_effect]
    simp only [Function.comp_apply, Option.map_some, Option.some.injEq]
  change (∑ b, (C.state ((decodedPoint C.alice u).effect b *
    ((C.bob q).map fun a => MvPolynomial.eval u (f a).val).effect b)).re) = _
  simp only [hread, mul_sum, map_sum, Complex.re_sum]
  rw [← sum_fiberwise univ (fun g : BoundedPolynomial F (n + 1) d => MvPolynomial.eval u g.val)]
  refine sum_congr rfl fun b _ => sum_congr rfl fun g hg => ?_
  rw [(mem_filter.mp hg).2]
  exact congrArg (fun x => (C.state x).re)
    (Measurement.commute_map_map _ _ (C.commute (.point u) q) decodePoint (some ∘ f) _ _).eq

/-- On the one-coordinate test, Bob's line measurement yields a local polynomial POVM
whose matching mass with Alice's point answers is at least the axis branch score. -/
theorem exists_one_coordinate_polynomial_POVM
    (S : QuantumStrategy (Question F 1) (Question F 1) (Answer F 1) (Answer F 1) ι ι)
    (hM : S.bob = S.alice) (hψ : ∀ a b, S.state.ofLp (a, b) = S.state.ofLp (b, a))
    (d : ℕ) :
    ∃ G : POVM (Option (BoundedPolynomial F 1 d)) ι,
      (branchGame (F := F) 0 d .axis).commutingWinProb S.toCommuting ≤
        𝔼 u : Point F 1, ∑ g : BoundedPolynomial F 1 d,
          (S.toCommuting.state ((QuantumStrategy.rightMeasurement (ι := ι) G).effect (some g) *
            (decodedPoint S.toCommuting.alice u).effect (MvPolynomial.eval u g.val))).re := by
  classical
  let C := S.toCommuting
  choose p hp using fun f : PolynomialFunction F d => f.exists_boundedPolynomial
  let f (a : Answer F 1) := p (decodePolynomial d a)
  apply exists_polynomial_POVM_of_decoding S (.axis univ) f
  rw [axisScore_one_eq_expect]
  refine expect_le_expect fun u _ => ?_
  rw [acceptScore_swap_of_symmetric S hM hψ d (.point u) (.axis univ)]
  have hscore := acceptScore_one_le_pointAgreement C d u
  simp only [← two_mul, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [Measurement.map_map] at hscore
  simpa only [C, f, hp, decodedPoint, Function.comp_def] using hscore

section DegreeZero

variable {n : ℕ}
local notation "Q" => Question F (n + 1)
local notation "Ans" => Answer F (n + 1)
local notation "Pt" => Point F (n + 1)
local notation "Joint" => Matrix (ι × ι) (ι × ι) ℂ

private theorem degreeZero_pointVariance
    (C : CommutingStrategy Q Q Ans Ans Joint) :
    (𝔼 u : Pt, 𝔼 v : Pt, ∑ a,
      C.state.norm ((decodedPoint C.alice u).effect a - (decodedPoint C.alice v).effect a) ^ 2) ≤
        8 * (n + 1 : ℝ) * (1 - (branchGame (F := F) n 0 .axis).commutingWinProb C) := by
  let φ := C.state
  let A (u : Pt) (a : F) := (decodedPoint C.alice u).effect a
  let R (i : Fin (n + 1)) (u : Pt) (a : F) :=
    ((decodedCoordinate C.bob 0 u i).map fun f => f.value 0).effect a
  let : InnerProductSpace ℝ φ.toPositiveLinearMap.GNS := InnerProductSpace.complexToReal
  let V (a : F) (u : Pt) : φ.toPositiveLinearMap.GNS := φ.toPreGNS (A u a)
  let W (i : Fin (n + 1)) (a : F) (u : Pt) : φ.toPositiveLinearMap.GNS := φ.toPreGNS (R i u a)
  have hd (x y : Joint) :
      ‖(φ.toPreGNS x : φ.toPositiveLinearMap.GNS) - φ.toPreGNS y‖ = φ.norm (x - y) := by
    rw [← UniformSpace.Completion.coe_sub, UniformSpace.Completion.norm_coe, ← map_sub]
    rfl
  have hglobal (a : F) :=
    Fintype.expect_expect_norm_sub_sq_le_sum_expect_expect_norm_sub_update_sq (V a)
  simp only [V, hd] at hglobal
  have hlocal (i : Fin (n + 1)) (a : F) :
      (𝔼 u : Pt, 𝔼 t : F, φ.norm (A u a - A (update u i t) a) ^ 2) ≤
        2 * (𝔼 u : Pt, φ.norm (A u a - R i u a) ^ 2) := by
    have h := Fintype.expect_expect_norm_sub_update_sq_le_two i (V a) (W i a)
      (fun u t => by simp only [W, R, decodedCoordinate_update])
    have hs (u : Pt) (t : F) := φ.norm_sub_comm (A (update u i t) a) (A u a)
    simpa only [V, W, hd, hs] using h
  have haxis :
      (𝔼 u : Pt, 𝔼 i : Fin (n + 1), ∑ a, φ.norm (A u a - R i u a) ^ 2) ≤
        4 * (1 - (branchGame (F := F) n 0 .axis).commutingWinProb C) :=
    (expect_le_expect fun u _ => expect_le_expect fun i _ => by
      dsimp only [φ, A, R]
      have hval : (fun f : PolynomialFunction F 0 => f.value 0) = fun f => f.value (u i) :=
        funext fun f => f.value_eq_of_degree_zero _ _
      rw [hval]).trans (axisPointStateDist_le C 0)
  change (𝔼 u : Pt, 𝔼 v : Pt, ∑ a, φ.norm (A u a - A v a) ^ 2) ≤ _
  calc
    _ ≤ ∑ a, ∑ i : Fin (n + 1),
        (𝔼 u : Pt, 𝔼 t : F, φ.norm (A u a - A (update u i t) a) ^ 2) := by
      simp only [expect_sum_comm]
      exact sum_le_sum fun a _ => hglobal a
    _ ≤ ∑ a, ∑ i : Fin (n + 1), 2 * (𝔼 u : Pt, φ.norm (A u a - R i u a) ^ 2) :=
      sum_le_sum fun a _ => sum_le_sum fun i _ => hlocal i a
    _ = 2 * (n + 1 : ℝ) *
        (𝔼 u : Pt, 𝔼 i : Fin (n + 1), ∑ a, φ.norm (A u a - R i u a) ^ 2) := by
      simp only [← mul_sum, expect_sum_comm]
      rw [sum_comm]
      simp only [← expect_sum_comm, mul_assoc]
      congr 1
      rw [mul_expect]
      exact expect_congr rfl fun u _ => by
        simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
          (Fintype.card_mul_expect fun i : Fin (n + 1) =>
            ∑ a, φ.norm (A u a - R i u a) ^ 2).symm
    _ ≤ (2 * (n + 1 : ℝ)) *
        (4 * (1 - (branchGame (F := F) n 0 .axis).commutingWinProb C)) := by gcongr
    _ = _ := by ring

/-- With degree zero, a constant-polynomial POVM agrees with the points. Its loss
is bounded by eight times the dimension times the axis loss, plus twice the
consistency loss. No diagonal branch estimate is needed. -/
theorem exists_degree_zero_polynomial_POVM
    (S : QuantumStrategy Q Q Ans Ans ι ι)
    (hA : ∀ u, (S.alice (.point u)).toMeasurement.IsProjective)
    (hB : ∀ u, (S.bob (.point u)).toMeasurement.IsProjective) :
    let C := S.toCommuting
    let ε := 1 - (branchGame (F := F) n 0 .axis).commutingWinProb C
    let δ := 1 - (branchGame (F := F) n 0 .consistency).commutingWinProb C
    ∃ G : POVM (Option (BoundedPolynomial F (n + 1) 0)) ι,
      1 - (8 * (n + 1 : ℝ) * ε + 2 * δ) ≤
        𝔼 u : Pt, ∑ g : BoundedPolynomial F (n + 1) 0,
          (C.state ((QuantumStrategy.rightMeasurement (ι := ι) G).effect (some g) *
            (decodedPoint C.alice u).effect (MvPolynomial.eval u g.val))).re := by
  classical
  dsimp only
  let C := S.toCommuting
  let ε := 1 - (branchGame (F := F) n 0 .axis).commutingWinProb C
  let δ := 1 - (branchGame (F := F) n 0 .consistency).commutingWinProb C
  let P := decodedPoint C.alice
  let R := decodedPoint C.bob
  let dist (M N : Measurement F Joint) : ℝ := ∑ a, C.state.norm (M.effect a - N.effect a) ^ 2
  have hpoint : (𝔼 u : Pt, dist (P u) (R u)) ≤ 2 * δ := by
    have h (u : Pt) (a : F) := C.state.norm_sub_comm ((P u).effect a) ((R u).effect a)
    simpa only [dist, h] using decodedPoint_stateDist_le C 0
  have hcross :
      (𝔼 u : Pt, 𝔼 v : Pt, dist (P u) (R v)) ≤ 2 * (8 * (n + 1 : ℝ) * ε + 2 * δ) := by
    calc
      _ ≤ 𝔼 u : Pt, 𝔼 v : Pt, 2 * (dist (P u) (P v) + dist (P v) (R v)) :=
        expect_le_expect fun u _ => expect_le_expect fun v _ =>
          Measurement.sum_norm_sub_sq_triangle C.state (P u) (P v) (R v)
      _ ≤ _ := by
        simp only [← mul_expect, expect_add_distrib, Fintype.expect_const]
        linarith only [hpoint, degreeZero_pointVariance C]
  have hidentity (u v : Pt) :
      dist (P u) (R v) = 2 - 2 * Measurement.agreement C.state (P u) (R v) :=
    Measurement.sum_norm_sub_sq_eq_of_isProjective _ _ _
      (fun a => Measurement.commute_map_map _ _ (C.commute (.point u) (.point v)) _ _ a a)
      ((QuantumStrategy.leftMeasurement_isProjective (S.alice (.point u)) (hA _)).map _)
      ((QuantumStrategy.rightMeasurement_isProjective (S.bob (.point v)) (hB _)).map _)
  simp only [hidentity, expect_sub_distrib, ← mul_expect, Fintype.expect_const] at hcross
  obtain ⟨v, _, hv⟩ := exists_le_of_le_expect univ_nonempty
    (show 1 - (8 * (n + 1 : ℝ) * ε + 2 * δ) ≤
      𝔼 v : Pt, 𝔼 u : Pt, Measurement.agreement C.state (P u) (R v) by
      rw [expect_comm univ univ fun v u => Measurement.agreement C.state (P u) (R v)]
      linarith only [hcross])
  apply exists_polynomial_POVM_of_decoding S (.point v)
    (fun a => ⟨MvPolynomial.C (decodePoint a), fun i => (MvPolynomial.degreeOf_C _ i).le⟩)
  simpa only [R, P, decodedPoint, MvPolynomial.eval_C] using hv

end DegreeZero

end Cslib.PCP.LowIndividualDegree
