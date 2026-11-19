/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.SchmidtReduction
public import CslibFrontier.Computability.PCP.TwoProverGame.AlmostSynchronous
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Canonical purification and the synchrony deficit

Cauchy–Schwarz bounds a strategy's diagonal answer agreement by the square root of the
agreement in the canonical purification of Alice's reduced state. This is the reduction
to symmetric strategies used in [Vidick, Corollary 3.2][Vidick2022]. Finite projective
spectral mixtures for either party recover that party's original reduced state exactly
and bound the error of its measurements in the original local basis.
-/

public section

open Matrix Finset Cslib.Quantum
open scoped MatrixOrder ComplexOrder

namespace Cslib.PCP.QuantumStrategy

variable {ι κ X A : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [Fintype A]

omit [DecidableEq ι] in
private theorem sum_spectrum_support (d : ι → ℝ) (f : ι → ℝ)
    (hf : ∀ i, d i = 0 → f i = 0) :
    (∑ i, f i) = ∑ i : {i : ι // d i ≠ 0}, f i.val := by
  classical
  rw [← sum_filter_add_sum_filter_not univ (fun i => d i ≠ 0)]
  have hzero : (∑ i ∈ univ.filter (fun i => ¬d i ≠ 0), f i) = 0 :=
    sum_eq_zero fun i hi => hf i (not_not.mp (mem_filter.mp hi).2)
  rw [hzero, add_zero]
  exact Finset.sum_subtype (univ.filter _) (by simp) f

omit [Fintype κ] [DecidableEq κ] in
private theorem schmidtAgreement_support (M : Measurement A (Matrix ι ι ℂ)) (d : ι → ℝ) :
    M.schmidtAgreement d =
      ∑ a, ∑ i : {i : ι // d i ≠ 0}, ∑ j : {j : ι // d j ≠ 0},
        (Real.sqrt (d i.val) * Real.sqrt (d j.val)) * ‖M.effect a i.val j.val‖ ^ 2 := by
  unfold Measurement.schmidtAgreement
  simp_rw [mul_sum]
  rw [sum_spectrum_support d _ (fun i hi => by simp [hi])]
  have hsum (i : {i : ι // d i ≠ 0}) :
      (∑ j, ∑ a, (Real.sqrt (d i.val) * Real.sqrt (d j)) * ‖M.effect a i.val j‖ ^ 2) =
        ∑ j : {j : ι // d j ≠ 0}, ∑ a,
          (Real.sqrt (d i.val) * Real.sqrt (d j.val)) * ‖M.effect a i.val j.val‖ ^ 2 :=
    sum_spectrum_support d _ (fun j hj => by simp [hj])
  simp_rw [hsum]
  have hswap (i : {i : ι // d i ≠ 0}) :
      (∑ j : {j : ι // d j ≠ 0}, ∑ a,
        (Real.sqrt (d i.val) * Real.sqrt (d j.val)) * ‖M.effect a i.val j.val‖ ^ 2) =
        ∑ a, ∑ j : {j : ι // d j ≠ 0},
          (Real.sqrt (d i.val) * Real.sqrt (d j.val)) * ‖M.effect a i.val j.val‖ ^ 2 := sum_comm
  simp_rw [hswap]
  exact sum_comm

/-- Agreement for a paired Schmidt vector is at most the square root of the agreement
of Alice's measurement with its transpose on the canonical purification. -/
theorem sum_prob_same_le_sqrt_schmidtAgreement (S : QuantumStrategy X X A A ι κ)
    (d : ι → ℝ) (e : {i : ι // d i ≠ 0} ↪ κ) (hd : ∀ i, 0 ≤ d i)
    (htrace : ∑ i, d i = 1)
    (hψ : ∀ i k, S.state.ofLp (i, k) =
      if hi : d i ≠ 0 then if k = e ⟨i, hi⟩ then (Real.sqrt (d i) : ℂ) else 0 else 0)
    (x : X) :
    (∑ a, S.prob x x a a) ≤ Real.sqrt ((S.alice x).toMeasurement.schmidtAgreement d) := by
  let P := {i : ι // d i ≠ 0}
  let M := (S.alice x).toMeasurement
  let N := (S.bob x).toMeasurement.principalSubmatrix e
  let w (i j : P) := Real.sqrt (d i.val) * Real.sqrt (d j.val)
  have hw (i j : P) : 0 ≤ w i j := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  let u (p : A × P × P) := Real.sqrt (w p.2.1 p.2.2) * ‖M.effect p.1 p.2.1.val p.2.2.val‖
  let v (p : A × P × P) := Real.sqrt (w p.2.1 p.2.2) * ‖N.effect p.1 p.2.1 p.2.2‖
  have hleft : (∑ p, u p ^ 2) = M.schmidtAgreement d := by
    rw [schmidtAgreement_support]
    simp only [u, mul_pow, Real.sq_sqrt (hw _ _), Fintype.sum_prod_type, w, P]
  have hright : (∑ p, v p ^ 2) = N.schmidtAgreement (fun i => d i.val) := by
    unfold Measurement.schmidtAgreement
    simp only [v, mul_pow, Real.sq_sqrt (hw _ _), Fintype.sum_prod_type, w, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun i _ => sum_comm
  have hright_le : N.schmidtAgreement (fun i => d i.val) ≤ 1 := by
    apply N.schmidtAgreement_le_one _ (fun i => hd i.val)
    rw [← sum_spectrum_support d d (fun _ h => h), htrace]
  calc
    _ ≤ ∑ p, u p * v p := by
      simp only [Fintype.sum_prod_type, prob_eq_sum_paired_schmidt S d e hψ]
      refine sum_le_sum fun a _ => sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
      have hr := Complex.re_le_norm ((S.alice x).effect a i.val j.val *
        (S.bob x).effect a (e i) (e j))
      rw [norm_mul] at hr
      have he : u (a, i, j) * v (a, i, j) =
          w i j * (‖(S.alice x).effect a i.val j.val‖ * ‖(S.bob x).effect a (e i) (e j)‖) := by
        simp only [u, v, M, N, POVM.toMeasurement_effect,
          Measurement.principalSubmatrix_effect_apply]
        calc
          _ = (Real.sqrt (w i j) * Real.sqrt (w i j)) *
              (‖(S.alice x).effect a i.val j.val‖ * ‖(S.bob x).effect a (e i) (e j)‖) := by ring
          _ = _ := by rw [Real.mul_self_sqrt (hw i j)]
      rw [he]
      exact mul_le_mul_of_nonneg_left hr (hw i j)
    _ ≤ Real.sqrt (∑ p, u p ^ 2) * Real.sqrt (∑ p, v p ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt univ u v
    _ ≤ _ := by
      rw [hleft, hright]
      calc
        _ ≤ Real.sqrt (M.schmidtAgreement d) * 1 :=
          mul_le_mul_of_nonneg_left ((Real.sqrt_le_sqrt hright_le).trans_eq Real.sqrt_one)
            (Real.sqrt_nonneg _)
        _ = _ := mul_one _

variable [Fintype X]

/-- The defect of Alice's canonical purification is at most twice the original defect,
averaged over a finite question distribution. -/
theorem schmidtAgreement_defect_le_two_mul (S : QuantumStrategy X X A A ι κ)
    (ν : PMF X) (d : ι → ℝ) (e : {i : ι // d i ≠ 0} ↪ κ) (hd : ∀ i, 0 ≤ d i)
    (htrace : ∑ i, d i = 1)
    (hψ : ∀ i k, S.state.ofLp (i, k) =
      if hi : d i ≠ 0 then if k = e ⟨i, hi⟩ then (Real.sqrt (d i) : ℂ) else 0 else 0) :
    (∑ x, (ν x).toReal * (1 - (S.alice x).toMeasurement.schmidtAgreement d)) ≤
      2 * ∑ x, (ν x).toReal * (1 - ∑ a, S.prob x x a a) := by
  let q (x : X) := ∑ a, S.prob x x a a
  let p (x : X) := (S.alice x).toMeasurement.schmidtAgreement d
  let qavg := ∑ x, (ν x).toReal * q x
  let pavg := ∑ x, (ν x).toReal * p x
  have hp (x : X) : 0 ≤ p x := by
    unfold p Measurement.schmidtAgreement
    exact sum_nonneg fun i _ => sum_nonneg fun j _ => mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (sum_nonneg fun a _ => sq_nonneg ‖(S.alice x).toMeasurement.effect a i j‖)
  have hpavg : 0 ≤ pavg := sum_nonneg fun x _ => mul_nonneg ENNReal.toReal_nonneg (hp x)
  have hqavg : 0 ≤ qavg := sum_nonneg fun x _ => mul_nonneg ENNReal.toReal_nonneg
    (sum_nonneg fun a _ => S.prob_nonneg x x a a)
  have havg : qavg ≤ Real.sqrt pavg := by
    calc
      _ ≤ ∑ x, (ν x).toReal * Real.sqrt (p x) :=
        sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
          (S.sum_prob_same_le_sqrt_schmidtAgreement d e hd htrace hψ x) ENNReal.toReal_nonneg
      _ ≤ _ := by
        simpa only [smul_eq_mul, pavg] using Real.strictConcaveOn_sqrt.concaveOn.le_map_sum
          (t := univ) (w := fun x => (ν x).toReal) (p := p)
          (fun _ _ => ENNReal.toReal_nonneg) (Cslib.Probability.PMF.sum_toReal ν) (fun x _ => hp x)
  have hsq := (sq_le_sq₀ hqavg (Real.sqrt_nonneg _)).mpr havg
  rw [Real.sq_sqrt hpavg] at hsq
  change (∑ x, (ν x).toReal * (1 - p x)) ≤ 2 * ∑ x, (ν x).toReal * (1 - q x)
  simp only [mul_sub, mul_one, sum_sub_distrib, Cslib.Probability.PMF.sum_toReal ν]
  change 1 - pavg ≤ 2 - 2 * qavg
  nlinarith [sq_nonneg (qavg - 1)]

/-- The weighted probability of different answers when both players receive the same question. -/
noncomputable def synchronyDefect (S : QuantumStrategy X X A A ι κ) (ν : PMF X) : ℝ :=
  ∑ x, (ν x).toReal * (1 - ∑ a, S.prob x x a a)

/-- Express the diagonal synchrony defect as an average of conditional defects. -/
theorem synchronyDefect_eq_sum (S : QuantumStrategy X X A A ι κ) (ν : PMF X) :
    S.synchronyDefect ν = ∑ x, (ν x).toReal * (1 - ∑ a, S.prob x x a a) := by
  unfold synchronyDefect
  rfl

@[simp] theorem synchronyDefect_swap (S : QuantumStrategy X X A A ι κ) (ν : PMF X) :
    S.swap.synchronyDefect ν = S.synchronyDefect ν := by
  unfold synchronyDefect
  simp only [prob_swap]

local notation "Cuts" => {s : Finset ι // Finset.Nonempty s}

/-- The projective spectral mixture for the Alice marginal of an arbitrary strategy.
The cut states and extended effects are moved back to Alice's original basis.
This is the Alice case of the nonsymmetric reduction in
[Vidick, Corollary 3.2][Vidick2022]. -/
theorem exists_alice_projective_spectral_mixture (S : QuantumStrategy X X A A ι κ) :
    ∃ (d : ι → ℝ) (U : Matrix ι ι ℂ), U ∈ unitaryGroup ι ℂ ∧
    ∀ ν : PMF X,
      ∃ (T : (s : Cuts) → QuantumStrategy X X A A {i : ι // i ∈ s.val} {i : ι // i ∈ s.val}),
      (∀ s x a, ((T s).alice x).effect a * ((T s).alice x).effect a = ((T s).alice x).effect a) ∧
      (∀ s x a, ((T s).bob x).effect a * ((T s).bob x).effect a = ((T s).bob x).effect a) ∧
      (∀ s x a b, a ≠ b → (T s).prob x x a b = 0) ∧
      (∀ s x y a b, (T s).prob x y a b =
        (s.val.card : ℝ)⁻¹ *
          (Matrix.trace (((T s).alice x).effect a * ((T s).alice y).effect b)).re) ∧
      (∀ s : Cuts, extendCutMatrix s.val (partialTraceRight (pureState (T s).state)) =
        spectralCutDensity s) ∧
      (∀ s : Cuts, 0 ≤ spectralCutWeight d s) ∧
      (∑ s : Cuts, spectralCutWeight d s) = 1 ∧
      partialTraceRight (pureState S.state) =
        ∑ s : Cuts, spectralCutWeight d s • (U * spectralCutDensity s * Uᴴ) ∧
      (∑ x, (ν x).toReal * ∑ s : Cuts, spectralCutWeight d s *
        ∑ a, let E := (S.alice x).effect a -
                      U * extendCutMatrix s.val (((T s).alice x).effect a) * Uᴴ
             (Matrix.trace (E * E * (U * spectralCutDensity s * Uᴴ))).re) ≤
        18 * S.synchronyDefect ν + 20 * Real.sqrt (S.synchronyDefect ν) := by
  obtain ⟨d, e, U, V, hU, hV, hd, htrace, hψ⟩ := S.exists_changeBasis_schmidt
  refine ⟨d, U, hU, ?_⟩
  intro ν
  let Q := S.changeBasis U V hU hV
  let C := ofSchmidt d hd htrace Q.alice
  have hδ : C.synchronyDefect ν ≤ 2 * S.synchronyDefect ν := by
    have h := Q.schmidtAgreement_defect_le_two_mul ν d e hd htrace hψ
    unfold synchronyDefect
    simp only [C, sum_prob_same_ofSchmidt]
    simpa only [Q, prob_changeBasis] using h
  obtain ⟨T, hTa, hTb, hsync, hprob, hcut, hw, hsum, hρ, herr⟩ :=
    exists_projective_spectral_mixture d hd htrace Q.alice ν
  have hUU : U * Uᴴ = 1 := by
    rw [← star_eq_conjTranspose]
    exact mem_unitaryGroup_iff.mp hU
  have hU'U : Uᴴ * U = 1 := by
    rw [← star_eq_conjTranspose]
    exact mem_unitaryGroup_iff'.mp hU
  have hrestore (P : Matrix ι ι ℂ) : U * (Uᴴ * P * U) * Uᴴ = P := by
    calc
      _ = (U * Uᴴ) * P * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hUU, Matrix.one_mul, Matrix.mul_one]
  refine ⟨T, hTa, hTb, hsync, hprob, hcut, hw, hsum, ?_, ?_⟩
  · have hρ' : partialTraceRight (pureState C.state) =
        Uᴴ * partialTraceRight (pureState S.state) * U := by
      rw [← partialTraceRight_pureState_changeBasis S U V hU hV]
      change partialTraceRight (pureState C.state) = partialTraceRight (pureState Q.state)
      rw [partialTraceRight_pureState_of_paired_schmidt Q.state d e hd hψ]
      simp only [C, ofSchmidt_state, partialTraceRight_pureState_schmidtVector d hd]
    change partialTraceRight (pureState C.state) = _ at hρ
    rw [hρ'] at hρ
    have h := congrArg (fun Z : Matrix ι ι ℂ => U * Z * Uᴴ) hρ
    rw [hrestore] at h
    simpa only [Matrix.mul_sum, Matrix.sum_mul, Matrix.smul_mul, Matrix.mul_smul] using h
  · have hmul (P Q : Matrix ι ι ℂ) :
        (U * P * Uᴴ) * (U * Q * Uᴴ) = U * (P * Q) * Uᴴ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᴴ U, hU'U, Matrix.one_mul]
    have herror (x : X) (s : Cuts) (a : A) :
        let B := extendCutMatrix s.val (((T s).alice x).effect a)
        let E := (S.alice x).effect a - U * B * Uᴴ
        let F := (Q.alice x).effect a - B
        (Matrix.trace (E * E * (U * spectralCutDensity s * Uᴴ))).re =
          (Matrix.trace (F * F * spectralCutDensity s)).re := by
      intro B E F
      have hE : E = U * F * Uᴴ := by
        dsimp only [E, F, Q]
        rw [changeBasis_alice_effect, Matrix.mul_sub, Matrix.sub_mul]
        rw [hrestore]
      rw [hE, hmul, hmul, Matrix.trace_mul_comm (U * _), ← Matrix.mul_assoc, hU'U, Matrix.one_mul]
    simp_rw [herror]
    refine herr.trans ?_
    have hb : Real.sqrt (2 * C.synchronyDefect ν) ≤
        Real.sqrt (2 * (2 * S.synchronyDefect ν)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hδ (by norm_num))
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [show 2 * (2 * S.synchronyDefect ν) = 4 * S.synchronyDefect ν by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), h4] at hb
    change 9 * C.synchronyDefect ν + 10 * Real.sqrt (2 * C.synchronyDefect ν) ≤ _
    linarith

local notation "BobCuts" => {s : Finset κ // Finset.Nonempty s}

/-- The Bob marginal version of the projective spectral mixture,
by exchanging the two players. -/
theorem exists_bob_projective_spectral_mixture (S : QuantumStrategy X X A A ι κ) :
    ∃ (d : κ → ℝ) (U : Matrix κ κ ℂ), U ∈ unitaryGroup κ ℂ ∧
    ∀ ν : PMF X,
      ∃ (T : (s : BobCuts) → QuantumStrategy X X A A {i : κ // i ∈ s.val} {i : κ // i ∈ s.val}),
      (∀ s x a, ((T s).alice x).effect a * ((T s).alice x).effect a = ((T s).alice x).effect a) ∧
      (∀ s x a, ((T s).bob x).effect a * ((T s).bob x).effect a = ((T s).bob x).effect a) ∧
      (∀ s x a b, a ≠ b → (T s).prob x x a b = 0) ∧
      (∀ s x y a b, (T s).prob x y a b =
        (s.val.card : ℝ)⁻¹ *
          (Matrix.trace (((T s).alice x).effect a * ((T s).alice y).effect b)).re) ∧
      (∀ s : BobCuts, extendCutMatrix s.val (partialTraceRight (pureState (T s).state)) =
        spectralCutDensity s) ∧
      (∀ s : BobCuts, 0 ≤ spectralCutWeight d s) ∧
      (∑ s : BobCuts, spectralCutWeight d s) = 1 ∧
      partialTraceLeft (pureState S.state) =
        ∑ s : BobCuts, spectralCutWeight d s • (U * spectralCutDensity s * Uᴴ) ∧
      (∑ x, (ν x).toReal * ∑ s : BobCuts, spectralCutWeight d s *
        ∑ a, let E := (S.bob x).effect a -
                      U * extendCutMatrix s.val (((T s).alice x).effect a) * Uᴴ
             (Matrix.trace (E * E * (U * spectralCutDensity s * Uᴴ))).re) ≤
        18 * S.synchronyDefect ν + 20 * Real.sqrt (S.synchronyDefect ν) := by
  simpa only [swap_alice, partialTraceRight_pureState_swap, synchronyDefect_swap] using
    S.swap.exists_alice_projective_spectral_mixture

end Cslib.PCP.QuantumStrategy
