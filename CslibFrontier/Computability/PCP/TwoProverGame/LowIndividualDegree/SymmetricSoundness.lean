/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.InductionError
import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.InductionBase
import CslibFrontier.Foundations.Quantum.Algebra.MaxEntangled

/-!
# Dimension induction for symmetric low-individual-degree soundness

The one-coordinate measurement initializes the induction. Restricting the game to
each last coordinate keeps the diagonal cutoff fixed. The slice loss bounds and
Jensen's inequality control the average error passed to self-improvement and
pasting. This follows the dimension induction in [JNVWY2020LowIndividualDegree, §6.2].
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Cslib.Quantum Finset Matrix
open scoped BigOperators Real MatrixOrder ComplexOrder Kronecker Matrix.Norms.L2Operator

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]

local notation "Joint" => Matrix (ι × ι) (ι × ι) ℂ

private theorem exists_matchingMass_of_complete {n d : ℕ}
    (S : QuantumStrategy (Question F (n + 1)) (Question F (n + 1))
      (Answer F (n + 1)) (Answer F (n + 1)) ι ι)
    (H : POVM (BoundedPolynomial F (n + 1) d) ι) {s : ℝ}
    (h : (𝔼 u : Point F (n + 1), (1 - Measurement.agreement S.toCommuting.state
      ((QuantumStrategy.rightMeasurement H).map fun g => MvPolynomial.eval u g.val)
      (decodedPoint S.toCommuting.alice u))) ≤ s) :
    ∃ G : POVM (Option (BoundedPolynomial F (n + 1) d)) ι,
      1 - s ≤ 𝔼 u : Point F (n + 1), ∑ g : BoundedPolynomial F (n + 1) d,
        (S.toCommuting.state ((QuantumStrategy.rightMeasurement (ι := ι) G).effect (some g) *
          (decodedPoint S.toCommuting.alice u).effect (MvPolynomial.eval u g.val))).re := by
  classical
  let G := (H.toMeasurement.map some).toPOVM
  let R := QuantumStrategy.rightMeasurement (ι := ι) H
  let P := decodedPoint S.toCommuting.alice
  have hG (g : BoundedPolynomial F (n + 1) d) :
      (QuantumStrategy.rightMeasurement (ι := ι) G).effect (some g) = R.effect g := by
    have he : G.effect (some g) = H.effect g := by
      simp [G, Measurement.toPOVM_effect, Measurement.map_effect, sum_filter]
    change (1 : Matrix ι ι ℂ) ⊗ₖ G.effect (some g) = _ ⊗ₖ H.effect g
    rw [he]
  have hread (u : Point F (n + 1)) := Measurement.agreement_map_left S.toCommuting.state R (P u)
    (fun g => MvPolynomial.eval u g.val)
  change (𝔼 u : Point F (n + 1), (1 - Measurement.agreement S.toCommuting.state
    (R.map fun g => MvPolynomial.eval u g.val) (P u))) ≤ s at h
  simp only [hread, expect_sub_distrib, Fintype.expect_const] at h
  refine ⟨G, ?_⟩
  simp only [hG]
  linarith only [h]

private theorem loss_mem_Icc {n : ℕ}
    (S : CommutingStrategy (Question F (n + 1)) (Question F (n + 1))
      (Answer F (n + 1)) (Answer F (n + 1)) Joint) (d D : ℕ) (b : Branch) :
    1 - (branchGameWithDiagonalCap (F := F) n d D b).commutingWinProb S ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨sub_nonneg.mpr (TwoProverGame.commutingWinProb_le_one _ _),
    sub_le_self _ (TwoProverGame.commutingWinProb_nonneg _ _)⟩

/-- For a symmetric projective tensor strategy, the measurement supplied by the
induction agrees with Alice's decoded point answers up to the explicit
dimension-dependent bound. The sampling parameter can be any `k` between
`400 * (n + 1) * d` and the field cardinality, with `k > 0`. -/
private theorem exists_polynomial_POVM_of_symmetric_in_range
    {n d k : ℕ} (D : ℕ) (hk : 0 < k) (hsize : 400 * (n + 1) * d ≤ k)
    (hfield : k ≤ Fintype.card F)
    (S : QuantumStrategy (Question F (n + 1)) (Question F (n + 1))
      (Answer F (n + 1)) (Answer F (n + 1)) ι ι)
    (hM : S.bob = S.alice) (hψ : ∀ a b, S.state.ofLp (a, b) = S.state.ofLp (b, a))
    (hP : ∀ q, (S.alice q).toMeasurement.IsProjective) :
    let C := S.toCommuting
    let ε := 1 - (branchGame (F := F) n d .axis).commutingWinProb C
    let δ := 1 - (branchGame (F := F) n d .consistency).commutingWinProb C
    let γ :=
      1 - (branchGameWithDiagonalCap (F := F) n d D .diagonal).commutingWinProb C
    let r := (d : ℝ) / Fintype.card F
    ∃ G : POVM (Option (BoundedPolynomial F (n + 1) d)) ι,
      1 - dimensionInductionError (n + 1) k ε δ γ r ≤
        𝔼 u : Point F (n + 1), ∑ g : BoundedPolynomial F (n + 1) d,
          (C.state ((QuantumStrategy.rightMeasurement (ι := ι) G).effect (some g) *
            (decodedPoint C.alice u).effect (MvPolynomial.eval u g.val))).re := by
  classical
  intro C ε δ γ r
  have hε : ε ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [axisWinProbAtDegrees_eq] using loss_mem_Icc C d D .axis
  have hδ : δ ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [consistencyWinProbAtDegrees_eq] using loss_mem_Icc C d D .consistency
  have hγ : γ ∈ Set.Icc (0 : ℝ) 1 := loss_mem_Icc C d D .diagonal
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have hdq : d ≤ Fintype.card F := by
    have h : d ≤ 400 * (n + 1) * d := Nat.le_mul_of_pos_left d (by positivity)
    exact (h.trans hsize).trans hfield
  have hr : r ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (Nat.cast_nonneg _) hq.le, (div_le_one hq).2 (by exact_mod_cast hdq)⟩
  by_cases hd₀ : d = 0
  · subst d
    obtain ⟨G, hG⟩ := exists_degree_zero_polynomial_POVM S (fun u => hP (.point u)) (fun u => by
      rw [hM]
      exact hP (.point u))
    have hbase := baseError_le_dimensionInductionError
      (m := (n + 1 : ℝ)) (by linarith [Nat.cast_nonneg (α := ℝ) n]) hk hε hδ hγ.1 hr.1
    exact ⟨G, (sub_le_sub_left hbase 1).trans hG⟩
  -- The positive-degree induction retains the sampling length and the diagonal cutoff.
  clear hε hδ hγ hr hdq
  induction n with
  | zero =>
    obtain ⟨G, hG⟩ := exists_one_coordinate_polynomial_POVM S hM hψ d
    refine ⟨G, ?_⟩
    apply le_trans ?_ hG
    have hε : ε ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [axisWinProbAtDegrees_eq] using loss_mem_Icc C d D .axis
    have hδ := loss_mem_Icc C d D .consistency
    have hγ := loss_mem_Icc C d D .diagonal
    rw [consistencyWinProbAtDegrees_eq] at hδ
    have hr : 0 ≤ r := div_nonneg (Nat.cast_nonneg _) hq.le
    have hbase := baseError_le_dimensionInductionError (m := 1) (by norm_num) hk hε hδ hγ.1 hr
    rw [show (branchGame (F := F) 0 d .axis).commutingWinProb S.toCommuting = 1 - ε by
      dsimp only [ε, C]
      exact (sub_sub_cancel 1 _).symm]
    simp only [Nat.cast_zero, zero_add]
    apply sub_le_sub_left
    linarith only [hbase, hε.1, hδ.1]
  | succ n ih =>
    let m := (n + 1 : ℝ)
    let M := (n + 2 : ℝ)
    have hm : 1 ≤ m := by dsimp [m]; linarith [Nat.cast_nonneg (α := ℝ) n]
    have hmM : m ≤ M := by dsimp [m, M]; linarith
    have hM₀ : 0 < M := by dsimp [M]; positivity
    let θ : ℝ := 1 / (200 * M)
    have hθ₀ : 0 < θ := by positivity
    have hθ₁ : θ < 1 := by dsimp only [θ]; rw [div_lt_iff₀ (by positivity)]; linarith
    have hs : 2 * (d : ℝ) ≤ θ * k := by
      dsimp only [θ]
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have h : (400 : ℝ) * M * d ≤ k := by
        dsimp [M]
        exact_mod_cast hsize
      linarith only [h]
    have hdq : d ≤ Fintype.card F := by
      have h : d ≤ 400 * (n + 2) * d := Nat.le_mul_of_pos_left d (by positivity)
      exact (h.trans hsize).trans hfield
    have hrq : 1 / (Fintype.card F : ℝ) ≤ r :=
      div_le_div_of_nonneg_right (by exact_mod_cast Nat.pos_of_ne_zero hd₀) hq.le
    have hr : r ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (Nat.cast_nonneg _) hq.le, (div_le_one hq).2 (by exact_mod_cast hdq)⟩
    let T (x : F) := restrictSliceTensor S x
    let e (x : F) := 1 - (branchGame (F := F) n d .axis).commutingWinProb (T x).toCommuting
    let f (x : F) := 1 - (branchGame (F := F) n d .consistency).commutingWinProb (T x).toCommuting
    let g (x : F) := 1 - (branchGameWithDiagonalCap (F := F) n d D .diagonal).commutingWinProb
      (T x).toCommuting
    let σ (x : F) := dimensionInductionError m k (e x) (f x) (g x) r
    have hs' : 400 * (n + 1) * d ≤ k :=
      (Nat.mul_le_mul_right d (Nat.mul_le_mul_left 400 (by omega))).trans hsize
    have hex (x : F) := ih hs' (T x) (restrictSliceTensor_bob_eq_alice S x hM)
      (by simpa only [T, restrictSliceTensor_state] using hψ)
      (restrictSliceTensor_alice_isProjective S x hP)
    choose G hG using hex
    have ht (x : F) : (T x).toCommuting = restrictStrategy x C :=
      restrictSliceTensor_toCommuting S x
    have hstate (x : F) : (T x).toCommuting.state = C.state := restrictSliceTensor_joint_state S x
    have hpt (x : F) (u : Point F (n + 1)) :
        decodedPoint (T x).toCommuting.alice u = decodedPoint C.alice (Fin.snoc u x) := by
      rw [ht, decodedPoint_restrictSlice]
    have hinput (x : F) : 1 - σ x ≤ 𝔼 u : Point F (n + 1), ∑ p : BoundedPolynomial F (n + 1) d,
        (C.state ((QuantumStrategy.rightMeasurement (ι := ι) (G x)).effect (some p) *
          (decodedPoint C.alice (Fin.snoc u x)).effect (MvPolynomial.eval u p.val))).re := by
      simpa only [hstate, hpt] using hG x
    let _ : Nonempty (Fin k ↪ F) :=
      Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_fin] using hfield)
    obtain ⟨H, hH⟩ := exists_paste_of_slice_agreement S D k hk hM hψ hP G σ θ hθ₀ hθ₁ hs hinput
    have haxis : m * (𝔼 x, e x) ≤ M * ε := by
      simpa only [m, M, e, ht, axisWinProbAtDegrees_eq] using average_slice_axis_loss_le C d D
    have hcons : (𝔼 x, f x) ≤ δ := by
      simpa only [f, ht, consistencyWinProbAtDegrees_eq] using
        average_slice_consistency_loss_le C d D
    have hdiag : m * (𝔼 x, g x) ≤ M * γ := by
      simpa only [m, M, g, ht] using average_slice_diagonal_loss_le C d D
    have he (x : F) : 0 ≤ e x :=
      sub_nonneg.mpr (TwoProverGame.commutingWinProb_le_one _ _)
    have hf (x : F) : 0 ≤ f x :=
      sub_nonneg.mpr (TwoProverGame.commutingWinProb_le_one _ _)
    have hg (x : F) : 0 ≤ g x :=
      sub_nonneg.mpr (TwoProverGame.commutingWinProb_le_one _ _)
    have hε : ε ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [axisWinProbAtDegrees_eq] using loss_mem_Icc C d D .axis
    have hδ : δ ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [consistencyWinProbAtDegrees_eq] using loss_mem_Icc C d D .consistency
    have hγ : γ ∈ Set.Icc (0 : ℝ) 1 := loss_mem_Icc C d D .diagonal
    have hav := mul_expect_inductionLossTerm_le (show 0 < m by linarith) hmM hε.1 hδ.1 hγ.1 hr.1
      he hf hg haxis hcons hdiag
    have hσ : (𝔼 x, σ x) ≤ m ^ 2 * (100000 * (k : ℝ) ^ 2 * M * inductionLossTerm ε δ γ r +
      Real.exp (-(k : ℝ) / (80000 * m ^ 2))) := by
      simp only [σ, dimensionInductionError, ← mul_expect, expect_add_distrib, Fintype.expect_const]
      rw [mul_assoc (100000 * (k : ℝ) ^ 2) m, mul_assoc (100000 * (k : ℝ) ^ 2) M]
      gcongr
    have err : slicePastingError M k (Fintype.card F) ε δ γ r (𝔼 x, σ x) θ ≤
        dimensionInductionError M k ε δ γ r := by
      have hsucc : m + 1 = M := by dsimp [m, M]; ring
      change slicePastingError M k (Fintype.card F) ε δ γ r (𝔼 x, σ x) (1 / (200 * M)) ≤ _
      rw [← hsucc] at hσ ⊢
      exact slicePastingError_le_dimensionInductionError (m := m) hm hk hq hrq hε hδ hγ hr hσ
    rw [show ((n + 1 : ℕ) : ℝ) + 1 = M by
      push_cast
      dsimp only [M]
      ring]
    exact exists_matchingMass_of_complete S H (hH.trans err)

private theorem exists_complete_of_matchingMass {n d : ℕ}
    (S : QuantumStrategy (Question F (n + 1)) (Question F (n + 1))
      (Answer F (n + 1)) (Answer F (n + 1)) ι ι)
    (G : POVM (Option (BoundedPolynomial F (n + 1) d)) ι) {s : ℝ}
    (h : 1 - s ≤ 𝔼 u : Point F (n + 1), ∑ g : BoundedPolynomial F (n + 1) d,
      (S.toCommuting.state ((QuantumStrategy.rightMeasurement (ι := ι) G).effect (some g) *
        (decodedPoint S.toCommuting.alice u).effect (MvPolynomial.eval u g.val))).re) :
    ∃ H : POVM (BoundedPolynomial F (n + 1) d) ι,
      (𝔼 u : Point F (n + 1), (1 - Measurement.agreement S.toCommuting.state
        ((QuantumStrategy.rightMeasurement H).map fun g => MvPolynomial.eval u g.val)
        (decodedPoint S.toCommuting.alice u))) ≤ s := by
  classical
  let fallback : BoundedPolynomial F (n + 1) d := ⟨0, by simp⟩
  let f (a : Option (BoundedPolynomial F (n + 1) d)) := a.getD fallback
  let H := (G.toMeasurement.map f).toPOVM
  let R := QuantumStrategy.rightMeasurement (ι := ι) G
  let C := S.toCommuting
  have hH : QuantumStrategy.rightMeasurement (ι := ι) H = R.map f := by
    apply Measurement.ext
    intro g
    change oneKronecker (ι := ι) (H.effect g) = _
    simp only [H, Measurement.toPOVM_effect, Measurement.map_effect, POVM.toMeasurement_effect,
      map_sum, R]
    rfl
  have hm (u : Point F (n + 1)) :
      (∑ g : BoundedPolynomial F (n + 1) d,
        (C.state (R.effect (some g) *
          (decodedPoint C.alice u).effect (MvPolynomial.eval u g.val))).re) ≤
        Measurement.agreement C.state
          ((QuantumStrategy.rightMeasurement H).map fun g => MvPolynomial.eval u g.val)
          (decodedPoint C.alice u) := by
    rw [hH, Measurement.map_map, Measurement.agreement_map_left, Fintype.sum_option]
    apply le_add_of_nonneg_left
    apply C.state.re_apply_nonneg
    have hc (a : Answer F (n + 1)) :
        Commute (R.effect none) ((C.alice (.point u)).effect a) :=
      (commute_kroneckerOne_oneKronecker ((S.alice (.point u)).effect a) (G.effect none)).symm
    exact Commute.mul_nonneg (R.nonneg none) ((decodedPoint C.alice u).nonneg _)
      (Measurement.commute_map_right (C.alice (.point u)) decodePoint _ hc _)
  have hg := h.trans (expect_le_expect fun u _ => hm u)
  refine ⟨H, ?_⟩
  simp only [expect_sub_distrib, Fintype.expect_const]
  linarith only [hg]

/-- A quantitative variant of [JNVWY2020LowIndividualDegree, Theorem 6.1]
for symmetric projective tensor strategies. It follows the same dimension induction
with a different explicit error bound.

Every sampling parameter `k ≥ (n + 1) * d` yields a complete local polynomial
measurement. Its mean disagreement with Alice's decoded point answers is
bounded by the sum of a polynomial in the dimension and sample count times
the `1/128` powers of the branch losses and degree ratio, and an exponential
sampling error. The estimate works with an independent diagonal cutoff `D`. The verifier
in Figure 2 uses `D = (n + 1) * d`. -/
theorem exists_polynomial_POVM_of_symmetric
    {n d k : ℕ} (D : ℕ) (hk : (n + 1) * d ≤ k)
    (S : QuantumStrategy (Question F (n + 1)) (Question F (n + 1))
      (Answer F (n + 1)) (Answer F (n + 1)) ι ι)
    (hM : S.bob = S.alice) (hψ : ∀ a b, S.state.ofLp (a, b) = S.state.ofLp (b, a))
    (hP : ∀ q, (S.alice q).toMeasurement.IsProjective) :
    let C := S.toCommuting
    let ε := 1 - (branchGame (F := F) n d .axis).commutingWinProb C
    let δ := 1 - (branchGame (F := F) n d .consistency).commutingWinProb C
    let γ :=
      1 - (branchGameWithDiagonalCap (F := F) n d D .diagonal).commutingWinProb C
    let r := (d : ℝ) / Fintype.card F
    ∃ H : POVM (BoundedPolynomial F (n + 1) d) ι,
      (𝔼 u : Point F (n + 1), (1 - Measurement.agreement C.state
        ((QuantumStrategy.rightMeasurement H).map fun g => MvPolynomial.eval u g.val)
        (decodedPoint C.alice u))) ≤
        160000 * dimensionInductionError (n + 1) k ε δ γ r := by
  classical
  intro C ε δ γ r
  let m := (n + 1 : ℝ)
  let q := (Fintype.card F : ℝ)
  let B := dimensionInductionError m k ε δ γ r
  have hε : ε ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [axisWinProbAtDegrees_eq] using loss_mem_Icc C d D .axis
  have hδ : δ ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [consistencyWinProbAtDegrees_eq] using loss_mem_Icc C d D .consistency
  have hγ : γ ∈ Set.Icc (0 : ℝ) 1 := loss_mem_Icc C d D .diagonal
  have hm : 1 ≤ m := by dsimp [m]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := F)
  have hr : 0 ≤ r := div_nonneg (Nat.cast_nonneg _) hq.le
  have htrivial (h : 1 ≤ B) :
      ∃ H : POVM (BoundedPolynomial F (n + 1) d) ι,
        (𝔼 u : Point F (n + 1), (1 - Measurement.agreement C.state
          ((QuantumStrategy.rightMeasurement H).map fun g => MvPolynomial.eval u g.val)
          (decodedPoint C.alice u))) ≤ 160000 * B := by
    let G : POVM (Option (BoundedPolynomial F (n + 1) d)) ι := POVM.const none
    apply exists_complete_of_matchingMass S G
    have hzero (g : BoundedPolynomial F (n + 1) d) :
        (QuantumStrategy.rightMeasurement (ι := ι) G).effect (some g) = 0 := by
      change (1 : Matrix ι ι ℂ) ⊗ₖ G.effect (some g) = 0
      simp [G, POVM.const]
    simp only [hzero, zero_mul, map_zero, Complex.zero_re, sum_const_zero, Fintype.expect_const]
    linarith
  by_cases hk₀ : k = 0
  · apply htrivial
    dsimp only [B, dimensionInductionError]
    simp only [hk₀, Nat.cast_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_mul,
      zero_add, neg_zero, zero_div, Real.exp_zero, mul_one]
    exact one_le_pow₀ hm
  have hpos := Nat.pos_of_ne_zero hk₀
  by_cases hd : d = 0
  · subst d
    obtain ⟨G, hG⟩ := exists_degree_zero_polynomial_POVM S
      (fun u => hP (.point u)) (fun u => by rw [hM]; exact hP (.point u))
    apply exists_complete_of_matchingMass S G
    refine (sub_le_sub_left ?_ 1).trans hG
    have hB : 8 * m * ε + 2 * δ ≤ B :=
      baseError_le_dimensionInductionError hm hpos hε hδ hγ.1 hr
    have hnonneg : 0 ≤ 8 * m * ε + 2 * δ :=
      add_nonneg (mul_nonneg (by linarith) hε.1) (mul_nonneg (by norm_num) hδ.1)
    linarith only [hB, hnonneg]
  let K := max k (400 * (n + 1) * d)
  have hkK : k ≤ K := le_max_left _ _
  have hK : K ≤ 400 * k := by
    apply max_le
    · omega
    · simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 400 hk
  by_cases hfield : K ≤ Fintype.card F
  · obtain ⟨G, hG⟩ := exists_polynomial_POVM_of_symmetric_in_range D
      (hpos.trans_le hkK) (le_max_right _ _) hfield S hM hψ hP
    apply exists_complete_of_matchingMass S G
    exact (sub_le_sub_left
      (dimensionInductionError_pad (show 0 ≤ m by linarith) hε.1 hδ.1 hγ.1 hr hkK hK) 1).trans hG
  · apply htrivial
    have hqK : Fintype.card F ≤ 400 * k := (Nat.lt_of_not_ge hfield).le.trans hK
    have hqK' : q ≤ 400 * (k : ℝ) := by dsimp [q]; exact_mod_cast hqK
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast Nat.pos_of_ne_zero hd
    have hratio : 1 / (400 * (k : ℝ)) ≤ r :=
      (div_le_div_of_nonneg_left zero_le_one hq hqK').trans
        (div_le_div_of_nonneg_right hd' hq.le)
    exact one_le_dimensionInductionError_of_large_ratio hm hpos hε.1 hδ.1 hγ.1 hratio

end Cslib.PCP.LowIndividualDegree
