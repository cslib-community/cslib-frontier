/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.BinomialTail
public import CslibFrontier.Foundations.Quantum.Algebra.MeasurementMixture
public import CslibFrontier.Foundations.Quantum.Algebra.SequentialCopy
public import Mathlib.Algebra.BigOperators.Expect
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Counting successes of sequential measurements

The hybrid score uses sequential outcomes for the remaining measurements and the
binomial effect for the trials already transferred to the other side. Splitting off
one more trial changes the score by the copy and transcript commutator errors.

## Main results

* `Cslib.Quantum.Measurement.abs_sequentialSuccess_sub_binomialAtLeast_le` compares the
  sequential success-count probability with the binomial effect for uniform questions.
-/

public section

namespace Cslib.Quantum.Measurement

open Finset
open scoped BigOperators Real

variable {A α Q : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype α] [Fintype Q] [Nonempty Q]

/-- The success effect after uniformly mixing the question measurements and
coarsening their answers to success or failure. -/
@[expose] noncomputable def averageSuccessEffect (M : Q → Measurement α A)
    (success : α → Bool) : A :=
  ((mixture (Cslib.Probability.PMF.uniformOfFintype Q) M).map success).effect true

/-- The averaged success effect is the mean of the sums of the successful effects. -/
theorem averageSuccessEffect_eq (M : Q → Measurement α A) (success : α → Bool) :
    averageSuccessEffect M success =
      (Fintype.card Q : ℝ)⁻¹ • ∑ x, ∑ a with success a, (M x).effect a := by
  rw [averageSuccessEffect, map_mixture, mixture_uniform_effect]
  simp only [map_effect]

theorem averageSuccessEffect_mem_Icc (M : Q → Measurement α A) (success : α → Bool) :
    averageSuccessEffect M success ∈ Set.Icc (0 : A) 1 :=
  ⟨nonneg _ true, effect_le_one _ true⟩

private theorem commute_averageSuccessEffect (M : Q → Measurement α A) (success : α → Bool)
    (E : A) (h : ∀ x a, Commute E ((M x).effect a)) :
    Commute E (averageSuccessEffect M success) := by
  rw [averageSuccessEffect_eq]
  exact ((Commute.sum_left _ _ _ fun x _ =>
    Commute.sum_left _ _ _ fun a _ => (h x a).symm).symm).smul_right _

/-- Count the successful entries of an outcome word. -/
@[expose] def transcriptSuccessCount {k : ℕ} (success : α → Bool) (g : Fin k → α) : ℕ :=
  ∑ i, if success (g i) then 1 else 0

/-- The approximation with `l` binomial trials and `k` still measured in sequence. -/
private noncomputable def hybridSuccessScore (φ : AlgState A) (M : Q → Measurement α A)
    (hM : ∀ x, (M x).IsProjective) (success : α → Bool) (G : A) (l k threshold : ℕ) : ℝ :=
  𝔼 x : Fin k → Q, ∑ g, (φ ((sequentialProjective (fun j => M (x j)) (fun j => hM (x j))).effect g *
    binomialAtLeast l (threshold - transcriptSuccessCount success g) G)).re

omit [Nonempty Q] in
private theorem first_successScore_eq (φ : AlgState A) (M : Q → Measurement α A)
    (hM : ∀ x, (M x).IsProjective) (success : α → Bool) (G : A) (l k threshold : ℕ) :
    hybridSuccessScore φ M hM success G l (k + 1) threshold =
      𝔼 y : Q, 𝔼 x : Fin k → Q, ∑ a, ∑ g : Fin k → α,
        (φ ((M y).effect a *
          (sequentialProjective (fun j => M (x j)) (fun j => hM (x j))).effect g *
          (M y).effect a *
          binomialAtLeast l
            (threshold - (transcriptSuccessCount success g + if success a then 1 else 0))
            G)).re := by
  unfold hybridSuccessScore
  let score (z : Q × (Fin k → Q)) :=
    ∑ a, ∑ g : Fin k → α, (φ ((M z.1).effect a *
      (sequentialProjective (fun j => M (z.2 j)) (fun j => hM (z.2 j))).effect g *
      (M z.1).effect a * binomialAtLeast l
        (threshold - (transcriptSuccessCount success g + if success a then 1 else 0)) G)).re
  change _ = 𝔼 y : Q, 𝔼 x : Fin k → Q, score (y, x)
  rw [← Fintype.expect_prod_type score]
  refine Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => Q)).symm _ _ fun x => ?_
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => α)).sum_comp, Fintype.sum_prod_type]
  simp only [score, Fin.consEquiv_apply, Fin.consEquiv_symm_apply, Fin.cons_zero, Fin.tail_cons,
    sequentialProjective_effect_succ, transcriptSuccessCount, Fin.sum_univ_succ,
    Fin.cons_succ, Fin.tail, add_comm]

private theorem average_class_effect (R : Q → Measurement α A) (success : α → Bool)
    (b : Bool) :
    ((Fintype.card Q : ℝ)⁻¹ • ∑ y, ∑ a with success a = b, (R y).effect a) =
      if b then averageSuccessEffect R success else 1 - averageSuccessEffect R success := by
  let T := (mixture (Cslib.Probability.PMF.uniformOfFintype Q) R).map success
  have h (c : Bool) : T.effect c =
      (Fintype.card Q : ℝ)⁻¹ • ∑ y, ∑ a with success a = c, (R y).effect a := by
    simp only [T, map_mixture, mixture_uniform_effect, map_effect]
  rw [← h]
  cases b
  · simp only [Bool.false_eq_true, ite_false]
    apply eq_sub_of_add_eq
    change T.effect false + T.effect true = 1
    simpa only [Fintype.sum_bool, add_comm] using T.sum_effect
  · rfl

private theorem transferred_trial_eq (φ : AlgState A) (M R : Q → Measurement α A)
    (hM : ∀ x, (M x).IsProjective) (success : α → Bool) (l k threshold : ℕ) :
    (𝔼 y : Q, 𝔼 x : Fin k → Q, ∑ a, ∑ g : Fin k → α,
      (φ ((sequentialProjective (fun j => M (x j)) (fun j => hM (x j))).effect g *
        binomialAtLeast l
          (threshold - (transcriptSuccessCount success g + if success a then 1 else 0))
          (averageSuccessEffect R success) * (R y).effect a)).re) =
      hybridSuccessScore φ M hM success (averageSuccessEffect R success) (l + 1) k threshold := by
  let G := averageSuccessEffect R success
  let H (x : Fin k → Q) (g : Fin k → α) :=
    (sequentialProjective (fun j => M (x j)) (fun j => hM (x j))).effect g
  let W (g : Fin k → α) (b : Bool) :=
    binomialAtLeast l (threshold - (transcriptSuccessCount success g + if b then 1 else 0)) G
  change (𝔼 y : Q, 𝔼 x : Fin k → Q, ∑ a, ∑ g, (φ (H x g * W g (success a) * (R y).effect a)).re)
    = _
  rw [expect_comm univ univ]
  refine expect_congr rfl fun x _ => ?_
  simp_rw [sum_comm (s := (univ : Finset α)) (t := (univ : Finset (Fin k → α)))]
  rw [expect_sum_comm]
  refine sum_congr rfl fun g _ => ?_
  have hgroup (y : Q) : (∑ a, (φ (H x g * W g (success a) * (R y).effect a)).re) =
      ∑ b : Bool, (φ (H x g * W g b * ∑ a with success a = b, (R y).effect a)).re := by
    rw [← sum_fiberwise univ success]
    refine sum_congr rfl fun b _ => ?_
    simp only [mul_sum, map_sum, Complex.re_sum]
    exact sum_congr rfl fun a ha => by rw [(mem_filter.mp ha).2]
  simp only [hgroup, expect_sum_comm]
  have havg (b : Bool) :
      (𝔼 y : Q, (φ (H x g * W g b * ∑ a with success a = b, (R y).effect a)).re) =
        (φ (H x g * W g b * if b then G else 1 - G)).re := by
    rw [← AlgState.re_apply_uniformAverage, ← mul_sum, ← mul_smul_comm, average_class_effect]
  rw [Fintype.sum_bool]
  simp only [havg, Bool.false_eq_true, ite_false, ite_true]
  dsimp only [hybridSuccessScore, W, H, G, Bool.false_eq_true, ite_false, ite_true, add_zero]
  rw [binomialAtLeast_succ, Nat.sub_sub, mul_add, map_add, Complex.add_re]
  simp only [mul_assoc, Bool.false_eq_true, ite_false, ite_true, Nat.zero_add, add_comm]

/-- Moving one trial from the sequential part to the binomial part costs the
average copy discrepancy and the average transcript commutator error. -/
private theorem abs_hybridSuccessScore_step_le (φ : AlgState A) (M R : Q → Measurement α A)
    (hM : ∀ x, (M x).IsProjective) (hR : ∀ x, (R x).IsProjective)
    (hc : ∀ x y a b, Commute ((M x).effect a) ((R y).effect b))
    (success : α → Bool) (l k threshold : ℕ) :
    |hybridSuccessScore φ M hM success (averageSuccessEffect R success) l (k + 1) threshold -
      hybridSuccessScore φ M hM success (averageSuccessEffect R success) (l + 1) k threshold| ≤
      (1 + √2) * (√(𝔼 y : Q, copyDefect φ (M y) (R y)) +
        √(𝔼 y : Q, 𝔼 x : Fin k → Q,
          transcriptCommutatorDefect φ (M y) (fun j => M (x j)))) := by
  let G := averageSuccessEffect R success
  have hG := averageSuccessEffect_mem_Icc R success
  have hcomm (x : Q) (a : α) : Commute ((M x).effect a) G :=
    commute_averageSuccessEffect R success _ (fun y b => hc x y a b)
  rw [first_successScore_eq, ← transferred_trial_eq φ M R hM success l k threshold,
    ← expect_sub_distrib]
  refine (abs_expect_le _ _).trans ?_
  simp_rw [← expect_sub_distrib]
  refine (expect_le_expect fun y _ => abs_expect_le _ _).trans ?_
  let δ (y : Q) := copyDefect φ (M y) (R y)
  let ε (y : Q) (x : Fin k → Q) := transcriptCommutatorDefect φ (M y) (fun j => M (x j))
  have hδ := Fintype.expect_sqrt_le_sqrt_expect δ (fun y => by
    unfold δ copyDefect
    exact sum_nonneg fun a _ => sq_nonneg _)
  have hε : (𝔼 y : Q, 𝔼 x : Fin k → Q, √(ε y x)) ≤ √(𝔼 y : Q, 𝔼 x : Fin k → Q, ε y x) := by
    simpa only [Fintype.expect_prod_type] using
      Fintype.expect_sqrt_le_sqrt_expect (fun z : Q × (Fin k → Q) => ε z.1 z.2)
        (fun z => by
          unfold ε transcriptCommutatorDefect
          exact sum_nonneg fun a _ => sum_nonneg fun g _ => sq_nonneg _)
  refine (expect_le_expect fun y _ => expect_le_expect fun x _ => ?_).trans
    (show (𝔼 y : Q, 𝔼 x : Fin k → Q, (1 + √2) * (√(δ y) + √(ε y x))) ≤ _ from ?_)
  · have h := abs_first_transcript_score_sub_le φ (M y) (R y) (hM y) (hR y)
      (fun j : Fin k => M (x j)) (fun j => hM (x j)) (hc y y) (fun j => hc (x j) y)
      success (fun b g => binomialAtLeast l
        (threshold - (transcriptSuccessCount success g + if b then 1 else 0)) G)
      (fun b g => binomialAtLeast_mem_Icc _ _ hG.1 hG.2)
      (fun a b g => commute_binomialAtLeast _ _ (hcomm y a))
      (fun j a b g => commute_binomialAtLeast _ _ (hcomm (x j) a))
    simpa only [Fintype.card_bool, Nat.cast_ofNat, G, δ, ε] using h
  · simp only [← Finset.mul_expect, expect_add_distrib, Fintype.expect_const]
    exact mul_le_mul_of_nonneg_left (add_le_add hδ hε) (by positivity)

private theorem average_tailComm_le (φ : AlgState A) (M R : Q → Measurement α A)
    (hM : ∀ x, (M x).IsProjective) (hR : ∀ x, (R x).IsProjective)
    (hc : ∀ x y a b, Commute ((M x).effect a) ((R y).effect b)) (k : ℕ) {χ ζ : ℝ}
    (hpair : (𝔼 x : Q, 𝔼 y : Q, pairCommutatorDefect φ (M x) (M y)) ≤ χ)
    (hcopy : (𝔼 x : Q, copyDefect φ (M x) (R x)) ≤ ζ) :
    (𝔼 y : Q, 𝔼 x : Fin k → Q, transcriptCommutatorDefect φ (M y) (fun j => M (x j))) ≤
      (k : ℝ) ^ 2 * (2 * χ + 8 * ζ) := by
  let f (z : Q × (Fin k → Q)) :=
    transcriptCommutatorDefect φ (M z.1) (fun j => M (z.2 j))
  change (𝔼 y : Q, 𝔼 x : Fin k → Q, f (y, x)) ≤ _
  rw [← Fintype.expect_prod_type f]
  have he := Fintype.expect_equiv (Fin.snocEquiv (fun _ : Fin (k + 1) => Q)) f
    (fun v => prefixCommutatorDefect φ (M ∘ v) (Fin.last k)) (fun z => by
      simp only [f, prefixCommutatorDefect, Function.comp_apply, Fin.snocEquiv_apply,
        Fin.snoc_last]
      congr 1
      funext j
      change M (z.2 j) = M ((Fin.snocEquiv (fun _ : Fin (k + 1) => Q)) z j.castSucc)
      rw [Fin.snocEquiv_apply, Fin.snoc_castSucc])
  rw [he]
  exact average_prefixCommutatorDefect_le φ M R hM hR hc (Fin.last k) hpair hcopy

/-- Comparing all sequential trials with the binomial operator costs at most linearly
many copy errors and quadratically many pair commutator errors. The constants are
independent of the number of answer outcomes. -/
theorem abs_sequentialSuccess_sub_binomialAtLeast_le
    (φ : AlgState A) (M R : Q → Measurement α A)
    (hM : ∀ x, (M x).IsProjective) (hR : ∀ x, (R x).IsProjective)
    (hc : ∀ x y a b, Commute ((M x).effect a) ((R y).effect b)) (success : α → Bool)
    (k threshold : ℕ) {χ ζ : ℝ}
    (hpair : (𝔼 x : Q, 𝔼 y : Q, pairCommutatorDefect φ (M x) (M y)) ≤ χ)
    (hcopy : (𝔼 x : Q, copyDefect φ (M x) (R x)) ≤ ζ) :
    |(𝔼 x : Fin k → Q, ∑ g with threshold ≤ transcriptSuccessCount success g,
        (φ ((sequentialProjective (fun j => M (x j)) (fun j => hM (x j))).effect g)).re) -
      (φ (binomialAtLeast k threshold (averageSuccessEffect R success))).re| ≤
      (1 + √2) * (k * √ζ + (k : ℝ) ^ 2 * √(2 * χ + 8 * ζ)) := by
  let G := averageSuccessEffect R success
  let C : ℝ := 1 + √2
  let D : ℝ := √(2 * χ + 8 * ζ)
  let score (l n : ℕ) := hybridSuccessScore φ M hM success G l n threshold
  have hz (l : ℕ) : score l 0 = (φ (binomialAtLeast l threshold G)).re := by
    simp [score, hybridSuccessScore, transcriptSuccessCount, sequentialProjective_effect,
      transcriptProduct_zero]
  have hstart : score 0 k =
      𝔼 x : Fin k → Q, ∑ g with threshold ≤ transcriptSuccessCount success g,
        (φ ((sequentialProjective (fun j => M (x j)) (fun j => hM (x j))).effect g)).re := by
    unfold score hybridSuccessScore
    simp only [binomialAtLeast_zero, Nat.sub_eq_zero_iff_le, sum_filter]
    refine expect_congr rfl fun x _ => sum_congr rfl fun g _ => ?_
    split_ifs <;> simp
  have hstep (l n : ℕ) : |score l (n + 1) - score (l + 1) n| ≤ C * (√ζ + n * D) := by
    have hn := Real.sqrt_le_sqrt (average_tailComm_le φ M R hM hR hc n hpair hcopy)
    rw [Real.sqrt_mul (sq_nonneg (n : ℝ)), Real.sqrt_sq (Nat.cast_nonneg n)] at hn
    exact (abs_hybridSuccessScore_step_le φ M R hM hR hc success l n threshold).trans
      (mul_le_mul_of_nonneg_left (add_le_add (Real.sqrt_le_sqrt hcopy) hn) (by positivity))
  have hwhole (j : ℕ) : ∀ l, |score l j - score (l + j) 0| ≤
      C * (j * √ζ + (j : ℝ) ^ 2 * D) := by
    induction j with
    | zero => intro l; simp
    | succ j ih =>
      intro l
      have he : l + (j + 1) = (l + 1) + j := by omega
      rw [he]
      calc
        _ ≤ |score l (j + 1) - score (l + 1) j| +
            |score (l + 1) j - score ((l + 1) + j) 0| := abs_sub_le _ _ _
        _ ≤ C * (√ζ + j * D) + C * (j * √ζ + (j : ℝ) ^ 2 * D) :=
          add_le_add (hstep l j) (ih (l + 1))
        _ = C * (((j : ℝ) + 1) * √ζ + ((j : ℝ) ^ 2 + j) * D) := by ring
        _ ≤ _ := by
          have hD : 0 ≤ D := Real.sqrt_nonneg _
          have hC : 0 ≤ C := by dsimp [C]; positivity
          push_cast
          gcongr
          nlinarith
  rw [← hstart, ← hz k]
  simpa only [Nat.zero_add, C, D] using hwhole k 0

end Cslib.Quantum.Measurement
