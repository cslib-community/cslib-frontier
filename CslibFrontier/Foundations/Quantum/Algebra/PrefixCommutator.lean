/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.SequentialDisturbance
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Commutation through a sequential measurement prefix

For a family of projective measurements with commuting copies on the other side,
commuting a target projector through a product costs the pairwise commutator error
and the error of replacing each factor by its copy. The root of the total squared
defect grows at most linearly with the prefix length. This is the product argument
used in [Ji, Natarajan, Vidick, Wright and Yuen, Lemma 12.15][JNVWY2020LowIndividualDegree].

## Main definitions

* `Cslib.Quantum.Measurement.pairCommutatorDefect`: sum of squared commutator norms.
* `Cslib.Quantum.Measurement.copyDefect`: sum of squared discrepancies with a copy.

## Main results

* `Cslib.Quantum.Measurement.sqrt_transcriptCommutatorDefect_le`: a bound for a fixed sequence.
* `Cslib.Quantum.Measurement.average_prefixCommutatorDefect_le`: the bound for independently
  sampled measurement questions.
-/

public section

namespace Cslib.Quantum.Measurement

open Finset
open scoped Real BigOperators

variable {A α β : Type*} [Fintype α] [Fintype β] [Ring A] [StarRing A] [PartialOrder A]
  [StarOrderedRing A] [Algebra ℂ A] [StarModule ℂ A] [SelfAdjointDecompose A]

private theorem sum_norm_left_mul_sq {ι : Type*} [Fintype ι] (φ : AlgState A)
    (U : ι → A) (hU : ∑ j, star (U j) * U j = 1) (x : A) :
    ∑ j, φ.norm (U j * x) ^ 2 = φ.norm x ^ 2 := by
  simp only [AlgState.norm_sq, star_mul, ← Complex.re_sum, ← map_sum]
  have he (j : ι) : star x * star (U j) * (U j * x) =
      star x * (star (U j) * U j) * x := by simp only [mul_assoc]
  simp only [he, ← sum_mul, ← mul_sum, hU, mul_one]

/-- Summing over projective outcomes preserves the squared state norm of a right factor. -/
theorem sum_norm_effect_mul_sq (φ : AlgState A) (M : Measurement α A) (hM : M.IsProjective)
    (x : A) : ∑ a, φ.norm (M.effect a * x) ^ 2 = φ.norm x ^ 2 := by
  have hidem : ∀ a, M.effect a * M.effect a = M.effect a := hM
  exact sum_norm_left_mul_sq φ M.effect
    (by simp only [fun a => (M.nonneg a).isSelfAdjoint.star_eq, hidem, M.sum_effect]) x

/-- Summing over adjoints of the normalized transcript products preserves the squared state norm
of a right factor. -/
theorem sum_norm_star_transcriptProduct_mul_sq (φ : AlgState A) {k : ℕ}
    (M : Fin k → Measurement α A) (hM : ∀ j, (M j).IsProjective) (x : A) :
    ∑ p, φ.norm (star (transcriptProduct M p) * x) ^ 2 = φ.norm x ^ 2 :=
  sum_norm_left_mul_sq φ _ (by simpa only [star_star] using sum_transcriptProduct_mul_star M hM) x

private noncomputable def rootEnergy {ι : Type*} [Fintype ι] (φ : AlgState A) (U : ι → A) : ℝ :=
  √(∑ j, φ.norm (U j) ^ 2)

private theorem rootEnergy_add_le {ι : Type*} [Fintype ι] (φ : AlgState A) (U V : ι → A) :
    rootEnergy φ (fun j => U j + V j) ≤ rootEnergy φ U + rootEnergy φ V := by
  unfold rootEnergy
  have hu : (0 : ℝ) ≤ ∑ j, φ.norm (U j) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hv : (0 : ℝ) ≤ ∑ j, φ.norm (V j) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hcross := Real.sum_mul_le_sqrt_mul_sqrt univ (fun j => φ.norm (U j))
    (fun j => φ.norm (V j))
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ ∑ j, (φ.norm (U j) + φ.norm (V j)) ^ 2 := sum_le_sum fun j _ =>
      pow_le_pow_left₀ (φ.norm_nonneg _) (φ.norm_add_le _ _) _
    _ = (∑ j, φ.norm (U j) ^ 2) + (∑ j, φ.norm (V j) ^ 2) +
          2 * (∑ j, φ.norm (U j) * φ.norm (V j)) := by
      simp only [add_sq, sum_add_distrib, mul_assoc, ← mul_sum]
      ring
    _ ≤ (∑ j, φ.norm (U j) ^ 2) + (∑ j, φ.norm (V j) ^ 2) +
          2 * (√(∑ j, φ.norm (U j) ^ 2) * √(∑ j, φ.norm (V j) ^ 2)) := by gcongr
    _ = (√(∑ j, φ.norm (U j) ^ 2) + √(∑ j, φ.norm (V j) ^ 2)) ^ 2 := by
      rw [add_sq, Real.sq_sqrt hu, Real.sq_sqrt hv]; ring

private theorem rootEnergy_neg {ι : Type*} [Fintype ι] (φ : AlgState A) (U : ι → A) :
    rootEnergy φ (fun j => -U j) = rootEnergy φ U := by
  simp only [rootEnergy, φ.norm_neg]

/-- Sum of squared commutators of two measurements, over their outcome pairs. -/
@[expose] noncomputable def pairCommutatorDefect (φ : AlgState A) (E : Measurement β A)
    (M : Measurement α A) : ℝ :=
  ∑ a, ∑ b, φ.norm (E.effect a * M.effect b - M.effect b * E.effect a) ^ 2

/-- Squared state-dependent discrepancy between a measurement and its commuting copy. -/
@[expose] noncomputable def copyDefect (φ : AlgState A) (M R : Measurement α A) : ℝ :=
  ∑ b, φ.norm (M.effect b - R.effect b) ^ 2

theorem pairCommutatorDefect_eq_zero (φ : AlgState A) (E : Measurement β A)
    (M : Measurement α A) (h : ∀ a b, Commute (E.effect a) (M.effect b)) :
    pairCommutatorDefect φ E M = 0 := by
  simp [pairCommutatorDefect, fun a b => (h a b).eq, AlgState.norm_zero]

@[simp] theorem copyDefect_self (φ : AlgState A) (M : Measurement α A) :
    copyDefect φ M M = 0 := by
  simp [copyDefect, AlgState.norm_zero]

private theorem transcriptCommutatorDefect_succ_le {k : ℕ} (φ : AlgState A)
    (E : Measurement β A) (hE : E.IsProjective) (M : Fin (k + 1) → Measurement α A)
    (hM : ∀ i, (M i).IsProjective) (R : Measurement α A) (hR : R.IsProjective)
    (hER : ∀ a b, Commute (E.effect a) (R.effect b))
    (hMR : ∀ j a b, Commute ((M j).effect a) (R.effect b)) :
    √(transcriptCommutatorDefect φ E M) ≤
      √(transcriptCommutatorDefect φ E (fun j : Fin k => M j.succ)) +
        √(pairCommutatorDefect φ E (M 0)) + 2 * √(copyDefect φ (M 0) R) := by
  let T : Fin k → Measurement α A := fun j => M j.succ
  let K (p : Fin k → α) := star (transcriptProduct T p)
  let C (a : β) (p : Fin k → α) := E.effect a * K p - K p * E.effect a
  let D (b : α) := (M 0).effect b - R.effect b
  let U (z : β × α × (Fin k → α)) := R.effect z.2.1 * C z.1 z.2.2
  let V (z : β × α × (Fin k → α)) :=
    K z.2.2 * (E.effect z.1 * (M 0).effect z.2.1 - (M 0).effect z.2.1 * E.effect z.1)
  let W (z : β × α × (Fin k → α)) := E.effect z.1 * (K z.2.2 * D z.2.1)
  let Z (z : β × α × (Fin k → α)) := K z.2.2 * (E.effect z.1 * D z.2.1)
  have hT (j : Fin k) : (T j).IsProjective := hM j.succ
  have hsplit (b : α) (a : β) (p : Fin k → α) :
      E.effect a * star (transcriptProduct M (Fin.cons b p)) -
          star (transcriptProduct M (Fin.cons b p)) * E.effect a =
        U (a, b, p) + V (a, b, p) + W (a, b, p) + -Z (a, b, p) := by
    rw [transcriptProduct_succ, star_mul, Fin.cons_zero, Fin.tail_cons,
      ((M 0).nonneg b).isSelfAdjoint.star_eq]
    change E.effect a * (K p * (M 0).effect b) - K p * (M 0).effect b * E.effect a = _
    have hk : Commute (K p) (R.effect b) :=
      star_transcriptProduct_commute T (R.effect b) (fun j c => hMR j.succ c b) p
    have hcomm : R.effect b * C a p = C a p * R.effect b :=
      (((hER a b).mul_left hk).sub_left (hk.mul_left (hER a b))).eq.symm
    dsimp only [U, V, W, Z]
    rw [hcomm]
    dsimp only [C, D]
    noncomm_ring
  have hfull : √(transcriptCommutatorDefect φ E M) =
      rootEnergy φ (fun z => U z + V z + W z + -Z z) := by
    unfold transcriptCommutatorDefect rootEnergy
    congr 1
    simp only [Fintype.sum_prod_type]
    refine sum_congr rfl fun a _ => ?_
    rw [← (Fin.consEquiv fun _ : Fin (k + 1) => α).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, hsplit]
  have hU : rootEnergy φ U = √(transcriptCommutatorDefect φ E T) := by
    simp only [rootEnergy, transcriptCommutatorDefect, U, C, K, Fintype.sum_prod_type]
    exact congrArg Real.sqrt (sum_congr rfl fun a _ => by
      rw [sum_comm, sum_congr rfl fun _ _ => sum_norm_effect_mul_sq φ R hR _])
  have hV : rootEnergy φ V = √(pairCommutatorDefect φ E (M 0)) := by
    simp only [rootEnergy, pairCommutatorDefect, V, K, Fintype.sum_prod_type,
      sum_norm_star_transcriptProduct_mul_sq φ T hT]
  have hW : rootEnergy φ W = √(copyDefect φ (M 0) R) := by
    simp only [rootEnergy, copyDefect]
    rw [Fintype.sum_prod_type, sum_comm]
    simp only [W, K, D, sum_norm_effect_mul_sq φ E hE, Fintype.sum_prod_type,
      sum_norm_star_transcriptProduct_mul_sq φ T hT]
  have hZ : rootEnergy φ Z = √(copyDefect φ (M 0) R) := by
    simp only [rootEnergy, copyDefect, Z, K, D, Fintype.sum_prod_type,
      sum_norm_star_transcriptProduct_mul_sq φ T hT]
    rw [sum_comm]
    simp only [sum_norm_effect_mul_sq φ E hE]
  calc √(transcriptCommutatorDefect φ E M)
      = rootEnergy φ (fun z => U z + V z + W z + -Z z) := hfull
    _ ≤ rootEnergy φ (fun z => U z + V z + W z) + rootEnergy φ (fun z => -Z z) :=
      rootEnergy_add_le _ _ _
    _ ≤ (rootEnergy φ (fun z => U z + V z) + rootEnergy φ W) + rootEnergy φ Z := by
      rw [rootEnergy_neg]; gcongr; exact rootEnergy_add_le _ _ _
    _ ≤ (rootEnergy φ U + rootEnergy φ V + rootEnergy φ W) + rootEnergy φ Z := by
      gcongr; exact rootEnergy_add_le _ _ _
    _ = _ := by rw [hU, hV, hW, hZ]; ring

/-- The square root of the squared commutator defect with a transcript is bounded by
the sum of the pairwise root defects and twice the root discrepancies with the commuting
copies. All measurements on each side may fail to commute with others on that side. -/
theorem sqrt_transcriptCommutatorDefect_le {k : ℕ} (φ : AlgState A)
    (E : Measurement β A) (hE : E.IsProjective) (M R : Fin k → Measurement α A)
    (hM : ∀ i, (M i).IsProjective) (hR : ∀ i, (R i).IsProjective)
    (hER : ∀ j a b, Commute (E.effect a) ((R j).effect b))
    (hMR : ∀ i j a b, Commute ((M i).effect a) ((R j).effect b)) :
    √(transcriptCommutatorDefect φ E M) ≤
      ∑ j, (√(pairCommutatorDefect φ E (M j)) + 2 * √(copyDefect φ (M j) (R j))) := by
  induction k with
  | zero =>
    simp [transcriptCommutatorDefect, AlgState.norm_zero]
  | succ k ih =>
    rw [Fin.sum_univ_succ]
    linarith [transcriptCommutatorDefect_succ_le φ E hE M hM (R 0) (hR 0)
        (hER 0) (fun j => hMR j 0),
      ih (fun j => M j.succ) (fun j => R j.succ) (fun j => hM j.succ) (fun j => hR j.succ)
        (fun j => hER j.succ) (fun i j => hMR i.succ j.succ)]

/-- Sum-of-squares form of the transcript commutator bound. -/
theorem transcriptCommutatorDefect_le {k : ℕ} (φ : AlgState A)
    (E : Measurement β A) (hE : E.IsProjective) (M R : Fin k → Measurement α A)
    (hM : ∀ i, (M i).IsProjective) (hR : ∀ i, (R i).IsProjective)
    (hER : ∀ j a b, Commute (E.effect a) ((R j).effect b))
    (hMR : ∀ i j a b, Commute ((M i).effect a) ((R j).effect b)) :
    transcriptCommutatorDefect φ E M ≤
      k * ∑ j, (2 * pairCommutatorDefect φ E (M j) + 8 * copyDefect φ (M j) (R j)) := by
  let f (j : Fin k) := √(pairCommutatorDefect φ E (M j)) + 2 * √(copyDefect φ (M j) (R j))
  have h0 : 0 ≤ transcriptCommutatorDefect φ E M := by
    unfold transcriptCommutatorDefect
    exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
  have h := (Real.sq_sqrt h0).symm.trans_le (pow_le_pow_left₀ (Real.sqrt_nonneg _)
    (sqrt_transcriptCommutatorDefect_le φ E hE M R hM hR hER hMR) 2)
  have hcs : (∑ j, f j) ^ 2 ≤ (k : ℝ) * ∑ j, f j ^ 2 := by
    simpa only [one_mul, one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one] using (Finset.sum_mul_sq_le_sq_mul_sq univ (fun _ => (1 : ℝ)) f)
  refine (h.trans hcs).trans (mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => ?_) (by positivity))
  have hpair : 0 ≤ pairCommutatorDefect φ E (M j) :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
  have hcopy : 0 ≤ copyDefect φ (M j) (R j) := sum_nonneg fun _ _ => sq_nonneg _
  dsimp only [f]
  refine sub_nonneg.mp ((sq_nonneg
    (√(pairCommutatorDefect φ E (M j)) - 2 * √(copyDefect φ (M j) (R j)))).trans_eq ?_)
  linear_combination 2 * Real.sq_sqrt hpair + 8 * Real.sq_sqrt hcopy

/-- For uniform independent questions, the average defect at a coordinate is at most
the square of its prefix length times a combination of the pairwise and copy bounds. -/
theorem average_prefixCommutatorDefect_le {Q : Type*} [Fintype Q] [Nonempty Q] {k : ℕ}
    (φ : AlgState A) (M R : Q → Measurement α A)
    (hM : ∀ x, (M x).IsProjective) (hR : ∀ x, (R x).IsProjective)
    (hc : ∀ x y a b, Commute ((M x).effect a) ((R y).effect b)) (i : Fin k) {χ ζ : ℝ}
    (hpair : (𝔼 x : Q, 𝔼 y : Q, pairCommutatorDefect φ (M x) (M y)) ≤ χ)
    (hcopy : (𝔼 x : Q, copyDefect φ (M x) (R x)) ≤ ζ) :
    (𝔼 x : Fin k → Q, prefixCommutatorDefect φ (M ∘ x) i) ≤
      (i.val : ℝ) ^ 2 * (2 * χ + 8 * ζ) := by
  let pos (j : Fin i.val) : Fin k := j.castLT (j.isLt.trans i.isLt)
  let P (x : Fin k → Q) (j : Fin i.val) := pairCommutatorDefect φ (M (x i)) (M (x (pos j)))
  let C (x : Fin k → Q) (j : Fin i.val) := copyDefect φ (M (x (pos j))) (R (x (pos j)))
  have hp (j : Fin i.val) :
      (𝔼 x : Fin k → Q, P x j) = 𝔼 x : Q, 𝔼 y : Q, pairCommutatorDefect φ (M x) (M y) := by
    have hj : i ≠ pos j := fun he => (Nat.ne_of_gt j.isLt) (congrArg Fin.val he)
    exact Fintype.expect_apply_pair (fun x y => pairCommutatorDefect φ (M x) (M y)) hj
  have hcopy' (j : Fin i.val) :
      (𝔼 x : Fin k → Q, C x j) = 𝔼 x : Q, copyDefect φ (M x) (R x) := by
    simpa only [C, Function.update_self, Fintype.expect_const] using
      (Fintype.expect_expect_update
        (fun x : Fin k → Q => copyDefect φ (M (x (pos j))) (R (x (pos j)))) (pos j)).symm
  calc
    _ ≤ 𝔼 x : Fin k → Q, ((i.val : ℝ) * ∑ j, (2 * P x j + 8 * C x j)) := by
      refine expect_le_expect fun x _ => ?_
      unfold prefixCommutatorDefect
      exact transcriptCommutatorDefect_le φ (M (x i)) (hM _)
        (before (M ∘ x) i) (before (R ∘ x) i)
        (fun _ => hM _) (fun _ => hR _) (fun _ => hc _ _) (fun _ _ => hc _ _)
    _ = (i.val : ℝ) *
        ∑ j, (2 * (𝔼 x : Fin k → Q, P x j) + 8 * (𝔼 x : Fin k → Q, C x j)) := by
      simp only [← Finset.mul_expect, Finset.expect_sum_comm, Finset.expect_add_distrib]
    _ ≤ (i.val : ℝ) * ∑ _j : Fin i.val, (2 * χ + 8 * ζ) := by
      refine mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => ?_) (by positivity)
      rw [hp, hcopy']
      linarith
    _ = _ := by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, pow_two, mul_assoc]

/-- Summed sequential disturbance in terms of pairwise commutators and copy defects. -/
theorem sum_prefixDisturbance_le_of_pairwise {Q : Type*} [Fintype Q] [Nonempty Q] (k : ℕ)
    (φ : AlgState A) (M R : Q → Measurement α A)
    (hM : ∀ x, (M x).IsProjective) (hR : ∀ x, (R x).IsProjective)
    (hc : ∀ x y a b, Commute ((M x).effect a) ((R y).effect b)) {χ ζ : ℝ}
    (hpair : (𝔼 x : Q, 𝔼 y : Q, pairCommutatorDefect φ (M x) (M y)) ≤ χ)
    (hcopy : (𝔼 x : Q, copyDefect φ (M x) (R x)) ≤ ζ) :
    (∑ i : Fin k, 2 * √(𝔼 x : Fin k → Q, prefixCommutatorDefect φ (fun j => M (x j)) i)) ≤
      k * ((k - 1 : ℕ) : ℝ) * √(2 * χ + 8 * ζ) := by
  have h (i : Fin k) := average_prefixCommutatorDefect_le φ M R hM hR hc i hpair hcopy
  calc
    _ ≤ ∑ i : Fin k, 2 * ((i.val : ℝ) * √(2 * χ + 8 * ζ)) := by
      refine sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (by norm_num)
      simpa only [Function.comp_def, Real.sqrt_mul (sq_nonneg (i.val : ℝ)),
        Real.sqrt_sq (Nat.cast_nonneg i.val)] using Real.sqrt_le_sqrt (h i)
    _ = _ := by
      have hk : (∑ i : Fin k, (i.val : ℝ)) * 2 = k * ((k - 1 : ℕ) : ℝ) := by
        exact_mod_cast (Fin.sum_univ_eq_sum_range (fun j : ℕ => j) k).symm ▸ sum_range_id_mul_two k
      rw [← hk, sum_mul, sum_mul]
      exact sum_congr rfl fun _ _ => by ring

end Cslib.Quantum.Measurement
