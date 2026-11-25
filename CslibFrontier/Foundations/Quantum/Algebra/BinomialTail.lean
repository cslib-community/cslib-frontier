/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.AlgState
public import Mathlib.Analysis.SpecialFunctions.Exp
import CslibFrontier.Foundations.Combinatorics.BinomialTail
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-!
# Binomial success tails for effects

The binomial tail polynomial evaluated at a positive contraction gives an
operator version of the probability of more than `d` successes in `k` trials.
A scalar lower-tail bound on the unit interval gives an operator inequality
by continuous functional calculus.

## Main results

* `Cslib.Quantum.one_sub_binomialTail_le` bounds the failure effect by an affine
  function of the original effect.
* `Cslib.Quantum.AlgState.one_sub_le_re_binomialTail` gives the corresponding
  state bound from Lemma 12.22 of [Ji, Natarajan, Vidick, Wright and Yuen]
  [JNVWY2020LowIndividualDegree].
-/

public section

namespace Cslib.Quantum

open Finset

/-- The upper binomial tail polynomial at `X`, keeping the terms for more than `d` successes. -/
@[expose] def binomialTail {A : Type*} [Ring A] (k d : ℕ) (X : A) : A :=
  ∑ i ∈ range (k + 1) with d < i, (k.choose i : A) * X ^ i * (1 - X) ^ (k - i)

/-- Each subset of the trials contributes the product of the corresponding success and
failure powers. Grouping by its cardinality gives the binomial coefficients. -/
theorem binomialTail_eq_sum_powerset {A ι : Type*} [Ring A]
    (s : Finset ι) (d : ℕ) (X : A) :
    binomialTail s.card d X =
      ∑ t ∈ s.powerset with d < t.card, X ^ t.card * (1 - X) ^ (s.card - t.card) := by
  classical
  rw [binomialTail, sum_filter, sum_filter, sum_powerset_apply_card (fun i =>
    if d < i then X ^ i * (1 - X) ^ (s.card - i) else 0)]
  refine sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [nsmul_eq_mul, mul_assoc]

/-- The binomial effect for at least `r` successes. A zero threshold accepts every outcome. -/
@[expose] def binomialAtLeast {A : Type*} [Ring A] (k r : ℕ) (X : A) : A :=
  if r = 0 then 1 else binomialTail k (r - 1) X

@[simp] theorem binomialAtLeast_zero {A : Type*} [Ring A] (r : ℕ) (X : A) :
    binomialAtLeast 0 r X = if r = 0 then 1 else 0 := by
  cases r <;> simp [binomialAtLeast, binomialTail, filter_singleton]

private theorem binomialAtLeast_eq_sum_powerset {A ι : Type*} [Ring A]
    (s : Finset ι) (r : ℕ) (X : A) :
    binomialAtLeast s.card r X =
      ∑ t ∈ s.powerset, if r ≤ t.card then X ^ t.card * (1 - X) ^ (s.card - t.card) else 0 := by
  classical
  cases r with
  | zero =>
    simp only [binomialAtLeast, Nat.zero_le, ite_true]
    rw [sum_powerset_apply_card (fun i => X ^ i * (1 - X) ^ (s.card - i))]
    have hp := ((Commute.one_right X).sub_right (Commute.refl X)).add_pow s.card
    rw [add_sub_cancel, one_pow] at hp
    exact hp.trans (sum_congr rfl fun i _ => by rw [nsmul_eq_mul, Nat.cast_commute])
  | succ r =>
    simp [binomialAtLeast, binomialTail_eq_sum_powerset, sum_filter]

/-- Splitting off one trial updates the success threshold on the success branch. -/
theorem binomialAtLeast_succ {A : Type*} [Ring A] (k r : ℕ) (X : A) :
    binomialAtLeast (k + 1) r X =
      binomialAtLeast k r X * (1 - X) + binomialAtLeast k (r - 1) X * X := by
  have hz : k ∉ range k := notMem_range_self
  have hc := binomialAtLeast_eq_sum_powerset (insert k (range k)) r X
  rw [card_insert_of_notMem hz, card_range, sum_powerset_insert hz] at hc
  have h (l : ℕ) := binomialAtLeast_eq_sum_powerset (range k) l X
  simp only [card_range] at h
  rw [hc, h r, h (r - 1), sum_mul, sum_mul]
  congr 1
  · refine sum_congr rfl fun t ht => ?_
    have htk : t.card ≤ k := by simpa only [card_range] using card_le_card (mem_powerset.mp ht)
    rw [show k + 1 - t.card = k - t.card + 1 by omega, pow_succ]
    split_ifs <;> simp [mul_assoc]
  · refine sum_congr rfl fun t ht => ?_
    simp only [card_insert_of_notMem fun hm => hz (mem_powerset.mp ht hm),
      show k + 1 - (t.card + 1) = k - t.card by omega,
      show r ≤ t.card + 1 ↔ r - 1 ≤ t.card by omega]
    have hcomm := (((Commute.one_right X).sub_right (Commute.refl X)).symm).pow_left (k - t.card)
    split_ifs <;> simp [pow_succ, mul_assoc, ← hcomm.eq]

/-- An operator commuting with the trial effect commutes with its binomial effects. -/
theorem commute_binomialAtLeast {A : Type*} [Ring A] (k r : ℕ) {X Y : A}
    (h : Commute Y X) : Commute Y (binomialAtLeast k r X) := by
  unfold binomialAtLeast binomialTail
  split_ifs
  · exact Commute.one_right Y
  · exact (Commute.sum_left _ _ _ fun i _ =>
      (((Nat.cast_commute (k.choose i) Y).mul_left (h.symm.pow_left i)).mul_left
        (((Commute.one_right Y).sub_right h).symm.pow_left _))).symm

private theorem one_sub_binomialTail_real_le {k d : ℕ} (hk : 0 < k) {θ p : ℝ}
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hsize : 2 * (d : ℝ) ≤ θ * k)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    1 - binomialTail k d p ≤ (1 - p) / (1 - θ) + Real.exp (-(θ ^ 2 * k) / 2) := by
  have hθ : 0 < 1 - θ := sub_pos.mpr hθ₁
  by_cases hp : p ≤ θ
  · have h : 1 ≤ (1 - p) / (1 - θ) := (le_div_iff₀ hθ).2 (by linarith)
    have htail : 0 ≤ binomialTail k d p := sum_nonneg fun i _ => by positivity
    linarith [Real.exp_pos (-(θ ^ 2 * k) / 2)]
  · have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    have hgap : θ * k / 2 ≤ (k : ℝ) * p - d := by
      have := mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge hp)) hk'.le; linarith
    have hcomp : 1 - binomialTail k d p =
        ∑ i ∈ (range (k + 1)).filter (fun i : ℕ => (k : ℝ) * p - d ≤ k * p - i),
          (k.choose i : ℝ) * p ^ i * (1 - p) ^ (k - i) := by
      rw [sub_eq_iff_eq_add, binomialTail]
      refine (Cslib.sum_choose_mul_pow_eq_one k p).symm.trans
        ((sum_filter_not_add_sum_filter (range (k + 1)) (d < ·) _).symm.trans ?_)
      congr 1; congr 1; ext i
      simp only [mem_filter, not_lt, sub_le_sub_iff_left, Nat.cast_le]
    rw [hcomp]
    refine (Cslib.sum_filter_le_mul_sub_choose_mul_pow_le k hp₀ hp₁
      (le_trans (by positivity) hgap)).trans ?_
    have hexp : -2 * ((k : ℝ) * p - d) ^ 2 / k ≤ -(θ ^ 2 * k) / 2 := by
      rw [div_le_iff₀ hk']
      nlinarith [pow_le_pow_left₀ (by positivity : 0 ≤ θ * k / 2) hgap 2]
    exact (Real.exp_le_exp.mpr hexp).trans
      (le_add_of_nonneg_left (div_nonneg (sub_nonneg.mpr hp₁) hθ.le))

section CStar

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
private theorem cfc_binomialTail (k d : ℕ) (X : A) (hX : IsSelfAdjoint X) :
    cfc (binomialTail k d : ℝ → ℝ) X = binomialTail k d X := by
  let q := binomialTail k d (Polynomial.X : Polynomial ℝ)
  have heval : q.eval = binomialTail k d := by
    funext p
    change Polynomial.evalRingHom p (∑ i ∈ range (k + 1) with d < i,
      (k.choose i : Polynomial ℝ) * Polynomial.X ^ i * (1 - Polynomial.X) ^ (k - i)) = _
    simp [map_sum, binomialTail]
  rw [← heval, cfc_polynomial q X hX]
  simp [q, binomialTail]

/-- A binomial tail of a positive contraction is again a positive contraction. -/
theorem binomialTail_mem_Icc (k d : ℕ) {X : A} (hX₀ : 0 ≤ X) (hX₁ : X ≤ 1) :
    binomialTail k d X ∈ Set.Icc (0 : A) 1 := by
  have hX := hX₀.isSelfAdjoint
  have hf : ContinuousOn (binomialTail k d : ℝ → ℝ) (spectrum ℝ X) := by
    unfold binomialTail; fun_prop
  have hs (p : ℝ) (hp : p ∈ spectrum ℝ X) : 0 ≤ p ∧ 0 ≤ 1 - p :=
    ⟨spectrum_nonneg_of_nonneg hX₀ hp,
      sub_nonneg.mpr ((le_algebraMap_iff_spectrum_le hX).mp (by simpa using hX₁) p hp)⟩
  rw [← cfc_binomialTail k d X hX]
  refine ⟨(cfc_nonneg_iff _ X hf hX).2 fun p hp => ?_, ?_⟩
  · have ⟨hp₀, hp₁⟩ := hs p hp; exact sum_nonneg fun i _ => by positivity
  · rw [← cfc_const_one ℝ X hX]
    refine cfc_mono (fun p hp => ?_) hf continuousOn_const
    have ⟨hp₀, hp₁⟩ := hs p hp
    rw [← Cslib.sum_choose_mul_pow_eq_one k p]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun i _ _ => by positivity

theorem binomialAtLeast_mem_Icc (k r : ℕ) {X : A} (hX₀ : 0 ≤ X) (hX₁ : X ≤ 1) :
    binomialAtLeast k r X ∈ Set.Icc (0 : A) 1 := by
  unfold binomialAtLeast; split_ifs
  exacts [⟨zero_le_one, le_rfl⟩, binomialTail_mem_Icc _ _ hX₀ hX₁]

/-- If the success effect is a positive contraction, the failure effect of the binomial
tail is bounded by an affine function of the original failure effect. -/
theorem one_sub_binomialTail_le {k d : ℕ} (hk : 0 < k) {θ : ℝ}
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hsize : 2 * (d : ℝ) ≤ θ * k)
    {X : A} (hX₀ : 0 ≤ X) (hX₁ : X ≤ 1) :
    1 - binomialTail k d X ≤
      (1 - θ)⁻¹ • (1 - X) + algebraMap ℝ A (Real.exp (-(θ ^ 2 * k) / 2)) := by
  have hX := hX₀.isSelfAdjoint
  have hf : ContinuousOn (binomialTail k d : ℝ → ℝ) (spectrum ℝ X) := by
    unfold binomialTail; fun_prop
  have hs₁ : ∀ p ∈ spectrum ℝ X, p ≤ 1 :=
    (le_algebraMap_iff_spectrum_le hX).mp (by simpa using hX₁)
  have h := cfc_mono (a := X) (f := fun p : ℝ => 1 - binomialTail k d p)
    (g := fun p => (1 - θ)⁻¹ * (1 - p) + Real.exp (-(θ ^ 2 * k) / 2))
    (fun p hp => by
      simpa only [div_eq_inv_mul] using one_sub_binomialTail_real_le hk hθ₀ hθ₁ hsize
        (spectrum_nonneg_of_nonneg hX₀ hp) (hs₁ p hp))
    (continuousOn_const.sub hf) (by fun_prop)
  rwa [cfc_sub (fun _ : ℝ => 1) (binomialTail k d) X continuousOn_const hf,
    cfc_const_one ℝ X hX, cfc_binomialTail k d X hX,
    cfc_add_const _ (fun p : ℝ => (1 - θ)⁻¹ * (1 - p)) X (by fun_prop) hX,
    cfc_const_mul (1 - θ)⁻¹ (fun p : ℝ => 1 - p) X (by fun_prop),
    cfc_sub (fun _ : ℝ => 1) (fun p => p) X continuousOn_const continuousOn_id,
    cfc_const_one ℝ X hX, cfc_id' ℝ X hX] at h

/-- Binomial-tail amplification in any algebraic state. The number of trials must
put the threshold at most halfway below the mean at parameter `θ`. -/
theorem AlgState.one_sub_le_re_binomialTail (φ : AlgState A) {k d : ℕ} (hk : 0 < k)
    {θ κ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hsize : 2 * (d : ℝ) ≤ θ * k)
    {X : A} (hX₀ : 0 ≤ X) (hX₁ : X ≤ 1) (hstate : 1 - κ ≤ (φ X).re) :
    1 - κ / (1 - θ) - Real.exp (-(θ ^ 2 * k) / 2) ≤ (φ (binomialTail k d X)).re := by
  have h := φ.re_apply_mono (one_sub_binomialTail_le hk hθ₀ hθ₁ hsize hX₀ hX₁)
  rw [map_sub, φ.map_one, Complex.sub_re, Complex.one_re, map_add, Complex.add_re,
    IsScalarTower.algebraMap_apply ℝ ℂ A, φ.apply_algebraMap, Complex.coe_algebraMap,
    Complex.ofReal_re, ← IsScalarTower.algebraMap_smul ℂ, map_smul, Complex.coe_algebraMap,
    smul_eq_mul, Complex.re_ofReal_mul, map_sub, φ.map_one, Complex.sub_re, Complex.one_re] at h
  have hmul := mul_le_mul_of_nonneg_left (show 1 - (φ X).re ≤ κ by linarith)
    (inv_nonneg.mpr (sub_nonneg.mpr hθ₁.le))
  simp only [← div_eq_inv_mul] at hmul h
  linarith

end CStar

end Cslib.Quantum
