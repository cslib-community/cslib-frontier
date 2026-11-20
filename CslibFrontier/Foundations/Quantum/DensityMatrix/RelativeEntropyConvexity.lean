/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.DensityMatrix.RelativeEntropy
public import CslibFrontier.Foundations.Quantum.DensityMatrix.RelativeEntropyResolvent
import Mathlib.Algebra.BigOperators.WithTop
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Joint convexity of quantum relative entropy

The resolvent bound yields joint convexity by the scalar logarithm integral in
[Ruskai, Theorem 1 and Section 2][Ruskai2007] (arXiv:quant-ph/0604206v1,
printed pp. 2–5). Here the integral is over the unit interval, using the resolvent
parameter `s / (1 - s)`. Finite complex positive semidefinite matrices may be
singular, and the statement uses natural logarithms and extended divergence.
A support mismatch contributes infinity when its weight is positive.

## Main results

* `relativeEntropy_sum_smul_le`: joint convexity for finite nonnegative weighted sums.
-/

public section

namespace Cslib.Quantum

open Matrix Finset Set MeasureTheory
open scoped ComplexOrder Interval MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private noncomputable def scalarIntegrand (a b w s : ℝ) : ℝ :=
  (a * w) * (a - b) / (b + s * (a - b))

private theorem scalarIntegrand_integral {a b w : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsupp : b = 0 → a * w = 0) :
    ContinuousOn (scalarIntegrand a b w) (Icc 0 1) ∧
      (∫ s in (0 : ℝ)..1, scalarIntegrand a b w s) =
        (a * Real.log a - a * Real.log b) * w := by
  by_cases hzero : a * w = 0
  · have hf : scalarIntegrand a b w = fun _ => 0 :=
      funext fun s => by simp [scalarIntegrand, hzero]
    rw [hf]
    refine ⟨continuousOn_const, ?_⟩
    rcases mul_eq_zero.mp hzero with h | h <;> simp [h]
  have ha' : 0 < a := lt_of_le_of_ne ha (left_ne_zero_of_mul hzero).symm
  have hb' : 0 < b := lt_of_le_of_ne hb (fun h => hzero (hsupp h.symm))
  have hpos (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : 0 < b + s * (a - b) := by
    rcases eq_or_lt_of_le hs.2 with rfl | h
    · simpa only [one_mul, add_sub_cancel] using ha'
    · nlinarith [mul_pos hb' (sub_pos.mpr h), mul_nonneg hs.1 ha]
  have hcont : ContinuousOn (scalarIntegrand a b w) (Icc 0 1) :=
    continuousOn_const.div (by fun_prop) (fun s hs => (hpos s hs).ne')
  refine ⟨hcont, ?_⟩
  have hderiv (s : ℝ) (hs : s ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt (fun x => (a * w) * Real.log (b + x * (a - b)))
        (scalarIntegrand a b w s) s := by
    have hs' : s ∈ Icc (0 : ℝ) 1 := by rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    have hne := (hpos s hs').ne'
    have hlin : HasDerivAt (fun x => b + x * (a - b)) (1 * (a - b)) s :=
      ((hasDerivAt_id s).mul_const (a - b)).const_add b
    convert (hlin.log hne).const_mul (a * w) using 1
    simp only [scalarIntegrand, one_mul, div_eq_mul_inv]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable_of_Icc zero_le_one)]
  simp only [one_mul, zero_mul, add_zero]
  rw [show b + (a - b) = a by ring]
  ring

private noncomputable def spectralIntegrand {ρ σ : Matrix ι ι ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (s : ℝ) : ℝ :=
  ∑ i, ∑ j, scalarIntegrand (hρ.eigenvalues i) (hσ.eigenvalues j)
    (Complex.normSq (((hρ.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *
      (hσ.eigenvectorUnitary : Matrix ι ι ℂ)) i j)) s

private theorem spectralIntegrand_integral {ρ σ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ) :
    IntervalIntegrable (spectralIntegrand hρ.isHermitian hσ.isHermitian) volume 0 1 ∧
      (∫ s in (0 : ℝ)..1, spectralIntegrand hρ.isHermitian hσ.isHermitian s) =
        relativeEntropyReal ρ σ := by
  let a := hρ.isHermitian.eigenvalues
  let b := hσ.isHermitian.eigenvalues
  let W : Matrix ι ι ℂ :=
    (hρ.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * hσ.isHermitian.eigenvectorUnitary
  let w (i j : ι) := Complex.normSq (W i j)
  let f (i j : ι) := scalarIntegrand (a i) (b j) (w i j)
  have h (i j : ι) := scalarIntegrand_integral (w := w i j)
    (hρ.eigenvalues_nonneg i) (hσ.eigenvalues_nonneg j)
    (eigenvalue_mul_overlap_eq_zero_of_supportLE hρ.isHermitian hσ.isHermitian hs i j)
  have hi (i j : ι) : IntervalIntegrable (f i j) volume 0 1 :=
    (h i j).1.intervalIntegrable_of_Icc zero_le_one
  have hi' (i : ι) : IntervalIntegrable (fun s => ∑ j, f i j s) volume 0 1 := by
    convert IntervalIntegrable.sum univ (fun j _ => hi i j) using 1
    ext s
    rw [Finset.sum_apply]
  refine ⟨?_, ?_⟩
  · convert IntervalIntegrable.sum univ (fun i _ => hi' i) using 1
    ext s
    rw [Finset.sum_apply]
    rfl
  change (∫ s in (0 : ℝ)..1, ∑ i, ∑ j, f i j s) = _
  rw [intervalIntegral.integral_finsetSum (fun i _ => hi' i),
    relativeEntropyReal_eq_sum_eigenbasis hρ.isHermitian hσ.isHermitian]
  refine sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_finsetSum (fun j _ => hi i j)]
  exact sum_congr rfl fun j _ => (h i j).2

private theorem scalarIntegrand_eq_resolvent {a b w s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hs : s ∈ Ioo (0 : ℝ) 1) :
    scalarIntegrand a b w s =
      (a ^ 2 * w / (b + (s / (1 - s)) * a) - (1 - s) * (a * w)) / (1 - s) ^ 2 := by
  rcases ha.eq_or_lt with rfl | ha
  · simp [scalarIntegrand]
  have hs' := sub_pos.mpr hs.2
  have hp : 0 < b + s * (a - b) := by
    nlinarith [mul_nonneg hb hs'.le, mul_pos hs.1 ha]
  have he : b + s / (1 - s) * a = (b + s * (a - b)) / (1 - s) := by
    field_simp [hs'.ne']
    ring
  rw [scalarIntegrand, he, div_div_eq_mul_div]
  generalize hd : b + s * (a - b) = d at hp ⊢
  field_simp [hs'.ne', hp.ne']
  rw [← hd]
  ring

private theorem spectralIntegrand_eq_resolvent {ρ σ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    spectralIntegrand hρ.isHermitian hσ.isHermitian s =
      (relativeEntropyResolvent (s / (1 - s)) ρ σ - (1 - s) * ρ.trace.re) / (1 - s) ^ 2 := by
  let a := hρ.isHermitian.eigenvalues
  let b := hσ.isHermitian.eigenvalues
  let W : Matrix ι ι ℂ :=
    (hρ.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * hσ.isHermitian.eigenvectorUnitary
  let w (i j : ι) := Complex.normSq (W i j)
  have htrace : ρ.trace.re = ∑ i, ∑ j, a i * w i j := by
    rw [hρ.isHermitian.trace_eq_sum_eigenvalues, Complex.re_sum]
    simp only [← mul_sum]
    refine sum_congr rfl fun i _ => ?_
    change ((a i : ℝ) : ℂ).re = a i * ∑ j, w i j
    rw [Complex.ofReal_re,
      show ∑ j, w i j = 1 from sum_eigenbasis_overlap_row hρ.isHermitian hσ.isHermitian i,
      mul_one]
  rw [relativeEntropyResolvent_eq_sum (div_pos hs.1 (sub_pos.mpr hs.2)) hρ hσ, htrace]
  simp only [mul_sum, ← sum_sub_distrib]
  rw [div_eq_mul_inv, sum_mul]
  unfold spectralIntegrand
  refine sum_congr rfl fun i _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun j _ => ?_
  rw [← div_eq_mul_inv]
  exact scalarIntegrand_eq_resolvent (hρ.eigenvalues_nonneg i) (hσ.eigenvalues_nonneg j) hs

/-- Comparing resolvents at all positive parameters compares relative entropies when the
source traces agree and support inclusion for the second pair implies it for the first. -/
theorem relativeEntropy_le_of_resolvent_le {κ : Type*} [Fintype κ] [DecidableEq κ]
    {ρ σ : Matrix ι ι ℂ} {τ ω : Matrix κ κ ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hτ : τ.PosSemidef) (hω : ω.PosSemidef)
    (htrace : ρ.trace.re = τ.trace.re) (hsupport : SupportLE τ ω → SupportLE ρ σ)
    (h : ∀ t : ℝ, 0 < t →
      relativeEntropyResolvent t ρ σ ≤ relativeEntropyResolvent t τ ω) :
    relativeEntropy ρ σ ≤ relativeEntropy τ ω := by
  by_cases hs : SupportLE τ ω
  · have hs' := hsupport hs
    rw [relativeEntropy_of_supportLE hs', relativeEntropy_of_supportLE hs, WithTop.coe_le_coe]
    obtain ⟨hi, he⟩ := spectralIntegrand_integral hρ hσ hs'
    obtain ⟨hi', he'⟩ := spectralIntegrand_integral hτ hω hs
    rw [← he, ← he']
    apply intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one hi hi'
    intro s hmem
    rw [spectralIntegrand_eq_resolvent hρ hσ hmem, spectralIntegrand_eq_resolvent hτ hω hmem,
      htrace]
    exact div_le_div_of_nonneg_right (sub_le_sub_right
      (h _ (div_pos hmem.1 (sub_pos.mpr hmem.2))) _) (sq_nonneg _)
  · rw [relativeEntropy_of_not_supportLE hs]
    exact le_top

private theorem relativeEntropyReal_sum_smul_le {κ : Type*} [Fintype κ]
    (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (ρ σ : κ → Matrix ι ι ℂ)
    (hρ : ∀ k, (ρ k).PosSemidef) (hσ : ∀ k, (σ k).PosSemidef)
    (hs : ∀ k, SupportLE (ρ k) (σ k)) :
    relativeEntropyReal (∑ k, w k • ρ k) (∑ k, w k • σ k) ≤
      ∑ k, w k * relativeEntropyReal (ρ k) (σ k) := by
  let A : Matrix ι ι ℂ := ∑ k, w k • ρ k
  let B : Matrix ι ι ℂ := ∑ k, w k • σ k
  have hA : A.PosSemidef := posSemidef_sum _ (fun k _ => (hρ k).smul (hw k))
  have hB : B.PosSemidef := posSemidef_sum _ (fun k _ => (hσ k).smul (hw k))
  have hsAB : SupportLE A B := SupportLE.sum_smul w hw hσ hs
  let f (k : κ) := spectralIntegrand (hρ k).isHermitian (hσ k).isHermitian
  have hf (k : κ) := spectralIntegrand_integral (hρ k) (hσ k) (hs k)
  rw [← (spectralIntegrand_integral hA hB hsAB).2]
  simp_rw [← (hf _).2, ← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_finsetSum (fun k _ => (hf k).1.const_mul (w k))]
  have hi : IntervalIntegrable (fun s => ∑ k, w k * f k s) volume 0 1 := by
    convert IntervalIntegrable.sum univ (fun k _ => (hf k).1.const_mul (w k)) using 1
    ext s
    rw [Finset.sum_apply]
  refine intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one
    (spectralIntegrand_integral hA hB hsAB).1 hi fun s hs => ?_
  change spectralIntegrand hA.isHermitian hB.isHermitian s ≤ ∑ k, w k * f k s
  have htrace : A.trace.re = ∑ k, w k * (ρ k).trace.re := by
    have hre (r : ℝ) (z : ℂ) : (r • z).re = r * z.re := Complex.reLm.map_smul r z
    dsimp only [A]
    rw [trace_sum, Complex.re_sum]
    exact sum_congr rfl fun k _ => by rw [trace_smul, hre]
  rw [spectralIntegrand_eq_resolvent hA hB hs, htrace]
  simp only [f, spectralIntegrand_eq_resolvent (hρ _) (hσ _) hs, ← mul_div_assoc]
  simp only [div_eq_mul_inv, ← sum_mul, mul_sub, sum_sub_distrib]
  have hlin : ((1 - s) * ∑ k, w k * (ρ k).trace.re) =
      ∑ k, w k * ((1 - s) * (ρ k).trace.re) := by
    rw [mul_sum]
    exact sum_congr rfl fun _ _ => mul_left_comm _ _ _
  rw [hlin]
  exact mul_le_mul_of_nonneg_right
    (sub_le_sub_right (relativeEntropyResolvent_sum_smul_le
      (div_pos hs.1 (sub_pos.mpr hs.2)) w hw ρ σ hρ hσ) _) (inv_nonneg.mpr (sq_nonneg _))

/-- Umegaki relative entropy is jointly convex for finite complex positive semidefinite
matrices. This is the homogeneous form of Ruskai's Theorem 1, with zero weights contributing
zero and a positive-weight support mismatch giving an infinite right-hand side. -/
theorem relativeEntropy_sum_smul_le {κ : Type*} [Fintype κ]
    (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (ρ σ : κ → Matrix ι ι ℂ)
    (hρ : ∀ k, (ρ k).PosSemidef) (hσ : ∀ k, (σ k).PosSemidef) :
    relativeEntropy (∑ k, w k • ρ k) (∑ k, w k • σ k) ≤
      ∑ k, (w k : WithTop ℝ) * relativeEntropy (ρ k) (σ k) := by
  classical
  by_cases hs : ∀ k, w k ≠ 0 → SupportLE (ρ k) (σ k)
  · let ρ' (k : κ) := if w k = 0 then 0 else ρ k
    let σ' (k : κ) := if w k = 0 then 0 else σ k
    have hρ' (k : κ) : (ρ' k).PosSemidef := by
      by_cases hk : w k = 0 <;> simp [ρ', hk, hρ k, PosSemidef.zero]
    have hσ' (k : κ) : (σ' k).PosSemidef := by
      by_cases hk : w k = 0 <;> simp [σ', hk, hσ k, PosSemidef.zero]
    have hs' (k : κ) : SupportLE (ρ' k) (σ' k) := by
      by_cases hk : w k = 0
      · simpa only [ρ', σ', hk, ite_eq_left] using (SupportLE.refl (0 : Matrix ι ι ℂ))
      · simpa [ρ', σ', hk] using hs k hk
    have heρ : (∑ k, w k • ρ' k) = ∑ k, w k • ρ k :=
      sum_congr rfl fun k _ => by by_cases hk : w k = 0 <;> simp [ρ', hk]
    have heσ : (∑ k, w k • σ' k) = ∑ k, w k • σ k :=
      sum_congr rfl fun k _ => by by_cases hk : w k = 0 <;> simp [σ', hk]
    have heterm : (∑ k, (w k : WithTop ℝ) * relativeEntropy (ρ k) (σ k)) =
        ((∑ k, w k * relativeEntropyReal (ρ' k) (σ' k) : ℝ) : WithTop ℝ) := by
      rw [WithTop.coe_sum]
      refine sum_congr rfl fun k _ => ?_
      by_cases hk : w k = 0
      · simp [hk, WithTop.coe_zero]
      · rw [relativeEntropy_of_supportLE (hs k hk), WithTop.coe_mul]
        simp [ρ', σ', hk]
    rw [heterm, ← heρ, ← heσ, relativeEntropy_of_supportLE (SupportLE.sum_smul w hw hσ' hs'),
      WithTop.coe_le_coe]
    exact relativeEntropyReal_sum_smul_le w hw ρ' σ' hρ' hσ' hs'
  · push Not at hs
    obtain ⟨k, hk, hsupp⟩ := hs
    have htop : (∑ i, (w i : WithTop ℝ) * relativeEntropy (ρ i) (σ i)) = ⊤ := by
      refine WithTop.sum_eq_top.mpr ⟨k, mem_univ _, ?_⟩
      rw [relativeEntropy_of_not_supportLE hsupp, WithTop.mul_top]
      exact_mod_cast hk
    rw [htop]
    exact le_top

end Cslib.Quantum
