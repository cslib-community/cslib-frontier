/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Fooling
public import CslibFrontier.Probability.SmallBias
import CslibFrontier.Foundations.BooleanAnalysis.Fourier
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.StatisticalDistance

/-!
# Almost `k`-wise independence and Fourier smoothing

A `k`-wise `ε`-biased distribution on `n` bits is close in statistical distance to an exact
`k`-wise independent distribution: this module gives an elementary Fourier smoothing argument
adjusting the low-degree Fourier coefficients of the probability mass function
(`Cslib.BitString.exists_isKWiseIndependent_dist_le`), along with the direct converse that
`γ`-closeness on every `k`-subset implies `k`-wise `(2 * γ)`-bias
(`Cslib.BitString.isKWiseSmallBias_of_dist_map_restrict_le`).

Compare the classic smoothing theorem of Alon, Goldreich, and Mansour (2003) and
[Chattopadhyay–Zuckerman][ChattopadhyayZuckerman2019]; our explicit Fourier-projection density
perturbation gives a self-contained bound `dist D D' ≤ B / (1 + B) ≤ n ^ k * ε` with an
unconditional counting bound `#{S | S.Nonempty ∧ #S ≤ k} ≤ n ^ k`
(`Cslib.BitString.card_filter_nonempty_card_le_pow`).

## Main results

* `Cslib.Probability.PMF.abs_sum_mul_sub_le_dist`: expectation shift of `[0, 1]`-valued
  observables is at most the statistical distance.
* `Cslib.BitString.card_filter_nonempty_card_le_pow`: at most `n ^ k` nonempty sets have
  size at most `k`.
* `Cslib.BitString.isKWiseSmallBias_of_dist_map_restrict_le`: `γ`-close `k`-marginals imply
  `k`-wise `(2 * γ)`-bias.
* `Cslib.BitString.exists_isKWiseIndependent_dist_le`,
  `Cslib.BitString.exists_isKWiseIndependent_dist_le_of_isKWiseSmallBias`,
  `Cslib.BitString.exists_isKWiseIndependent_dist_le_of_dist_map_restrict_le`: Fourier smoothing
  to an exact `k`-wise independent distribution.

## References

* [N. Alon, O. Goldreich, J. Håstad, R. Peralta, *Simple constructions of almost `k`-wise
  independent random variables*][AlonGoldreichHastadPeralta1992]
* [E. Chattopadhyay, D. Zuckerman, *Explicit two-source extractors and resilient
  functions*][ChattopadhyayZuckerman2019]
-/

public section

namespace Cslib.Probability.PMF

open Finset
open scoped BigOperators

/-- Changing the distribution moves the expectation of a `[0, 1]`-valued function by at most
the statistical distance (removing the factor of `2` from symmetric bounds). -/
theorem abs_sum_mul_sub_le_dist {α : Type*} [Fintype α] (p q : PMF α) (g : α → ℝ)
    (hg0 : ∀ a, 0 ≤ g a) (hg1 : ∀ a, g a ≤ 1) :
    |(∑ a, (p a).toReal * g a) - ∑ a, (q a).toReal * g a| ≤ dist p q := by
  let score : α → ℝ := fun a => g a - 1 / 2
  have hscore (a : α) : |score a| ≤ 1 / 2 := by
    rw [abs_le]
    dsimp only [score]
    constructor <;> linarith [hg0 a, hg1 a]
  have hmean (r : PMF α) :
      ∑ a, (r a).toReal * score a = (∑ a, (r a).toReal * g a) - 1 / 2 := by
    simp only [score, mul_sub, sum_sub_distrib, ← sum_mul, sum_toReal, one_mul]
  have h := abs_sum_mul_sub_le p q score hscore
  rwa [hmean, hmean, sub_sub_sub_cancel_right, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
    one_mul] at h

end Cslib.Probability.PMF

namespace Cslib.BitString

open Finset Probability Cslib.Probability.PMF
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- At most `n ^ k` nonempty subsets of an `n`-element type have cardinality at most `k`. -/
theorem card_filter_nonempty_card_le_pow (k : ℕ) :
    #({S : Finset ι | S.Nonempty ∧ #S ≤ k} : Finset (Finset ι)) ≤ Fintype.card ι ^ k := by
  classical
  have hsub : ({S : Finset ι | S.Nonempty ∧ #S ≤ k} : Finset (Finset ι)) ⊆
      univ.image fun f : Fin k → ι => univ.image f := by
    intro S hS
    obtain ⟨⟨a, ha⟩, hSk⟩ := (mem_filter.1 hS).2
    let e := S.equivFin
    refine mem_image.2 ⟨fun i => if h : (i : ℕ) < #S then e.symm ⟨i, h⟩ else a, mem_univ _, ?_⟩
    ext x
    simp only [mem_image, mem_univ, true_and]
    refine ⟨?_, fun hx => ⟨⟨e ⟨x, hx⟩, (e ⟨x, hx⟩).isLt.trans_le hSk⟩, ?_⟩⟩
    · rintro ⟨i, rfl⟩
      split_ifs with h
      · exact (e.symm ⟨i, h⟩).property
      · exact ha
    · simp only [(e ⟨x, hx⟩).isLt, ↓reduceDIte, Fin.eta, Equiv.symm_apply_apply]
  calc _ ≤ #(univ.image fun f : Fin k → ι => univ.image f) := card_le_card hsub
    _ ≤ #(univ : Finset (Fin k → ι)) := card_image_le
    _ = Fintype.card ι ^ k := by simp [card_univ]

/-- If every marginal of `D` on at most `k` coordinates is within statistical distance `γ` of
uniform, then `D` is `k`-wise `(2 * γ)`-biased. -/
theorem isKWiseSmallBias_of_dist_map_restrict_le {D : PMF (ι → Bool)} {k : ℕ} {γ : ℝ}
    (hD : ∀ T : Finset ι, #T ≤ k →
      dist (D.map T.restrict) (PMF.uniformOfFintype (T → Bool)) ≤ γ) :
    IsKWiseSmallBias k (2 * γ) D := by
  intro S hS hSk
  have hmap : S = (univ : Finset S).map (Function.Embedding.subtype (· ∈ S)) := by
    ext i
    simp
  have hbias := bias_map_restrict D S (univ : Finset S)
  rw [← hmap] at hbias
  have : Nonempty S := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  have huniv_ne : (univ : Finset S) ≠ ∅ := univ_nonempty.ne_empty
  have hunif : bias (PMF.uniformOfFintype (S → Bool)) univ = 0 := by
    rw [bias_uniformOfFintype, ite_eq_right huniv_ne]
  have hscore (u : S → Bool) : |chi ℝ (univ : Finset S) u| ≤ 1 := by
    rw [abs_chi]
  have hdiff := abs_sum_mul_sub_le (D.map S.restrict) (PMF.uniformOfFintype (S → Bool))
    (fun u => chi ℝ (univ : Finset S) u) hscore
  change |bias (D.map S.restrict) univ - bias (PMF.uniformOfFintype (S → Bool)) univ| ≤ _ at hdiff
  rw [hunif, sub_zero, mul_one] at hdiff
  rw [← hbias]
  exact hdiff.trans (mul_le_mul_of_nonneg_left (hD S hSk) (by norm_num))

/-- **Fourier smoothing (exact weight form)**: any distribution `D` on `ι → Bool` is within
statistical distance `B / (1 + B)` of an exact `k`-wise independent distribution `D'`, where
`B = ∑ S with S.Nonempty ∧ #S ≤ k, |bias D S|`. Constructed by subtracting the low-degree Fourier
perturbation from `D` and adding a uniform shift to restore nonnegativity. -/
theorem exists_isKWiseIndependent_dist_le (D : PMF (ι → Bool)) (k : ℕ) :
    ∃ D' : PMF (ι → Bool), IsKWiseIndependent k D' ∧
      dist D D' ≤
        (∑ S with S.Nonempty ∧ #S ≤ k, |bias D S|) /
          (1 + ∑ S with S.Nonempty ∧ #S ≤ k, |bias D S|) := by
  classical
  let lowSets : Finset (Finset ι) := univ.filter fun S => S.Nonempty ∧ #S ≤ k
  let B : ℝ := ∑ S ∈ lowSets, |bias D S|
  let N : ℝ := (2 : ℝ) ^ Fintype.card ι
  let Δ : (ι → Bool) → ℝ := fun x => ∑ S ∈ lowSets, bias D S * chi ℝ S x
  have hB : 0 ≤ B := sum_nonneg fun _ _ => abs_nonneg _
  have hN : 0 < N := by positivity
  have h1B : 0 < 1 + B := by linarith
  have hB_sub_Δ (x : ι → Bool) : 0 ≤ B - Δ x :=
    sub_nonneg.mpr ((le_abs_self _).trans (abs_sum_mul_chi_le lowSets (bias D) x))
  let w : (ι → Bool) → ℝ := fun x => ((D x).toReal + (B - Δ x) / N) / (1 + B)
  have hw_nonneg (x : ι → Bool) : 0 ≤ w x :=
    div_nonneg (add_nonneg ENNReal.toReal_nonneg (div_nonneg (hB_sub_Δ x) hN.le)) h1B.le
  have hsum_Δ : ∑ x, Δ x = 0 := by
    simp only [Δ]
    rw [sum_comm]
    refine sum_eq_zero fun S hS => ?_
    rw [← mul_sum, sum_chi, ite_eq_right (mem_filter.mp hS).2.1.ne_empty, mul_zero]
  have hsum_corr : ∑ x, (B - Δ x) / N = B := by
    rw [← sum_div, sum_sub_distrib, sum_const, card_univ, Fintype.card_fun, Fintype.card_bool,
      nsmul_eq_mul, hsum_Δ, sub_zero]
    push_cast [N]
    field_simp
  have hsum_w : ∑ x, w x = 1 := by
    simp only [w, ← sum_div, sum_add_distrib, sum_toReal, hsum_corr]
    field_simp
  have hsum_enn : ∑ x, ENNReal.ofReal (w x) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hw_nonneg x), hsum_w, ENNReal.ofReal_one]
  let D' : PMF (ι → Bool) := PMF.ofFintype (fun x => ENNReal.ofReal (w x)) hsum_enn
  have hD'_toReal (x : ι → Bool) : (D' x).toReal = w x := ENNReal.toReal_ofReal (hw_nonneg x)
  refine ⟨D', fun U hU hUk => ?_, ?_⟩
  · have hU_mem : U ∈ lowSets := mem_filter.mpr ⟨mem_univ U, hU, hUk⟩
    have hsum_Δ_U : ∑ x, Δ x * chi ℝ U x = bias D U * N := by
      simp only [Δ, sum_mul, mul_assoc]
      rw [sum_comm]
      simp only [← mul_sum, chi_mul_chi, sum_chi, ← bot_eq_empty, symmDiff_eq_bot, mul_ite,
        mul_zero, sum_ite_eq', ite_eq_left hU_mem, N]
    have hexp (x : ι → Bool) : (D' x).toReal * chi ℝ U x =
        ((D x).toReal * chi ℝ U x + (B * chi ℝ U x - Δ x * chi ℝ U x) / N) / (1 + B) := by
      rw [hD'_toReal]
      ring
    rw [abs_nonpos_iff, bias, sum_congr rfl fun x _ => hexp x, ← sum_div, sum_add_distrib,
      ← sum_div, sum_sub_distrib, ← mul_sum, sum_chi, ite_eq_right hU.ne_empty, hsum_Δ_U, ← bias,
      mul_zero, zero_sub, neg_div, mul_div_cancel_right₀ _ hN.ne', add_neg_cancel, zero_div]
  · have hterm (x : ι → Bool) :
        |(D x).toReal - (D' x).toReal| ≤ ((B - Δ x) / N + B * (D x).toReal) / (1 + B) := by
      have h1 := mul_nonneg hB (D x).toReal_nonneg
      have h2 := div_nonneg (hB_sub_Δ x) hN.le
      rw [hD'_toReal, show (D x).toReal - w x = (B * (D x).toReal - (B - Δ x) / N) / (1 + B) by
        simp only [w]; field_simp; ring, abs_div, abs_of_pos h1B]
      exact div_le_div_of_nonneg_right (abs_sub_le_iff.2 ⟨by linarith, by linarith⟩) h1B.le
    rw [dist_eq]
    calc (∑ x, |(D x).toReal - (D' x).toReal|) / 2
        ≤ (∑ x, ((B - Δ x) / N + B * (D x).toReal) / (1 + B)) / 2 := by gcongr with x; exact hterm x
      _ = B / (1 + B) := by
          rw [← sum_div, sum_add_distrib, hsum_corr, ← mul_sum, sum_toReal, mul_one]
          ring

/-- **Fourier smoothing for `k`-wise `ε`-biased distributions**: a `k`-wise `ε`-biased
distribution on `n` bits is within statistical distance `n ^ k * ε` of an exact `k`-wise
independent distribution. -/
theorem exists_isKWiseIndependent_dist_le_of_isKWiseSmallBias {D : PMF (ι → Bool)} {k : ℕ} {ε : ℝ}
    (hε : 0 ≤ ε) (hD : IsKWiseSmallBias k ε D) :
    ∃ D' : PMF (ι → Bool), IsKWiseIndependent k D' ∧
      dist D D' ≤ (Fintype.card ι : ℝ) ^ k * ε := by
  obtain ⟨D', hD'_ind, hdist⟩ := exists_isKWiseIndependent_dist_le D k
  refine ⟨D', hD'_ind, hdist.trans ?_⟩
  set B : ℝ := ∑ S with S.Nonempty ∧ #S ≤ k, |bias D S|
  have hB : 0 ≤ B := sum_nonneg fun _ _ => abs_nonneg _
  have hB_le : B ≤ (Fintype.card ι : ℝ) ^ k * ε := by
    calc B ≤ ∑ _S ∈ univ.filter (fun S : Finset ι => S.Nonempty ∧ #S ≤ k), ε :=
          sum_le_sum fun S hS => hD S (mem_filter.mp hS).2.1 (mem_filter.mp hS).2.2
      _ = (#(univ.filter (fun S : Finset ι => S.Nonempty ∧ #S ≤ k)) : ℝ) * ε := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (Fintype.card ι : ℝ) ^ k * ε := by
          gcongr
          exact_mod_cast card_filter_nonempty_card_le_pow (ι := ι) k
  exact (div_le_self hB (by linarith)).trans hB_le

/-- **Fourier smoothing from marginal closeness**: if every `k`-subset marginal of `D` on `n` bits
is within statistical distance `γ` of uniform, then `D` is within statistical distance
`2 * n ^ k * γ` of an exact `k`-wise independent distribution. -/
theorem exists_isKWiseIndependent_dist_le_of_dist_map_restrict_le {D : PMF (ι → Bool)} {k : ℕ}
    {γ : ℝ} (hD : ∀ T : Finset ι, #T ≤ k →
      dist (D.map T.restrict) (PMF.uniformOfFintype (T → Bool)) ≤ γ) :
    ∃ D' : PMF (ι → Bool), IsKWiseIndependent k D' ∧
      dist D D' ≤ 2 * (Fintype.card ι : ℝ) ^ k * γ := by
  have hγ : 0 ≤ γ := dist_nonneg.trans (hD ∅ (Nat.zero_le k))
  obtain ⟨D', hD'_ind, hdist⟩ := exists_isKWiseIndependent_dist_le_of_isKWiseSmallBias
    (mul_nonneg zero_le_two hγ) (isKWiseSmallBias_of_dist_map_restrict_le hD)
  refine ⟨D', hD'_ind, hdist.trans_eq (by ring)⟩

end Cslib.BitString
