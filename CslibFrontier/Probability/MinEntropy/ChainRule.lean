/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.Conditioning
public import CslibFrontier.Probability.MinEntropy
public import CslibFrontier.Probability.StatisticalDistance
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Min-entropy conditioning chain rule and uniform-lifting

This module provides general min-entropy conditioning and smoothing lemmas used in randomness
extractor constructions (such as correlation breakers and sumset extractors):

* **Pointwise min-entropy chain rule** (`minEntropy_map_conditionalSnd_ge_of_apply_ge`):
  conditioning a joint distribution `J : PMF (L × α)` on an observation `ℓ : L` of probability at
  least `δ / |L|` reduces the min-entropy of any marginal `(J.map Prod.snd).map f` by at most
  `log₂ |L| + log₂ (1 / δ)` (compare [DodisOstrovskyReyzinSmith2008], Lemma 2.2, locator not
  verified against primary PDF).
* **Low-probability observation bound** (`toOuterMeasure_badLeak_le`): observations with probability
  strictly below `δ / |L|` have total probability at most `δ`.
* **Conditioned distance averaging** (`dist_bind_pair_le_of_compl_le`, `dist_bind_le_of_compl_le`):
  bounding the statistical distance of two mixtures when the conditional distance is at most `ε`
  outside an event of probability at most `δ`.
* **Support-injective min-entropy preservation** (`le_minEntropy_map_of_injOn`): a map injective on
  a distribution's support never decreases min-entropy.
* **Exact uniform-lifting** (`exists_dist_le_and_le_minEntropy_map_of_dist_uniform`): if `A.map f`
  is `γ`-close to uniform on a finite nonempty type `β` (`γ < 1`), there is a distribution `A'`
  within statistical distance `γ` of `A` itself such that `A'.map f` has exact min-entropy at least
  `log₂ |β| + log₂ (1 - γ)`.

## Main results

* `Cslib.Probability.PMF.le_minEntropy_map_of_injOn`: maps injective on the support preserve
  min-entropy lower bounds.
* `Cslib.Probability.PMF.minEntropy_map_conditionalSnd_ge_of_apply_ge`: pointwise min-entropy chain
  rule for `conditionalSnd`.
* `Cslib.Probability.PMF.toOuterMeasure_badLeak_le`: union bound on low-probability observations.
* `Cslib.Probability.PMF.dist_bind_pair_le_of_compl_le`,
  `Cslib.Probability.PMF.dist_bind_le_of_compl_le`: good/bad split averaging for statistical
  distance.
* `Cslib.Probability.PMF.exists_dist_le_and_le_minEntropy_map_of_dist_uniform`: exact lifting of
  closeness to uniform on a marginal back to the ambient distribution.

## References

* [Y. Dodis, R. Ostrovsky, L. Reyzin, A. Smith, *Fuzzy Extractors: How to Generate Strong Keys from
  Biometrics and Other Noisy Data*][DodisOstrovskyReyzinSmith2008] (min-entropy chain rule;
  locator not verified against primary PDF)
* [S. Vadhan, *Pseudorandomness*][Vadhan2012], Chapter 6 (locator not verified against primary PDF)
-/

public section

namespace Cslib.Probability.PMF

open Finset
open scoped ENNReal

variable {α β L : Type*}

/-- A map that is injective on the support of `p` preserves min-entropy lower bounds. -/
theorem le_minEntropy_map_of_injOn (p : PMF α) {f : α → β} (hf : Set.InjOn f p.support)
    {k : ℝ} (hk : k ≤ minEntropy p) : k ≤ minEntropy (p.map f) := by
  classical
  rw [le_minEntropy_iff] at hk ⊢
  intro b
  by_cases hb : ∃ a ∈ p.support, f a = b
  · obtain ⟨a, ha, rfl⟩ := hb
    have hmap : p.map f (f a) = p a := by
      rw [PMF.map_apply, tsum_eq_single a fun a' ha' => ?_, ite_eq_left rfl]
      exact ite_eq_right_iff.mpr fun heq =>
        (p.apply_eq_zero_iff a').mpr fun hsupp => ha' (hf hsupp ha heq.symm)
    exact hmap ▸ hk a
  · rw [(PMF.apply_eq_zero_iff _ _).mpr (by rwa [PMF.support_map]), ENNReal.toReal_zero]
    positivity

/-- **Pointwise min-entropy chain rule** for `conditionalSnd`: conditioning a joint law
`J : PMF (L × α)` on an observation `ℓ : L` whose marginal probability is at least `δ / |L|`
reduces the min-entropy of `(J.map Prod.snd).map f` by at most `log₂ |L| + log₂ (1 / δ)`. -/
theorem minEntropy_map_conditionalSnd_ge_of_apply_ge [Fintype L] (J : PMF (L × α))
    (f : α → β) {k δ : ℝ} (hδ : 0 < δ)
    (hk : k ≤ minEntropy ((J.map Prod.snd).map f))
    {ℓ : L} (hℓ : δ / Fintype.card L ≤ ((J.map Prod.fst) ℓ).toReal) :
    k - Real.logb 2 (Fintype.card L) - Real.logb 2 δ⁻¹ ≤
      minEntropy ((conditionalSnd J ℓ).map f) := by
  classical
  have : Nonempty L := ⟨ℓ⟩
  have hL_pos : (0 : ℝ) < Fintype.card L := by exact_mod_cast Fintype.card_pos
  have hmarg_pos : 0 < ((J.map Prod.fst) ℓ).toReal :=
    lt_of_lt_of_le (div_pos hδ hL_pos) hℓ
  rw [le_minEntropy_iff] at hk ⊢
  intro y
  have henn : (J.map Prod.fst) ℓ * (conditionalSnd J ℓ).map f y ≤
      ((J.map Prod.snd).map f) y := by
    rw [PMF.map_apply f (conditionalSnd J ℓ) y, ← ENNReal.tsum_mul_left]
    have hlhs : (∑' a, (J.map Prod.fst) ℓ * if y = f a then conditionalSnd J ℓ a else 0) =
        ∑' a, if y = f a then J (ℓ, a) else 0 := tsum_congr fun a => by
      split_ifs
      · exact marginal_mul_conditionalSnd J ℓ a
      · rw [mul_zero]
    rw [hlhs, PMF.map_comp, PMF.map_apply, tsum_prod']
    exact le_tsum (f := fun l : L => ∑' a : α, if y = (f ∘ Prod.snd) (l, a) then J (l, a) else 0) ℓ
  have hreal : ((J.map Prod.fst) ℓ).toReal * (((conditionalSnd J ℓ).map f) y).toReal ≤
      (((J.map Prod.snd).map f) y).toReal := by
    rw [← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (PMF.apply_ne_top _ _) henn
  have hdiv : (((conditionalSnd J ℓ).map f) y).toReal ≤
      2 ^ (-k) / (δ / Fintype.card L) := by
    calc (((conditionalSnd J ℓ).map f) y).toReal
        ≤ (((J.map Prod.snd).map f) y).toReal / ((J.map Prod.fst) ℓ).toReal :=
          (le_div_iff₀ hmarg_pos).mpr (by linarith)
      _ ≤ 2 ^ (-k) / (δ / Fintype.card L) :=
          div_le_div₀ (by positivity) (hk y) (div_pos hδ hL_pos) hℓ
  refine hdiv.trans_eq ?_
  rw [show -(k - Real.logb 2 (Fintype.card L) - Real.logb 2 δ⁻¹) =
      (-k) + Real.logb 2 (Fintype.card L) + Real.logb 2 δ⁻¹ by ring,
    Real.rpow_add two_pos, Real.rpow_add two_pos,
    Real.rpow_logb two_pos (by norm_num) hL_pos,
    Real.rpow_logb two_pos (by norm_num) (inv_pos.mpr hδ)]
  field_simp

/-- Observations with probability strictly below `δ / |L|` have total probability at most `δ`. -/
theorem toOuterMeasure_badLeak_le [Fintype L] (μ : PMF L) {δ : ℝ} (hδ : 0 ≤ δ) :
    (μ.toOuterMeasure {ℓ | (μ ℓ).toReal < δ / Fintype.card L}).toReal ≤ δ := by
  obtain ⟨ℓ₀, _⟩ := μ.support_nonempty
  have : Nonempty L := ⟨ℓ₀⟩
  have hL_pos : (0 : ℝ) < Fintype.card L := by exact_mod_cast Fintype.card_pos
  rw [toOuterMeasure_apply_toReal]
  calc ∑ ℓ, (if ℓ ∈ {ℓ | (μ ℓ).toReal < δ / Fintype.card L} then (μ ℓ).toReal else 0)
      ≤ ∑ _ℓ : L, δ / Fintype.card L := by
        refine Finset.sum_le_sum fun ℓ _ => ?_
        split_ifs with h
        · exact le_of_lt h
        · exact div_nonneg hδ hL_pos.le
    _ = δ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_cancel₀ _ hL_pos.ne']

/-- **Good/bad split averaging for paired mixtures**: if two kernels `p, q : L → PMF β` have
distance at most `ε` on every supported outcome in `G`, and `Gᶜ` has probability at most `δ` under
`μ`, then the paired mixtures have statistical distance at most `δ + ε`. -/
theorem dist_bind_pair_le_of_compl_le [Fintype L] [Fintype β] (μ : PMF L) (p q : L → PMF β)
    (G : Set L) {δ ε : ℝ} (hε : 0 ≤ ε)
    (hbad : (μ.toOuterMeasure Gᶜ).toReal ≤ δ)
    (hgood : ∀ ℓ ∈ G, ℓ ∈ μ.support → dist (p ℓ) (q ℓ) ≤ ε) :
    dist (μ.bind fun ℓ => (p ℓ).map (ℓ, ·)) (μ.bind fun ℓ => (q ℓ).map (ℓ, ·)) ≤ δ + ε := by
  classical
  rw [dist_bind_pair]
  calc ∑ ℓ, (μ ℓ).toReal * dist (p ℓ) (q ℓ)
      ≤ ∑ ℓ, ((if ℓ ∈ Gᶜ then (μ ℓ).toReal else 0) + (μ ℓ).toReal * ε) := by
        refine Finset.sum_le_sum fun ℓ _ => ?_
        have h0 : 0 ≤ (μ ℓ).toReal := ENNReal.toReal_nonneg
        by_cases hG : ℓ ∈ G
        · rw [ite_eq_right (show ℓ ∉ Gᶜ from not_not.mpr hG), zero_add]
          by_cases hsupp : ℓ ∈ μ.support
          · exact mul_le_mul_of_nonneg_left (hgood ℓ hG hsupp) h0
          · simp [(μ.apply_eq_zero_iff ℓ).mpr hsupp]
        · rw [ite_eq_left (show ℓ ∈ Gᶜ from hG)]
          nlinarith [dist_le_one (p ℓ) (q ℓ), mul_nonneg h0 hε]
    _ = (μ.toOuterMeasure Gᶜ).toReal + ε := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_toReal, one_mul,
          toOuterMeasure_apply_toReal]
        congr 1
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        by_cases h : ℓ ∈ Gᶜ <;> simp [h]
    _ ≤ δ + ε := by linarith

/-- **Good/bad split averaging for mixtures**: discarding the revealed observation from
`dist_bind_pair_le_of_compl_le` gives `dist (μ.bind p) (μ.bind q) ≤ δ + ε`. -/
theorem dist_bind_le_of_compl_le [Finite L] [Fintype β] (μ : PMF L) (p q : L → PMF β)
    (G : Set L) {δ ε : ℝ} (hε : 0 ≤ ε)
    (hbad : (μ.toOuterMeasure Gᶜ).toReal ≤ δ)
    (hgood : ∀ ℓ ∈ G, ℓ ∈ μ.support → dist (p ℓ) (q ℓ) ≤ ε) :
    dist (μ.bind p) (μ.bind q) ≤ δ + ε := by
  let _ := Fintype.ofFinite L
  have hmap (k : L → PMF β) : (μ.bind fun ℓ => (k ℓ).map (ℓ, ·)).map Prod.snd = μ.bind k := by
    rw [PMF.map_bind]
    exact congrArg (μ.bind ·) (funext fun _ => (PMF.map_comp _ _ _).trans (PMF.map_id _))
  rw [← hmap p, ← hmap q]
  exact (dist_map_le _ _ Prod.snd).trans
    (dist_bind_pair_le_of_compl_le μ p q G hε hbad hgood)

/-- **Exact uniform-lifting on a marginal**: if `A.map f` is within statistical distance `γ < 1` of
the uniform distribution on a finite nonempty type `β`, then there exists a distribution `A'`
within statistical distance `γ` of `A` itself whose pushforward `A'.map f` has exact min-entropy
at least `log₂ |β| + log₂ (1 - γ)`. In particular, for `γ ≤ 1 / 2`, `A'.map f` has min-entropy at
least `log₂ |β| - 1`. -/
theorem exists_dist_le_and_le_minEntropy_map_of_dist_uniform [Fintype α] [Fintype β] [Nonempty β]
    (A : PMF α) (f : α → β) {γ : ℝ} (hγ1 : γ < 1)
    (hdist : dist (A.map f) (PMF.uniformOfFintype β) ≤ γ) :
    ∃ A' : PMF α, dist A A' ≤ γ ∧
      Real.logb 2 (Fintype.card β) + Real.logb 2 (1 - γ) ≤ minEntropy (A'.map f) := by
  classical
  set d := dist (A.map f) (PMF.uniformOfFintype β)
  have hd0 : 0 ≤ d := dist_nonneg
  have hd1 : 0 < 1 - d := by linarith
  have hγ_pos : 0 < 1 - γ := by linarith
  have hcard_pos : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  set u : ℝ := (Fintype.card β : ℝ)⁻¹
  have hu_pos : 0 < u := inv_pos.mpr hcard_pos
  have hu_eq (y : β) : (PMF.uniformOfFintype β y).toReal = u := by
    simp [u, PMF.uniformOfFintype_apply]
  -- Rescale each fiber `f⁻¹(y)` by `min 1 (u / (A.map f y).toReal)` so its total mass is
  -- `min ((A.map f y).toReal) u`.
  let w : α → ℝ := fun a =>
    if ((A.map f) (f a)).toReal = 0 then 0
    else (A a).toReal * min 1 (u / ((A.map f) (f a)).toReal)
  have hw_nonneg (a : α) : 0 ≤ w a := by
    dsimp only [w]
    split_ifs <;> positivity
  have hw_le (a : α) : w a ≤ (A a).toReal := by
    dsimp only [w]
    split_ifs
    exacts [ENNReal.toReal_nonneg,
      mul_le_of_le_one_right ENNReal.toReal_nonneg (min_le_left _ _)]
  have hfiber (y : β) :
      (∑ a, if y = f a then w a else 0) = min (((A.map f) y).toReal) u := by
    by_cases hy : ((A.map f) y).toReal = 0
    · rw [hy, min_eq_left hu_pos.le]
      exact Finset.sum_eq_zero fun a _ =>
        ite_eq_right_iff.mpr fun h => by simp only [w, ← h, hy, ↓reduceIte]
    · have hy_pos : 0 < ((A.map f) y).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hy)
      have hterm (a : α) : (if y = f a then w a else 0) =
          (if y = f a then (A a).toReal else 0) * min 1 (u / ((A.map f) y).toReal) := by
        split_ifs with h
        · simp only [w, ← h, hy, ↓reduceIte]
        · simp only [zero_mul]
      simp_rw [hterm]
      rw [← Finset.sum_mul, ← map_apply_toReal A f y, mul_min_of_nonneg _ _ hy_pos.le,
        mul_one, mul_div_cancel₀ _ hy]
  have hw_sum : ∑ a, w a = 1 - d := by
    calc ∑ a, w a
        = ∑ a, ∑ y : β, if y = f a then w a else 0 := Finset.sum_congr rfl fun a _ => by simp
      _ = ∑ y : β, ∑ a, if y = f a then w a else 0 := Finset.sum_comm
      _ = ∑ y : β, min (((A.map f) y).toReal) u := Finset.sum_congr rfl fun y _ => hfiber y
      _ = ∑ y : β, min (((A.map f) y).toReal) ((PMF.uniformOfFintype β) y).toReal := by
          simp_rw [hu_eq]
      _ = 1 - d := sum_min_toReal (A.map f) (PMF.uniformOfFintype β)
  let A' : PMF α := PMF.ofFintype (fun a => ENNReal.ofReal (w a / (1 - d))) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun a _ => div_nonneg (hw_nonneg a) hd1.le,
      ← Finset.sum_div, hw_sum, div_self hd1.ne', ENNReal.ofReal_one])
  have hA'_toReal (a : α) : (A' a).toReal = w a / (1 - d) := by
    rw [PMF.ofFintype_apply, ENNReal.toReal_ofReal (div_nonneg (hw_nonneg a) hd1.le)]
  refine ⟨A', ?_, ?_⟩
  · refine hdist.trans' ?_
    rw [dist_eq]
    have hpt (a : α) : |(A a).toReal - (A' a).toReal| ≤
        ((A a).toReal - w a) + (w a / (1 - d) - w a) := by
      have h2 : w a ≤ w a / (1 - d) :=
        le_div_iff₀ hd1 |>.mpr (mul_le_of_le_one_right (hw_nonneg a) (by linarith))
      rw [hA'_toReal, abs_le]
      constructor <;> linarith [hw_le a]
    have hsum := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => hpt a
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_div, sum_toReal A, hw_sum, div_self hd1.ne'] at hsum
    linarith
  · rw [le_minEntropy_iff]
    intro y
    rw [map_apply_toReal]
    have hmap_y : (∑ a, if y = f a then (A' a).toReal else 0) =
        min (((A.map f) y).toReal) u / (1 - d) := by
      rw [← hfiber y, Finset.sum_div]
      exact Finset.sum_congr rfl fun a _ => by split_ifs <;> simp [hA'_toReal]
    rw [hmap_y]
    calc min (((A.map f) y).toReal) u / (1 - d)
        ≤ u / (1 - d) := div_le_div_of_nonneg_right (min_le_right _ _) hd1.le
      _ ≤ u / (1 - γ) := div_le_div_of_nonneg_left hu_pos.le hγ_pos (by linarith)
      _ = 2 ^ (-(Real.logb 2 (Fintype.card β) + Real.logb 2 (1 - γ))) := by
          rw [neg_add, Real.rpow_add two_pos, Real.rpow_neg zero_le_two, Real.rpow_neg zero_le_two,
            Real.rpow_logb two_pos (by norm_num) hcard_pos,
            Real.rpow_logb two_pos (by norm_num) hγ_pos]
          simp only [u, div_eq_mul_inv]

end Cslib.Probability.PMF
