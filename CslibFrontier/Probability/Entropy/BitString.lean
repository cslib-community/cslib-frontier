/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.List
public import CslibFrontier.Probability.Entropy
public import CslibFrontier.Probability.StatisticalDistance
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform

/-!
# Shannon Entropy Lemmas for BitString Distributions

This module collects reusable Shannon-entropy and statistical-distance bounds on `BitString n`
distributions:

* `Cslib.Probability.PMF.entropy_ge_of_dist_uniform`: general statistical-distance-to-entropy lower
  bound $H(p) \ge (n - 1)(1 - 2 \cdot \mathsf{SD}(p, U_n))$.
* `Cslib.Probability.PMF.entropy_ge_of_dist_uniform_le`: if $\mathsf{SD}(p, U_n) \le 1 / n^2$, then
  $H(p) \ge n - 2$ ([Liu and Pass, Lemma 2.2, §2.5, p. 9 of arXiv:2009.11514v1][LiuPass2020]).
* `Cslib.Probability.PMF.sum_filter_mass_le_ge_of_entropy_ge`: if $H(p) \ge B \ge 3$ on
  `BitString m` ($m \ge 1$), then outcomes with point mass at most $2^{-(B - 3)}$ have total
  probability at least $1 / m$
  ([Liu and Pass, Proof of Theorem 5.2, Claim 2, §5.2, p. 12 of arXiv:2009.11514v1][LiuPass2020]).
* `Cslib.Probability.PMF.entropy_ofList_take_ge`: truncating an `m`-bit distribution to its first
  `k ≤ m` bits decreases Shannon entropy by at most `m - k` bits.
* `Cslib.Probability.PMF.entropy_append_uniform`: appending `k` independent uniform bits to an
  `m`-bit distribution increases Shannon entropy by `k` bits.

## References

* [Y. Liu and R. Pass, *On One-Way Functions and Kolmogorov Complexity*][LiuPass2020],
  full version `arXiv:2009.11514v1` (Sections 2.5 and 5.2).
-/

public section

namespace Cslib.Probability.PMF

open Cslib
open scoped BigOperators ENNReal

/-- Auxiliary bound: for any $q \in (0, 1]$, $-q \log_2 q \le 2$. -/
private theorem mul_neg_logb_two_le_two {q : ℝ} (hq0 : 0 < q) :
    q * (-Real.logb 2 q) ≤ 2 := by
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    linarith [Real.log_inv (2 : ℝ), Real.log_le_sub_one_of_pos (inv_pos.mpr zero_lt_two)]
  have hnum : q * -Real.log q ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (inv_pos.mpr hq0)) hq0.le
    rw [Real.log_inv, mul_sub, mul_inv_cancel₀ hq0.ne', mul_one] at hmul
    linarith
  rw [Real.logb, ← neg_div, ← mul_div_assoc]
  calc
    (q * -Real.log q) / Real.log 2 ≤ 1 / Real.log 2 :=
      div_le_div_of_nonneg_right hnum (by linarith)
    _ ≤ 1 / (1 / 2) := one_div_le_one_div_of_le (by norm_num) hlog2
    _ = 2 := by norm_num

/-- **General statistical-distance-to-entropy lower bound.**
For any distribution $p$ on `BitString n`, the mass of outcomes with probability strictly above
$2^{-(n - 1)}$ is at most $2 \cdot \mathsf{SD}(p, U_n)$, so
$H(p) \ge (n - 1)(1 - 2 \cdot \mathsf{SD}(p, U_n))$. -/
theorem entropy_ge_of_dist_uniform {n : ℕ} (hn : 1 ≤ n) (p : PMF (BitString n)) :
    ((n : ℝ) - 1) * (1 - 2 * dist p (PMF.uniformOfFintype (BitString n))) ≤ entropy p := by
  classical
  let U := PMF.uniformOfFintype (BitString n)
  let S₁ : Finset (BitString n) :=
    Finset.univ.filter fun x => (p x).toReal ≤ (2 : ℝ) ^ (-((n : ℝ) - 1))
  have hgt (x : BitString n) (hx : x ∈ S₁ᶜ) : 2 * (U x).toReal < (p x).toReal := by
    simp only [S₁, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_le,
      neg_sub, Real.rpow_sub zero_lt_two, Real.rpow_one, Real.rpow_natCast] at hx
    simpa [U, uniformOfFintype_apply, div_eq_mul_inv] using hx
  -- Outcomes outside `S₁` have more than twice the uniform mass, so they carry at most
  -- `2 * dist p U`.
  have hS₂_mass : ∑ x ∈ S₁ᶜ, (p x).toReal ≤ 2 * dist p U := by
    rw [dist_eq_sum_filter_lt p U, Finset.mul_sum]
    calc ∑ x ∈ S₁ᶜ, (p x).toReal ≤ ∑ x ∈ S₁ᶜ, 2 * ((p x).toReal - (U x).toReal) :=
          Finset.sum_le_sum fun x hx => by linarith [hgt x hx]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
          (fun x hx => Finset.mem_filter.2
            ⟨Finset.mem_univ x, by linarith [hgt x hx, ENNReal.toReal_nonneg (a := U x)]⟩)
          fun x hx _ => by linarith [(Finset.mem_filter.1 hx).2]
  have hsurp (x : BitString n) (hx : x ∈ S₁) :
      (p x).toReal * ((n : ℝ) - 1) ≤ (p x).toReal * surprisal p x := by
    rcases (ENNReal.toReal_nonneg (a := p x)).eq_or_lt with hp0 | hpx
    · rw [← hp0, zero_mul, zero_mul]
    refine mul_le_mul_of_nonneg_left ?_ hpx.le
    rw [surprisal, le_neg]
    exact (Real.logb_le_iff_le_rpow (by norm_num) hpx).mpr (Finset.mem_filter.1 hx).2
  rw [entropy_eq_sum_surprisal]
  calc ((n : ℝ) - 1) * (1 - 2 * dist p U) ≤ ((n : ℝ) - 1) * ∑ x ∈ S₁, (p x).toReal :=
        mul_le_mul_of_nonneg_left
          (by linarith [Finset.sum_add_sum_compl S₁ fun x => (p x).toReal, sum_toReal p])
          (by linarith [(Nat.one_le_cast.2 hn : (1 : ℝ) ≤ n)])
    _ = ∑ x ∈ S₁, (p x).toReal * ((n : ℝ) - 1) := by rw [mul_comm, Finset.sum_mul]
    _ ≤ ∑ x ∈ S₁, (p x).toReal * surprisal p x := Finset.sum_le_sum hsurp
    _ ≤ ∑ x, (p x).toReal * surprisal p x :=
        Finset.sum_le_univ_sum_of_nonneg fun x =>
          mul_nonneg ENNReal.toReal_nonneg (surprisal_nonneg p x)

/-- **[Liu and Pass, Lemma 2.2, §2.5, p. 9 of arXiv:2009.11514v1][LiuPass2020]: Statistical
distance to uniform bounds Shannon entropy from below.**
If $\mathsf{SD}(p, U_n) \le 1 / n^2$, then $H(p) \ge n - 2$. -/
theorem entropy_ge_of_dist_uniform_le {n : ℕ} (p : PMF (BitString n))
    (hdist : dist p (PMF.uniformOfFintype (BitString n)) ≤ 1 / (n : ℝ) ^ 2) :
    (n : ℝ) - 2 ≤ entropy p := by
  rcases le_or_gt n 1 with hn1 | hn1
  · linarith [entropy_nonneg p, (by exact_mod_cast hn1 : (n : ℝ) ≤ 1)]
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn1
  have hdiv : 2 * ((n : ℝ) - 1) * (1 / (n : ℝ) ^ 2) ≤ 1 := by
    rw [mul_one_div, div_le_one (pow_pos (by linarith) 2)]
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  linarith [entropy_ge_of_dist_uniform hn1.le p,
    mul_le_mul_of_nonneg_left hdist (by linarith : (0 : ℝ) ≤ 2 * ((n : ℝ) - 1))]

/-- **[Liu and Pass, Proof of Theorem 5.2, Claim 2, §5.2, p. 12 of arXiv:2009.11514v1][LiuPass2020]:
High Shannon entropy implies non-negligible mass on low-probability outcomes.**
For any distribution $p$ on `BitString m` with $m \ge 1$ and $B \ge 3$ such that $H(p) \ge B$,
the set of outcomes $y$ with point mass $p(y) \le 2^{-(B - 3)}$ has total probability at least
$1 / m$. -/
theorem sum_filter_mass_le_ge_of_entropy_ge {m : ℕ} (hm : 1 ≤ m) (p : PMF (BitString m))
    {B : ℝ} (hB : 3 ≤ B) (hent : B ≤ entropy p) :
    1 / (m : ℝ) ≤
      ∑ y ∈ Finset.univ.filter (fun y => (p y).toReal ≤ (2 : ℝ) ^ (-(B - 3))), (p y).toReal := by
  classical
  let S : Finset (BitString m) :=
    Finset.univ.filter fun y => (p y).toReal ≤ (2 : ℝ) ^ (-(B - 3))
  let q : ℝ := ∑ y ∈ S, (p y).toReal
  change 1 / (m : ℝ) ≤ q
  -- Every `y ∉ S` has surprisal at most `B - 3`.
  have hout : ∑ y ∈ Sᶜ, (p y).toReal * surprisal p y ≤ B - 3 :=
    calc ∑ y ∈ Sᶜ, (p y).toReal * surprisal p y ≤ ∑ y ∈ Sᶜ, (p y).toReal * (B - 3) :=
          Finset.sum_le_sum fun y hy => mul_le_mul_of_nonneg_left
            (surprisal_le_of_mass_ge p y (le_of_lt (by simpa [S] using hy))) ENNReal.toReal_nonneg
      _ ≤ B - 3 := by
          rw [← Finset.sum_mul]
          exact mul_le_of_le_one_left (by linarith) ((Finset.sum_le_univ_sum_of_nonneg
            fun _ => ENNReal.toReal_nonneg).trans (sum_toReal p).le)
  -- The contribution inside `S` is at most `q * m + 2`.
  have hin : ∑ y ∈ S, (p y).toReal * surprisal p y ≤ q * (m : ℝ) + 2 := by
    rcases (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg : 0 ≤ q).eq_or_lt with hq0 | hq_pos
    · have hall0 := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => ENNReal.toReal_nonneg).mp hq0.symm
      rw [Finset.sum_eq_zero fun y hy => by simp [hall0 y hy]]
      simp [q, ← hq0]
    obtain ⟨y₀, hy₀, hpy₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq_pos.ne'
    let pS := p.filter (S : Set (BitString m))
      ⟨y₀, hy₀, (p.mem_support_iff y₀).2 fun h => hpy₀ (by simp [h])⟩
    have hmeas : (p.toOuterMeasure (S : Set (BitString m))).toReal = q := by
      rw [toOuterMeasure_apply_toReal]
      simp [q]
    have hterm (y : BitString m) : q * ((pS y).toReal * surprisal pS y) =
        if y ∈ S then (p y).toReal * surprisal p y + (p y).toReal * Real.logb 2 q else 0 := by
      rw [surprisal, surprisal, filter_apply_toReal, hmeas]
      simp only [Finset.mem_coe]
      split_ifs
      · rcases eq_or_ne (p y).toReal 0 with h0 | h0
        · simp [h0]
        · rw [Real.logb_div h0 hq_pos.ne', ← mul_assoc, mul_div_cancel₀ _ hq_pos.ne']
          ring
      · simp
    have hident : q * entropy pS =
        ∑ y ∈ S, (p y).toReal * surprisal p y + q * Real.logb 2 q := by
      rw [entropy_eq_sum_surprisal, Finset.mul_sum, Finset.sum_congr rfl fun y _ => hterm y,
        Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_add_distrib, ← Finset.sum_mul]
    have hent_pS : entropy pS ≤ m := by
      simpa only [BitString.logb_card] using entropy_le_log_card pS
    have hq_log := mul_neg_logb_two_le_two hq_pos
    rw [mul_neg] at hq_log
    linarith [mul_le_mul_of_nonneg_left hent_pS hq_pos.le]
  rw [div_le_iff₀ (by exact_mod_cast hm)]
  linarith [Finset.sum_add_sum_compl S fun y => (p y).toReal * surprisal p y,
    entropy_eq_sum_surprisal p]

/-- Truncating an `m`-bit distribution to its first `k ≤ m` bits decreases Shannon entropy by at
most `m - k` bits. -/
theorem entropy_ofList_take_ge {m k : ℕ} (hk : k ≤ m) (p : PMF (BitString m)) :
    entropy p - ((m - k : ℕ) : ℝ) ≤
      entropy (p.map fun x => BitString.ofList k ((List.ofFn x).take k)) := by
  let split (x : BitString m) : BitString k × BitString (m - k) :=
    (BitString.ofList k ((List.ofFn x).take k),
      BitString.ofList (m - k) ((List.ofFn x).drop k))
  have hinj : Function.Injective split := fun x y hxy => List.ofFn_inj.mp <| by
    have h1 := congrArg (List.ofFn ∘ Prod.fst) hxy
    have h2 := congrArg (List.ofFn ∘ Prod.snd) hxy
    simp only [Function.comp_apply, split, BitString.ofFn_ofList, List.length_take,
      List.length_ofFn, min_eq_left hk, List.length_drop] at h1 h2
    rw [← List.take_append_drop k (List.ofFn x), ← List.take_append_drop k (List.ofFn y), h1, h2]
  have hcond := conditionalEntropy_le_log_card (p.map split)
  rw [conditionalEntropy, entropy_map_of_injective p hinj, PMF.map_comp,
    BitString.logb_card] at hcond
  dsimp only [Function.comp_def, split] at hcond
  linarith

/-- Appending `k` independent uniform bits to an `m`-bit distribution increases Shannon entropy
by exactly `k` bits. -/
theorem entropy_append_uniform {m k : ℕ} (p : PMF (BitString m)) :
    entropy (p.bind fun x => (PMF.uniformOfFintype (BitString k)).map fun z =>
      BitString.ofList (m + k) (List.ofFn x ++ List.ofFn z)) =
      entropy p + (k : ℝ) := by
  let join (xz : BitString m × BitString k) : BitString (m + k) :=
    BitString.ofList (m + k) (List.ofFn xz.1 ++ List.ofFn xz.2)
  have hinj : Function.Injective join := by
    rintro ⟨x₁, z₁⟩ ⟨x₂, z₂⟩ hxy
    have h := congrArg List.ofFn hxy
    dsimp only [join] at h
    rw [BitString.ofFn_ofList (by simp), BitString.ofFn_ofList (by simp)] at h
    obtain ⟨hx, hz⟩ := List.append_inj h (by simp)
    exact Prod.ext (List.ofFn_inj.mp hx) (List.ofFn_inj.mp hz)
  have hmap : (p.bind fun x => (PMF.uniformOfFintype (BitString k)).map (x, ·)).map join =
      p.bind fun x => (PMF.uniformOfFintype (BitString k)).map fun z =>
        BitString.ofList (m + k) (List.ofFn x ++ List.ofFn z) := by
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, join]
  rw [← hmap, entropy_map_of_injective _ hinj, entropy_prod, entropy_uniform,
    BitString.logb_card]

end Cslib.Probability.PMF
