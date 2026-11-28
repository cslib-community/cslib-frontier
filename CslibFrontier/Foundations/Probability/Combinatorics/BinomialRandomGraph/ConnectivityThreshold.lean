/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Probability/Combinatorics/BinomialRandomGraph/`)

public import CslibFrontier.Foundations.Probability.Combinatorics.BinomialRandomGraph.IsolatedVertices
import CslibFrontier.Foundations.Data.Nat.Choose.Real
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Connectivity.Connected
import CslibFrontier.Foundations.Probability.Bonferroni
import CslibFrontier.Foundations.Probability.Combinatorics.BinomialRandomGraph.EdgePattern
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Sym
import Mathlib.Topology.Algebra.Monoid

/-!
# Connectivity threshold limit for binomial random graphs

At the Erdős–Rényi connectivity threshold `n p(n) - log n → c` (`c : ℝ`), the number `X_n` of
isolated vertices in Mathlib's binomial random graph `G(Fin n, p n)` (`SimpleGraph.binomialRandom`)
converges in distribution to `Poisson(exp (-c))`, and the connectivity probability converges to
`exp (-exp (-c))`. This completes the constant-`c` case of
[Frieze and Karoński, Theorem 4.1][FriezeKaronski2016] in `G(n, p)` (whose `c_n → ∞` and
`c_n → -∞` halves are in `BinomialRandomGraph.Connectivity` and
`BinomialRandomGraph.IsolatedVertices`).

* `SimpleGraph.binomialRandom_real_forall_isIsolated`: any fixed `r`-subset `S` of vertices is
  all isolated with probability `(1 - p) ^ (|S| |V| - |S| (|S| + 1) / 2)`.
* `SimpleGraph.tendsto_mul_one_sub_pow_sub_one`: the expected number of isolated vertices satisfies
  `n (1 - p(n)) ^ (n - 1) → exp (-c)` when `n p(n) - log n → c`.
* `SimpleGraph.tendsto_binomialRandom_real_natCard_isIsolated_eq`: by Brun's sieve
  (`ProbabilityTheory.tendsto_measureReal_natCard_eq_poisson_of_factorialMoments`),
  `P(X_n = k) → exp (-exp (-c)) * (exp (-c) ^ k / k!)` for every `k : ℕ`, with `k = 0`
  specialized to `SimpleGraph.tendsto_binomialRandom_real_forall_not_isIsolated_nhds`.
* `SimpleGraph.binomialRandom_real_forall_not_isIsolated_and_not_connected_le` and
  `SimpleGraph.tendsto_binomialRandom_real_forall_not_isIsolated_and_not_connected`: a graph with
  no isolated vertex that is still disconnected contains a connected component of size `2 ≤ k ≤ n/2`
  with a spanning tree of `k - 1` internal edges and an empty cut of `k (n - k)` edges; the
  resulting union bound vanishes when `n p(n) - log n → c`.
* `SimpleGraph.tendsto_binomialRandom_real_connected_nhds`: combining `k = 0` with the component
  gap gives `P(G(n, p(n)) is connected) → exp (-exp (-c))`.

## Main results

* `SimpleGraph.binomialRandom_real_forall_isIsolated`
* `SimpleGraph.tendsto_mul_one_sub_pow_sub_one`
* `SimpleGraph.tendsto_binomialRandom_real_natCard_isIsolated_eq`
* `SimpleGraph.tendsto_binomialRandom_real_forall_not_isIsolated_nhds`
* `SimpleGraph.binomialRandom_real_forall_not_isIsolated_and_not_connected_le`
* `SimpleGraph.tendsto_binomialRandom_real_forall_not_isIsolated_and_not_connected`
* `SimpleGraph.tendsto_binomialRandom_real_connected_nhds`

## References

* [A. Frieze, M. Karoński, *Introduction to Random Graphs*, Sections 3.1 and
  4.1][FriezeKaronski2016]
-/

public section

open MeasureTheory ProbabilityTheory unitInterval Finset Filter
open scoped Finset Topology

namespace SimpleGraph

variable {V : Type*}

/-! ### Exact probability of an isolated vertex subset -/

section IsolatedMoments

private theorem card_biUnion_incident [Fintype V] [DecidableEq V] (S : Finset V) :
    #(S.biUnion fun v => (Finset.univ.erase v).image (Sym2.mk v)) =
      #S * Fintype.card V - #S * (#S + 1) / 2 := by
  induction S using Finset.induction with
  | empty => simp
  | @insert v S hv ih =>
    have hcard : #((Finset.univ.erase v).image (Sym2.mk v)) = Fintype.card V - 1 := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => Sym2.congr_right.1 h),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    rw [Finset.biUnion_insert, Finset.card_union, hcard, ih]
    have hinter : (Finset.univ.erase v).image (Sym2.mk v) ∩
        (S.biUnion fun v' => (Finset.univ.erase v').image (Sym2.mk v')) =
          S.image fun w => s(v, w) := by
      ext e
      simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_image, Finset.mem_image]
      constructor
      · rintro ⟨⟨w, -, rfl⟩, u, hu, z, -, heq⟩
        rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact False.elim (hv hu)
        · exact ⟨_, hu, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        have hwv : w ≠ v := fun h => hv (h ▸ hw)
        exact ⟨⟨w, Finset.mem_erase.mpr ⟨hwv, Finset.mem_univ _⟩, rfl⟩, w, hw, v,
          Finset.mem_erase.mpr ⟨hwv.symm, Finset.mem_univ _⟩, Sym2.eq_swap⟩
    have hcard_inter : #((Finset.univ.erase v).image (Sym2.mk v) ∩
        S.biUnion (fun v' => (Finset.univ.erase v').image (Sym2.mk v'))) = #S := by
      rw [hinter, Finset.card_image_of_injective _ fun _ _ h => Sym2.congr_right.mp h]
    have hSn : #S + 1 ≤ Fintype.card V :=
      (Finset.card_insert_of_notMem hv).symm ▸ Finset.card_le_univ _
    have hdiv_step : (#S + 1) * (#S + 2) / 2 = #S * (#S + 1) / 2 + (#S + 1) := by
      rw [show (#S + 1) * (#S + 2) = #S * (#S + 1) + 2 * (#S + 1) by ring,
        Nat.add_mul_div_left _ _ (by norm_num)]
    have htri_le : #S * (#S + 1) / 2 ≤ #S * Fintype.card V :=
      Nat.div_le_of_le_mul <|
        (Nat.mul_le_mul_left #S hSn).trans (Nat.le_mul_of_pos_left _ (by decide))
    rw [hcard_inter, Finset.card_insert_of_notMem hv, hdiv_step,
      show (#S + 1) * Fintype.card V = #S * Fintype.card V + Fintype.card V by ring]
    omega

/-- In `G(V, p)`, every vertex in a finite subset `S` is isolated with probability
`(1 - p) ^ (|S| |V| - |S| (|S| + 1) / 2)`. -/
theorem binomialRandom_real_forall_isIsolated [Fintype V] (p : I) (S : Finset V) :
    G(V, p).real {G | ∀ v ∈ S, G.IsIsolated v} =
      (1 - p : ℝ) ^ (#S * Fintype.card V - #S * (#S + 1) / 2) := by
  classical
  let t : Finset (Sym2 V) := S.biUnion fun v => (Finset.univ.erase v).image (Sym2.mk v)
  have hdiag : ∀ e ∈ t, ¬e.IsDiag := by
    intro e he
    obtain ⟨v, _, hev⟩ := Finset.mem_biUnion.mp he
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hev
    simpa using (Finset.mem_erase.mp hw).1.symm
  have hset : {G : SimpleGraph V | ∀ v ∈ S, G.IsIsolated v} =
      {G | Disjoint (t : Set (Sym2 V)) G.edgeSet} := by
    ext G
    simp only [Set.mem_ofPred_eq, t, Finset.coe_biUnion, Finset.mem_coe,
      Set.disjoint_iUnion_left]
    exact forall₂_congr fun v _ => isIsolated_iff_disjoint_incident G v
  rw [hset, binomialRandom_real_disjoint_edgeSet p t hdiag, card_biUnion_incident]

end IsolatedMoments

/-! ### Threshold asymptotics and Poisson limit for isolated vertices -/

section ThresholdAsymptotics

private theorem tendsto_mul_pow_div_self_of_tendsto_mul_sub_log {p : ℕ → I} {c : ℝ}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ) - Real.log n) atTop (𝓝 c)) (m : ℕ) :
    Tendsto (fun n : ℕ => ((n : ℝ) * (p n : ℝ)) ^ m / (n : ℝ)) atTop (𝓝 0) := by
  have hbd : ∀ᶠ n : ℕ in atTop, |(n : ℝ) * (p n : ℝ) - Real.log n - c| < 1 := by
    filter_upwards [hp.eventually (Metric.ball_mem_nhds c zero_lt_one)] with n hn
    rwa [Real.dist_eq] at hn
  have hlog_big : ∀ᶠ n : ℕ in atTop, |c| + 1 ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  have hlog_div : Tendsto (fun n : ℕ => Real.log n ^ m / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 m one_ne_zero).comp tendsto_natCast_atTop_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using hlog_div.const_mul (2 ^ m))
    (Eventually.of_forall fun n => div_nonneg (pow_nonneg
      (mul_nonneg (Nat.cast_nonneg n) (unitInterval.nonneg _)) _) (Nat.cast_nonneg n)) ?_
  filter_upwards [hbd, hlog_big, eventually_ge_atTop 1] with n hbn hln _
  have hnp0 : 0 ≤ (n : ℝ) * (p n : ℝ) := mul_nonneg (Nat.cast_nonneg n) (unitInterval.nonneg _)
  have hle_log : (n : ℝ) * (p n : ℝ) ≤ 2 * Real.log n := by
    linarith [(abs_lt.mp hbn).2, le_abs_self c]
  calc ((n : ℝ) * (p n : ℝ)) ^ m / (n : ℝ)
      ≤ (2 * Real.log n) ^ m / (n : ℝ) := by gcongr
    _ = 2 ^ m * (Real.log n ^ m / (n : ℝ)) := by rw [mul_pow, mul_div_assoc]

private theorem tendsto_coe_atTop_zero {p : ℕ → I} {c : ℝ}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ) - Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (p n : ℝ)) atTop (𝓝 0) := by
  refine (tendsto_mul_pow_div_self_of_tendsto_mul_sub_log hp 1).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp [hn0]

private theorem tendsto_one_sub_atTop_one {p : ℕ → I} {c : ℝ}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ) - Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (1 - (p n : ℝ))) atTop (𝓝 1) := by
  simpa using tendsto_const_nhds.sub (tendsto_coe_atTop_zero hp)

private theorem tendsto_mul_exp_neg_mul {p : ℕ → I} {c : ℝ}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ) - Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-((n : ℝ) * (p n : ℝ))))
      atTop (𝓝 (Real.exp (-c))) := by
  have hexp : Tendsto (fun n : ℕ => Real.exp (-((n : ℝ) * (p n : ℝ) - Real.log n)))
      atTop (𝓝 (Real.exp (-c))) := (Real.continuous_exp.comp continuous_neg).tendsto c |>.comp hp
  refine hexp.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by positivity
  rw [show -((n : ℝ) * (p n : ℝ) - Real.log n) = Real.log n + (-((n : ℝ) * (p n : ℝ))) by ring,
    Real.exp_add, Real.exp_log hn0]

/-- When `n p(n) - log n → c`, the expected number of isolated vertices satisfies
`n (1 - p(n)) ^ (n - 1) → exp (-c)`. -/
theorem tendsto_mul_one_sub_pow_sub_one {p : ℕ → I} {c : ℝ}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ) - Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (n : ℝ) * (1 - (p n : ℝ)) ^ (n - 1))
      atTop (𝓝 (Real.exp (-c))) := by
  have h1sub : Tendsto (fun n : ℕ => 1 - (p n : ℝ)) atTop (𝓝 1) := tendsto_one_sub_atTop_one hp
  have hq_ev : ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) < 1 - (p n : ℝ) :=
    h1sub.eventually (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hsq : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ) ^ 2) atTop (𝓝 0) := by
    refine (tendsto_mul_pow_div_self_of_tendsto_mul_sub_log hp 2).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    field_simp [Nat.cast_ne_zero.mpr (by omega : n ≠ 0)]
  have hlog_err : Tendsto (fun n : ℕ => (n : ℝ) * Real.log (1 - (p n : ℝ)) +
      (n : ℝ) * (p n : ℝ)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (by simpa using (hsq.div h1sub one_ne_zero).neg) tendsto_const_nhds ?_ ?_
    · filter_upwards [hq_ev] with n hq
      have hq0 : 0 < 1 - (p n : ℝ) := by linarith
      have hinv := Real.log_inv (1 - (p n : ℝ)) ▸ Real.log_le_sub_one_of_pos (inv_pos.mpr hq0)
      have hsub : (1 - (p n : ℝ))⁻¹ - 1 = (p n : ℝ) / (1 - (p n : ℝ)) := by
        field_simp [hq0.ne']; ring
      have halg : (n : ℝ) * (-(p n : ℝ) / (1 - (p n : ℝ)) + (p n : ℝ)) =
          -((n : ℝ) * (p n : ℝ) ^ 2 / (1 - (p n : ℝ))) := by
        field_simp [hq0.ne']; ring
      have hmul := mul_le_mul_of_nonneg_left (show -(p n : ℝ) / (1 - (p n : ℝ)) + (p n : ℝ) ≤
        Real.log (1 - (p n : ℝ)) + (p n : ℝ) by linarith [neg_div (1 - (p n : ℝ)) (p n : ℝ)])
        (Nat.cast_nonneg n)
      linarith
    · filter_upwards [hq_ev] with n hq
      have hlog_ub := Real.log_le_sub_one_of_pos (show 0 < 1 - (p n : ℝ) by linarith)
      have hm := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n)
        (show Real.log (1 - (p n : ℝ)) + (p n : ℝ) ≤ 0 by linarith)
      linarith
  have hpow_n : Tendsto (fun n : ℕ => (n : ℝ) * (1 - (p n : ℝ)) ^ n)
      atTop (𝓝 (Real.exp (-c))) := by
    refine ((Real.continuous_exp.tendsto (-c)).comp (by simpa using hlog_err.sub hp)).congr' ?_
    filter_upwards [eventually_ge_atTop 1, hq_ev] with n hn hq
    have hn0 : (0 : ℝ) < n := by positivity
    rw [Function.comp_apply, show ((n : ℝ) * Real.log (1 - (p n : ℝ)) + (n : ℝ) * (p n : ℝ)) -
          ((n : ℝ) * (p n : ℝ) - Real.log n) =
        Real.log n + Real.log (1 - (p n : ℝ)) * (n : ℝ) by ring,
      Real.exp_add, Real.exp_log hn0, ← Real.rpow_def_of_pos (by linarith : 0 < 1 - (p n : ℝ)),
      Real.rpow_natCast]
  have hdiv := hpow_n.div h1sub one_ne_zero
  rw [div_one] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [eventually_ge_atTop 1, hq_ev] with n hn hq
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  dsimp only [Pi.div_apply]
  rw [Nat.succ_sub_one, pow_succ]
  field_simp [show (1 - (p (m + 1) : ℝ)) ≠ 0 by linarith]

private theorem tendsto_choose_div_pow (r : ℕ) :
    Tendsto (fun n : ℕ => (n.choose r : ℝ) / (n : ℝ) ^ r) atTop (𝓝 ((r.factorial : ℝ)⁻¹)) := by
  have h1 : ∀ i : ℕ, Tendsto (fun n : ℕ => 1 - (i : ℝ) / (n : ℝ)) atTop (𝓝 1) := fun i => by
    simpa using tendsto_const_nhds.sub
      (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hdiv : Tendsto (fun n : ℕ => (∏ i ∈ Finset.range r, (1 - (i : ℝ) / (n : ℝ))) /
      (r.factorial : ℝ)) atTop (𝓝 ((r.factorial : ℝ)⁻¹)) := by
    simpa [one_div] using (by simpa using tendsto_finsetProd (Finset.range r) fun i _ => h1 i :
      Tendsto (fun n : ℕ => ∏ i ∈ Finset.range r, (1 - (i : ℝ) / (n : ℝ))) atTop (𝓝 1)).div_const
      (r.factorial : ℝ)
  refine hdiv.congr' ?_
  filter_upwards [eventually_ge_atTop (max r 1)] with n hn
  have hnr : r ≤ n := (le_max_left r 1).trans hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (le_max_right r 1).trans hn; omega)
  have hdesc : ((n.choose r : ℝ) * r.factorial) = ∏ i ∈ Finset.range r, ((n : ℝ) - i) := by
    rw [show ((n.choose r : ℝ) * r.factorial) = (n.descFactorial r : ℝ) by
      exact_mod_cast (mul_comm r.factorial _ ▸ Nat.descFactorial_eq_factorial_mul_choose n r).symm,
      Nat.descFactorial_eq_prod_range]
    push_cast
    exact Finset.prod_congr rfl fun i hi =>
      Nat.cast_sub ((Finset.mem_range.mp hi).le.trans hnr)
  have hprod : (∏ i ∈ Finset.range r, (1 - (i : ℝ) / (n : ℝ))) =
      (∏ i ∈ Finset.range r, ((n : ℝ) - i)) / (n : ℝ) ^ r := by
    calc ∏ i ∈ Finset.range r, (1 - (i : ℝ) / (n : ℝ))
        = ∏ i ∈ Finset.range r, (((n : ℝ) - i) / (n : ℝ)) :=
          Finset.prod_congr rfl fun i _ => by field_simp [hn0]
      _ = (∏ i ∈ Finset.range r, ((n : ℝ) - i)) / (n : ℝ) ^ r := by
          rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  rw [hprod, ← hdesc, div_right_comm, mul_div_cancel_right₀ _ (by positivity)]

/-- At the connectivity threshold `n p(n) - log n → c`, the number of isolated vertices in
`G(Fin n, p n)` converges in distribution to `Poisson(exp (-c))`. -/
theorem tendsto_binomialRandom_real_natCard_isIsolated_eq {p : ℕ → I} {c : ℝ}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ) - Real.log n) atTop (𝓝 c)) (k : ℕ) :
    Tendsto (fun n : ℕ => G(Fin n, p n).real {G | Nat.card {v // G.IsIsolated v} = k})
      atTop (𝓝 (Real.exp (-Real.exp (-c)) * (Real.exp (-c) ^ k / k.factorial))) := by
  have h1sub : Tendsto (fun n : ℕ => 1 - (p n : ℝ)) atTop (𝓝 1) := tendsto_one_sub_atTop_one hp
  refine ProbabilityTheory.tendsto_measureReal_natCard_eq_poisson_of_factorialMoments
    (fun n => G(Fin n, p n)) (fun n v => {G : SimpleGraph (Fin n) | G.IsIsolated v})
    (fun n _ => MeasurableSet.of_discrete) (fun r => ?_) k
  have hlim : Tendsto (fun n : ℕ => ((n.choose r : ℝ) / (n : ℝ) ^ r) *
      ((n : ℝ) * (1 - (p n : ℝ)) ^ (n - 1)) ^ r / (1 - (p n : ℝ)) ^ (r * (r - 1) / 2))
      atTop (𝓝 (Real.exp (-c) ^ r / r.factorial)) := by
    rw [show Real.exp (-c) ^ r / r.factorial =
      ((r.factorial : ℝ)⁻¹ * Real.exp (-c) ^ r) / (1 : ℝ) ^ (r * (r - 1) / 2) by
      simp [div_eq_mul_inv, mul_comm]]
    exact ((tendsto_choose_div_pow r).mul ((tendsto_mul_one_sub_pow_sub_one hp).pow r)).div
      (h1sub.pow (r * (r - 1) / 2)) (by simp)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (max r 1),
    h1sub.eventually (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with n hn hq
  have hnr : r ≤ n := (le_max_left r 1).trans hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (le_max_right r 1).trans hn; omega)
  have hsum_eq : ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
        G(Fin n, p n).real (⋂ v ∈ S, {G : SimpleGraph (Fin n) | G.IsIsolated v}) =
      (n.choose r : ℝ) * (1 - (p n : ℝ)) ^ (r * n - r * (r + 1) / 2) := by
    have hterm : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
        G(Fin n, p n).real (⋂ v ∈ S, {G : SimpleGraph (Fin n) | G.IsIsolated v}) =
          (1 - (p n : ℝ)) ^ (r * n - r * (r + 1) / 2) := fun S hS => by
      rw [show (⋂ v ∈ S, {G : SimpleGraph (Fin n) | G.IsIsolated v}) =
          {G | ∀ v ∈ S, G.IsIsolated v} from by ext G; simp,
        binomialRandom_real_forall_isIsolated, Fintype.card_fin, (Finset.mem_powersetCard.mp hS).2]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hexp_eq : r * n - r * (r + 1) / 2 + r * (r - 1) / 2 = r * (n - 1) := by
    rcases r with _ | r
    · simp
    · have hdiv_diff : (r + 1) * (r + 2) / 2 = (r + 1) * r / 2 + (r + 1) := by
        rw [show (r + 1) * (r + 2) = (r + 1) * r + 2 * (r + 1) by ring,
          Nat.add_mul_div_left _ _ (by norm_num)]
      have hle2 : (r + 1) * (r + 2) / 2 ≤ (r + 1) * n := Nat.div_le_of_le_mul <|
        (Nat.mul_le_mul_left (r + 1) (by omega : r + 2 ≤ 2 * n)).trans_eq (by ring)
      simp only [Nat.add_sub_cancel] at hle2 ⊢
      rw [hdiv_diff, Nat.mul_sub_one]
      omega
  rw [hsum_eq, div_eq_iff (pow_ne_zero _ (by linarith : 1 - (p n : ℝ) ≠ 0))]
  calc ((n.choose r : ℝ) / (n : ℝ) ^ r) * ((n : ℝ) * (1 - (p n : ℝ)) ^ (n - 1)) ^ r
      = (n.choose r : ℝ) * ((1 - (p n : ℝ)) ^ (n - 1)) ^ r := by rw [mul_pow]; field_simp [hn0]
    _ = (n.choose r : ℝ) * (1 - (p n : ℝ)) ^ (r * n - r * (r + 1) / 2) *
          (1 - (p n : ℝ)) ^ (r * (r - 1) / 2) := by
        rw [← pow_mul, mul_comm (n - 1) r, ← hexp_eq, pow_add, mul_assoc]

/-- Specialization of `tendsto_binomialRandom_real_natCard_isIsolated_eq` to `k = 0`:
when `n p(n) - log n → c`, `G(Fin n, p n)` has no isolated vertex with probability tending to
`exp (-exp (-c))`. -/
theorem tendsto_binomialRandom_real_forall_not_isIsolated_nhds {p : ℕ → I} {c : ℝ}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ) - Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => G(Fin n, p n).real {G | ∀ v, ¬G.IsIsolated v})
      atTop (𝓝 (Real.exp (-Real.exp (-c)))) := by
  have h := tendsto_binomialRandom_real_natCard_isIsolated_eq hp 0
  have hset : ∀ n : ℕ, {G : SimpleGraph (Fin n) | Nat.card {v // G.IsIsolated v} = 0} =
      {G | ∀ v, ¬G.IsIsolated v} := fun n => by
    ext G
    have hfin : Finite {v : Fin n // G.IsIsolated v} := Subtype.finite
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Nat.card_eq_zero, or_iff_left hfin.not_infinite,
      isEmpty_subtype]
  simpa only [hset, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one] using h

end ThresholdAsymptotics

/-! ### Component gap between no isolated vertices and connectivity -/

section ComponentGap

private theorem card_sym2_filter_not_isDiag [DecidableEq V] (S : Finset V) :
    #(S.sym2.filter (¬ ·.IsDiag)) = (#S).choose 2 := by
  have heq : S.sym2.filter (¬ ·.IsDiag) = S.sym2 \ S.image Sym2.diag := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_image, Finset.mem_sym2_iff]
    refine ⟨fun ⟨he, hnd⟩ => ⟨he, fun ⟨u, _, hu⟩ => hnd (hu ▸ Sym2.diag_isDiag u)⟩,
      fun ⟨he, hnd⟩ => ⟨he, fun hd => ?_⟩⟩
    induction e using Sym2.ind with
    | h x y =>
      obtain rfl := Sym2.mk_isDiag_iff.mp hd
      exact hnd ⟨x, he x (by simp), rfl⟩
  have hsub : S.image Sym2.diag ⊆ S.sym2 := fun e he => by
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp he
    exact Finset.diag_mem_sym2_iff.mpr hu
  have hinj : Function.Injective (Sym2.diag : V → Sym2 V) := fun a b h => by
    simpa [Sym2.diag, Sym2.eq_iff] using h
  rw [heq, Finset.card_sdiff_of_subset hsub, Finset.card_sym2,
    Finset.card_image_of_injective _ hinj, Nat.choose_succ_succ (#S) 1, Nat.choose_one_right]
  change #S + (#S).choose 2 - #S = (#S).choose 2
  omega

private theorem disjoint_sym2_filter_not_isDiag_cutPairs [Fintype V] [DecidableEq V]
    (S : Finset V) :
    Disjoint (S.sym2.filter (¬ ·.IsDiag)) ((S ×ˢ Sᶜ).image Sym2.mk.uncurry) := by
  rw [Finset.disjoint_left]
  intro e he_in he_cut
  obtain ⟨⟨u, v⟩, h_in, rfl⟩ := Finset.mem_image.mp he_cut
  exact (Finset.mem_compl.mp (Finset.mem_product.mp h_in).2)
    (Finset.mk_mem_sym2_iff.mp (Finset.mem_filter.mp he_in).1).2

private theorem binomialRandom_real_edgeSet_and_cut [Fintype V] [DecidableEq V] (p : I)
    (S : Finset V) {t : Finset (Sym2 V)} (ht : t ⊆ S.sym2.filter (¬ ·.IsDiag)) :
    G(V, p).real {G | (∀ e ∈ t, e ∈ G.edgeSet) ∧ ∀ u ∈ S, ∀ v ∉ S, ¬G.Adj u v} =
      (p : ℝ) ^ #t * (1 - p : ℝ) ^ (#S * (Fintype.card V - #S)) := by
  let b : Sym2 V → Bool := fun e => decide (e ∈ t)
  let cP : Finset (Sym2 V) := (S ×ˢ Sᶜ).image Sym2.mk.uncurry
  have hdisj : Disjoint t cP := (disjoint_sym2_filter_not_isDiag_cutPairs S).mono_left ht
  have hdiag : ∀ e ∈ t ∪ cP, ¬e.IsDiag := fun e he => by
    rcases Finset.mem_union.mp he with het | hec
    · exact (Finset.mem_filter.mp (ht het)).2
    · obtain ⟨⟨u, v⟩, h_in, rfl⟩ := Finset.mem_image.mp hec
      exact fun hd => (Finset.mem_compl.mp (Finset.mem_product.mp h_in).2)
        (Sym2.mk_isDiag_iff.1 hd ▸ (Finset.mem_product.mp h_in).1)
  have hset : {G : SimpleGraph V | (∀ e ∈ t, e ∈ G.edgeSet) ∧ ∀ u ∈ S, ∀ v ∉ S, ¬G.Adj u v} =
      {G | ∀ e ∈ t ∪ cP, e ∈ G.edgeSet ↔ b e = true} := by
    ext G
    simp only [Set.mem_ofPred_eq, Finset.mem_union, b, decide_eq_true_eq]
    constructor
    · rintro ⟨ht_edge, hcut⟩ e he
      refine ⟨fun hedge => ?_, ht_edge e⟩
      rcases he with het | hec
      · exact het
      · obtain ⟨⟨u, v⟩, h_in, rfl⟩ := Finset.mem_image.mp hec
        have ⟨hu, hv⟩ := Finset.mem_product.mp h_in
        exact absurd (hcut u hu v (Finset.mem_compl.mp hv)) (not_not.mpr hedge)
    · intro h
      refine ⟨fun e he => (h e (Or.inl he)).mpr (by simp [he]), fun u hu v hv huv => ?_⟩
      have hec : s(u, v) ∈ cP := Finset.mem_image.mpr ⟨(u, v),
        Finset.mem_product.mpr ⟨hu, Finset.mem_compl.mpr hv⟩, rfl⟩
      exact Finset.disjoint_left.mp hdisj ((h (s(u, v)) (Or.inr hec)).mp huv) hec
  have hp1 : ∏ e ∈ t, (if b e = true then (p : ℝ) else 1 - p) = (p : ℝ) ^ #t := by
    have h1 : ∀ e ∈ t, (if b e = true then (p : ℝ) else 1 - p) = (p : ℝ) := fun e he => by
      simp [b, he]
    rw [Finset.prod_congr rfl h1, Finset.prod_const]
  have hcard_cP : #cP = #S * (Fintype.card V - #S) := by
    have hinj : Set.InjOn Sym2.mk.uncurry (↑(S ×ˢ Sᶜ) : Set (V × V)) := by
      rintro ⟨u, v⟩ huv ⟨u', v'⟩ huv' h
      simp only [Finset.coe_product, Finset.coe_compl, Set.mem_prod, Finset.mem_coe,
        Set.mem_compl_iff] at huv huv'
      rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact absurd huv.1 huv'.2
    change #((S ×ˢ Sᶜ).image Sym2.mk.uncurry) = _
    rw [Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_compl]
  have hp2 : ∏ e ∈ cP, (if b e = true then (p : ℝ) else 1 - p) =
      (1 - p : ℝ) ^ (#S * (Fintype.card V - #S)) := by
    have h2 : ∀ e ∈ cP, (if b e = true then (p : ℝ) else 1 - p) = (1 - p : ℝ) := fun e he => by
      simp [b, Finset.disjoint_right.mp hdisj he]
    rw [Finset.prod_congr rfl h2, Finset.prod_const, hcard_cP]
  rw [hset, binomialRandom_real_edgePattern p (t ∪ cP) hdiag b, Finset.prod_union hdisj, hp1, hp2]

/-- Explicit union bound for the event that `G(V, p)` has no isolated vertex yet fails to be
connected. -/
theorem binomialRandom_real_forall_not_isIsolated_and_not_connected_le [Fintype V] [Nonempty V]
    (p : I) :
    G(V, p).real {G | (∀ v, ¬G.IsIsolated v) ∧ ¬G.Connected} ≤
      ∑ k ∈ Icc 2 (Fintype.card V / 2),
        ((Fintype.card V).choose k : ℝ) * ((k.choose 2).choose (k - 1) : ℝ) *
          (p : ℝ) ^ (k - 1) * (1 - p : ℝ) ^ (k * (Fintype.card V - k)) := by
  classical
  set n := Fintype.card V
  have hsub : {G : SimpleGraph V | (∀ v, ¬G.IsIsolated v) ∧ ¬G.Connected} ⊆
      ⋃ k ∈ Icc 2 (n / 2), ⋃ S ∈ powersetCard k (univ : Finset V),
        ⋃ t ∈ powersetCard (k - 1) (S.sym2.filter (¬ ·.IsDiag)),
          {G | (∀ e ∈ t, e ∈ G.edgeSet) ∧ ∀ u ∈ S, ∀ v ∉ S, ¬G.Adj u v} := by
    intro G ⟨hni, hnc⟩
    obtain ⟨S, hS2, hShalf, hSconn, hScut⟩ :=
      exists_connected_induce_forall_not_adj_of_not_connected hnc hni
    obtain ⟨tS, htScard, htSedge⟩ := exists_card_sub_one_subset_edgeSet_of_connected hSconn
    let f : Sym2 (S : Set V) → Sym2 V := Sym2.map Subtype.val
    let t : Finset (Sym2 V) := tS.image f
    have ht_in : t ⊆ S.sym2.filter (¬ ·.IsDiag) := fun e he => by
      obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
      rw [Finset.mem_filter, Finset.mem_sym2_iff]
      refine ⟨fun u hu => by obtain ⟨x, _, rfl⟩ := Sym2.mem_map.mp hu; exact x.property, ?_⟩
      induction e' using Sym2.ind with
      | _ a b =>
        change ¬Sym2.IsDiag s(a.val, b.val)
        simpa using Subtype.coe_ne_coe.mpr (htSedge _ he').2
    have ht_card : #t = #S - 1 := by
      rw [Finset.card_image_of_injective _ (Sym2.map.injective Subtype.val_injective), htScard]
      simp
    have ht_edges : ∀ e ∈ t, e ∈ G.edgeSet := fun e he => by
      obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
      induction e' using Sym2.ind with
      | _ a b => exact (htSedge _ he').1
    simp only [Set.mem_iUnion, mem_Icc, mem_powersetCard, subset_univ, true_and,
      Set.mem_ofPred_eq, exists_prop]
    exact ⟨#S, ⟨hS2, by omega⟩, S, rfl, t, ⟨ht_in, ht_card⟩, ht_edges, hScut⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans <|
    (measureReal_biUnion_finset_le _ _).trans <| Finset.sum_le_sum fun k _ => ?_
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  have hS_bound : ∀ S ∈ (univ : Finset V).powersetCard k,
      G(V, p).real (⋃ t ∈ (S.sym2.filter (¬ ·.IsDiag)).powersetCard (k - 1),
          {G | (∀ e ∈ t, e ∈ G.edgeSet) ∧ ∀ u ∈ S, ∀ v ∉ S, ¬G.Adj u v}) ≤
        ((k.choose 2).choose (k - 1) : ℝ) * (p : ℝ) ^ (k - 1) * (1 - p : ℝ) ^ (k * (n - k)) := by
    intro S hS
    have hSk := (Finset.mem_powersetCard.mp hS).2
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    have hterm : ∀ t ∈ (S.sym2.filter (¬ ·.IsDiag)).powersetCard (k - 1),
        G(V, p).real {G | (∀ e ∈ t, e ∈ G.edgeSet) ∧ ∀ u ∈ S, ∀ v ∉ S, ¬G.Adj u v} =
          (p : ℝ) ^ (k - 1) * (1 - p : ℝ) ^ (k * (n - k)) := fun t ht => by
      obtain ⟨ht_in, ht_card⟩ := Finset.mem_powersetCard.mp ht
      rw [binomialRandom_real_edgeSet_and_cut p S ht_in, ht_card, hSk]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard,
      card_sym2_filter_not_isDiag, hSk, nsmul_eq_mul, mul_assoc]
  refine (Finset.sum_le_sum hS_bound).trans ?_
  rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, nsmul_eq_mul]
  exact le_of_eq (by ring)

private theorem tendsto_zero_of_nonneg_of_sq_tendsto_zero {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (hsq : Tendsto (fun n => f n ^ 2) atTop (𝓝 0)) : Tendsto f atTop (𝓝 0) := by
  simpa [Real.sqrt_sq (hf _)] using Filter.Tendsto.sqrt hsq

private noncomputable def componentGapTerm (p : ℕ → I) (n k : ℕ) : ℝ :=
  (n.choose k : ℝ) * ((k.choose 2).choose (k - 1) : ℝ) *
    (p n : ℝ) ^ (k - 1) * (1 - (p n : ℝ)) ^ (k * (n - k))

private theorem componentGapTerm_nonneg (p : ℕ → I) (n k : ℕ) :
    0 ≤ componentGapTerm p n k := by
  have hp_nn : 0 ≤ (p n : ℝ) := unitInterval.nonneg _
  have hq_nn : 0 ≤ 1 - (p n : ℝ) := by linarith [unitInterval.le_one (p n)]
  dsimp only [componentGapTerm]
  positivity

private theorem tendsto_componentGap_pair {p : ℕ → I} {c : ℝ}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ) - Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => componentGapTerm p n 2) atTop (𝓝 0) := by
  have hp0 : Tendsto (fun n : ℕ => (p n : ℝ)) atTop (𝓝 0) := tendsto_coe_atTop_zero hp
  have hne := tendsto_mul_exp_neg_mul hp
  have hexp4 : Tendsto (fun n : ℕ => Real.exp (4 * (p n : ℝ))) atTop (𝓝 1) := by
    simpa only [Function.comp_def, mul_zero, Real.exp_zero] using
      (Real.continuous_exp.tendsto (4 * 0)).comp (hp0.const_mul 4)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using ((hp0.div_const 2).mul (hne.pow 2)).mul hexp4)
    (Eventually.of_forall fun n => componentGapTerm_nonneg p n 2) ?_
  filter_upwards [eventually_ge_atTop 2] with n hn2
  have hq_exp : (1 - (p n : ℝ)) ^ (2 * (n - 2)) ≤ Real.exp (-(2 * ((n : ℝ) - 2) * (p n : ℝ))) :=
    Real.one_sub_pow_le_exp (unitInterval.le_one _) <| by
      rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hn2, Nat.cast_ofNat]
  have hch2 : ((n.choose 2 : ℝ) * ((2 : ℕ).choose 2 |>.choose 1 : ℝ)) ≤ (n : ℝ) ^ 2 / 2 := by
    have h2nat : n.choose 2 * 2 = n * (n - 1) := Nat.choose_two_right n ▸
      Nat.div_mul_cancel (Nat.even_mul_pred_self n).two_dvd
    have h2 : (n.choose 2 : ℝ) * 2 = (n : ℝ) * ((n : ℝ) - 1) := by
      have := congrArg (Nat.cast (R := ℝ)) h2nat
      push_cast [Nat.cast_sub (by omega : 1 ≤ n)] at this
      exact this
    rw [show ((2 : ℕ).choose 2).choose 1 = 1 by decide, Nat.cast_one, mul_one]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hexp_eq : ((n : ℝ) * Real.exp (-((n : ℝ) * (p n : ℝ)))) ^ 2 * Real.exp (4 * (p n : ℝ)) =
      (n : ℝ) ^ 2 * Real.exp (-(2 * ((n : ℝ) - 2) * (p n : ℝ))) := by
    rw [mul_pow, ← Real.exp_natCast_mul, mul_assoc ((n : ℝ) ^ 2), ← Real.exp_add]
    congr 2; push_cast; ring
  have hp_nn : 0 ≤ (p n : ℝ) := unitInterval.nonneg _
  have hq_nn : 0 ≤ 1 - (p n : ℝ) := by linarith [unitInterval.le_one (p n)]
  dsimp only [componentGapTerm]
  calc (n.choose 2 : ℝ) * (((2 : ℕ).choose 2).choose 1 : ℝ) * (p n : ℝ) ^ 1 *
        (1 - (p n : ℝ)) ^ (2 * (n - 2))
      ≤ ((n : ℝ) ^ 2 / 2) * (p n : ℝ) * Real.exp (-(2 * ((n : ℝ) - 2) * (p n : ℝ))) := by
        rw [pow_one]; gcongr
    _ = (p n : ℝ) / 2 * ((n : ℝ) * Real.exp (-((n : ℝ) * (p n : ℝ)))) ^ 2 *
          Real.exp (4 * (p n : ℝ)) := by
        rw [mul_assoc, mul_assoc _ (_ ^ 2), hexp_eq]; ring

private theorem componentGapTerm_le {p : ℕ → I} {n k : ℕ} (hk3 : 3 ≤ k) (hkn2 : k ≤ n / 2) :
    componentGapTerm p n k ≤
      ((n : ℝ) * Real.exp 1 * Real.exp (-((n : ℝ) * (p n : ℝ) / 2))) *
        (((n : ℝ) * Real.exp 1 ^ 2 * (p n : ℝ) / 2) *
          Real.exp (-((n : ℝ) * (p n : ℝ) / 2))) ^ (k - 1) := by
  have hkn : k ≤ n := by omega
  have hp_nn : 0 ≤ (p n : ℝ) := unitInterval.nonneg _
  have hq_nn : 0 ≤ 1 - (p n : ℝ) := by linarith [unitInterval.le_one (p n)]
  have hch1 : (n.choose k : ℝ) ≤ ((n : ℝ) * Real.exp 1 / k) ^ k := by
    simpa only [mul_comm (n : ℝ)] using Nat.choose_le_exp_mul_div_pow n k
  have hch2 : ((k.choose 2).choose (k - 1) : ℝ) ≤ ((k : ℝ) * Real.exp 1 / 2) ^ (k - 1) := by
    have h := Nat.choose_le_exp_mul_div_pow (k.choose 2) (k - 1)
    have hck : ((k.choose 2 : ℝ) * Real.exp 1 / ((k - 1 : ℕ) : ℝ)) = (k : ℝ) * Real.exp 1 / 2 := by
      have h2 : (k.choose 2 : ℝ) * 2 = (k : ℝ) * ((k - 1 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.choose_two_right k ▸
          Nat.div_mul_cancel (Nat.even_mul_pred_self k).two_dvd : k.choose 2 * 2 = k * (k - 1))
      rw [div_eq_div_iff (Nat.cast_ne_zero.mpr (by omega)) two_ne_zero]
      linear_combination Real.exp 1 * h2
    rwa [mul_comm (Real.exp 1), hck] at h
  have hq_exp : (1 - (p n : ℝ)) ^ (k * (n - k)) ≤
      Real.exp (-(k * ((n : ℝ) / 2) * (p n : ℝ))) := by
    refine Real.one_sub_pow_le_exp (unitInterval.le_one _) ?_
    rw [Nat.cast_mul, Nat.cast_sub hkn]
    have h2k : (2 * k : ℝ) ≤ n := by exact_mod_cast (by omega : 2 * k ≤ n)
    have hm := mul_le_mul_of_nonneg_left (show (n : ℝ) / 2 ≤ n - k by linarith) (Nat.cast_nonneg k)
    have := mul_le_mul_of_nonneg_right hm hp_nn
    linarith
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpow_comb : ((n : ℝ) * Real.exp 1 / k) ^ k * ((k : ℝ) * Real.exp 1 / 2) ^ (k - 1) *
        (p n : ℝ) ^ (k - 1) =
      ((n : ℝ) * Real.exp 1 / k) * ((n : ℝ) * Real.exp 1 ^ 2 * (p n : ℝ) / 2) ^ (k - 1) := by
    rw [← mul_pow_sub_one (by omega : k ≠ 0), mul_assoc, mul_assoc ((n : ℝ) * Real.exp 1 / k),
      ← mul_pow, ← mul_pow]
    congr 2
    field_simp [hk0]
  have hexp_split : Real.exp (-(k * ((n : ℝ) / 2) * (p n : ℝ))) =
      Real.exp (-((n : ℝ) * (p n : ℝ) / 2)) * Real.exp (-((n : ℝ) * (p n : ℝ) / 2)) ^ (k - 1) := by
    rw [← Real.exp_natCast_mul, ← Real.exp_add, Nat.cast_sub (by omega : 1 ≤ k)]
    ring_nf
  have hAn_div : (n : ℝ) * Real.exp 1 / k ≤ (n : ℝ) * Real.exp 1 :=
    div_le_self (by positivity) (by exact_mod_cast (by omega : 1 ≤ k))
  dsimp only [componentGapTerm]
  calc (n.choose k : ℝ) * ((k.choose 2).choose (k - 1) : ℝ) * (p n : ℝ) ^ (k - 1) *
        (1 - (p n : ℝ)) ^ (k * (n - k))
      ≤ ((n : ℝ) * Real.exp 1 / k) ^ k * ((k : ℝ) * Real.exp 1 / 2) ^ (k - 1) *
          (p n : ℝ) ^ (k - 1) * Real.exp (-(k * ((n : ℝ) / 2) * (p n : ℝ))) := by gcongr
    _ = ((n : ℝ) * Real.exp 1 / k * Real.exp (-((n : ℝ) * (p n : ℝ) / 2))) *
          (((n : ℝ) * Real.exp 1 ^ 2 * (p n : ℝ) / 2) *
            Real.exp (-((n : ℝ) * (p n : ℝ) / 2))) ^ (k - 1) := by
        rw [hpow_comb, hexp_split, mul_pow]; ring
    _ ≤ ((n : ℝ) * Real.exp 1 * Real.exp (-((n : ℝ) * (p n : ℝ) / 2))) *
          (((n : ℝ) * Real.exp 1 ^ 2 * (p n : ℝ) / 2) *
            Real.exp (-((n : ℝ) * (p n : ℝ) / 2))) ^ (k - 1) := by gcongr

private theorem tendsto_componentGap_tail {p : ℕ → I} {c : ℝ}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ) - Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => ∑ k ∈ Icc 3 (n / 2), componentGapTerm p n k) atTop (𝓝 0) := by
  have hne := tendsto_mul_exp_neg_mul hp
  let r : ℕ → ℝ := fun n =>
    ((n : ℝ) * Real.exp 1 ^ 2 * (p n : ℝ) / 2) * Real.exp (-((n : ℝ) * (p n : ℝ) / 2))
  let A : ℕ → ℝ := fun n => (n : ℝ) * Real.exp 1 * Real.exp (-((n : ℝ) * (p n : ℝ) / 2))
  have hr0 : Tendsto r atTop (𝓝 0) := by
    refine tendsto_zero_of_nonneg_of_sq_tendsto_zero (fun n => by
      have hp_nn : 0 ≤ (p n : ℝ) := unitInterval.nonneg _; dsimp [r]; positivity) ?_
    have hsq_lim : Tendsto (fun n : ℕ =>
        (Real.exp 1 ^ 4 / 4) * (((n : ℝ) * (p n : ℝ)) ^ 2 / (n : ℝ)) *
          ((n : ℝ) * Real.exp (-((n : ℝ) * (p n : ℝ))))) atTop (𝓝 0) := by
      have h := (((tendsto_mul_pow_div_self_of_tendsto_mul_sub_log hp 2).const_mul
        (Real.exp 1 ^ 4 / 4)).mul hne)
      simpa only [zero_mul, mul_zero] using h
    refine hsq_lim.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hexp2 : Real.exp (-((n : ℝ) * (p n : ℝ) / 2)) ^ 2 = Real.exp (-((n : ℝ) * (p n : ℝ))) := by
      rw [← Real.exp_natCast_mul]; congr 1; push_cast; ring
    dsimp [r]; rw [mul_pow, mul_pow, hexp2]
    field_simp [Nat.cast_ne_zero.mpr (by omega : n ≠ 0)]; ring
  have htail : Tendsto (fun n : ℕ => 2 * A n * r n ^ 2) atTop (𝓝 0) := by
    refine tendsto_zero_of_nonneg_of_sq_tendsto_zero (fun n => by
      have hp_nn : 0 ≤ (p n : ℝ) := unitInterval.nonneg _; dsimp [A, r]; positivity) ?_
    have hsq_lim : Tendsto (fun n : ℕ =>
        (Real.exp 1 ^ 10 / 4) * (((n : ℝ) * (p n : ℝ)) ^ 4 / (n : ℝ)) *
          ((n : ℝ) * Real.exp (-((n : ℝ) * (p n : ℝ)))) ^ 3) atTop (𝓝 0) := by
      have h := (((tendsto_mul_pow_div_self_of_tendsto_mul_sub_log hp 4).const_mul
        (Real.exp 1 ^ 10 / 4)).mul (hne.pow 3))
      simpa only [zero_mul, mul_zero] using h
    refine hsq_lim.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hexp6 : Real.exp (-((n : ℝ) * (p n : ℝ) / 2)) ^ 6 =
        Real.exp (-((n : ℝ) * (p n : ℝ))) ^ 3 := by
      rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, ← Real.exp_natCast_mul]; congr 2; push_cast; ring
    dsimp [A, r]
    rw [show (2 * ((n : ℝ) * Real.exp 1 * Real.exp (-((n : ℝ) * (p n : ℝ) / 2))) *
          ((n : ℝ) * Real.exp 1 ^ 2 * (p n : ℝ) / 2 *
            Real.exp (-((n : ℝ) * (p n : ℝ) / 2))) ^ 2) ^ 2 =
        ((n : ℝ) ^ 6 * Real.exp 1 ^ 10 * (p n : ℝ) ^ 4 / 4) *
          Real.exp (-((n : ℝ) * (p n : ℝ) / 2)) ^ 6 by ring,
      hexp6, mul_pow, mul_pow]
    field_simp [Nat.cast_ne_zero.mpr (by omega : n ≠ 0)]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htail
    (Eventually.of_forall fun n => Finset.sum_nonneg fun k _ => componentGapTerm_nonneg p n k) ?_
  filter_upwards [hr0.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with
    n hr_half
  have hp_nn : 0 ≤ (p n : ℝ) := unitInterval.nonneg _
  have hr_nn : 0 ≤ r n := by dsimp [r]; positivity
  have hA_nn : 0 ≤ A n := by dsimp [A]; positivity
  have hstep : ∀ k ∈ Icc 3 (n / 2),
      A n * r n ^ (k - 1) ≤ A n * r n ^ 2 * (1 / 2 : ℝ) ^ (k - 3) := fun k hk => by
    have hk3 : 3 ≤ k := (Finset.mem_Icc.mp hk).1
    rw [show r n ^ (k - 1) = r n ^ 2 * r n ^ (k - 3) by
      rw [← pow_add, show 2 + (k - 3) = k - 1 by omega], ← mul_assoc]
    gcongr
  have hsum_half : ∑ k ∈ Icc 3 (n / 2), (1 / 2 : ℝ) ^ (k - 3) ≤ 2 := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    exact sum_geometric_two_le _
  calc ∑ k ∈ Icc 3 (n / 2), componentGapTerm p n k
      ≤ ∑ k ∈ Icc 3 (n / 2), A n * r n ^ (k - 1) :=
        Finset.sum_le_sum fun k hk =>
          componentGapTerm_le (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
    _ ≤ (A n * r n ^ 2) * ∑ k ∈ Icc 3 (n / 2), (1 / 2 : ℝ) ^ (k - 3) := by
        rw [Finset.mul_sum]; exact Finset.sum_le_sum hstep
    _ ≤ 2 * A n * r n ^ 2 := by
        have := mul_le_mul_of_nonneg_left hsum_half (mul_nonneg hA_nn (sq_nonneg (r n)))
        linarith

/-- At the connectivity threshold `n p(n) - log n → c`, the probability that `G(Fin n, p n)` has
no isolated vertices yet is disconnected tends to `0`. -/
theorem tendsto_binomialRandom_real_forall_not_isIsolated_and_not_connected {p : ℕ → I} {c : ℝ}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ) - Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ =>
        G(Fin n, p n).real {G | (∀ v, ¬G.IsIsolated v) ∧ ¬G.Connected})
      atTop (𝓝 0) := by
  have hsum_all :
      Tendsto (fun n : ℕ => ∑ k ∈ Icc 2 (n / 2), componentGapTerm p n k) atTop (𝓝 0) := by
    refine (by simpa using (tendsto_componentGap_pair hp).add (tendsto_componentGap_tail hp) :
      Tendsto (fun n => componentGapTerm p n 2 + ∑ k ∈ Icc 3 (n / 2), componentGapTerm p n k)
        atTop (𝓝 0)).congr' ?_
    filter_upwards [eventually_ge_atTop 4] with n hn4
    rw [show Icc 2 (n / 2) = insert 2 (Icc 3 (n / 2)) from by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
      Finset.sum_insert (by simp : (2 : ℕ) ∉ Icc 3 (n / 2))]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum_all
    (Eventually.of_forall fun _ => measureReal_nonneg) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn1
  dsimp only [componentGapTerm]
  simpa only [Fintype.card_fin] using
    @binomialRandom_real_forall_not_isIsolated_and_not_connected_le (Fin n) _
      (Fin.pos_iff_nonempty.mp hn1) (p n)

/-- **Erdős–Rényi connectivity threshold (constant case)**: if `n p(n) - log n → c`, then
`G(Fin n, p n)` is connected with probability tending to `exp (-exp (-c))`. -/
theorem tendsto_binomialRandom_real_connected_nhds {p : ℕ → I} {c : ℝ}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ) - Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => G(Fin n, p n).real {G | G.Connected})
      atTop (𝓝 (Real.exp (-Real.exp (-c)))) := by
  have hiso := tendsto_binomialRandom_real_forall_not_isIsolated_nhds hp
  have hgap := tendsto_binomialRandom_real_forall_not_isIsolated_and_not_connected hp
  have hdiff : Tendsto (fun n : ℕ =>
      G(Fin n, p n).real {G | ∀ v, ¬G.IsIsolated v} -
        G(Fin n, p n).real {G | (∀ v, ¬G.IsIsolated v) ∧ ¬G.Connected})
      atTop (𝓝 (Real.exp (-Real.exp (-c)))) := by
    simpa using hiso.sub hgap
  refine hdiff.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn2
  have hsdiff :
      {G : SimpleGraph (Fin n) | ∀ v, ¬G.IsIsolated v} \ {G | G.Connected} =
        {G | (∀ v, ¬G.IsIsolated v) ∧ ¬G.Connected} := rfl
  rw [← hsdiff, measureReal_sdiff (@setOf_connected_subset (Fin n)
      (Fin.nontrivial_iff_two_le.mpr hn2)) MeasurableSet.of_discrete]
  ring

end ComponentGap

end SimpleGraph
