/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.PlantedClique.CommonNeighborPolyTime
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Common-neighbor recovery above every fixed square-root threshold

The seed size depends only on the fixed positive constant in `k ≥ c √n`. Geometric shrinkage
of the common neighborhood then puts its retained clique in the base solver's recovery regime.
The exceptional probabilities vanish: the neighborhood-size tail is exponentially small in
`n`, the recovery and outside-degree tails are exponentially small in `k`, and the first-moment
bound for an outside clique of size `⌊k / 4⌋` tends to zero.

`exists_commonNeighborRecover_ppt_tendsto_failure` supplies one explicitly specified native
program for each fixed `c > 0`. The same program works for every target schedule eventually
above `c √n` and every prior on hidden sets of those sizes. The high-probability claim concerns
exact recovery of the hidden set. All graph construction, seed enumeration, reduced solving,
lifting and verification are charged by the native certificate.

This completes the constant-reduction mechanism of Section 2.3 of
[AlonKrivelevichSudakov1998] using the verified integer matrix-power algorithm as its base.
The literal raw-adjacency second-eigenvector specification and its mathematical correctness
are treated separately in `Eigenvector` and `EigenvectorFinal`.
-/

public section

namespace Cslib.Algorithms.PlantedClique

open Filter Real
open scoped Topology

private theorem commonNeighbor_size_promise {n k s : ℕ} {c : ℝ}
    (hc : 0 < c) (hsize : c * sqrt n ≤ k)
    (hs : 16 * (1024 : ℝ) ^ 2 * ((2 : ℝ) ^ s)⁻¹ ≤ c ^ 2)
    (hks : 2 * s ≤ k) (hk : 8 * 1024 ^ 2 ≤ k) :
    1024 * sqrt ((k : ℝ) + 2 * n * ((2 : ℝ) ^ s)⁻¹) ≤ (k - s : ℕ) := by
  have hsk : s ≤ k := by omega
  have hks' : 2 * (s : ℝ) ≤ k := by exact_mod_cast hks
  have hk' : 8 * (1024 : ℝ) ^ 2 ≤ k := by exact_mod_cast hk
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ c * sqrt n) hsize
  simp only [← sq, mul_pow, sq_sqrt (Nat.cast_nonneg n)] at hsq
  have hsmall := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg n)
  have hlarge := mul_le_mul_of_nonneg_right hk' (Nat.cast_nonneg k)
  have hhalf : (k : ℝ) / 2 ≤ (k - s : ℕ) := by
    rw [Nat.cast_sub hsk]
    linarith
  have hhalfSq := mul_self_le_mul_self (by positivity : 0 ≤ (k : ℝ) / 2) hhalf
  have hrad : 0 ≤ (k : ℝ) + 2 * n * ((2 : ℝ) ^ s)⁻¹ := by positivity
  have htotal : (1024 * sqrt ((k : ℝ) + 2 * n * ((2 : ℝ) ^ s)⁻¹)) ^ 2 ≤
      ((k - s : ℕ) : ℝ) ^ 2 := by
    rw [mul_pow, sq_sqrt hrad]
    nlinarith
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp htotal

private theorem exists_commonNeighbor_shrink {c : ℝ} (hc : 0 < c) :
    ∃ s : ℕ, 16 * (1024 : ℝ) ^ 2 * ((2 : ℝ) ^ s)⁻¹ ≤ c ^ 2 := by
  have h : Tendsto (fun s : ℕ => 16 * (1024 : ℝ) ^ 2 * ((2 : ℝ) ^ s)⁻¹)
      atTop (𝓝 0) := by
    simpa only [inv_pow, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)).const_mul
        (16 * (1024 : ℝ) ^ 2)
  exact (h.eventually (gt_mem_nhds (sq_pos_of_pos hc))).exists.imp fun _ h => h.le

private theorem tendsto_size_atTop {k : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hk : ∀ᶠ n : ℕ in atTop, c * sqrt n ≤ (k n : ℝ)) :
    Tendsto (fun n => (k n : ℝ)) atTop atTop :=
  tendsto_atTop_mono' _ hk
    ((tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hc)

private theorem eventually_sub_size {k : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hk : ∀ᶠ n : ℕ in atTop, c * sqrt n ≤ (k n : ℝ)) (s : ℕ) :
    ∀ᶠ n : ℕ in atTop, c / 2 * sqrt n ≤ (k n - s : ℕ) := by
  have hlarge : ∀ᶠ n : ℕ in atTop, 2 * (s : ℝ) ≤ c * sqrt n :=
    ((tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hc).eventually
      (eventually_ge_atTop _)
  filter_upwards [hk, hlarge] with n hn hlarge
  have hsk : s ≤ k n := by exact_mod_cast (by linarith : (s : ℝ) ≤ k n)
  rw [Nat.cast_sub hsk]
  linarith

private theorem tendsto_nat_mul_exp_neg_sqrt {b : ℝ} (hb : 0 < b) :
    Tendsto (fun n : ℕ => (n : ℝ) * exp (-b * sqrt n)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 b hb).comp
    (tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  simpa only [Function.comp_def, rpow_two, sq_sqrt (Nat.cast_nonneg _)] using h

private theorem tendsto_nat_mul_exp_neg_size {k : ℕ → ℕ} {c a : ℝ}
    (hc : 0 < c) (ha : 0 < a) (hk : ∀ᶠ n : ℕ in atTop, c * sqrt n ≤ (k n : ℝ)) :
    Tendsto (fun n : ℕ => (n : ℝ) * exp (-a * k n)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) _
    (tendsto_nat_mul_exp_neg_sqrt (mul_pos ha hc))
  filter_upwards [hk] with n hn
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
  apply exp_le_exp.mpr
  nlinarith

private theorem choose_mul_inv_pow_le_exp {n r : ℕ} (hn : 0 < n)
    (hlog : log n + 1 ≤ ((r : ℝ) - 1) / 2 * log 2) :
    (n.choose r : ℝ) * ((2 : ℝ) ^ r.choose 2)⁻¹ ≤ exp (-(r : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnpow : (n : ℝ) ^ r = exp ((r : ℝ) * log n) := by
    rw [exp_natCast_mul, exp_log hnR]
  have htwo : (2 : ℝ) ^ r.choose 2 = exp ((r.choose 2 : ℝ) * log 2) := by
    rw [exp_natCast_mul, exp_log (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ (n : ℝ) ^ r * ((2 : ℝ) ^ r.choose 2)⁻¹ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Nat.choose_le_pow n r
    _ = exp ((r : ℝ) * log n - ((r : ℝ) * (r - 1) / 2) * log 2) := by
      rw [hnpow, htwo, ← exp_neg, ← exp_add, Nat.cast_choose_two]
      rfl
    _ ≤ _ := exp_le_exp.mpr (by
      have h := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg r)
      nlinarith)

private theorem eventually_choose_log_bound {k : ℕ → ℕ} {c : ℝ}
    (hc : 0 < c) (hk : ∀ᶠ n : ℕ in atTop, c * sqrt n ≤ (k n : ℝ)) :
    ∀ᶠ n : ℕ in atTop, log n + 1 ≤ (((k n / 4 : ℕ) : ℝ) - 1) / 2 * log 2 := by
  have hlog := (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).bound
    (show 0 < c / 64 by positivity)
  have hlogN := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hlog
  have hlarge : ∀ᶠ n : ℕ in atTop, 64 ≤ c * sqrt n :=
    ((tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hc).eventually
      (eventually_ge_atTop _)
  have hlog2 : (1 : ℝ) / 2 ≤ log 2 := by
    have h := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  filter_upwards [hk, hlogN, hlarge] with n hn hlogn hlarge
  have hlogn' : log n ≤ c / 64 * sqrt n := by
    apply (le_abs_self _).trans
    simpa only [Real.norm_eq_abs, ← sqrt_eq_rpow, abs_of_nonneg (sqrt_nonneg _)] using hlogn
  have hfloor : (k n : ℝ) < 4 * (k n / 4 : ℕ) + 4 := by
    exact_mod_cast (show k n < 4 * (k n / 4) + 4 by omega)
  have hr : (k n : ℝ) / 8 ≤ (k n / 4 : ℕ) - 1 := by linarith
  have hprod := mul_le_mul hr hlog2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by linarith : (0 : ℝ) ≤ (k n / 4 : ℕ) - 1)
  nlinarith

private theorem tendsto_choose_quarter_inv_pow {k : ℕ → ℕ} {c : ℝ}
    (hc : 0 < c) (hk : ∀ᶠ n : ℕ in atTop, c * sqrt n ≤ (k n : ℝ)) :
    Tendsto (fun n => (n.choose (k n / 4) : ℝ) * ((2 : ℝ) ^ (k n / 4).choose 2)⁻¹)
      atTop (𝓝 0) := by
  have hr : Tendsto (fun n => ((k n / 4 : ℕ) : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono' _ (Eventually.of_forall fun n => ?_)
      (tendsto_atTop_add_const_right _ (-1)
        ((tendsto_size_atTop hc hk).atTop_div_const (by norm_num : (0 : ℝ) < 4)))
    have hfloor : (k n : ℝ) < 4 * (k n / 4 : ℕ) + 4 := by
      exact_mod_cast (show k n < 4 * (k n / 4) + 4 by omega)
    linarith
  apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) _
    (tendsto_exp_neg_atTop_nhds_zero.comp hr)
  filter_upwards [eventually_choose_log_bound hc hk, eventually_gt_atTop 0] with n hn hn0
  exact choose_mul_inv_pow_le_exp hn0 hn

private theorem tendsto_commonNeighbor_error {k : ℕ → ℕ} {c : ℝ}
    (hc : 0 < c) (hk : ∀ᶠ n : ℕ in atTop, c * sqrt n ≤ (k n : ℝ)) (s : ℕ) :
    Tendsto (fun n : ℕ =>
      (exp (-2 * n * (((2 : ℝ) ^ s)⁻¹) ^ 2) +
        (2 * exp (-((k n - s : ℕ) : ℝ)) + n * exp (-((k n - s : ℕ) : ℝ) / 32))) +
      (n * exp (-(k n : ℝ) / 32) +
        n.choose (k n / 4) * ((2 : ℝ) ^ (k n / 4).choose 2)⁻¹)) atTop (𝓝 0) := by
  have htail : Tendsto (fun n : ℕ => exp (-2 * n * (((2 : ℝ) ^ s)⁻¹) ^ 2))
      atTop (𝓝 0) := by
    have h := tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop
        (by positivity : 0 < 2 * (((2 : ℝ) ^ s)⁻¹) ^ 2))
    convert h using 1
    ext n
    congr 1
    ring
  have hks := eventually_sub_size hc hk s
  have hc2 : 0 < c / 2 := by positivity
  have hfirst := (tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_size_atTop hc2 hks)).const_mul 2
  have hdegree : Tendsto
      (fun n : ℕ => (n : ℝ) * exp (-((k n - s : ℕ) : ℝ) / 32)) atTop (𝓝 0) := by
    simpa only [neg_div, div_eq_mul_inv, one_mul, neg_mul, mul_neg, mul_comm] using
      tendsto_nat_mul_exp_neg_size hc2 (by norm_num : (0 : ℝ) < 1 / 32) hks
  have huniqueness : Tendsto (fun n : ℕ => (n : ℝ) * exp (-(k n : ℝ) / 32))
      atTop (𝓝 0) := by
    simpa only [neg_div, div_eq_mul_inv, one_mul, neg_mul, mul_neg, mul_comm] using
      tendsto_nat_mul_exp_neg_size hc (by norm_num : (0 : ℝ) < 1 / 32) hk
  simpa only [Function.comp_def, mul_zero, zero_add] using
    (htail.add (hfirst.add hdegree)).add (huniqueness.add (tendsto_choose_quarter_inv_pow hc hk))

/-- For each fixed positive square-root coefficient, one fixed seed size puts every eventually
admissible target schedule in the common-neighbor recovery regime for all sufficiently large
dimensions. The seed size is chosen before the schedule and does not grow with the input. -/
theorem exists_commonNeighbor_seedSize {c : ℝ} (hc : 0 < c) :
    ∃ s : ℕ, ∀ k : ℕ → ℕ,
      (∀ᶠ n : ℕ in atTop, c * sqrt n ≤ (k n : ℝ)) →
      ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ 6 ≤ k n - s ∧
        1024 * sqrt ((k n : ℝ) + 2 * n * ((2 : ℝ) ^ s)⁻¹) ≤ (k n - s : ℕ) := by
  obtain ⟨s, hs⟩ := exists_commonNeighbor_shrink hc
  refine ⟨s, fun k hk => ?_⟩
  have hlarge := tendsto_size_atTop hc hk
  have hremaining := tendsto_size_atTop (by positivity : 0 < c / 2)
    (eventually_sub_size hc hk s)
  filter_upwards [hk, eventually_ge_atTop 1,
    hlarge.eventually (eventually_ge_atTop (2 * (s : ℝ))),
    hlarge.eventually (eventually_ge_atTop (8 * (1024 : ℝ) ^ 2)),
    hremaining.eventually (eventually_ge_atTop 6)] with n hn hn1 hn2 hnC hn6
  refine ⟨hn1, by exact_mod_cast hn6, ?_⟩
  exact commonNeighbor_size_promise hc hn hs (by exact_mod_cast hn2) (by exact_mod_cast hnC)

private theorem tendsto_commonNeighborFailureBound {k : ℕ → ℕ} {c : ℝ}
    (hc : 0 < c) (hk : ∀ᶠ n : ℕ in atTop, c * sqrt n ≤ (k n : ℝ)) (s : ℕ)
    (hpromise : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ 6 ≤ k n - s ∧
      1024 * sqrt ((k n : ℝ) + 2 * n * ((2 : ℝ) ^ s)⁻¹) ≤ (k n - s : ℕ)) :
    Tendsto (fun n => commonNeighborFailureBound n (k n) s) atTop (𝓝 0) := by
  have h := ENNReal.tendsto_ofReal (tendsto_commonNeighbor_error hc hk s)
  simp only [ENNReal.ofReal_zero] at h
  apply h.congr'
  filter_upwards [hpromise] with n hn
  simp only [commonNeighborFailureBound, ite_eq_left hn]

open Cslib.Probability Cslib.Probability.PlantedClique Turing.MultiTapeTM

/-- For every fixed `c > 0`, one fixed native polynomial-time program recovers the hidden
clique with probability tending to one whenever `k(n) ≥ c √n` eventually. The seed size is
chosen before the target schedule and before any priors. The priors may be arbitrary laws on
sets of the given cardinalities; the program receives only the dense graph and public target
size. This theorem proves both uniform native admissibility and vanishing actual failure. -/
theorem exists_commonNeighborRecover_ppt_tendsto_failure {c : ℝ} (hc : 0 < c) :
    ∃ s : ℕ,
      IsPPTOn encRecoveryInput (encList encUnary)
        (fun input => pure (commonNeighborRecover recoverInput s input)) ∧
      ∀ (k : ℕ → ℕ) (prior : ∀ n, PMF {S : Finset (Fin n) // S.card = k n}),
        (∀ᶠ n : ℕ in atTop, c * sqrt n ≤ (k n : ℝ)) →
        Tendsto (fun n => (searchProblem (prior n)).experiment
          (fun G => PMF.pure (vertexSet n
            (commonNeighborRecover recoverInput s (RecoveryInput.ofGraph G (k n))))) false)
          atTop (𝓝 0) := by
  obtain ⟨s, hs⟩ := exists_commonNeighbor_seedSize hc
  refine ⟨s,
    (computableInPolyTime_commonNeighborRecover s computableInPolyTime_recoverInput).isPPTOn,
    fun k prior hk => ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_commonNeighborFailureBound hc hk s (hs k hk))
    (fun _ => bot_le) (fun n => commonNeighborRecover_failure_le (prior n) s)

end Cslib.Algorithms.PlantedClique
