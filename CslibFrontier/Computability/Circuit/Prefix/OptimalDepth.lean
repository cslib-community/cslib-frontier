/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Prefix.ConsistentTree
public import CslibFrontier.Computability.Circuit.Prefix.OptimalDepth.CharPoly
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.NumberTheory.Real.GoldenRatio
-- `import all`: reads `exists_rippleOptimalPrefixCircuit` from `ConsistentTree` and private
-- characteristic-polynomial identities (`prefixCharPoly_three_halves_pos`, `pow_recurrence_sub`)
-- from `OptimalDepth.CharPoly` without widening the public export surface.
import all CslibFrontier.Computability.Circuit.Prefix.ConsistentTree
import all CslibFrontier.Computability.Circuit.Prefix.OptimalDepth.CharPoly
import CslibFrontier.Computability.Circuit.Prefix.OptimalDepth.SegmentDecomposition
import CslibFrontier.Computability.Circuit.Prefix.OptimalDepth.TreeBound

/-!
# Minimal depth of optimal fanout-bounded prefix circuits

Following Sergeev [Sergeev2025PrefixDepth], we complete the depth characterization of optimal
(zero-deficiency) fanout-`k` universal prefix circuits. Extracting principal-chain segments directly
from any zero-deficiency universal prefix DAG yields sharp `k = 2` width bounds
(`width_le_one_add_maxCircuitWidthUpper_two`, `width_le_maxCircuitWidthUpper_two`) and general
exponential circuit width upper bounds (`width_le_mul_alphaRoot_pow`) in terms of the unique
positive root `α_k` (`alphaRoot k`) of the characteristic polynomial
`P_k(x) = 2 + x + ⋯ + x^{k-2} - x^k` (`prefixCharPoly k`).

Combining these upper bounds with the constructive lower bounds of
`CslibFrontier.Computability.Circuit.Prefix.ConsistentTree`, we establish that for each fanout bound
`k ≥ 2`, there exists a constant `C ≥ 0` (depending on `k`) such that for every input width
`N ≥ 1`, the minimal depth `D(N, k)` (`optimalPrefixDepth N k`) of an optimal fanout-`k` universal
prefix circuit on `N` inputs satisfies
`|(optimalPrefixDepth N k : ℝ) - Real.logb (alphaRoot k) N| ≤ C`
(`abs_optimalPrefixDepth_sub_logb_le`), together with the exact `k = 2` threshold characterization
(`optimalPrefixDepth_two_le_iff`), strict monotonicity of `α_k` on `k ≥ 2`
(`alphaRoot_strictMonoOn`), and convergence `α_k → φ` (`tendsto_alphaRoot_atTop`).

## Main definitions

* `Cslib.Circuits.Prefix.prefixCharPoly`, `Cslib.Circuits.Prefix.alphaRoot`: characteristic
  polynomial `P_k(x)` and its unique positive root `α_k`.
* `Cslib.Circuits.Prefix.optimalPrefixDepth`: minimal depth `D(N, k)` of an optimal fanout-`k`
  universal prefix circuit on `N` inputs.

## Main results

* `Cslib.Circuits.Prefix.width_le_one_add_maxCircuitWidthUpper_two`,
  `Cslib.Circuits.Prefix.width_le_maxCircuitWidthUpper_two`,
  `Cslib.Circuits.Prefix.width_le_mul_alphaRoot_pow`: sharp `k = 2` and general exponential width
  upper bounds for optimal fanout-`k` universal prefix circuits.
* `Cslib.Circuits.Prefix.prefixCharPoly_alphaRoot`,
  `Cslib.Circuits.Prefix.eq_alphaRoot_of_pos_of_prefixCharPoly_eq_zero`,
  `Cslib.Circuits.Prefix.one_lt_alphaRoot`,
  `Cslib.Circuits.Prefix.alphaRoot_lt_goldenRatio`,
  `Cslib.Circuits.Prefix.three_halves_lt_alphaRoot`,
  `Cslib.Circuits.Prefix.alphaRoot_two`,
  `Cslib.Circuits.Prefix.alphaRoot_strictMonoOn`,
  `Cslib.Circuits.Prefix.tendsto_alphaRoot_atTop`: existence, uniqueness, enclosure, `k = 2` value
  `√2`, strict monotonicity, and convergence `α_k → φ` of `α_k`.
* `Cslib.Circuits.Prefix.exists_optimalPrefixCircuit_depth_eq`,
  `Cslib.Circuits.Prefix.optimalPrefixDepth_one`,
  `Cslib.Circuits.Prefix.optimalPrefixDepth_two_le_iff`,
  `Cslib.Circuits.Prefix.abs_optimalPrefixDepth_sub_logb_le`: attainment of `D(N, k)`, `N = 1`
  base case, exact `k = 2` threshold characterization, and main theorem
  `D(N, k) = log_{α_k} N ± O(1)`.

## References

* [I. S. Sergeev, *A Note on the Depth of Optimal Fanout-Bounded Prefix
  Circuits*][Sergeev2025PrefixDepth]
-/

public section

namespace Cslib.Circuits.Prefix

/-- The segment boundaries telescope: `T D = 1 + ∑_{d < D} (T (d + 1) - T d)`. -/
private theorem eq_one_add_sum_sub {T : ℕ → ℕ} (hT0 : T 0 = 1) {D : ℕ}
    (hlt : ∀ d < D, T d < T (d + 1)) : T D = 1 + ∑ d ∈ Finset.range D, (T (d + 1) - T d) := by
  induction D with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, Nat.add_zero, hT0]
  | succ r ih =>
    rw [Finset.sum_range_succ, ← Nat.add_assoc, ← ih fun d hd => hlt d (by omega)]
    have := hlt r (by omega)
    omega

/-- Exact maximum width bound for optimal fanout-2 prefix circuits of positive depth:
`N ≤ 1 + w_2*(c.depth - 1)` ([Sergeev2025PrefixDepth], p. 3, `w_2(D) = w_2*(D - 1)`). -/
theorem width_le_one_add_maxCircuitWidthUpper_two {N : ℕ} (hN : 1 ≤ N)
    {c : PrefixCircuit N} (hopt : IsOptimalPrefixCircuit c) (hfan : FanoutAtMost c 2)
    (hD : 1 ≤ c.depth) :
    N ≤ 1 + maxCircuitWidthUpper 2 (c.depth - 1) := by
  obtain ⟨T, hT0, hTD, hseg⟩ := optimal_segment_decomposition hN hopt hfan
  set D := c.depth
  rw [← hTD, eq_one_add_sum_sub hT0 fun d hd => (hseg d hd).1]
  unfold maxCircuitWidthUpper
  rw [show D - 1 + 1 = D by omega]
  refine Nat.add_le_add_left (Finset.sum_le_sum fun d hd => ?_) 1
  rw [Finset.mem_range] at hd
  obtain ⟨hTd_lt, I, t, hI_d, _, _, hbud, hfan_t, hd_t, _, hout_at, _, hw_le⟩ := hseg d hd
  rw [maxConsistentWidth_two]
  have hd_bound : T (d + 1) - T d ≤ 2 ^ d :=
    (I.width_le_two_pow).trans (Nat.pow_le_pow_right (by omega) hI_d)
  have hh_bound : T (d + 1) - T d ≤ 2 ^ (D - 1 - d) := by
    rcases t with ⟨st, hasOut, r, isMul, child⟩
    simp only [GenPrefixTree.rootBudget] at hbud
    obtain ⟨_, hch_fan⟩ := hfan_t
    have hch_out (i : Fin r) (s : ℕ) : (child i).outAt s ≤ 1 := by
      have hs := hout_at s
      simp only [GenPrefixTree.outAt] at hs
      have := Finset.single_le_sum (f := fun j : Fin r => (child j).outAt s)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    by_cases hr0 : r = 0
    · subst hr0
      simp only [GenPrefixTree.outCount, Finset.univ_eq_empty, Finset.sum_empty] at hw_le
      have h1 : 1 ≤ 2 ^ (D - 1 - d) := Nat.one_le_pow _ _ (by omega)
      cases hasOut <;> simp only [Bool.false_eq_true, ↓reduceIte] at hw_le <;> omega
    · obtain rfl : r = 1 := by omega
      obtain rfl : hasOut = false := Bool.eq_false_iff.mpr fun h => by
        simp only [h, ↓reduceIte] at hbud; omega
      simp only [GenPrefixTree.outCount, Bool.false_eq_true, ↓reduceIte,
        Nat.zero_add, Fin.sum_univ_one] at hw_le
      have hc0_d : (child 0).depth + 1 ≤
          (GenPrefixTree.node st false 1 isMul child).depth :=
        GenPrefixTree.child_depth_lt 0
      have hc0_ub := (child 0).outCount_le_two_pow (hch_fan 0) (hch_out 0)
      exact hw_le.trans (hc0_ub.trans (Nat.pow_le_pow_right (by omega) (by omega)))
  by_cases hmin : d ≤ D - 1 - d
  · rw [Nat.min_eq_left hmin]; exact hd_bound
  · rw [Nat.min_eq_right (by omega)]; exact hh_bound

/-- Every optimal fanout-2 prefix circuit on `N ≥ 1` inputs satisfies
`N ≤ maxCircuitWidthUpper 2 c.depth` ([Sergeev2025PrefixDepth], p. 3, Eq. (3)). -/
theorem width_le_maxCircuitWidthUpper_two {N : ℕ} (hN : 1 ≤ N)
    {c : PrefixCircuit N} (hopt : IsOptimalPrefixCircuit c) (hfan : FanoutAtMost c 2) :
    N ≤ maxCircuitWidthUpper 2 c.depth := by
  by_cases hD0 : c.depth = 0
  · obtain ⟨T, hT0, hTD, _⟩ := optimal_segment_decomposition hN hopt hfan
    rw [hD0, hT0] at hTD
    rw [hD0, maxCircuitWidthUpper, Finset.sum_range_one, Nat.sub_zero,
      maxConsistentWidth_zero_left le_rfl]
    omega
  · refine (width_le_one_add_maxCircuitWidthUpper_two hN hopt hfan (by omega)).trans ?_
    set D := c.depth
    unfold maxCircuitWidthUpper
    rw [show D - 1 + 1 = D by omega, Finset.sum_range_succ, Nat.sub_self,
      maxConsistentWidth_zero_right (by omega), Nat.add_comm 1]
    refine Nat.add_le_add_right (Finset.sum_le_sum fun d hd => ?_) 1
    rw [maxConsistentWidth_two, maxConsistentWidth_two]
    exact Nat.pow_le_pow_right (by omega) (by omega)


private theorem width_le_vStar {N k : ℕ} (hk : 3 ≤ k) (hN : 1 ≤ N)
    {c : PrefixCircuit N} (hopt : IsOptimalPrefixCircuit c) (hfan : FanoutAtMost c k) :
    (N : ℝ) ≤ vStar k c.depth := by
  obtain ⟨T, hT0, hTD, hseg⟩ := optimal_segment_decomposition hN hopt hfan
  set D := c.depth
  rw [← hTD, eq_one_add_sum_sub hT0 fun d hd => (hseg d hd).1, Nat.cast_add, Nat.cast_one,
    Nat.cast_sum]
  unfold vStar
  rw [Finset.sum_range_succ, Nat.sub_self, V_zero_right, add_comm (1 : ℝ)]
  have h1 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ D := one_le_pow₀ (by norm_num)
  have hsum : (∑ d ∈ Finset.range D, ((T (d + 1) - T d : ℕ) : ℝ)) ≤
      ∑ d ∈ Finset.range D, V k d (D - d) := by
    refine Finset.sum_le_sum fun d hd => ?_
    rw [Finset.mem_range] at hd
    obtain ⟨_, I, t, hI_d, hst, hmax, hbud, hfan_t, hd_t, hval, hout_at, hmul_cnt, hw_le⟩ :=
      hseg d hd
    have hcast : ((T (d + 1) - T d : ℕ) : ℝ) ≤ (t.outCount : ℝ) := by exact_mod_cast hw_le
    have hW := t.outCount_le_W hk d (D - d) k (T d) (T (d + 1)) I le_rfl hI_d (by omega)
      hst hmax (by omega) hfan_t hval hout_at hmul_cnt
    rw [W_eq_V (by omega)] at hW
    exact hcast.trans hW
  linarith


private theorem alphaRoot_pow_le_maxCircuitWidthUpper {k : ℕ} (hk : 2 ≤ k) :
    ∀ D : ℕ, ((alphaRoot k) ^ k)⁻¹ * (alphaRoot k) ^ D ≤ (maxCircuitWidthUpper k D : ℝ) := by
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
    set α := alphaRoot k
    have hα1 := one_lt_alphaRoot hk
    have hα_pos : 0 < α := zero_lt_one.trans hα1
    have hαk_pos : 0 < α ^ k := pow_pos hα_pos k
    by_cases hD : D < k
    · have hpow_le : α ^ D ≤ α ^ k := pow_le_pow_right₀ hα1.le hD.le
      have hlhs_le : (α ^ k)⁻¹ * α ^ D ≤ 1 := by
        have := mul_le_mul_of_nonneg_left hpow_le (inv_nonneg.mpr hαk_pos.le)
        rwa [inv_mul_cancel₀ hαk_pos.ne'] at this
      have hw1 : 1 ≤ maxCircuitWidthUpper k D := by
        rw [maxCircuitWidthUpper]
        conv_lhs => rw [← maxConsistentWidth_zero_left hk (h := D - 0)]
        exact Finset.single_le_sum (f := fun d => maxConsistentWidth k d (D - d))
          (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega : 0 < D + 1))
      exact hlhs_le.trans (by exact_mod_cast hw1)
    · have hkD : k ≤ D := le_of_not_gt hD
      have hrec_α := pow_recurrence_sub hk hkD α
      rw [prefixCharPoly_alphaRoot hk, mul_zero] at hrec_α
      have hαD : α ^ D = (∑ j ∈ Finset.Ico 2 k, α ^ (D - j)) + 2 * α ^ (D - k) := by linarith
      have hlhs : (α ^ k)⁻¹ * α ^ D =
          (∑ j ∈ Finset.Ico 2 k, (α ^ k)⁻¹ * α ^ (D - j)) +
            2 * ((α ^ k)⁻¹ * α ^ (D - k)) := by
        rw [hαD, mul_add, Finset.mul_sum]
        ring
      have hsum_le : (∑ j ∈ Finset.Ico 2 k, (α ^ k)⁻¹ * α ^ (D - j)) ≤
          ∑ j ∈ Finset.Ico 2 k, (maxCircuitWidthUpper k (D - j) : ℝ) :=
        Finset.sum_le_sum fun j hj => ih (D - j) (by simp only [Finset.mem_Ico] at hj; omega)
      have hrec_W_real : (maxCircuitWidthUpper k D : ℝ) =
          (∑ j ∈ Finset.Ico 2 k, (maxCircuitWidthUpper k (D - j) : ℝ)) +
            2 * (maxCircuitWidthUpper k (D - k) : ℝ) + (k : ℝ) := by
        exact_mod_cast maxCircuitWidthUpper_recurrence hk hkD
      linarith [ih (D - k) (by omega), (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

private theorem maxCircuitWidthUpper_zero {k : ℕ} (hk : 2 ≤ k) :
    maxCircuitWidthUpper k 0 = 1 := by
  rw [maxCircuitWidthUpper, Finset.sum_range_one, Nat.sub_zero, maxConsistentWidth_zero_left hk]

/-- Exponential upper bound on the input width of any optimal (zero-deficiency) fanout-`k`
universal prefix circuit in terms of `(alphaRoot k) ^ c.depth` ([Sergeev2025PrefixDepth],
pp. 3–5). -/
theorem width_le_mul_alphaRoot_pow {k : ℕ} (hk : 2 ≤ k) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {N : ℕ}, 1 ≤ N →
      ∀ {c : PrefixCircuit N}, IsOptimalPrefixCircuit c → FanoutAtMost c k →
        (N : ℝ) ≤ A * (alphaRoot k) ^ c.depth := by
  by_cases hk2 : k = 2
  · subst hk2
    refine ⟨4, by norm_num, fun {N} hN {c} hopt hfan => ?_⟩
    set α := alphaRoot 2
    have hα1 := one_lt_alphaRoot (k := 2) le_rfl
    have hα_pos : 0 < α := zero_lt_one.trans hα1
    have hα_sq : α ^ 2 = 2 := by
      have h0 := prefixCharPoly_alphaRoot (k := 2) le_rfl
      unfold prefixCharPoly at h0
      simp only [Nat.reduceSub, Finset.Ico_self, Finset.sum_empty, add_zero] at h0
      linarith
    have hu_bound (D : ℕ) : (maxCircuitWidthUpper 2 D : ℝ) + 2 ≤ 4 * α ^ D := by
      induction D using Nat.twoStepInduction with
      | zero =>
        rw [maxCircuitWidthUpper_zero le_rfl, pow_zero]
        norm_num
      | one =>
        have h1 : maxCircuitWidthUpper 2 1 = 2 := by
          rw [maxCircuitWidthUpper, Finset.sum_range_succ, Finset.sum_range_one, Nat.sub_zero,
            Nat.sub_self, maxConsistentWidth_zero_left le_rfl,
            maxConsistentWidth_zero_right le_rfl]
        rw [h1, pow_one, Nat.cast_ofNat]
        linarith only [hα1]
      | more m ih _ =>
        have hrec := maxCircuitWidthUpper_recurrence (k := 2) le_rfl (by lia : 2 ≤ m + 2)
        simp only [Finset.Ico_self, Finset.sum_empty, zero_add, Nat.add_sub_cancel] at hrec
        have hcast : (maxCircuitWidthUpper 2 (m + 2) : ℝ) =
            2 * (maxCircuitWidthUpper 2 m : ℝ) + 2 := by exact_mod_cast hrec
        rw [hcast, pow_add, hα_sq]
        linarith only [ih]
    have hN_r : (N : ℝ) ≤ maxCircuitWidthUpper 2 c.depth :=
      mod_cast width_le_maxCircuitWidthUpper_two hN hopt hfan
    linarith only [hN_r, hu_bound c.depth]
  · have hk3 : 3 ≤ k := by omega
    set α := alphaRoot k
    have hα1 := one_lt_alphaRoot hk
    have hp32 := prefixCharPoly_three_halves_pos hk3
    set b : ℝ := (3 / 2 : ℝ) ^ k / prefixCharPoly k (3 / 2)
    have hb_pos : 0 < b := div_pos (by positivity) hp32
    set A : ℝ := 1 + ∑ m ∈ Finset.range k, (vStar k m + b * (3 / 2 : ℝ) ^ m + 1)
    have hterm_nn (m : ℕ) : 0 ≤ vStar k m + b * (3 / 2 : ℝ) ^ m + 1 :=
      add_nonneg (add_nonneg (Finset.sum_nonneg fun d _ => V_nonneg k d (m - d))
        (mul_nonneg hb_pos.le (by positivity))) zero_le_one
    have hA1 : 1 ≤ A := le_add_of_nonneg_right (Finset.sum_nonneg fun m _ => hterm_nn m)
    set B : ℕ → ℝ := fun D => A * α ^ D - b * (3 / 2 : ℝ) ^ D - 1
    have hV_le_B (D : ℕ) : vStar k D ≤ B D := by
      induction D using Nat.strong_induction_on with
      | _ D ih =>
        by_cases hD : D < k
        · have hle_A : vStar k D + b * (3 / 2 : ℝ) ^ D + 1 ≤ A := by
            linarith [Finset.single_le_sum (fun m _ => hterm_nn m) (Finset.mem_range.mpr hD)]
          have hA_le : A ≤ A * α ^ D := le_mul_of_one_le_right (by linarith) (one_le_pow₀ hα1.le)
          dsimp only [B]
          linarith
        · have hkD : k ≤ D := le_of_not_gt hD
          have hrec_α := pow_recurrence_sub hk hkD α
          rw [prefixCharPoly_alphaRoot hk, mul_zero] at hrec_α
          have hrec_32 := pow_recurrence_sub hk hkD (3 / 2)
          have hb_mul : b * ((3 / 2 : ℝ) ^ (D - k) * prefixCharPoly k (3 / 2)) =
              (3 / 2 : ℝ) ^ D := by
            dsimp only [b]
            rw [div_mul_eq_mul_div, ← mul_assoc, mul_div_cancel_right₀ _ hp32.ne',
              ← pow_add, Nat.add_sub_of_le hkD]
          have hconst : (∑ j ∈ Finset.Ico 2 k, (1 : ℝ)) = ((k - 2 : ℕ) : ℝ) := by
            simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
          have hk_cast : ((k - 1 : ℕ) : ℝ) = ((k - 2 : ℕ) : ℝ) + 1 := by
            rw [show k - 1 = (k - 2) + 1 by omega, Nat.cast_add, Nat.cast_one]
          have hB_rec : B D = (∑ j ∈ Finset.Ico 2 k, B (D - j)) + 2 * B (D - k) +
              (3 / 2 : ℝ) ^ D + ((k - 1 : ℕ) : ℝ) := by
            have hsum_B : ∑ j ∈ Finset.Ico 2 k, B (D - j) =
                A * (∑ j ∈ Finset.Ico 2 k, α ^ (D - j)) -
                  b * (∑ j ∈ Finset.Ico 2 k, (3 / 2 : ℝ) ^ (D - j)) -
                  ((k - 2 : ℕ) : ℝ) := by
              dsimp only [B]
              rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
                ← Finset.mul_sum, hconst]
            dsimp only [B]
            rw [hsum_B, hk_cast]
            linear_combination A * hrec_α - b * hrec_32 + hb_mul
          have hV_rec := vStar_recurrence hk3 hkD
          have hsum_le : ∑ j ∈ Finset.Ico 2 k, vStar k (D - j) ≤
              ∑ j ∈ Finset.Ico 2 k, B (D - j) :=
            Finset.sum_le_sum fun j hj => ih (D - j) (by simp only [Finset.mem_Ico] at hj; omega)
          linarith [ih (D - k) (by omega)]
    refine ⟨A, hA1, fun {N} hN {c} hopt hfan => ?_⟩
    have hVB := hV_le_B c.depth
    dsimp only [B] at hVB
    linarith [width_le_vStar hk3 hN hopt hfan,
      mul_nonneg hb_pos.le (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) c.depth)]

/-- Minimal depth `D(N, k)` of an optimal (zero-deficiency) universal prefix circuit on `N` inputs
with wire fanout bounded by `k` ([Sergeev2025PrefixDepth], p. 2). -/
@[expose] noncomputable def optimalPrefixDepth (N k : ℕ) : ℕ :=
  sInf {D : ℕ | ∃ c : PrefixCircuit N,
    IsOptimalPrefixCircuit c ∧ FanoutAtMost c k ∧ c.depth = D}

/-- For every `k ≥ 2` and `N ≥ 1`, there exists an optimal fanout-`k` universal prefix circuit on
`N` inputs attaining depth `optimalPrefixDepth N k`. -/
theorem exists_optimalPrefixCircuit_depth_eq {N k : ℕ} (hk : 2 ≤ k) (hN : 1 ≤ N) :
    ∃ c : PrefixCircuit N,
      IsOptimalPrefixCircuit c ∧ FanoutAtMost c k ∧ c.depth = optimalPrefixDepth N k := by
  obtain ⟨c₀, _, hopt₀, hfan₀, _⟩ := exists_rippleOptimalPrefixCircuit hk hN
  exact Nat.sInf_mem (s := {D : ℕ | ∃ c : PrefixCircuit N,
    IsOptimalPrefixCircuit c ∧ FanoutAtMost c k ∧ c.depth = D}) ⟨c₀.depth, c₀, hopt₀, hfan₀, rfl⟩

/-- On a single input `N = 1`, the minimal depth of an optimal fanout-`k` prefix circuit is `0`. -/
theorem optimalPrefixDepth_one {k : ℕ} (hk : 2 ≤ k) : optimalPrefixDepth 1 k = 0 := by
  obtain ⟨c₀, _, hopt₀, hfan₀, hd₀⟩ := exists_rippleOptimalPrefixCircuit hk (le_rfl : 1 ≤ 1)
  have hle : optimalPrefixDepth 1 k ≤ c₀.depth := Nat.sInf_le ⟨c₀, hopt₀, hfan₀, rfl⟩
  omega

/-- Exact threshold characterization of `optimalPrefixDepth N 2` for `D ≥ 1` and `N ≥ 1`:
`optimalPrefixDepth N 2 ≤ D` if and only if `N ≤ 1 + maxCircuitWidthUpper 2 (D - 1)`
([Sergeev2025PrefixDepth], pp. 2–3, following Eq. (3)). -/
theorem optimalPrefixDepth_two_le_iff {N D : ℕ} (hN : 1 ≤ N) (hD : 1 ≤ D) :
    optimalPrefixDepth N 2 ≤ D ↔ N ≤ 1 + maxCircuitWidthUpper 2 (D - 1) := by
  constructor
  · intro hle
    by_cases hN1 : N = 1
    · omega
    · obtain ⟨c, hopt, hfan, hd_eq⟩ := exists_optimalPrefixCircuit_depth_eq (k := 2) le_rfl hN
      have hcD_pos : 1 ≤ c.depth := by
        by_contra h0
        have hw := width_le_maxCircuitWidthUpper_two hN hopt hfan
        rw [(by omega : c.depth = 0), maxCircuitWidthUpper_zero le_rfl] at hw
        omega
      have hw := width_le_one_add_maxCircuitWidthUpper_two hN hopt hfan hcD_pos
      refine hw.trans (Nat.add_le_add_left ?_ 1)
      refine monotone_nat_of_le_succ (fun m => ?_) (by omega : c.depth - 1 ≤ D - 1)
      unfold maxCircuitWidthUpper
      rw [Finset.sum_range_succ (n := m + 1)]
      refine le_trans (Finset.sum_le_sum fun d hd => ?_) (Nat.le_add_right _ _)
      rw [Finset.mem_range] at hd
      rw [maxConsistentWidth_two, maxConsistentWidth_two]
      exact Nat.pow_le_pow_right (by omega) (by omega)
  · intro hN_ub
    obtain ⟨c, hopt, hfan, hd_le⟩ :=
      exists_optimalPrefixCircuit_of_le_maxCircuitWidthUpper le_rfl hD hN hN_ub
    exact (Nat.sInf_le (s := {D' : ℕ | ∃ c : PrefixCircuit N,
      IsOptimalPrefixCircuit c ∧ FanoutAtMost c 2 ∧ c.depth = D'}) ⟨c, hopt, hfan, rfl⟩).trans hd_le

/-- **Sergeev's Theorem** ([Sergeev2025PrefixDepth], p. 2): for every fanout bound `k ≥ 2`, there
exists a constant `C ≥ 0` (depending only on `k`) such that for every input width `N ≥ 1`, the
minimal depth `optimalPrefixDepth N k` of an optimal (zero-deficiency) fanout-`k` universal prefix
circuit on `N` inputs satisfies
`|(optimalPrefixDepth N k : ℝ) - Real.logb (alphaRoot k) N| ≤ C`. -/
theorem abs_optimalPrefixDepth_sub_logb_le {k : ℕ} (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      |(optimalPrefixDepth N k : ℝ) - Real.logb (alphaRoot k) N| ≤ C := by
  set α := alphaRoot k
  have hα1 := one_lt_alphaRoot hk
  have hα_pos : 0 < α := zero_lt_one.trans hα1
  obtain ⟨A, hA1, hA_bound⟩ := width_le_mul_alphaRoot_pow hk
  have hlogA_nn : 0 ≤ Real.logb α A := Real.logb_nonneg hα1 hA1
  set C : ℝ := Real.logb α A + ((k : ℝ) + 2)
  have hC_nn : 0 ≤ C := add_nonneg hlogA_nn (by positivity)
  refine ⟨C, hC_nn, fun N hN => ?_⟩
  set D := optimalPrefixDepth N k
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN_ge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN_nn : 0 ≤ Real.logb α N := Real.logb_nonneg hα1 hN_ge1
  have hlow : Real.logb α N - C ≤ (D : ℝ) := by
    obtain ⟨c, hopt, hfan, hd_eq⟩ := exists_optimalPrefixCircuit_depth_eq hk hN
    change c.depth = D at hd_eq
    have hN_ub : (N : ℝ) ≤ A * α ^ D := hd_eq ▸ hA_bound hN hopt hfan
    have hlog_ub := Real.logb_le_logb_of_le hα1 hN_pos hN_ub
    rw [Real.logb_mul (by linarith) (pow_pos hα_pos D).ne', Real.logb_pow,
      Real.logb_self_eq_one hα1, mul_one] at hlog_ub
    dsimp only [C]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hhigh : (D : ℝ) - Real.logb α N ≤ C := by
    by_cases hsmall : D ≤ k + 1
    · have hD_le : (D : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast hsmall
      dsimp only [C]
      linarith
    · have hk2_le : k + 2 ≤ D := by omega
      have hnot_prev : 1 + maxCircuitWidthUpper k (D - 2) < N := by
        by_contra hge
        obtain ⟨c, hopt, hfan, hd_le⟩ := exists_optimalPrefixCircuit_of_le_maxCircuitWidthUpper hk
          (by omega : 1 ≤ D - 1) hN
          (by
            rw [show D - 1 - 1 = D - 2 by omega]
            omega)
        have : D ≤ c.depth := Nat.sInf_le (s := {D' : ℕ | ∃ c : PrefixCircuit N,
          IsOptimalPrefixCircuit c ∧ FanoutAtMost c k ∧ c.depth = D'}) ⟨c, hopt, hfan, rfl⟩
        omega
      have hw_lt : (maxCircuitWidthUpper k (D - 2) : ℝ) < (N : ℝ) := by
        exact_mod_cast (by omega : maxCircuitWidthUpper k (D - 2) < N)
      have hpow_lt : (α ^ k)⁻¹ * α ^ (D - 2) < (N : ℝ) :=
        (alphaRoot_pow_le_maxCircuitWidthUpper hk (D - 2)).trans_lt hw_lt
      have hαD_eq : α ^ D = α ^ (k + 2) * ((α ^ k)⁻¹ * α ^ (D - 2)) := by
        have h1 : α ^ (k + 2) * ((α ^ k)⁻¹ * α ^ (D - 2)) =
            (α ^ k * (α ^ k)⁻¹) * (α ^ 2 * α ^ (D - 2)) := by
          rw [pow_add α k 2]
          ring
        rw [h1, mul_inv_cancel₀ (pow_pos hα_pos k).ne', one_mul, ← pow_add,
          show 2 + (D - 2) = D by omega]
      have hαD_le : α ^ D ≤ α ^ (k + 2) * (N : ℝ) :=
        hαD_eq ▸ mul_le_mul_of_nonneg_left hpow_lt.le (pow_pos hα_pos (k + 2)).le
      have hlog_le := Real.logb_le_logb_of_le hα1 (pow_pos hα_pos D) hαD_le
      rw [Real.logb_pow, Real.logb_self_eq_one hα1, mul_one,
        Real.logb_mul (pow_pos hα_pos (k + 2)).ne' hN_pos.ne',
        Real.logb_pow, Real.logb_self_eq_one hα1, mul_one, Nat.cast_add,
        Nat.cast_ofNat] at hlog_le
      dsimp only [C]
      linarith
  exact abs_sub_le_iff.mpr ⟨hhigh, by linarith⟩

end Cslib.Circuits.Prefix
