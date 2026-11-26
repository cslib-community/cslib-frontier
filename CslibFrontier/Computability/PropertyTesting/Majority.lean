/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.LocalTest.DecisionTree
public import CslibFrontier.Foundations.Data.BitString.Basic
public import CslibFrontier.Foundations.Data.BitString.Threshold
public import Mathlib.Data.Nat.Log
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
import CslibFrontier.Foundations.Data.BitString.Weight.ZeroExtend
import CslibFrontier.Probability.HypothesisSelection.LeCamBirge
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Tactic.Linarith

/-!
# Testing strict majority by sampling

The probe-bound step of [Goldreich2007DraftR5, Exercise 10.9, p. 498] samples independently with
replacement from a power-of-two range, treating out-of-range positions as zeros.
The test compares the observed fraction of ones to a threshold between
the minimum member density and the maximum density allowed by the farness promise.
A nonmember can reach strict majority by changing just enough zeros to ones, so being far
implies a gap in density even when the input length is odd.

The proof uses Hoeffding concentration and the existing local-test decision-tree semantics.
Each probe uses a block of `Nat.log 2 n + 1` fair bits. The decision-tree model
does not certify running time in the direct-access model of Definition 10.10.

## Main definitions

* `Cslib.BitString.majorityTester`: the local test with a rational tolerance.
* `Cslib.BitString.majoritySampleAccepts`: the natural number comparison used after sampling.

## Main results

* `Cslib.BitString.majorityTester_spec`: completeness, soundness and worst-case probe cost.
* `Cslib.BitString.majorityTester_passes_iff_sampleAccepts`: a pointwise bridge from binary
  addresses and a sampled count to the local test's verdict.
* `Cslib.BitString.exists_majorityTester_probeBound`: a fixed probe count works at every length
  for each positive real distance.
-/

public section

namespace Cslib.BitString

open Finset Cslib.PCP
open scoped BigOperators

private def sampleAnswers {n k : ℕ} (r : Fin k → BitString (Nat.log 2 n + 1))
    (a : BitString k) : BitString k :=
  fun i => if (equivFin _ (r i)).val < n then a i else false

/-- Sample one binary address per probe. For an out-of-range address the query uses index
zero and its answer is discarded. Accept when the resulting fraction of ones is at least
the minimum padded member density minus one quarter of the tolerance. -/
def majorityTester (n k : ℕ) [NeZero n] (δ : ℚ) :
    LocalTest (Fin n) (Fin k → BitString (Nat.log 2 n + 1)) (Fin k) Bool where
  query r i := if h : (equivFin _ (r i)).val < n then ⟨_, h⟩ else 0
  Accepts r a := ((n / 2 + 1 : ℕ) : ℚ) / (2 ^ (Nat.log 2 n + 1) : ℕ) -
    δ / 4 ≤ (weight (sampleAnswers r a) : ℚ) / k

@[no_expose] instance (n k : ℕ) [NeZero n] (δ : ℚ) (r : Fin k → BitString (Nat.log 2 n + 1))
    (a : BitString k) :
    Decidable ((majorityTester n k δ).Accepts r a) := by
  change Decidable (((n / 2 + 1 : ℕ) : ℚ) / (2 ^ (Nat.log 2 n + 1) : ℕ) -
    δ / 4 ≤ (weight (sampleAnswers r a) : ℚ) / k)
  infer_instance

private theorem sampleAnswers_query {n k : ℕ} [NeZero n] (δ : ℚ) (x : BitString n)
    (r : Fin k → BitString (Nat.log 2 n + 1)) (i : Fin k) :
    sampleAnswers r (fun j => x ((majorityTester n k δ).query r j)) i =
      zeroExtend x (equivFin _ (r i)) := by
  by_cases h : (equivFin _ (r i)).val < n <;>
    simp [sampleAnswers, majorityTester, zeroExtend, h]

/-- The sampler's decision from the input length and the count of sampled ones, using only
natural number arithmetic. The numerator of the tolerance is interpreted as nonnegative. -/
@[expose] def majoritySampleAccepts (n k : ℕ) (δ : ℚ) (ones : ℕ) : Prop :=
  4 * δ.den * k * (n / 2 + 1) ≤
    2 ^ (Nat.log 2 n + 1) * (4 * δ.den * ones + δ.num.toNat * k)

instance (n k : ℕ) (δ : ℚ) (ones : ℕ) :
    Decidable (majoritySampleAccepts n k δ ones) := by
  unfold majoritySampleAccepts
  infer_instance

/-- For each fixed seed, counting ones returned at its binary addresses (with out-of-range
addresses answered by zero) and applying the natural comparison gives the same verdict as
the local test. -/
theorem majorityTester_passes_iff_sampleAccepts {n k : ℕ} [NeZero n] {δ : ℚ}
    (hk : 0 < k) (hδ : 0 ≤ δ) (x : BitString n) (r : Fin k → BitString (Nat.log 2 n + 1)) :
    (majorityTester n k δ).Passes x r ↔
      majoritySampleAccepts n k δ (weight fun i => zeroExtend x (equivFin _ (r i))) := by
  let M := 2 ^ (Nat.log 2 n + 1)
  let s := weight (fun i => zeroExtend x (equivFin _ (r i)))
  let b := n / 2 + 1
  have hs : weight (sampleAnswers r (fun i => x ((majorityTester n k δ).query r i))) = s :=
    congrArg weight (funext (sampleAnswers_query δ x r))
  have hδ4 : δ / 4 = (δ.num.toNat : ℚ) / δ.den / 4 := by
    conv_lhs => rw [← Rat.num_div_den δ, ← Int.toNat_of_nonneg (Rat.num_nonneg.mpr hδ),
      Int.cast_natCast]
  have hden : (0 : ℚ) < δ.den := Nat.cast_pos.mpr δ.den_pos
  have hk' : (0 : ℚ) < k := Nat.cast_pos.mpr hk
  have hM : (0 : ℚ) < (M : ℕ) := by positivity
  change (b : ℚ) / (M : ℕ) - δ / 4 ≤ (weight (sampleAnswers r _) : ℚ) / k ↔
    4 * δ.den * k * b ≤ M * (4 * δ.den * s + δ.num.toNat * k)
  rw [hs, sub_le_iff_le_add, hδ4]
  field_simp
  norm_cast
  simp only [mul_comm, mul_left_comm, mul_assoc, add_comm, left_distrib]

private theorem exists_majority_close {n : ℕ} (hn : 0 < n) (x : BitString n) :
    ∃ y : BitString n, strictMajority n y = true ∧
      hammingDist x y ≤ n / 2 + 1 - weight x := by
  let ones := univ.filter fun i => x i = true
  let zeros := univ.filter fun i => x i = false
  have hzeros : #zeros = n - weight x := by
    simp [zeros, card_filter_eq_false_eq_card_sub_weight]
  obtain ⟨S, hS, hcard⟩ := exists_subset_card_eq (s := zeros)
    (n := n / 2 + 1 - weight x) (by rw [hzeros]; omega)
  let y : BitString n := fun i => if i ∈ S then true else x i
  have hdisj : Disjoint S ones := disjoint_left.mpr fun i hi hi' =>
    Bool.false_ne_true ((mem_filter.mp (hS hi)).2.symm.trans (mem_filter.mp hi').2)
  have hy : (univ.filter fun i => y i = true) = S ∪ ones :=
    ext fun i => by by_cases hi : i ∈ S <;> simp [y, ones, hi]
  have hdiff : (univ.filter fun i => x i ≠ y i) = S :=
    ext fun i => by
      by_cases hi : i ∈ S <;> simp [y, hi, fun j (hj : j ∈ S) => (mem_filter.mp (hS hj)).2]
  refine ⟨y, strictMajority_eq_true_iff.mpr ?_, ?_⟩
  · change n / 2 < #(univ.filter fun i => y i = true)
    rw [hy, card_union_of_disjoint hdisj, hcard]
    change n / 2 < n / 2 + 1 - weight x + weight x
    omega
  · rw [hammingDist, hdiff, hcard]

open Cslib.Probability.PMF Cslib.Probability.HypothesisSelection in
private theorem majorityTester_error {n k : ℕ} [NeZero n] {δ : ℚ}
    (hδ : 0 < δ) (x : BitString n) :
    (strictMajority n x = true →
      1 - (majorityTester n k δ).acceptProb x ≤ Real.exp (-2 * k * ((δ : ℝ) / 4) ^ 2)) ∧
    ((∀ y : BitString n, strictMajority n y = true →
      (δ : ℝ) * n ≤ hammingDist x y) →
      (majorityTester n k δ).acceptProb x ≤ Real.exp (-2 * k * ((δ : ℝ) / 4) ^ 2)) := by
  classical
  let w := Nat.log 2 n + 1
  let M := 2 ^ w
  let x' : BitString M := zeroExtend x
  let A := univ.filter fun u : BitString w => x' (equivFin w u) = true
  let p := uniformOfFintype (BitString w)
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hM : n ≤ M := (Nat.lt_pow_succ_log_self Nat.one_lt_two n).le
  have hM' : M ≤ 2 * n := ((pow_succ 2 (Nat.log 2 n)).trans (mul_comm _ _)).trans_le
    (Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 hn.ne'))
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hn.trans_le hM
  have hp : (p.toOuterMeasure (A : Set (BitString w))).toReal = (weight x : ℝ) / M := by
    rw [toOuterMeasure_uniformOfFintype_toReal]
    have hcard : #A = weight x' := by
      rw [weight]
      apply card_equiv (equivFin w)
      simp [A]
    have hfilt : univ.filter (· ∈ (A : Set (BitString w))) = A := by
      ext u
      simp
    rw [hfilt, hcard, BitString.card, weight_zeroExtend hM x]
  have hemp (r : Fin k → BitString w) :
      empiricalMass A r = (weight (sampleAnswers r
        (fun i => x ((majorityTester n k δ).query r i))) : ℝ) / k := by
    rw [empiricalMass, weight_eq_sum_toNat, Nat.cast_sum]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [sampleAnswers_query]
    change (if r i ∈ A then (1 : ℝ) else 0) = (x' (equivFin w (r i))).toNat
    cases h : x' (equivFin w (r i)) <;> simp [A, h]
  have hpasses (r : Fin k → BitString w) :
      (majorityTester n k δ).Passes x r ↔
        ((n / 2 + 1 : ℕ) : ℝ) / M - (δ : ℝ) / 4 ≤ empiricalMass A r := by
    change ((n / 2 + 1 : ℕ) : ℚ) / (M : ℕ) - δ / 4 ≤ _ ↔ _
    simpa only [hemp, Rat.cast_div, Rat.cast_sub, Rat.cast_natCast, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ) (p := (n / 2 + 1 : ℕ) / (M : ℕ) - δ / 4) (q := (weight _ : ℚ) / k)).symm
  have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδ
  have hquarter : 0 ≤ (δ : ℝ) / 4 := by positivity
  let μ := uniformOfFintype (Fin k → BitString w)
  let event : Set (Fin k → BitString w) := {r | (majorityTester n k δ).Passes x r}
  have hprob : (majorityTester n k δ).acceptProb x = (μ.toOuterMeasure event).toReal := by
    rw [LocalTest.acceptProb_eq_card_div, toOuterMeasure_uniformOfFintype_toReal]
    congr 3
    ext r
    simp [event]
  constructor
  · intro hx
    have hmean : ((n / 2 + 1 : ℕ) : ℝ) / M ≤ (p.toOuterMeasure (A : Set (BitString w))).toReal := by
      rw [hp]
      exact div_le_div_of_nonneg_right (by exact_mod_cast strictMajority_eq_true_iff.mp hx) hMpos.le
    rw [hprob, ← eq_sub_of_add_eq' (toOuterMeasure_toReal_add_compl μ event)]
    refine (toOuterMeasure_toReal_mono μ ?_).trans
      (iid_uniformOfFintype (α := BitString w) k ▸
        toOuterMeasure_empiricalMass_le_sub_le p A k hquarter)
    exact fun r hr => Set.mem_ofPred.mpr (by linarith [mt (hpasses r).mpr hr])
  · intro hfar
    obtain ⟨y, hy, hd⟩ := exists_majority_close hn x
    have hdist : (δ : ℝ) * n ≤ ((n / 2 + 1 - weight x : ℕ) : ℝ) :=
      (hfar y hy).trans (by exact_mod_cast hd)
    have hmean : (p.toOuterMeasure (A : Set (BitString w))).toReal + (δ : ℝ) / 2 ≤
        ((n / 2 + 1 : ℕ) : ℝ) / M := by
      rw [hp, add_comm, add_div_eq_mul_add_div _ _ hMpos.ne',
        div_le_div_iff_of_pos_right hMpos]
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hδn := mul_pos hδR hnR
      have hw : weight x ≤ n / 2 + 1 := by
        have hdiff : 0 < n / 2 + 1 - weight x := by exact_mod_cast hδn.trans_le hdist
        omega
      rw [Nat.cast_sub hw] at hdist
      have hscale := mul_le_mul_of_nonneg_left (show (M : ℝ) ≤ 2 * n by exact_mod_cast hM')
        hquarter
      linarith
    rw [hprob]
    refine (toOuterMeasure_toReal_mono μ ?_).trans
      (iid_uniformOfFintype (α := BitString w) k ▸
        toOuterMeasure_add_le_empiricalMass_le p A k hquarter)
    exact fun r hr => Set.mem_ofPred.mpr (by linarith [(hpasses r).mp hr])

/-- With `16 ≤ k δ²`, every seed probes at most `k` positions. The test accepts members
with probability at least `2/3` and accepts inputs at relative Hamming distance at least
`δ` from every member with probability at most `1/3`. -/
theorem majorityTester_spec {n k : ℕ} [NeZero n] {δ : ℚ} (hδ : 0 < δ)
    (hk : (16 : ℝ) ≤ k * (δ : ℝ) ^ 2) :
    (∀ r, ((majorityTester n k δ).decisionTree r).depth ≤ k) ∧
    (∀ x, strictMajority n x = true → 2 / 3 ≤ (majorityTester n k δ).acceptProb x) ∧
    (∀ x, (∀ y, strictMajority n y = true → (δ : ℝ) * n ≤ hammingDist x y) →
      (majorityTester n k δ).acceptProb x ≤ 1 / 3) := by
  have hexp : Real.exp (-2 * k * ((δ : ℝ) / 4) ^ 2) ≤ 1 / 3 :=
    (Real.exp_le_exp.mpr (by linarith)).trans Real.exp_neg_two_le_one_third
  refine ⟨fun r => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · simpa only [FinEnum.card_fin] using (majorityTester n k δ).depth_decisionTree_le r
  · linarith [((majorityTester_error hδ x).1 hx).trans hexp]
  · exact ((majorityTester_error hδ x).2 hx).trans hexp

/-- The probe-bound step for strict majority gives one budget at all lengths for every positive
real distance. Probabilities are
over the uniform seed of `k` blocks of `Nat.log 2 n + 1` fair bits. At length zero the tree
rejects without querying. -/
theorem exists_majorityTester_probeBound {δ : ℝ} (hδ : 0 < δ) :
    ∃ (k : ℕ) (T : ∀ n, (Fin k → BitString (Nat.log 2 n + 1)) → DecisionTree (Fin n) Bool),
      (∀ n r, (T n r).depth ≤ k) ∧
      (∀ n x, strictMajority n x = true →
        2 / 3 ≤ 𝔼 r, if (T n r).eval x = true then (1 : ℝ) else 0) ∧
      (∀ n x, (∀ y, strictMajority n y = true → δ * n ≤ hammingDist x y) →
        (𝔼 r, if (T n r).eval x = true then (1 : ℝ) else 0) ≤ 1 / 3) := by
  obtain ⟨q, hq, hqδ⟩ := exists_rat_btwn hδ
  obtain ⟨k, hk⟩ := exists_nat_ge (16 / (q : ℝ) ^ 2)
  have hbudget : (16 : ℝ) ≤ k * (q : ℝ) ^ 2 := (div_le_iff₀ (pow_pos hq _)).mp hk
  have hqpos : 0 < q := by exact_mod_cast hq
  let T (n : ℕ) (r : Fin k → BitString (Nat.log 2 n + 1)) : DecisionTree (Fin n) Bool :=
    if hn : n = 0 then .leaf false
    else
      let _ : NeZero n := ⟨hn⟩
      (majorityTester n k q).decisionTree r
  refine ⟨k, T, fun n r => ?_, fun n x hx => ?_, fun n x hx => ?_⟩ <;> by_cases hn : n = 0
  · simp [T, hn]
  · let _ : NeZero n := ⟨hn⟩
    simpa only [T, dite_eq_right hn] using (majorityTester_spec hqpos hbudget).1 r
  · subst hn
    have := strictMajority_eq_true_iff.mp hx
    have := weight_le_length x
    omega
  · let _ : NeZero n := ⟨hn⟩
    simpa only [T, dite_eq_right hn, LocalTest.acceptProb_eq_expect_decisionTree] using
      (majorityTester_spec hqpos hbudget).2.1 x hx
  · simp [T, hn]
  · let _ : NeZero n := ⟨hn⟩
    simpa only [T, dite_eq_right hn, LocalTest.acceptProb_eq_expect_decisionTree] using
      (majorityTester_spec hqpos hbudget).2.2 x (fun y hy =>
        (mul_le_mul_of_nonneg_right hqδ.le (Nat.cast_nonneg n)).trans (hx y hy))

end Cslib.BitString
