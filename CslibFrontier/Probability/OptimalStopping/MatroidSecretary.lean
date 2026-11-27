/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Matroid.Greedy
public import CslibFrontier.Algorithms.Lean.Matroid.Intersection.Konig
public import CslibFrontier.Algorithms.Lean.Matroid.PSystem
public import CslibFrontier.Probability.OptimalStopping.Secretary
public import CslibFrontier.Probability.PMF.Uniform
public import Mathlib.Combinatorics.Matroid.Rank.ENat
import CslibFrontier.Foundations.GroupTheory.Perm.Fixing
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Matroid.Minor.Restrict
import Mathlib.Combinatorics.Matroid.Rank.Finite
import Mathlib.Data.Nat.Log
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Matroid secretary problems: threshold-price and partition algorithms

In the **matroid secretary problem** ([BabaioffImmorlicaKleinberg2007], Section 2), elements of a
finite matroid `M : Matroid α` with nonnegative weights `w : α → ℝ` arrive in uniformly random
order `σ : Fin (Fintype.card α) ≃ α`. Upon each arrival the algorithm makes an irrevocable
accept/reject decision maintaining matroid independence (`M.Indep`), seeking to maximize the total
weight of selected elements relative to an offline maximum-weight independent set.

## Main definitions

* `Cslib.Probability.OptimalStopping.MatroidSecretary.sampleSet`,
  `.postSampleList`: the first `s` elements observed during sampling and the remaining arrival
  stream.
* `Cslib.Probability.OptimalStopping.MatroidSecretary.sampleMax`: maximum weight of a sample
  (`0` on empty samples).
* `Cslib.Probability.OptimalStopping.MatroidSecretary.partitionSelect`,
  `.partitionSecretaryPMF`, `.expectedPartitionSecretary`: independent per-block execution of
  the optimal classical secretary cutoff rule on a unit-capacity partition matroid
  ([BabaioffImmorlicaKleinberg2007], Section 6).
* `Cslib.Probability.OptimalStopping.MatroidSecretary.thresholdPriceRun`,
  `.thresholdPricePMF`, `.expectedThresholdPrice`: the **Threshold Price Algorithm** of
  [BabaioffImmorlicaKleinberg2007], Section 3.2 (filtering `0`-weight items as in Section 6 so
  `0`-weight ties cannot block the maximum element).

## Main results

* `Cslib.Probability.OptimalStopping.MatroidSecretary.card_filter_mem_sample_not_mem_sample`,
  `.one_fourth_le_prob_split`: exact count `s * (n - s) * (n - 2)!` and `≥ 1/4` half-sampling
  split probability for any two distinct elements.
* `Cslib.Probability.OptimalStopping.MatroidSecretary.exp_neg_one_le_successProb_optimalCutoff`:
  for all `n ≥ 1`, `Secretary.successProb (cutoffRule (optimalCutoff n)) n` decreases monotonically
  to `exp (-1)` and hence is at least `exp (-1)`.
* `Cslib.Probability.OptimalStopping.MatroidSecretary.partitionSelect_indep`,
  `.exp_neg_one_mul_sum_le_expectedPartitionSecretary`: `partitionSelect` always produces an
  independent set in `unitPartitionMatroid part` and achieves expected weight at least
  `(1 / e) · w(I)` for every independent set `I` ([BabaioffImmorlicaKleinberg2007], Section 6).
* `Cslib.Probability.OptimalStopping.MatroidSecretary.thresholdPriceRun_indep`,
  `.sum_le_mul_expectedThresholdPrice`, `.sum_le_sixtyFour_clog_mul_expectedThresholdPrice`:
  **Theorem 3.2** of [BabaioffImmorlicaKleinberg2007] (Section 3.2): on well-behaved nonnegative
  weights (`w x = w y → w x = 0` for `x ≠ y`) over a loopless finite matroid (`∀ x, M.Indep {x}`)
  of size `n ≥ 2` and rank `k = M.eRank.toNat`, `Threshold Price` outputs an independent set with
  expected weight at least `OPT / (32 * (⌈log₂ k⌉ + 1))` (and `OPT / (64 * ⌈log₂ k⌉)` for
  `k ≥ 2`). BIK07 states `32 ⌈log₂ k⌉` by writing `1 / log k` for the probability of picking an
  exponent in `{0, …, ⌈log₂ k⌉}`; keeping the exact uniform count `⌈log₂ k⌉ + 1` covers `k = 1`
  as well (`1/32` of `OPT`). Requiring `2 ≤ Fintype.card α` is sharp because `s = ⌈n/2⌉ = 1`
  leaves an empty suffix when `n = 1`.

## References

* [M. Babaioff, N. Immorlica, and R. Kleinberg, *Matroids, Secretary Problems, and Online
  Mechanisms*][BabaioffImmorlicaKleinberg2007], Sections 2, 3.2, and 6
* [E. B. Dynkin, *The optimum choice of the instant for stopping a Markov process*][Dynkin1963]
-/

public section

namespace Cslib.Probability.OptimalStopping.MatroidSecretary

open Cslib.Algorithms.Lean.Matroid
open Cslib.Probability.OptimalStopping
open Cslib.Probability.PMF
open scoped ENNReal

/-! ### Sampling splits under uniform arrival orders -/

section Sampling

local instance instNonemptyPermCard (α : Type*) [Fintype α] :
    Nonempty (Fin (Fintype.card α) ≃ α) :=
  ⟨(Fintype.equivFin α).symm⟩

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The sample set consisting of the first `s` elements in the arrival order `σ`. -/
@[expose] def sampleSet (σ : Fin (Fintype.card α) ≃ α) (s : ℕ) : Finset α :=
  (Finset.univ.filter fun t : Fin (Fintype.card α) => t.val < s).image σ

/-- The post-sample arrival sequence (elements arriving at times `s, …, n - 1` in order). -/
@[expose] def postSampleList (σ : Fin (Fintype.card α) ≃ α) (s : ℕ) : List α :=
  ((List.finRange (Fintype.card α)).drop s).map σ

@[simp]
theorem mem_sampleSet_iff (σ : Fin (Fintype.card α) ≃ α) (s : ℕ) (x : α) :
    x ∈ sampleSet σ s ↔ (σ.symm x).val < s := by
  simp only [sampleSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, ht, rfl⟩
    simpa using ht
  · intro h
    exact ⟨σ.symm x, h, by simp⟩

omit [DecidableEq α] in
@[simp]
theorem mem_postSampleList_iff (σ : Fin (Fintype.card α) ≃ α) (s : ℕ) (x : α) :
    x ∈ postSampleList σ s ↔ s ≤ (σ.symm x).val := by
  simp only [postSampleList, List.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [List.mem_iff_getElem] at ht
    obtain ⟨k, hk, hget⟩ := ht
    have hk_sub : k < Fintype.card α - s := by
      simpa [List.length_drop, List.length_finRange] using hk
    have hk' : s + k < Fintype.card α := by omega
    have htval : t = ⟨s + k, hk'⟩ := by
      rw [← hget, List.getElem_drop, List.getElem_finRange]
      simp
    simp [htval]
  · intro h
    refine ⟨σ.symm x, ?_, by simp⟩
    rw [List.mem_iff_getElem]
    refine ⟨(σ.symm x).val - s, ?_, ?_⟩
    · simp only [List.length_drop, List.length_finRange]
      omega
    · rw [List.getElem_drop, List.getElem_finRange]
      ext
      simp only [Fin.val_cast]
      omega

theorem mem_postSampleList_iff_notMem_sampleSet (σ : Fin (Fintype.card α) ≃ α) (s : ℕ) (x : α) :
    x ∈ postSampleList σ s ↔ x ∉ sampleSet σ s := by
  rw [mem_postSampleList_iff, mem_sampleSet_iff, not_lt]

omit [DecidableEq α] in
theorem postSampleList_nodup (σ : Fin (Fintype.card α) ≃ α) (s : ℕ) :
    (postSampleList σ s).Nodup :=
  List.Nodup.map σ.injective ((List.nodup_finRange _).drop)

theorem sampleSet_nonempty {σ : Fin (Fintype.card α) ≃ α} {s : ℕ}
    (hs : 1 ≤ s) (hn : 1 ≤ Fintype.card α) : (sampleSet σ s).Nonempty :=
  ⟨σ ⟨0, hn⟩, (mem_sampleSet_iff σ s (σ ⟨0, hn⟩)).mpr (by simp; omega)⟩

private theorem card_filter_perm_eq_two {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {p q : Fin n} (hpq : p ≠ q) :
    (Finset.univ.filter fun τ : Equiv.Perm (Fin n) => τ i = p ∧ τ j = q).card =
      Nat.factorial (n - 2) := by
  let U : Finset (Fin n) := {i, j}
  let f : Fin n → Fin n := fun x => if x = i then p else q
  have hUcard : U.card = 2 := Finset.card_pair hij
  have hf : Set.InjOn f U := by
    intro a ha b hb hab
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, U] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · simp only [f, ↓reduceIte, hij.symm] at hab
      exact absurd hab hpq
    · simp only [f, ↓reduceIte, hij.symm] at hab
      exact absurd hab.symm hpq
    · rfl
  have hset : (Finset.univ.filter fun τ : Equiv.Perm (Fin n) => τ i = p ∧ τ j = q) =
      Finset.univ.filter fun τ : Equiv.Perm (Fin n) => ∀ u ∈ U, τ u = f u := by
    ext τ
    simp [Finset.mem_filter, Finset.mem_univ, U, f, hij.symm]
  rw [hset]
  have hres := Equiv.Perm.card_filter_forall_eq_of_injOn U f hf
  rw [Fintype.card_fin, hUcard] at hres
  convert hres

private theorem card_filter_fin_lt (n s : ℕ) (hs : s ≤ n) :
    (Finset.univ.filter fun p : Fin n => p.val < s).card = s := by
  have hset : (Finset.univ.filter fun p : Fin n => p.val < s) =
      (Finset.univ : Finset (Fin s)).map
        ⟨fun k => ⟨k.val, k.isLt.trans_le hs⟩,
          fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩ := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro hp
      exact ⟨⟨p.val, hp⟩, Fin.ext rfl⟩
    · rintro ⟨k, rfl⟩
      exact k.isLt
  rw [hset, Finset.card_map, Finset.card_univ, Fintype.card_fin]

private theorem card_filter_fin_ge (n s : ℕ) (hs : s ≤ n) :
    (Finset.univ.filter fun q : Fin n => s ≤ q.val).card = n - s := by
  have hpart := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (p := fun q : Fin n => q.val < s)
  simp only [Finset.card_univ, Fintype.card_fin, card_filter_fin_lt n s hs, not_lt] at hpart
  omega

/-- For any two distinct elements `a ≠ b` and sample size `s ≤ |α|`, exactly
`s * (|α| - s) * (|α| - 2)!` arrival orders place `a` in the sample and `b` after the sample. -/
theorem card_filter_mem_sample_not_mem_sample {a b : α} (hab : a ≠ b) {s : ℕ}
    (hs : s ≤ Fintype.card α) :
    (Finset.univ.filter fun σ : Fin (Fintype.card α) ≃ α =>
      a ∈ sampleSet σ s ∧ b ∉ sampleSet σ s).card =
      s * (Fintype.card α - s) * Nat.factorial (Fintype.card α - 2) := by
  set n := Fintype.card α
  let e : α ≃ Fin n := Fintype.equivFin α
  let conv : (Fin n ≃ α) ≃ Equiv.Perm (Fin n) :=
    { toFun := fun σ => e.symm.trans σ.symm
      invFun := fun τ => τ.symm.trans e.symm
      left_inv := fun σ => by ext x; simp
      right_inv := fun τ => by ext x; simp }
  have hbij : (Finset.univ.filter fun σ : Fin n ≃ α =>
      a ∈ sampleSet σ s ∧ b ∉ sampleSet σ s).card =
      (Finset.univ.filter fun τ : Equiv.Perm (Fin n) =>
        (τ (e a)).val < s ∧ s ≤ (τ (e b)).val).card := by
    refine Finset.card_bij (fun σ _ => conv σ) ?_ ?_ ?_
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_sampleSet_iff, not_lt] at hσ ⊢
      simpa [conv, Equiv.trans_apply] using hσ
    · intro σ₁ _ σ₂ _ h
      exact conv.injective h
    · intro τ hτ
      refine ⟨conv.symm τ, ?_, conv.apply_symm_apply τ⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_sampleSet_iff, not_lt] at hτ ⊢
      simpa [conv, Equiv.trans_apply] using hτ
  rw [hbij]
  let P : Finset (Fin n) := Finset.univ.filter fun p : Fin n => p.val < s
  let Q : Finset (Fin n) := Finset.univ.filter fun q : Fin n => s ≤ q.val
  let F : Fin n × Fin n → Finset (Equiv.Perm (Fin n)) := fun pq =>
    Finset.univ.filter fun τ : Equiv.Perm (Fin n) => τ (e a) = pq.1 ∧ τ (e b) = pq.2
  have hcover : Finset.univ.filter (fun τ : Equiv.Perm (Fin n) =>
      (τ (e a)).val < s ∧ s ≤ (τ (e b)).val) = (P ×ˢ Q).biUnion F := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_product, P, Q, F]
    exact ⟨fun h => ⟨(τ (e a), τ (e b)), h, rfl, rfl⟩, by rintro ⟨⟨p, q⟩, hpq, rfl, rfl⟩; exact hpq⟩
  have hdisj : ((P ×ˢ Q : Finset (Fin n × Fin n)) : Set (Fin n × Fin n)).PairwiseDisjoint F := by
    rintro ⟨p₁, q₁⟩ _ ⟨p₂, q₂⟩ _ hne
    refine Finset.disjoint_left.mpr fun τ h₁ h₂ => hne ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, F] at h₁ h₂
    exact Prod.ext (h₁.1.symm.trans h₂.1) (h₁.2.symm.trans h₂.2)
  rw [hcover, Finset.card_biUnion hdisj]
  have hfib : ∀ pq ∈ P ×ˢ Q, (F pq).card = Nat.factorial (n - 2) := by
    rintro ⟨p, q⟩ hpq
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, P, Q] at hpq
    have hpqne : p ≠ q := by rintro rfl; omega
    exact card_filter_perm_eq_two (e.injective.ne hab) hpqne
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, Finset.card_product, smul_eq_mul,
    card_filter_fin_lt n s hs, card_filter_fin_ge n s hs]

/-- Under a uniformly random arrival order of `n ≥ 2` elements, observing `s = (n + 1) / 2`
elements puts any chosen `a` in the sample and any distinct `b` after the sample with probability
at least `1 / 4`. -/
theorem one_fourth_le_prob_split {a b : α} (hab : a ≠ b) (hn : 2 ≤ Fintype.card α) :
    (1 / 4 : ℝ) ≤
      ((uniformOfFintype (Fin (Fintype.card α) ≃ α)).toOuterMeasure
        {σ | a ∈ sampleSet σ ((Fintype.card α + 1) / 2) ∧
          b ∉ sampleSet σ ((Fintype.card α + 1) / 2)}).toReal := by
  classical
  set n := Fintype.card α
  set s := (n + 1) / 2
  have hs : s ≤ n := by omega
  rw [toOuterMeasure_uniformOfFintype_toReal]
  have hcard : Fintype.card (Fin n ≃ α) = Nat.factorial n := by
    rw [Fintype.card_equiv (Fintype.equivFin α).symm, Fintype.card_fin]
  have hfact : Nat.factorial n = n * (n - 1) * Nat.factorial (n - 2) := by
    have h1 : Nat.factorial n = n * Nat.factorial (n - 1) :=
      (Nat.mul_factorial_pred (show n ≠ 0 by omega)).symm
    have h2 : Nat.factorial (n - 1) = (n - 1) * Nat.factorial (n - 2) := by
      rw [← Nat.mul_factorial_pred (show n - 1 ≠ 0 by omega), show n - 1 - 1 = n - 2 by omega]
    rw [h1, h2, mul_assoc]
  have hnum : n * (n - 1) ≤ 4 * (s * (n - s)) := by
    rcases Nat.even_or_odd' n with ⟨m, hm | hm⟩
    · have hs' : s = m := by dsimp [s]; omega
      rw [hs', hm, show 2 * m - m = m by omega]
      calc 2 * m * (2 * m - 1) ≤ 2 * m * (2 * m) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ = 4 * (m * m) := by ring
    · have hs' : s = m + 1 := by dsimp [s]; omega
      rw [hs', hm, show 2 * m + 1 - 1 = 2 * m by omega, show 2 * m + 1 - (m + 1) = m by omega]
      nlinarith
  have hle_nat : Fintype.card (Fin n ≃ α) ≤
      4 * (Finset.univ.filter fun σ : Fin n ≃ α =>
        a ∈ sampleSet σ s ∧ b ∉ sampleSet σ s).card := by
    rw [hcard, card_filter_mem_sample_not_mem_sample hab hs, hfact]
    have h := Nat.mul_le_mul_right (Nat.factorial (n - 2)) hnum
    simpa [mul_assoc] using h
  have hden : (0 : ℝ) < (Fintype.card (Fin n ≃ α) : ℝ) := by
    rw [hcard]
    exact_mod_cast Nat.factorial_pos n
  have hle_real : (Fintype.card (Fin n ≃ α) : ℝ) ≤
      4 * ((Finset.univ.filter fun σ : Fin n ≃ α =>
        a ∈ sampleSet σ s ∧ b ∉ sampleSet σ s).card : ℝ) := by
    exact_mod_cast hle_nat
  simp only [Set.mem_ofPred_eq]
  rw [le_div_iff₀ hden]
  linarith

end Sampling

/-! ### Lower bound for optimal classical secretary cutoff -/

section OptimalCutoff

open Cslib.Probability.OptimalStopping.Secretary

private theorem optimalCutoff_le_self (n : ℕ) (hn : 1 ≤ n) : optimalCutoff n ≤ n := by
  refine optimalCutoff_le hn ?_
  simp

private theorem cutoffValue_eq_zero (n : ℕ) : cutoffValue n 0 = 1 / (n : ℝ) := by
  rw [← successProb_cutoffRule_succ 0 n, zero_add, successProb_cutoffRule_one]

private theorem cutoffValue_eq_of_pos {n s : ℕ} (hs : 0 < s) :
    cutoffValue n s = (s : ℝ) / n * ∑ i ∈ Finset.Ico s n, (1 : ℝ) / i := by
  have h1 := successProb_cutoffRule_succ s n
  have h2 := successProb_cutoffRule (r := s + 1) (n := n) (by omega)
  rw [h1] at h2
  rw [h2]
  push_cast
  rw [add_sub_cancel_right, ← Finset.Ico_add_one_right_eq_Icc, ← Finset.sum_Ico_add']
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

private theorem cutoffValue_antitone_step {n : ℕ} (hn : 1 ≤ n) :
    cutoffValue (n + 1) (optimalCutoff (n + 1) - 1) ≤
      successProb (cutoffRule (optimalCutoff n)) n := by
  set c := optimalCutoff (n + 1) - 1
  have hc1 : optimalCutoff (n + 1) = c + 1 := by
    have := one_le_optimalCutoff (n + 1)
    omega
  have hc_le : c ≤ n := by
    have := optimalCutoff_le_self (n + 1) (by omega)
    omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  rcases Nat.eq_zero_or_pos c with hc0 | hcpos
  · rw [hc0]
    have hstep : cutoffValue (n + 1) 0 ≤ cutoffValue n 0 := by
      rw [cutoffValue_eq_zero, cutoffValue_eq_zero]
      gcongr
      exact_mod_cast Nat.le_succ n
    have hsp := successProb_le_successProb_optimalCutoff (cutoffRule 1) n
    rw [successProb_cutoffRule_succ 0 n] at hsp
    exact hstep.trans hsp
  · have hlt_sum := lt_sum_of_lt_optimalCutoff (n := n + 1) hcpos
      (by omega : c < optimalCutoff (n + 1))
    rw [Finset.sum_Ico_succ_top (by omega)] at hlt_sum
    set S := ∑ i ∈ Finset.Ico c n, (1 : ℝ) / i
    have hS_nonneg : 0 ≤ S := Finset.sum_nonneg fun i _ => by positivity
    by_cases hS1 : 1 ≤ S
    · have hcv : cutoffValue (n + 1) c ≤ cutoffValue n c := by
        rw [cutoffValue_eq_of_pos hcpos, cutoffValue_eq_of_pos hcpos]
        rw [Finset.sum_Ico_succ_top (by omega)]
        change (c : ℝ) / ((n + 1 : ℕ) : ℝ) * (S + 1 / (n : ℝ)) ≤ (c : ℝ) / (n : ℝ) * S
        -- The difference of the two sides is `c * (S - 1) / (n * (n + 1)) ≥ 0`.
        have hdiff : (c : ℝ) / (n : ℝ) * S - (c : ℝ) / ((n + 1 : ℕ) : ℝ) * (S + 1 / (n : ℝ)) =
            (c : ℝ) * (S - 1) / ((n : ℝ) * ((n + 1 : ℕ) : ℝ)) := by
          field_simp
          push_cast
          ring
        have hS1' := sub_nonneg.mpr hS1
        have hpos : 0 ≤ (c : ℝ) * (S - 1) / ((n : ℝ) * ((n + 1 : ℕ) : ℝ)) := by positivity
        linarith
      have hsp := successProb_le_successProb_optimalCutoff (cutoffRule (c + 1)) n
      rw [successProb_cutoffRule_succ c n] at hsp
      exact hcv.trans hsp
    · push Not at hS1
      have hcv : cutoffValue (n + 1) c ≤ cutoffValue n (c - 1) := by
        rcases eq_or_lt_of_le (Nat.succ_le_of_lt hcpos) with h1 | hc2
        · have hce : c = 1 := h1.symm
          rw [hce]
          have hn_eq : n = 1 := by
            by_contra hne
            have hn2 : 2 ≤ n := by omega
            have hmem : 1 ∈ Finset.Ico 1 n := Finset.mem_Ico.mpr ⟨le_rfl, hn2⟩
            have hge : (1 : ℝ) ≤ S := by
              calc (1 : ℝ) = 1 / ((1 : ℕ) : ℝ) := by norm_num
                _ ≤ ∑ i ∈ Finset.Ico 1 n, (1 : ℝ) / i :=
                  Finset.single_le_sum (f := fun i : ℕ => (1 : ℝ) / i)
                    (fun (i : ℕ) _ => div_nonneg zero_le_one (Nat.cast_nonneg i)) hmem
                _ = S := by dsimp [S]; rw [hce]
            linarith
          subst hn_eq
          rw [cutoffValue_eq_of_pos one_pos, cutoffValue_eq_zero]
          norm_num [Finset.sum_Ico_succ_top]
        · have hcm : 1 ≤ c - 1 := by omega
          have hcm_lt : c - 1 < n := by omega
          have hS_eq : ∑ i ∈ Finset.Ico (c - 1) n, (1 : ℝ) / i =
              1 / ((c - 1 : ℕ) : ℝ) + S := by
            rw [Finset.sum_eq_sum_Ico_succ_bot hcm_lt, show c - 1 + 1 = c by omega]
          rw [cutoffValue_eq_of_pos hcpos, cutoffValue_eq_of_pos hcm,
            Finset.sum_Ico_succ_top hc_le, hS_eq]
          change (c : ℝ) / ((n + 1 : ℕ) : ℝ) * (S + 1 / (n : ℝ)) ≤
            ((c - 1 : ℕ) : ℝ) / (n : ℝ) * (1 / ((c - 1 : ℕ) : ℝ) + S)
          have hcmr : (0 : ℝ) < ((c - 1 : ℕ) : ℝ) := by exact_mod_cast hcm
          have hcm_cast : ((c - 1 : ℕ) : ℝ) + 1 = (c : ℝ) := by
            exact_mod_cast show c - 1 + 1 = c by omega
          have h_le : (c : ℝ) ≤ (n : ℝ) := by exact_mod_cast hc_le
          -- The difference of the two sides is `(n + 1 - c) * (1 - S) / (n * (n + 1)) ≥ 0`.
          have hdiff : ((c - 1 : ℕ) : ℝ) / (n : ℝ) * (1 / ((c - 1 : ℕ) : ℝ) + S) -
              (c : ℝ) / ((n + 1 : ℕ) : ℝ) * (S + 1 / (n : ℝ)) =
              ((n : ℝ) + 1 - (c : ℝ)) * (1 - S) / ((n : ℝ) * ((n + 1 : ℕ) : ℝ)) := by
            rw [← hcm_cast]
            field_simp
            push_cast
            ring
          have hn1c : 0 ≤ (n : ℝ) + 1 - (c : ℝ) := by linarith
          have hS1' : 0 ≤ 1 - S := by linarith
          have hpos : 0 ≤ ((n : ℝ) + 1 - (c : ℝ)) * (1 - S) / ((n : ℝ) * ((n + 1 : ℕ) : ℝ)) := by
            positivity
          linarith
      have hsp := successProb_le_successProb_optimalCutoff (cutoffRule c) n
      have hsp' := successProb_cutoffRule_succ (c - 1) n
      rw [show c - 1 + 1 = c by omega] at hsp'
      rw [hsp'] at hsp
      exact hcv.trans hsp

/-- **Non-asymptotic `1/e` bound for the optimal secretary cutoff**: for every `n ≥ 1`, the
optimal cutoff rule selects the best of `n` candidates with probability at least `1/e` (without an
`O(1/n)` slack, because the optimal success probability decreases monotonically to `1/e`). -/
theorem exp_neg_one_le_successProb_optimalCutoff {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-1) ≤ successProb (cutoffRule (optimalCutoff n)) n := by
  have hanti : ∀ m, 1 ≤ m →
      successProb (cutoffRule (optimalCutoff (m + 1))) (m + 1) ≤
        successProb (cutoffRule (optimalCutoff m)) m := by
    intro m hm
    have hstep := cutoffValue_antitone_step hm
    have heq := successProb_cutoffRule_succ (optimalCutoff (m + 1) - 1) (m + 1)
    have h1 := one_le_optimalCutoff (m + 1)
    rw [show optimalCutoff (m + 1) - 1 + 1 = optimalCutoff (m + 1) by omega] at heq
    rwa [heq]
  have hle_all : ∀ k, successProb (cutoffRule (optimalCutoff (n + k))) (n + k) ≤
      successProb (cutoffRule (optimalCutoff n)) n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => exact (hanti (n + k) (by omega)).trans ih
  have htend :
      Filter.Tendsto (fun k : ℕ => successProb (cutoffRule (optimalCutoff (n + k))) (n + k))
        Filter.atTop (nhds (Real.exp (-1))) := by
    have h := tendsto_successProb_optimalCutoff.comp (Filter.tendsto_add_atTop_nat n)
    simpa [Function.comp_def, Nat.add_comm] using h
  exact le_of_tendsto htend (Filter.Eventually.of_forall hle_all)

end OptimalCutoff

/-! ### Partition matroids: `e`-competitive independent secretary copies -/

section PartitionMatroid

open Cslib.Probability.OptimalStopping.Secretary

local instance instNonemptyEquivPartition (α : Type*) [Fintype α] :
    Nonempty (Fin (Fintype.card α) ≃ α) :=
  ⟨(Fintype.equivFin α).symm⟩

private def blockKey {α : Type*} (w : α → ℝ) (a : α) : ℝ ×ₗ α := toLex (w a, a)

private theorem blockKey_injective {α : Type*} (w : α → ℝ) : Function.Injective (blockKey w) := by
  intro a b h
  have : (w a, a) = (w b, b) := ofLex.injective h
  exact (Prod.ext_iff.mp this).2

/-- Relative arrival sequence within block `i` under arrival order `σ`. -/
private noncomputable def blockArrivalList {α ι : Type*} [Fintype α] [DecidableEq ι]
    (part : α → ι) (σ : Fin (Fintype.card α) ≃ α) (i : ι) : List α :=
  ((List.finRange (Fintype.card α)).map σ).filter fun a => decide (part a = i)

private theorem blockArrivalList_nodup {α ι : Type*} [Fintype α] [DecidableEq ι]
    (part : α → ι) (σ : Fin (Fintype.card α) ≃ α) (i : ι) :
    (blockArrivalList part σ i).Nodup :=
  ((List.nodup_finRange (Fintype.card α)).map σ.injective).filter _

private theorem mem_blockArrivalList_iff {α ι : Type*} [Fintype α] [DecidableEq ι]
    (part : α → ι) (σ : Fin (Fintype.card α) ≃ α) (i : ι) (a : α) :
    a ∈ blockArrivalList part σ i ↔ part a = i := by
  simp only [blockArrivalList, List.mem_filter, List.mem_map, List.mem_finRange,
    decide_eq_true_eq, true_and]
  exact ⟨fun ⟨_, hp⟩ => hp, fun hp => ⟨⟨σ.symm a, by simp⟩, hp⟩⟩

/-- Block size `|{a | part a = i}|`. -/
@[expose] def partitionBlockSize {α ι : Type*} [Fintype α] [DecidableEq ι]
    (part : α → ι) (i : ι) : ℕ :=
  (Finset.univ.filter fun a : α => part a = i).card

private theorem blockArrivalList_length {α ι : Type*} [Fintype α] [DecidableEq ι]
    (part : α → ι) (σ : Fin (Fintype.card α) ≃ α) (i : ι) :
    (blockArrivalList part σ i).length = partitionBlockSize part i := by
  classical
  rw [← List.toFinset_card_of_nodup (blockArrivalList_nodup part σ i), partitionBlockSize]
  congr 1
  ext a
  simp [mem_blockArrivalList_iff]

variable {α ι : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [DecidableEq ι]

/-- Online selection on a unit-capacity partition matroid `unitPartitionMatroid part`: runs
`Secretary.cutoffRule (Secretary.optimalCutoff m)` independently on each block of size `m`, using
`toLex (w a, a)` for tie-breaking independent of `σ`. -/
noncomputable def partitionSelect (part : α → ι) (w : α → ℝ)
    (σ : Fin (Fintype.card α) ≃ α) : Finset α :=
  Finset.univ.filter fun a =>
    let seq := blockArrivalList part σ (part a)
    let ranks := List.ofFn fun k : Fin seq.length =>
      ((seq.take k.val).filter fun y => decide (blockKey w seq[k.val] < blockKey w y)).length
    ∃ k : Fin seq.length, seq[k.val] = a ∧
      stopIndex (cutoffRule (optimalCutoff seq.length)) [] ranks = some k.val

/-- Every set selected by `partitionSelect` is independent in `unitPartitionMatroid part` (at most
one element per block). -/
theorem partitionSelect_indep (part : α → ι) (w : α → ℝ)
    (σ : Fin (Fintype.card α) ≃ α) :
    (unitPartitionMatroid part).Indep ((partitionSelect part w σ : Finset α) : Set α) := by
  rw [unitPartitionMatroid_indep_iff]
  intro a ha b hb hab
  simp only [Finset.mem_coe, partitionSelect, Finset.mem_filter, Finset.mem_univ,
    true_and] at ha hb
  obtain ⟨k₁, hk₁_eq, hk₁_stop⟩ := ha
  obtain ⟨k₂, hk₂_eq, hk₂_stop⟩ := hb
  have hseq : blockArrivalList part σ (part a) = blockArrivalList part σ (part b) := by rw [hab]
  have hk₁_stop' : stopIndex (cutoffRule (optimalCutoff (blockArrivalList part σ (part b)).length))
      [] (List.ofFn fun k : Fin (blockArrivalList part σ (part b)).length =>
        (((blockArrivalList part σ (part b)).take k.val).filter fun y =>
          decide (blockKey w (blockArrivalList part σ (part b))[k.val] < blockKey w y)).length) =
      some k₁.val := by
    simpa [hab] using hk₁_stop
  have hk_val : k₁.val = k₂.val := by
    rw [hk₁_stop', Option.some.injEq] at hk₂_stop
    exact hk₂_stop
  rw [← hk₁_eq, ← hk₂_eq]
  simp only [hab, hk_val]

/-- The PMF of the independent set selected by `partitionSelect` under a uniformly random arrival
order. -/
noncomputable def partitionSecretaryPMF (part : α → ι) (w : α → ℝ) :
    PMF (Finset α) :=
  (uniformOfFintype (Fin (Fintype.card α) ≃ α)).map (partitionSelect part w)

/-- Expected weight collected by `partitionSelect` under a uniformly random arrival order. -/
noncomputable def expectedPartitionSecretary (part : α → ι) (w : α → ℝ) : ℝ :=
  ∑ σ : Fin (Fintype.card α) ≃ α,
    ((uniformOfFintype (Fin (Fintype.card α) ≃ α) σ).toReal) * ∑ x ∈ partitionSelect part w σ, w x

open scoped Classical in
private theorem blockKeyFilter_ssubset {α : Type*} [LinearOrder α]
    (w : α → ℝ) (B : Finset α) {a b : B} (h : blockKey w a.1 < blockKey w b.1) :
    (Finset.univ.filter fun y : B => blockKey w y.1 < blockKey w a.1) ⊂
      (Finset.univ.filter fun y : B => blockKey w y.1 < blockKey w b.1) := by
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩,
      fun ha => lt_irrefl _ (Finset.mem_filter.mp ha).2⟩
  · intro y hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2.trans h⟩

open scoped Classical in
private noncomputable def blockOrderEquiv {α : Type*} [LinearOrder α]
    (w : α → ℝ) (B : Finset α) : B ≃ Fin B.card :=
  let f : B → Fin B.card := fun x =>
    ⟨(Finset.univ.filter fun y : B => blockKey w y.1 < blockKey w x.1).card, by
      have hss : (Finset.univ.filter fun y : B => blockKey w y.1 < blockKey w x.1) ⊂ Finset.univ :=
        Finset.ssubset_univ_iff.mpr fun h => by
          have hx : x ∈ Finset.univ := Finset.mem_univ x
          rw [← h] at hx
          exact lt_irrefl _ (Finset.mem_filter.mp hx).2
      simpa [Fintype.card_coe] using Finset.card_lt_card hss⟩
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    have hlt_or : blockKey w a.1 < blockKey w b.1 ∨ blockKey w b.1 < blockKey w a.1 :=
      lt_or_gt_of_ne ((blockKey_injective w).ne (Subtype.coe_ne_coe.mpr hne))
    rcases hlt_or with h | h
    · have hcard := Finset.card_lt_card (blockKeyFilter_ssubset w B h)
      have heq : (f a).val = (f b).val := congrArg Fin.val hab
      exact absurd heq hcard.ne
    · have hcard := Finset.card_lt_card (blockKeyFilter_ssubset w B h)
      have heq : (f a).val = (f b).val := congrArg Fin.val hab
      exact absurd heq hcard.ne'
  Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, by simp⟩)

open scoped Classical in
private theorem blockOrderEquiv_val {α : Type*} [LinearOrder α]
    (w : α → ℝ) (B : Finset α) (x : B) :
    (blockOrderEquiv w B x).val =
      (Finset.univ.filter fun y : B => blockKey w y.1 < blockKey w x.1).card :=
  rfl

open scoped Classical in
private theorem blockOrderEquiv_lt_iff {α : Type*} [LinearOrder α]
    (w : α → ℝ) (B : Finset α) (a b : B) :
    blockOrderEquiv w B a < blockOrderEquiv w B b ↔ blockKey w a.1 < blockKey w b.1 := by
  constructor
  · intro h
    by_contra hge
    rcases eq_or_lt_of_le (not_lt.mp hge) with heq | hgt
    · have heq' : a = b := Subtype.ext (blockKey_injective w heq.symm)
      subst heq'
      exact lt_irrefl _ h
    · have hcard := Finset.card_lt_card (blockKeyFilter_ssubset w B hgt)
      rw [← blockOrderEquiv_val w B b, ← blockOrderEquiv_val w B a] at hcard
      change (blockOrderEquiv w B a).val < (blockOrderEquiv w B b).val at h
      omega
  · intro h
    rw [Fin.lt_def, blockOrderEquiv_val, blockOrderEquiv_val]
    exact Finset.card_lt_card (blockKeyFilter_ssubset w B h)

omit [LinearOrder α] in
private theorem perm_ofSubtype_preserves_block (part : α → ι) (i : ι)
    (τ : Equiv.Perm {a : α // a ∈ Finset.univ.filter fun x => part x = i}) (a : α) :
    part ((Equiv.Perm.ofSubtype τ) a) = i ↔ part a = i := by
  by_cases ha : part a = i
  · have hm : a ∈ Finset.univ.filter fun x => part x = i :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
    rw [Equiv.Perm.ofSubtype_apply_of_mem τ hm]
    exact ⟨fun _ => ha, fun _ => (Finset.mem_filter.mp (τ ⟨a, hm⟩).2).2⟩
  · have hm : a ∉ Finset.univ.filter fun x => part x = i := by
      simpa using ha
    rw [Equiv.Perm.ofSubtype_apply_of_not_mem τ hm]

omit [LinearOrder α] in
private theorem blockArrivalList_comp_ofSubtype (part : α → ι) (σ : Fin (Fintype.card α) ≃ α)
    (i : ι) (τ : Equiv.Perm {a : α // a ∈ Finset.univ.filter fun x => part x = i}) :
    blockArrivalList part (σ.trans (Equiv.Perm.ofSubtype τ)) i =
      (blockArrivalList part σ i).map (Equiv.Perm.ofSubtype τ) := by
  unfold blockArrivalList
  have hcomp : (List.finRange (Fintype.card α)).map (⇑(σ.trans (Equiv.Perm.ofSubtype τ))) =
      ((List.finRange (Fintype.card α)).map σ).map (Equiv.Perm.ofSubtype τ) := by
    simp [List.map_map, Function.comp_def]
  rw [hcomp, List.filter_map]
  have hpred : (fun a => decide (part a = i)) ∘ (Equiv.Perm.ofSubtype τ) =
      fun a => decide (part a = i) := by
    funext a
    simp [Function.comp_apply, perm_ofSubtype_preserves_block]
  rw [hpred]

private noncomputable def blockArrivalEquiv (part : α → ι) (σ : Fin (Fintype.card α) ≃ α)
    (i : ι) :
    Fin (partitionBlockSize part i) ≃ {a : α // a ∈ Finset.univ.filter fun x => part x = i} :=
  let seq := blockArrivalList part σ i
  have hlen : seq.length = partitionBlockSize part i := blockArrivalList_length part σ i
  let f : Fin (partitionBlockSize part i) → {a : α // a ∈ Finset.univ.filter fun x => part x = i} :=
    fun k => ⟨seq[k.val]'(by rw [hlen]; exact k.isLt), Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (mem_blockArrivalList_iff part σ i _).mp (List.getElem_mem _)⟩⟩
  have hbij : Function.Bijective f := by
    have hinj : Function.Injective f := by
      intro k₁ k₂ h
      have hget : seq[k₁.val]'(by rw [hlen]; exact k₁.isLt) =
          seq[k₂.val]'(by rw [hlen]; exact k₂.isLt) := congrArg Subtype.val h
      exact Fin.ext ((blockArrivalList_nodup part σ i).getElem_inj_iff.mp hget)
    refine (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, ?_⟩
    rw [Fintype.card_fin, Fintype.card_coe, partitionBlockSize]
  Equiv.ofBijective f hbij

private theorem block_prob_max_eq_successProb (part : α → ι) (w : α → ℝ) (i : ι)
    (hi : (Finset.univ.filter fun a : α => part a = i).Nonempty) :
    let B := Finset.univ.filter fun a : α => part a = i
    let xStar := (blockOrderEquiv w B).symm ⟨B.card - 1, Nat.sub_lt hi.card_pos one_pos⟩
    ((uniformOfFintype (Fin (Fintype.card α) ≃ α)).toOuterMeasure
      {σ | xStar.1 ∈ partitionSelect part w σ}).toReal =
      Secretary.successProb (cutoffRule (optimalCutoff B.card)) B.card := by
  classical
  intro B xStar
  set m := B.card
  have hm : 1 ≤ m := hi.card_pos
  let q := blockOrderEquiv w B
  have htop : ∀ y : B, q y ≤ q xStar := by
    intro y
    change (q y).val ≤ (q xStar).val
    have hxq : (q xStar).val = m - 1 := by simp [xStar, q, m]
    rw [hxq]
    exact Nat.le_pred_of_lt (q y).isLt
  have hunif : uniformOfFintype (Fin (Fintype.card α) ≃ α) =
      (uniformOfFintype (Fin (Fintype.card α) ≃ α)).bind fun σ =>
        (uniformOfFintype (Equiv.Perm B)).map fun τ => σ.trans (Equiv.Perm.ofSubtype τ) := by
    simp_rw [← PMF.bind_pure_comp]
    rw [PMF.bind_comm]
    refine Eq.symm ?_
    calc (uniformOfFintype (Equiv.Perm B)).bind (fun τ =>
          (uniformOfFintype (Fin (Fintype.card α) ≃ α)).bind fun σ =>
            PMF.pure (σ.trans (Equiv.Perm.ofSubtype τ)))
        = (uniformOfFintype (Equiv.Perm B)).bind (fun _ =>
            uniformOfFintype (Fin (Fintype.card α) ≃ α)) := by
          congr 1 with τ : 1
          change (uniformOfFintype (Fin (Fintype.card α) ≃ α)).bind
            (PMF.pure ∘ fun σ : Fin (Fintype.card α) ≃ α => σ.trans (Equiv.Perm.ofSubtype τ)) = _
          rw [PMF.bind_pure_comp]
          exact uniformOfFintype_map_equiv
            (Equiv.equivCongr (Equiv.refl _) (Equiv.Perm.ofSubtype τ))
      _ = uniformOfFintype (Fin (Fintype.card α) ≃ α) := PMF.bind_const _ _
  rw [hunif, PMF.toOuterMeasure_apply]
  have hrew : (∑' x : Fin (Fintype.card α) ≃ α,
      ({σ | xStar.1 ∈ partitionSelect part w σ} : Set _).indicator
        (⇑((uniformOfFintype (Fin (Fintype.card α) ≃ α)).bind fun σ =>
          PMF.map (fun τ => σ.trans (Equiv.Perm.ofSubtype τ))
            (uniformOfFintype (Equiv.Perm ↥B)))) x) =
      ∑' x : Fin (Fintype.card α) ≃ α,
        ((uniformOfFintype (Fin (Fintype.card α) ≃ α)).bind fun σ =>
          PMF.map (fun τ => σ.trans (Equiv.Perm.ofSubtype τ))
            (uniformOfFintype (Equiv.Perm ↥B))) x *
          ({σ | xStar.1 ∈ partitionSelect part w σ} : Set _).indicator 1 x := by
    refine tsum_congr fun x => ?_
    by_cases hx : xStar.1 ∈ partitionSelect part w x <;> simp [Set.indicator, hx]
  rw [hrew, tsum_bind_mul]
  have hinner : ∀ σ : Fin (Fintype.card α) ≃ α,
      ∑' a, ((uniformOfFintype (Equiv.Perm B)).map fun τ => σ.trans (Equiv.Perm.ofSubtype τ)) a *
        ({σ' | xStar.1 ∈ partitionSelect part w σ'} : Set _).indicator 1 a =
        (uniformOfFintype (Equiv.Perm (Fin m))).toOuterMeasure
          {π | Secretary.Wins (cutoffRule (optimalCutoff m)) π} := by
    intro σ
    rw [tsum_map_mul]
    let pσ : Fin m ≃ B := blockArrivalEquiv part σ i
    let eτ : Equiv.Perm B ≃ Equiv.Perm (Fin m) :=
      { toFun := fun τ => pσ.trans (τ.trans q)
        invFun := fun π => (pσ.symm.trans π).trans q.symm
        left_inv := fun τ => by ext y; simp
        right_inv := fun π => by ext k; simp }
    have hiff : ∀ τ : Equiv.Perm B,
        xStar.1 ∈ partitionSelect part w (σ.trans (Equiv.Perm.ofSubtype τ)) ↔
          Secretary.Wins (cutoffRule (optimalCutoff m)) (eτ τ) := by
      intro τ
      set σ' := σ.trans (Equiv.Perm.ofSubtype τ)
      set seq' := blockArrivalList part σ' i
      have hlen' : seq'.length = m := blockArrivalList_length part σ' i
      have hseq_eq : seq' = (blockArrivalList part σ i).map (Equiv.Perm.ofSubtype τ) :=
        blockArrivalList_comp_ofSubtype part σ i τ
      have hget' : ∀ (k : ℕ) (hk : k < m),
          seq'[k]'(by rw [hlen']; exact hk) = (τ (pσ ⟨k, hk⟩)).1 := by
        intro k hk
        simp only [seq', hseq_eq, List.getElem_map]
        have hget0 : (blockArrivalList part σ i)[k]'(by
            rw [blockArrivalList_length part σ i]; exact hk) = (pσ ⟨k, hk⟩).1 := rfl
        rw [hget0, Equiv.Perm.ofSubtype_apply_of_mem τ (pσ ⟨k, hk⟩).2]
      have hranks_eq : (List.ofFn fun k : Fin seq'.length =>
            ((seq'.take k.val).filter fun y =>
              decide (blockKey w seq'[k.val] < blockKey w y)).length) =
          Secretary.relRanks (eτ τ) := by
        rw [Secretary.relRanks, List.ext_getElem_iff]
        refine ⟨by simp [hlen'], fun k hk₁ hk₂ => ?_⟩
        simp only [List.length_ofFn, hlen'] at hk₁
        simp only [List.getElem_ofFn, Secretary.relRank]
        have hlen_take : (seq'.take k).length = k :=
          List.length_take_of_le (by rw [hlen']; exact hk₁.le)
        have htake_eq : ((seq'.take k).filter fun y =>
            decide (blockKey w seq'[k] < blockKey w y)).length =
            (Finset.univ.filter fun j : Fin m => j < ⟨k, hk₁⟩ ∧ eτ τ ⟨k, hk₁⟩ < eτ τ j).card := by
          have hbij : (Finset.univ.filter fun j : Fin k =>
              blockKey w seq'[k] < blockKey w (seq'.take k)[j.val]).card =
              (Finset.univ.filter fun j : Fin m =>
                j < ⟨k, hk₁⟩ ∧ eτ τ ⟨k, hk₁⟩ < eτ τ j).card := by
            refine Finset.card_bij (fun j _ => ⟨j.val, j.isLt.trans hk₁⟩) ?_ ?_ ?_
            · intro j hj
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
              refine ⟨j.isLt, ?_⟩
              have hjlt : j.val < m := j.isLt.trans hk₁
              rw [List.getElem_take, hget' k hk₁, hget' j.val hjlt] at hj
              change q (τ (pσ ⟨k, hk₁⟩)) < q (τ (pσ ⟨j.val, hjlt⟩))
              exact (blockOrderEquiv_lt_iff w B _ _).mpr hj
            · intro j₁ _ j₂ _ h
              exact Fin.ext (by simpa using congrArg Fin.val h)
            · intro j hj
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
              refine ⟨⟨j.val, hj.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Fin.ext rfl⟩
              rw [List.getElem_take, hget' k hk₁, hget' j.val j.isLt]
              exact (blockOrderEquiv_lt_iff w B _ _).mp hj.2
          rw [← hbij]
          have hfin_filter : ∀ (l : List α) (p : α → Bool),
              (l.filter p).length =
                (Finset.univ.filter fun j : Fin l.length => p l[j.val] = true).card := by
            intro l p
            induction l with
            | nil => simp
            | cons a t ih =>
              simp only [List.filter_cons]
              change (if p a = true then a :: t.filter p else t.filter p).length =
                (Finset.univ.filter fun i_1 : Fin (t.length + 1) =>
                  p (a :: t)[i_1.val] = true).card
              rw [Finset.card_filter, Fin.sum_univ_succ]
              rw [Finset.card_filter] at ih
              cases hpa : p a with
              | false =>
                simp only [hpa, Bool.false_eq_true, ↓reduceIte, Fin.val_zero,
                  List.getElem_cons_zero, Fin.val_succ, List.getElem_cons_succ, ih, zero_add]
              | true =>
                simp only [hpa, ↓reduceIte, List.length_cons, Fin.val_zero,
                  List.getElem_cons_zero, Fin.val_succ, List.getElem_cons_succ, ih]
                ring
          rw [hfin_filter]
          refine Finset.card_bij (fun j hj => Fin.cast hlen_take j) ?_ ?_ ?_
          · intro j hj; simpa using hj
          · intro j₁ _ j₂ _ h; exact Fin.ext (by simpa using congrArg Fin.val h)
          · intro j hj
            refine ⟨Fin.cast hlen_take.symm j, ?_, by ext; simp⟩
            simpa using hj
        rw [← htake_eq]
      have hxStar_part : part xStar.1 = i := (Finset.mem_filter.mp xStar.2).2
      have hxStar_seq : xStar.1 ∈ partitionSelect part w σ' ↔
          ∃ k : Fin seq'.length, seq'[k.val] = xStar.1 ∧
            stopIndex (cutoffRule (optimalCutoff seq'.length)) []
              (List.ofFn fun k : Fin seq'.length =>
                ((seq'.take k.val).filter fun y =>
                  decide (blockKey w seq'[k.val] < blockKey w y)).length) = some k.val := by
        have hpart : ∀ seq, blockArrivalList part σ' (part xStar.1) = seq →
            (xStar.1 ∈ partitionSelect part w σ' ↔
              ∃ k : Fin seq.length, seq[k.val] = xStar.1 ∧
                stopIndex (cutoffRule (optimalCutoff seq.length)) []
                  (List.ofFn fun k : Fin seq.length =>
                    ((seq.take k.val).filter fun y =>
                      decide (blockKey w seq[k.val] < blockKey w y)).length) =
                  some k.val) := by
          intro seq hseq
          subst hseq
          simp [partitionSelect]
        exact hpart seq' (by rw [hxStar_part])
      have hlen_cut : optimalCutoff seq'.length = optimalCutoff m := by rw [hlen']
      rw [hranks_eq, hlen_cut] at hxStar_seq
      have hxStar_mem_iff : xStar.1 ∈ partitionSelect part w σ' ↔
          ∃ k : Fin m, seq'[k.val]'(by rw [hlen']; exact k.isLt) = xStar.1 ∧
            stopIndex (cutoffRule (optimalCutoff m)) [] (Secretary.relRanks (eτ τ)) =
              some k.val := by
        rw [hxStar_seq]
        exact ⟨fun ⟨k, hk1, hk2⟩ => ⟨⟨k.val, hlen' ▸ k.isLt⟩, hk1, hk2⟩,
          fun ⟨k, hk1, hk2⟩ => ⟨⟨k.val, by rw [hlen']; exact k.isLt⟩, hk1, hk2⟩⟩
      rw [hxStar_mem_iff, Secretary.Wins]
      constructor
      · rintro ⟨k, hkq, hstop⟩
        refine ⟨k, hstop, ?_⟩
        intro j
        have hxk : τ (pσ k) = xStar := by
          apply Subtype.ext
          have hkget : seq'[k.val]'(by rw [hlen']; exact k.isLt) = (τ (pσ ⟨k.val, k.isLt⟩)).1 :=
            hget' k.val k.isLt
          rw [hkq] at hkget
          exact hkget.symm
        change q (τ (pσ j)) ≤ q (τ (pσ k))
        rw [hxk]
        exact htop _
      · rintro ⟨k, hstop, hmax⟩
        refine ⟨k, ?_, hstop⟩
        rw [hget' k.val k.isLt]
        have hmax' := hmax ((eτ τ).symm (q xStar))
        simp only [Equiv.apply_symm_apply] at hmax'
        have hxk : eτ τ k = q xStar := le_antisymm (htop _) hmax'
        exact congrArg Subtype.val (q.injective hxk)
    calc ∑' τ : Equiv.Perm B, uniformOfFintype (Equiv.Perm B) τ *
          ({σ' | xStar.1 ∈ partitionSelect part w σ'} : Set _).indicator 1
            (σ.trans (Equiv.Perm.ofSubtype τ))
        = ∑' τ : Equiv.Perm B, uniformOfFintype (Equiv.Perm B) τ *
            ({π | Secretary.Wins (cutoffRule (optimalCutoff m)) π} : Set _).indicator 1 (eτ τ) := by
          refine tsum_congr fun τ => ?_
          simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply, hiff τ]
      _ = ∑' π : Equiv.Perm (Fin m), uniformOfFintype (Equiv.Perm (Fin m)) π *
            ({π | Secretary.Wins (cutoffRule (optimalCutoff m)) π} : Set _).indicator 1 π := by
          rw [← uniformOfFintype_map_equiv eτ, tsum_map_mul]
      _ = (uniformOfFintype (Equiv.Perm (Fin m))).toOuterMeasure
            {π | Secretary.Wins (cutoffRule (optimalCutoff m)) π} := by
          rw [PMF.toOuterMeasure_apply]
          refine tsum_congr fun π => ?_
          by_cases h : Secretary.Wins (cutoffRule (optimalCutoff m)) π <;>
            simp [Set.indicator, h]
  have hsum : ∑' σ : Fin (Fintype.card α) ≃ α,
      uniformOfFintype (Fin (Fintype.card α) ≃ α) σ *
        ((uniformOfFintype (Equiv.Perm (Fin m))).toOuterMeasure
          {π | Secretary.Wins (cutoffRule (optimalCutoff m)) π}) =
      (uniformOfFintype (Equiv.Perm (Fin m))).toOuterMeasure
        {π | Secretary.Wins (cutoffRule (optimalCutoff m)) π} := by
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have hrew2 :
      (∑' σ : Fin (Fintype.card α) ≃ α,
        (uniformOfFintype (Fin (Fintype.card α) ≃ α)) σ *
          ∑' b : Fin (Fintype.card α) ≃ α,
            (PMF.map (fun τ => σ.trans (Equiv.Perm.ofSubtype τ))
              (uniformOfFintype (Equiv.Perm ↥B))) b *
              ({σ' | xStar.1 ∈ partitionSelect part w σ'} : Set _).indicator 1 b) =
        ∑' σ : Fin (Fintype.card α) ≃ α,
          uniformOfFintype (Fin (Fintype.card α) ≃ α) σ *
            ((uniformOfFintype (Equiv.Perm (Fin m))).toOuterMeasure
              {π | Secretary.Wins (cutoffRule (optimalCutoff m)) π}) :=
    tsum_congr fun σ => congrArg ((uniformOfFintype (Fin (Fintype.card α) ≃ α)) σ * ·) (hinner σ)
  rw [hrew2, hsum]
  rfl

omit [DecidableEq α] in
private noncomputable def blockMaxElem (part : α → ι) (w : α → ℝ) (i : ι)
    (hi : (Finset.univ.filter fun a : α => part a = i).Nonempty) : α :=
  ((blockOrderEquiv w (Finset.univ.filter fun a : α => part a = i)).symm
    ⟨(Finset.univ.filter fun a : α => part a = i).card - 1, Nat.sub_lt hi.card_pos one_pos⟩).1

omit [DecidableEq α] in
private theorem mem_block_le_blockMaxElem (part : α → ι) (w : α → ℝ) (i : ι)
    (hi : (Finset.univ.filter fun a : α => part a = i).Nonempty) {a : α}
    (ha : a ∈ Finset.univ.filter fun x : α => part x = i) :
    w a ≤ w (blockMaxElem part w i hi) := by
  let B := Finset.univ.filter fun x : α => part x = i
  let q := blockOrderEquiv w B
  let xStar : B := q.symm ⟨B.card - 1, Nat.sub_lt hi.card_pos one_pos⟩
  change w a ≤ w xStar.1
  by_contra hlt
  push Not at hlt
  have hkey : blockKey w xStar.1 < blockKey w a :=
    (Prod.Lex.toLex_lt_toLex).mpr (Or.inl hlt)
  have hq : q xStar < q ⟨a, ha⟩ := (blockOrderEquiv_lt_iff w B xStar ⟨a, ha⟩).mpr hkey
  have hx : (q xStar).val = B.card - 1 := by simp [xStar, q]
  change (q xStar).val < (q ⟨a, ha⟩).val at hq
  have ha_lt : (q ⟨a, ha⟩).val < B.card := (q ⟨a, ha⟩).isLt
  omega

/-- **Partition matroid secretary theorem** ([BabaioffImmorlicaKleinberg2007], Section 6, p. 9):
running independent copies of the optimal classical secretary cutoff rule on each part of a
unit-capacity partition matroid `unitPartitionMatroid part` achieves expected weight at least
`(1 / e) · ∑ x ∈ I, w x` for every independent set `I` and nonnegative weight function `w`. -/
theorem exp_neg_one_mul_sum_le_expectedPartitionSecretary (part : α → ι) (w : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) {I : Finset α}
    (hI : (unitPartitionMatroid part).Indep (I : Set α)) :
    Real.exp (-1) * ∑ x ∈ I, w x ≤ expectedPartitionSecretary part w := by
  classical
  rcases isEmpty_or_nonempty α with hα | hα
  · have hI_eq : I = ∅ := Finset.eq_empty_of_forall_notMem fun x => (hα.false x).elim
    simp only [hI_eq, Finset.sum_empty, mul_zero]
    unfold expectedPartitionSecretary
    exact Finset.sum_nonneg fun σ _ =>
      mul_nonneg ENNReal.toReal_nonneg (Finset.sum_nonneg fun x _ => hw x)
  have hinj : Set.InjOn part (I : Set α) := unitPartitionMatroid_indep_iff.mp hI
  let J : Finset ι := I.image part
  let B : ι → Finset α := fun i => Finset.univ.filter fun a : α => part a = i
  let blkW : ι → ℝ := fun i => if h : (B i).Nonempty then w (blockMaxElem part w i h) else 0
  have hI_bound : ∑ x ∈ I, w x ≤ ∑ i ∈ J, blkW i := by
    dsimp only [J]
    rw [Finset.sum_image hinj]
    refine Finset.sum_le_sum fun x _ => ?_
    have hxB : x ∈ B (part x) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    simp only [blkW, show (B (part x)).Nonempty from ⟨x, hxB⟩, ↓reduceDIte]
    exact mem_block_le_blockMaxElem part w (part x) ⟨x, hxB⟩ hxB
  let μ := uniformOfFintype (Fin (Fintype.card α) ≃ α)
  have hstep : ∀ i ∈ J, Real.exp (-1) * blkW i ≤
      ∑ σ : Fin (Fintype.card α) ≃ α, (μ σ).toReal *
        ∑ x ∈ partitionSelect part w σ ∩ B i, w x := by
    intro i _
    dsimp only [blkW]
    by_cases hne : (B i).Nonempty
    · simp only [hne, ↓reduceDIte]
      set xStar := blockMaxElem part w i hne
      have hxStar_mem : xStar ∈ B i := Subtype.prop _
      have hprob_eq : ((μ.toOuterMeasure {σ | xStar ∈ partitionSelect part w σ}).toReal) =
          Secretary.successProb (cutoffRule (optimalCutoff (B i).card)) (B i).card :=
        block_prob_max_eq_successProb part w i hne
      have hexp_le : Real.exp (-1) ≤
          ((μ.toOuterMeasure {σ | xStar ∈ partitionSelect part w σ}).toReal) := by
        rw [hprob_eq]
        exact exp_neg_one_le_successProb_optimalCutoff hne.card_pos
      have hprob_sum : (μ.toOuterMeasure {σ | xStar ∈ partitionSelect part w σ}).toReal =
          ∑ σ : Fin (Fintype.card α) ≃ α, (μ σ).toReal *
            if xStar ∈ partitionSelect part w σ then (1 : ℝ) else 0 := by
        dsimp only [μ]
        rw [toOuterMeasure_uniformOfFintype_toReal]
        simp only [uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
          Set.mem_ofPred_eq, ← Finset.mul_sum, Finset.sum_boole]
        rw [inv_mul_eq_div]
      calc Real.exp (-1) * w xStar
          ≤ (μ.toOuterMeasure {σ | xStar ∈ partitionSelect part w σ}).toReal * w xStar :=
            mul_le_mul_of_nonneg_right hexp_le (hw xStar)
        _ = ∑ σ : Fin (Fintype.card α) ≃ α, (μ σ).toReal *
              (if xStar ∈ partitionSelect part w σ then w xStar else 0) := by
            rw [hprob_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun σ _ => ?_
            split_ifs <;> ring
        _ ≤ ∑ σ : Fin (Fintype.card α) ≃ α, (μ σ).toReal *
              ∑ x ∈ partitionSelect part w σ ∩ B i, w x := by
            refine Finset.sum_le_sum fun σ _ =>
              mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
            split_ifs with hs
            · exact Finset.single_le_sum (fun x _ => hw x) (Finset.mem_inter.mpr ⟨hs, hxStar_mem⟩)
            · exact Finset.sum_nonneg fun x _ => hw x
    · simp only [hne, ↓reduceDIte, mul_zero]
      exact Finset.sum_nonneg fun σ _ =>
        mul_nonneg ENNReal.toReal_nonneg (Finset.sum_nonneg fun x _ => hw x)
  have hsum_blk : Real.exp (-1) * ∑ x ∈ I, w x ≤
      ∑ i ∈ J, ∑ σ : Fin (Fintype.card α) ≃ α, (μ σ).toReal *
        ∑ x ∈ partitionSelect part w σ ∩ B i, w x := by
    calc Real.exp (-1) * ∑ x ∈ I, w x
        ≤ Real.exp (-1) * ∑ i ∈ J, blkW i :=
          mul_le_mul_of_nonneg_left hI_bound (Real.exp_pos (-1)).le
      _ = ∑ i ∈ J, Real.exp (-1) * blkW i := Finset.mul_sum _ _ _
      _ ≤ _ := Finset.sum_le_sum hstep
  refine hsum_blk.trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun σ _ => ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  have hdisj : (J : Set ι).PairwiseDisjoint fun i => partitionSelect part w σ ∩ B i := by
    intro i₁ _ i₂ _ hne
    refine Finset.disjoint_left.mpr fun x h₁ h₂ => hne ?_
    have hm₁ := (Finset.mem_filter.mp (Finset.mem_inter.mp h₁).2).2
    have hm₂ := (Finset.mem_filter.mp (Finset.mem_inter.mp h₂).2).2
    exact hm₁.symm.trans hm₂
  rw [← Finset.sum_biUnion hdisj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => hw x)
  intro x hx
  obtain ⟨i, _, hx'⟩ := Finset.mem_biUnion.mp hx
  exact (Finset.mem_inter.mp hx').1

end PartitionMatroid

/-! ### General matroids: `O(log k)` Threshold Price algorithm -/

section ThresholdPrice

local instance instNonemptyEquivThreshold (α : Type*) [Fintype α] :
    Nonempty (Fin (Fintype.card α) ≃ α) :=
  ⟨(Fintype.equivFin α).symm⟩

/-- Maximum weight of a sample `S`, or `0` when empty. -/
@[expose] def sampleMax {α : Type*} (w : α → ℝ) (S : Finset α) : ℝ :=
  if h : S.Nonempty then S.sup' h w else 0

theorem sampleMax_nonempty {α : Type*} {w : α → ℝ} {S : Finset α} (hS : S.Nonempty) :
    sampleMax w S = S.sup' hS w := by
  classical
  simp [sampleMax, hS]

theorem le_sampleMax_of_mem {α : Type*} {w : α → ℝ} {S : Finset α} {x : α} (hx : x ∈ S) :
    w x ≤ sampleMax w S := by
  have hS : S.Nonempty := ⟨x, hx⟩
  rw [sampleMax_nonempty hS]
  exact Finset.le_sup' w hx

theorem sampleMax_le {α : Type*} {w : α → ℝ} {S : Finset α} {b : ℝ} (hS : S.Nonempty)
    (hb : ∀ x ∈ S, w x ≤ b) : sampleMax w S ≤ b := by
  rw [sampleMax_nonempty hS]
  exact Finset.sup'_le hS w hb

theorem exists_mem_sampleMax {α : Type*} {w : α → ℝ} {S : Finset α} (hS : S.Nonempty) :
    ∃ x ∈ S, sampleMax w S = w x := by
  obtain ⟨x, hx, hmax⟩ := S.exists_max_image w hS
  refine ⟨x, hx, le_antisymm (sampleMax_le hS fun y hy => hmax y hy) (le_sampleMax_of_mem hx)⟩

private theorem card_indep_le_eRank_toNat {α : Type*} [Finite α] (M : Matroid α) {I : Finset α}
    (hI : M.Indep (I : Set α)) : I.card ≤ M.eRank.toNat := by
  let _instFintype : Fintype α := Fintype.ofFinite α
  have hrank : M.eRank ≤ (Fintype.card α : ℕ∞) := by
    calc M.eRank = M.eRk M.E := M.eRank_def
      _ ≤ M.E.encard := M.eRk_le_encard _
      _ ≤ Set.univ.encard := Set.encard_mono (Set.subset_univ _)
      _ = (Fintype.card α : ℕ∞) := by rw [Set.encard_univ, ENat.card_eq_coe_fintype_card]
  have htop : M.eRank ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hrank
  have hc : (I.card : ℕ∞) ≤ M.eRank := by
    calc (I.card : ℕ∞) = (I : Set α).encard := (Set.encard_coe_eq_coe_finsetCard I).symm
      _ = M.eRk (I : Set α) := hI.eRk_eq_encard.symm
      _ ≤ M.eRank := M.eRk_le_eRank _
  exact_mod_cast (ENat.natCast_toNat htop ▸ hc)

private def layerGap (v : ℕ → ℝ) (q : ℕ) (i : Fin q) : ℝ :=
  v i.val - if i.val + 1 < q then v (i.val + 1) else 0

private theorem sum_Ico_sub_succ (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ k ∈ Finset.Ico a b, (f k - f (k + 1)) = f a - f b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab, ih]
    ring

private theorem sum_layerGap_ge {v : ℕ → ℝ} {q : ℕ} (j : Fin q) :
    ∑ i : Fin q, (if j ≤ i then layerGap v q i else 0) = v j.val := by
  have hfilter : ∑ i : Fin q, (if j ≤ i then layerGap v q i else 0) =
      ∑ k ∈ Finset.Ico j.val q, (v k - if k + 1 < q then v (k + 1) else 0) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun i _ => i.val) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def] at hi
      exact Finset.mem_Ico.mpr ⟨hi, i.isLt⟩
    · intro a _ b _ h
      exact Fin.ext h
    · intro k hk
      obtain ⟨hjk, hkq⟩ := Finset.mem_Ico.mp hk
      exact ⟨⟨k, hkq⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjk⟩, rfl⟩
    · intro i _
      rfl
  rw [hfilter]
  let f : ℕ → ℝ := fun k => if k < q then v k else 0
  have hcongr : ∑ k ∈ Finset.Ico j.val q, (v k - if k + 1 < q then v (k + 1) else 0) =
      ∑ k ∈ Finset.Ico j.val q, (f k - f (k + 1)) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkq : k < q := (Finset.mem_Ico.mp hk).2
    simp [f, hkq]
  rw [hcongr, sum_Ico_sub_succ f j.isLt.le]
  simp [f, j.isLt]

private theorem sum_layerGap_mul_succ {v : ℕ → ℝ} {q : ℕ} :
    ∑ i : Fin q, layerGap v q i * ((i.val + 1 : ℕ) : ℝ) = ∑ j : Fin q, v j.val := by
  have hcard : ∀ i : Fin q, ((i.val + 1 : ℕ) : ℝ) = ∑ j : Fin q, if j ≤ i then (1 : ℝ) else 0 := by
    intro i
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hset : (Finset.univ.filter fun j : Fin q => j ≤ i) = Finset.Iic i := by
      ext j
      simp
    rw [hset, Fin.card_Iic]
  simp_rw [hcard, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  calc ∑ i : Fin q, layerGap v q i * (if j ≤ i then (1 : ℝ) else 0)
      = ∑ i : Fin q, (if j ≤ i then layerGap v q i else 0) :=
        Finset.sum_congr rfl fun i _ => by split_ifs <;> ring
    _ = v j.val := sum_layerGap_ge j

open scoped Classical in
private theorem sum_layerGap_mul_countHalf {α : Type*} (w : α → ℝ) {v : ℕ → ℝ} {q : ℕ}
    (hv_anti : ∀ ⦃a b : ℕ⦄, a ≤ b → b < q → v b ≤ v a)
    {S : Finset α} (hS : ∀ y ∈ S, 0 ≤ w y) :
    ∑ i : Fin q, layerGap v q i *
        (((S.filter fun y => v i.val / 2 ≤ w y).card : ℕ) : ℝ) ≤
      2 * ∑ y ∈ S, w y := by
  have hcard : ∀ i : Fin q, (((S.filter fun y => v i.val / 2 ≤ w y).card : ℕ) : ℝ) =
      ∑ y ∈ S, if v i.val / 2 ≤ w y then (1 : ℝ) else 0 := by
    intro i
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun y _ => by split_ifs <;> simp
  simp_rw [hcard, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun y hy => ?_
  by_cases hex : ∃ i : Fin q, v i.val / 2 ≤ w y
  · let F : Finset (Fin q) := Finset.univ.filter fun i : Fin q => v i.val / 2 ≤ w y
    have hFne : F.Nonempty := let ⟨i, hi⟩ := hex; ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    let i0 := F.min' hFne
    have hi0_mem : v i0.val / 2 ≤ w y := (Finset.mem_filter.mp (F.min'_mem hFne)).2
    have hiff : ∀ i : Fin q, v i.val / 2 ≤ w y ↔ i0 ≤ i := fun i =>
      ⟨fun hi => Finset.min'_le F i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩),
        fun hi => by linarith [hv_anti hi i.isLt]⟩
    calc ∑ i : Fin q, layerGap v q i * (if v i.val / 2 ≤ w y then (1 : ℝ) else 0)
        = ∑ i : Fin q, (if i0 ≤ i then layerGap v q i else 0) :=
          Finset.sum_congr rfl fun i _ => by simp only [hiff i]; split_ifs <;> ring
      _ = v i0.val := sum_layerGap_ge i0
      _ ≤ 2 * w y := by linarith
  · push Not at hex
    rw [Finset.sum_eq_zero fun i _ => by simp [not_le.mpr (hex i)]]
    linarith [hS y hy]

private theorem list_map_sum_eq_sum_fin {α : Type*} (w : α → ℝ) (xs : List α) :
    (xs.map w).sum = ∑ t : Fin xs.length, w xs[t.val] := by
  induction xs with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, ih]
    change w a + ∑ k : Fin t.length, w t[k.val] = ∑ k : Fin (t.length + 1), w (a :: t)[k.val]
    rw [Fin.sum_univ_succ]
    simp

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Threshold Price Algorithm ([BabaioffImmorlicaKleinberg2007], Section 3.2) for fixed arrival
order `σ` and log-scale exponent `j`: observes `s = ⌈n/2⌉` elements (`sampleSet σ s`), sets
threshold `τ = sampleMax w S / 2^j`, and greedily selects positive-weight elements above `τ` in
the remaining stream while maintaining matroid independence (`M.Indep`). Filtering `0`-weight
elements (Section 6) ensures zero-weight ties cannot block the maximum element when `sampleMax = 0`.
-/
@[expose] noncomputable def thresholdPriceRun (M : Matroid α)
    [DecidablePred fun S : Finset α => M.Indep (S : Set α)]
    (w : α → ℝ) (σ : Fin (Fintype.card α) ≃ α)
    (j : Fin (Nat.clog 2 M.eRank.toNat + 1)) : Finset α :=
  let s := (Fintype.card α + 1) / 2
  let τ := sampleMax w (sampleSet σ s) / (2 : ℝ) ^ (j : ℕ)
  greedySelect (fun S => decide (M.Indep (S : Set α)))
    ((postSampleList σ s).filter fun x => decide (0 < w x ∧ τ ≤ w x))

/-- Every run of `thresholdPriceRun` outputs an independent set of `M`. -/
theorem thresholdPriceRun_indep (M : Matroid α)
    [DecidablePred fun S : Finset α => M.Indep (S : Set α)]
    (w : α → ℝ) (σ : Fin (Fintype.card α) ≃ α)
    (j : Fin (Nat.clog 2 M.eRank.toNat + 1)) :
    M.Indep ((thresholdPriceRun M w σ j : Finset α) : Set α) :=
  greedySelect_indep (fun _ => decide_eq_true_iff) _

/-- The randomized Threshold Price experiment drawing `σ` and `j` uniformly and independently. -/
noncomputable def thresholdPricePMF (M : Matroid α)
    [DecidablePred fun S : Finset α => M.Indep (S : Set α)] (w : α → ℝ) : PMF (Finset α) :=
  (uniformOfFintype (Fin (Fintype.card α) ≃ α)).bind fun σ =>
    (uniformOfFintype (Fin (Nat.clog 2 M.eRank.toNat + 1))).map fun j =>
      thresholdPriceRun M w σ j

/-- Every set in the support of `thresholdPricePMF M w` is independent in `M`. -/
theorem thresholdPricePMF_indep (M : Matroid α)
    [DecidablePred fun S : Finset α => M.Indep (S : Set α)] (w : α → ℝ)
    {B : Finset α} (hB : B ∈ (thresholdPricePMF M w).support) :
    M.Indep (B : Set α) := by
  simp only [thresholdPricePMF, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hB
  obtain ⟨σ, _, j, _, rfl⟩ := hB
  exact thresholdPriceRun_indep M w σ j

/-- Expected weight collected by the Threshold Price Algorithm under uniform random arrival order
and uniform random threshold exponent `j : Fin (Nat.clog 2 M.eRank.toNat + 1)`. -/
@[expose] noncomputable def expectedThresholdPrice (M : Matroid α)
    [DecidablePred fun S : Finset α => M.Indep (S : Set α)] (w : α → ℝ) : ℝ :=
  ∑ σ : Fin (Fintype.card α) ≃ α, ∑ j : Fin (Nat.clog 2 M.eRank.toNat + 1),
    ((uniformOfFintype (Fin (Fintype.card α) ≃ α) σ).toReal) *
      ((uniformOfFintype (Fin (Nat.clog 2 M.eRank.toNat + 1)) j).toReal) *
      ∑ x ∈ thresholdPriceRun M w σ j, w x

private theorem expectedThresholdPrice_nonneg (M : Matroid α)
    [DecidablePred fun S : Finset α => M.Indep (S : Set α)] {w : α → ℝ} (hw : ∀ x, 0 ≤ w x) :
    0 ≤ expectedThresholdPrice M w :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (Finset.sum_nonneg fun x _ => hw x)

theorem expectedThresholdPrice_eq_tsum (M : Matroid α)
    [DecidablePred fun S : Finset α => M.Indep (S : Set α)] (w : α → ℝ) :
    expectedThresholdPrice M w =
      ∑ B : Finset α, ((thresholdPricePMF M w B).toReal) * ∑ x ∈ B, w x := by
  classical
  have hpmf : ∀ B : Finset α, (thresholdPricePMF M w B).toReal =
      ∑ σ : Fin (Fintype.card α) ≃ α, ∑ j : Fin (Nat.clog 2 M.eRank.toNat + 1),
        ((uniformOfFintype (Fin (Fintype.card α) ≃ α) σ).toReal) *
          ((uniformOfFintype (Fin (Nat.clog 2 M.eRank.toNat + 1)) j).toReal) *
          (if B = thresholdPriceRun M w σ j then (1 : ℝ) else 0) := by
    intro B
    unfold thresholdPricePMF
    rw [PMF.bind_apply, tsum_fintype]
    simp_rw [PMF.map_apply, tsum_fintype, Finset.mul_sum]
    rw [ENNReal.toReal_sum]
    · refine Finset.sum_congr rfl fun σ _ => ?_
      rw [ENNReal.toReal_sum]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [ENNReal.toReal_mul]
        split_ifs
        · simp
        · simp
      · intro j _
        split_ifs with hB
        · exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)
        · simp
    · intro σ _
      refine ENNReal.sum_ne_top.mpr fun j _ => ?_
      split_ifs with hB
      · exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)
      · simp
  unfold expectedThresholdPrice
  simp_rw [hpmf, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [mul_assoc]
  have hfin :
      (∑ B : Finset α,
          (if B = thresholdPriceRun M w σ j then (1 : ℝ) else 0) * ∑ x ∈ B, w x) =
        ∑ x ∈ thresholdPriceRun M w σ j, w x := by
    simp [Finset.sum_ite_eq']
  calc ((uniformOfFintype (Fin (Fintype.card α) ≃ α) σ).toReal) *
          (((uniformOfFintype (Fin (Nat.clog 2 M.eRank.toNat + 1)) j).toReal) *
            ∑ x ∈ thresholdPriceRun M w σ j, w x)
      = ((uniformOfFintype (Fin (Fintype.card α) ≃ α) σ).toReal) *
          (((uniformOfFintype (Fin (Nat.clog 2 M.eRank.toNat + 1)) j).toReal) *
            ∑ B : Finset α,
              (if B = thresholdPriceRun M w σ j then (1 : ℝ) else 0) * ∑ x ∈ B, w x) := by
          rw [hfin]
    _ = ∑ B : Finset α, ((uniformOfFintype (Fin (Fintype.card α) ≃ α) σ).toReal) *
          (((uniformOfFintype (Fin (Nat.clog 2 M.eRank.toNat + 1)) j).toReal) *
            ((if B = thresholdPriceRun M w σ j then (1 : ℝ) else 0) * ∑ x ∈ B, w x)) := by
          simp_rw [Finset.mul_sum]

/-- Every element chosen by `thresholdPriceRun` arrived after the sample, has strictly positive
weight, and exceeds or equals the sampled threshold `τ = sampleMax w S / 2 ^ j`. -/
theorem thresholdPriceRun_subset_post (M : Matroid α)
    [DecidablePred fun S : Finset α => M.Indep (S : Set α)]
    (w : α → ℝ) (σ : Fin (Fintype.card α) ≃ α)
    (j : Fin (Nat.clog 2 M.eRank.toNat + 1)) {x : α}
    (hx : x ∈ thresholdPriceRun M w σ j) :
    x ∈ postSampleList σ ((Fintype.card α + 1) / 2) ∧ 0 < w x ∧
      sampleMax w (sampleSet σ ((Fintype.card α + 1) / 2)) / (2 : ℝ) ^ (j : ℕ) ≤ w x := by
  have hmem := mem_of_mem_greedySelect hx
  simpa only [List.mem_filter, decide_eq_true_eq] using hmem

private theorem thresholdPriceRun_blocked (M : Matroid α)
    [DecidablePred fun S : Finset α => M.Indep (S : Set α)]
    (w : α → ℝ) (σ : Fin (Fintype.card α) ≃ α)
    (j : Fin (Nat.clog 2 M.eRank.toNat + 1)) {t : α}
    (ht_post : t ∈ postSampleList σ ((Fintype.card α + 1) / 2))
    (ht_pos : 0 < w t)
    (ht_tau : sampleMax w (sampleSet σ ((Fintype.card α + 1) / 2)) / (2 : ℝ) ^ (j : ℕ) ≤ w t)
    (ht_not : t ∉ thresholdPriceRun M w σ j) :
    ¬ M.Indep ((insert t (thresholdPriceRun M w σ j) : Finset α) : Set α) := by
  have hbas := greedySelect_isBasis' (M := M) (indep := fun S => decide (M.Indep (S : Set α)))
    (fun _ => decide_eq_true_iff)
    ((postSampleList σ ((Fintype.card α + 1) / 2)).filter fun x =>
      decide (0 < w x ∧
        sampleMax w (sampleSet σ ((Fintype.card α + 1) / 2)) / (2 : ℝ) ^ (j : ℕ) ≤ w x))
  have ht_in : t ∈ ((postSampleList σ ((Fintype.card α + 1) / 2)).filter fun x =>
      decide (0 < w x ∧
        sampleMax w (sampleSet σ ((Fintype.card α + 1) / 2)) / (2 : ℝ) ^ (j : ℕ) ≤ w x)) :=
    List.mem_filter.mpr ⟨ht_post, decide_eq_true ⟨ht_pos, ht_tau⟩⟩
  intro hins
  dsimp only [thresholdPriceRun] at ht_not hins
  rw [Finset.coe_insert] at hins
  exact hbas.insert_not_indep ⟨ht_in, ht_not⟩ hins

private theorem exists_best_weight_mem_greedyMaxBasis (M : Matroid α)
    [DecidablePred fun S : Finset α => M.Indep (S : Set α)]
    (w : α → ℝ) (hnl : ∀ x, M.Indep ({x} : Set α)) (hn : 1 ≤ Fintype.card α) :
    let BStar := greedyMaxBasis (fun S => decide (M.Indep (S : Set α))) w Finset.univ.toList
    ∃ x0 ∈ BStar, ∀ y : α, w y ≤ w x0 := by
  intro BStar
  let L := Finset.univ.toList.mergeSort (fun a b => decide (w b ≤ w a))
  have hperm := List.mergeSort_perm Finset.univ.toList (fun a b => decide (w b ≤ w a))
  have hne : L ≠ [] := by
    intro h
    have h0 : (Finset.univ : Finset α).toList.length = 0 := by
      have hlen : L.length = (Finset.univ : Finset α).toList.length := hperm.length_eq
      rw [← hlen, h, List.length_nil]
    rw [Finset.length_toList, Finset.card_univ] at h0
    omega
  cases hL : L with
  | nil => exact absurd hL hne
  | cons u rest =>
    have hsorted : L.Pairwise (fun a b => w b ≤ w a) := by
      simpa [L] using List.pairwise_mergeSort (le := fun a b => decide (w b ≤ w a))
        (fun a b c h₁ h₂ => decide_eq_true (le_trans (of_decide_eq_true h₂) (of_decide_eq_true h₁)))
        (fun a b => by rcases le_total (w b) (w a) with h | h <;> simp [h])
        Finset.univ.toList
    rw [hL] at hsorted
    have hu_mem : u ∈ BStar := by
      change u ∈ greedySelect (fun S => decide (M.Indep (S : Set α))) L
      rw [hL]
      unfold greedySelect
      rw [List.foldl_cons]
      have hu0 : greedyStep (fun S => decide (M.Indep (S : Set α))) ∅ u = {u} := by
        dsimp only [greedyStep]
        have hsing : decide (M.Indep ((insert u (∅ : Finset α) : Finset α) : Set α)) = true :=
          decide_eq_true (by simpa using hnl u)
        simp only [hsing, ↓reduceIte]
        rfl
      rw [hu0]
      have hmono : ∀ (l : List α) (acc : Finset α), acc ⊆ l.foldl
          (greedyStep fun S => decide (M.Indep (S : Set α))) acc := by
        intro l
        induction l with
        | nil => intro acc; exact Finset.Subset.rfl
        | cons z zs ih =>
          intro acc
          simp only [List.foldl_cons]
          refine Finset.Subset.trans ?_ (ih _)
          unfold greedyStep
          split_ifs
          · exact Finset.subset_insert _ _
          · exact Finset.Subset.rfl
      exact hmono rest {u} (Finset.mem_singleton_self u)
    refine ⟨u, hu_mem, fun y => ?_⟩
    have hy_mem : y ∈ L := (hperm.mem_iff).mpr (Finset.mem_toList.mpr (Finset.mem_univ y))
    rw [hL, List.mem_cons] at hy_mem
    rcases hy_mem with rfl | hy_rest
    · exact le_rfl
    · exact (List.pairwise_cons.mp hsorted).1 y hy_rest

private theorem le_half_pow_clog_find {v₁ vi : ℝ} (hv₁ : 0 < v₁) {k : ℕ}
    (hlow : v₁ / (2 : ℝ) ^ Nat.clog 2 k ≤ vi) (hupper : vi ≤ v₁) :
    ∃ j : Fin (Nat.clog 2 k + 1), vi / 2 ≤ v₁ / (2 : ℝ) ^ (j : ℕ) ∧
      v₁ / (2 : ℝ) ^ (j : ℕ) ≤ vi := by
  classical
  have hex : ∃ j : ℕ, v₁ / (2 : ℝ) ^ j ≤ vi := ⟨Nat.clog 2 k, hlow⟩
  let j0 := Nat.find hex
  have hj0_spec : v₁ / (2 : ℝ) ^ j0 ≤ vi := Nat.find_spec hex
  have hj0_le : j0 ≤ Nat.clog 2 k := Nat.find_min' hex hlow
  refine ⟨⟨j0, Nat.lt_succ_of_le hj0_le⟩, ?_, hj0_spec⟩
  rcases Nat.eq_zero_or_pos j0 with hj0 | hj0pos
  · simp only [hj0, pow_zero, div_one]
    have hvi_nonneg : 0 ≤ vi := le_trans (by positivity) hlow
    linarith
  · have hlt := Nat.find_min hex (show j0 - 1 < j0 by omega)
    push Not at hlt
    have hpow : (2 : ℝ) ^ j0 = 2 * (2 : ℝ) ^ (j0 - 1) := by
      have : j0 = j0 - 1 + 1 := by omega
      conv_lhs => rw [this, pow_succ']
    rw [hpow]
    have : v₁ / (2 * (2 : ℝ) ^ (j0 - 1)) = (v₁ / (2 : ℝ) ^ (j0 - 1)) / 2 := by ring
    linarith

/-- **Theorem 3.2 (Threshold Price Algorithm)** of [BabaioffImmorlicaKleinberg2007] (Section 3.2,
p. 5): on well-behaved nonnegative weights (`w x = w y → w x = 0` for `x ≠ y`) over a loopless
finite matroid (`∀ x, M.Indep {x}`) with `2 ≤ |α|`, the expected weight output by
`thresholdPriceRun` is at least `1 / (32 * (⌈log₂ k⌉ + 1))` of the weight of any independent set
`I`, where `k = M.eRank.toNat`. -/
theorem sum_le_mul_expectedThresholdPrice (M : Matroid α)
    [DecidablePred fun S : Finset α => M.Indep (S : Set α)]
    (w : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hwb : ∀ x y, x ≠ y → w x = w y → w x = 0)
    (hnl : ∀ x, M.Indep ({x} : Set α))
    (hn : 2 ≤ Fintype.card α)
    {I : Finset α} (hI : M.Indep (I : Set α)) :
    ∑ x ∈ I, w x ≤
      32 * ((Nat.clog 2 M.eRank.toNat + 1 : ℕ) : ℝ) * expectedThresholdPrice M w := by
  classical
  set n := Fintype.card α
  set s := (n + 1) / 2
  set k := M.eRank.toNat
  set d := Nat.clog 2 k
  set indepB : Finset α → Bool := fun S => decide (M.Indep (S : Set α))
  let BStar := greedyMaxBasis indepB w Finset.univ.toList
  have hBStar_indep : M.Indep (BStar : Set α) :=
    (greedyMaxBasis_isBasis' (M := M) (fun _ => decide_eq_true_iff) w Finset.univ.toList).indep
  have hI_le_BStar : ∑ x ∈ I, w x ≤ ∑ x ∈ BStar, w x :=
    sum_le_greedyMaxBasis_of_indep (M := M) (fun _ => decide_eq_true_iff) w Finset.univ.toList
      (fun x _ => hw x) hI fun x _ => Finset.mem_toList.mpr (Finset.mem_univ x)
  by_cases hzero : ∑ x ∈ BStar, w x = 0
  · rw [hzero] at hI_le_BStar
    exact hI_le_BStar.trans (mul_nonneg (by positivity) (expectedThresholdPrice_nonneg M hw))
  -- `xs`: elements of `BStar` sorted descending by `w`.
  let xs : List α := BStar.toList.mergeSort (fun a b => decide (w b ≤ w a))
  have hperm : xs.Perm BStar.toList := List.mergeSort_perm BStar.toList _
  have hxs_nodup : xs.Nodup := hperm.nodup_iff.mpr BStar.nodup_toList
  have hxs_sorted : xs.Pairwise (fun a b => w b ≤ w a) := by
    simpa [xs] using List.pairwise_mergeSort (le := fun a b => decide (w b ≤ w a))
      (fun a b c h₁ h₂ => decide_eq_true (le_trans (of_decide_eq_true h₂) (of_decide_eq_true h₁)))
      (fun a b => by rcases le_total (w b) (w a) with h | h <;> simp [h])
      BStar.toList
  have hBStar_sum : ∑ x ∈ BStar, w x = (xs.map w).sum := by
    rw [(hperm.map w).sum_eq]
    simp
  have hxs_ne : xs ≠ [] := fun h => hzero (by simp [hBStar_sum, h])
  have hxs_len_pos : 0 < xs.length := List.length_pos_of_ne_nil hxs_ne
  have hxs_len_le_k : xs.length ≤ k := by
    rw [hperm.length_eq, Finset.length_toList]
    exact card_indep_le_eRank_toNat M hBStar_indep
  have hk_pos : 1 ≤ k := Nat.le_trans hxs_len_pos hxs_len_le_k
  let x1 : α := xs[0]'hxs_len_pos
  have hx1_max : ∀ y : α, w y ≤ w x1 := by
    obtain ⟨u, hu_mem, hu_max⟩ := exists_best_weight_mem_greedyMaxBasis M w hnl (by omega)
    have hu_xs : u ∈ xs := hperm.mem_iff.mpr (Finset.mem_toList.mpr hu_mem)
    intro y
    refine (hu_max y).trans ?_
    obtain ⟨idx, hidx, hget⟩ := List.mem_iff_getElem.mp hu_xs
    rw [← hget]
    rcases Nat.eq_zero_or_pos idx with rfl | hidx_pos
    · exact le_rfl
    · exact (List.pairwise_iff_getElem.mp hxs_sorted) 0 idx hxs_len_pos hidx hidx_pos
  have hv1_pos : 0 < w x1 := (hw x1).lt_of_ne fun h => hzero <|
    Finset.sum_eq_zero fun y _ => le_antisymm ((hx1_max y).trans h.ge) (hw y)
  -- Define `v : ℕ → ℝ` with `v t = w xs[t]` for `t < xs.length`, and `q = #{t | w x1 / k ≤ v t}`.
  let v : ℕ → ℝ := fun t => if h : t < xs.length then w (xs[t]'h) else 0
  have hv_nonneg : ∀ t, 0 ≤ v t := fun t => by
    unfold v; split_ifs
    exacts [hw _, le_rfl]
  have hv_anti : ∀ ⦃a b : ℕ⦄, a ≤ b → b < xs.length → v b ≤ v a := by
    intro a b hab hb
    have ha : a < xs.length := hab.trans_lt hb
    simp only [v, ha, hb, ↓reduceDIte]
    rcases eq_or_lt_of_le hab with rfl | halt
    · exact le_rfl
    · exact (List.pairwise_iff_getElem.mp hxs_sorted) a b ha hb halt
  let qFin : Finset (Fin xs.length) := Finset.univ.filter fun t : Fin xs.length =>
    w x1 / (k : ℝ) ≤ v t.val
  have hq0 : (⟨0, hxs_len_pos⟩ : Fin xs.length) ∈ qFin := by
    simp only [qFin, Finset.mem_filter, Finset.mem_univ, true_and, v, hxs_len_pos, ↓reduceDIte]
    change w x1 / (k : ℝ) ≤ w x1
    exact div_le_self hv1_pos.le (by exact_mod_cast hk_pos)
  set q := qFin.card
  have hq_pos : 1 ≤ q := Finset.card_pos.mpr ⟨_, hq0⟩
  have hq_le_len : q ≤ xs.length := (Finset.card_le_univ qFin).trans_eq (Fintype.card_fin _)
  -- Since `v` is antitone, indices `< q` are precisely those with `w x1 / k ≤ v t`.
  have hlt_q_ge : ∀ t : Fin q, w x1 / (k : ℝ) ≤ v t.val := by
    intro t
    by_contra hlt
    push Not at hlt
    have hsub : qFin ⊆ Finset.univ.filter fun u : Fin xs.length => u.val < t.val := by
      intro u hu
      have hu_ge : w x1 / (k : ℝ) ≤ v u.val := (Finset.mem_filter.mp hu).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      by_contra hge
      push Not at hge
      have hle : v u.val ≤ v t.val := hv_anti hge u.isLt
      linarith
    have hcard : q ≤ t.val := by
      calc q = qFin.card := rfl
        _ ≤ (Finset.univ.filter fun u : Fin xs.length => u.val < t.val).card :=
          Finset.card_le_card hsub
        _ = t.val := card_filter_fin_lt xs.length t.val (t.isLt.le.trans hq_le_len)
    exact absurd t.isLt (not_lt.mpr hcard)
  have hge_q_lt : ∀ t : Fin xs.length, q ≤ t.val → v t.val < w x1 / (k : ℝ) := by
    intro t ht
    by_contra hge
    push Not at hge
    have hsub : (Finset.univ.filter fun u : Fin xs.length => u.val ≤ t.val) ⊆ qFin := by
      intro u hu
      have hut : u.val ≤ t.val := (Finset.mem_filter.mp hu).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      exact hge.trans (hv_anti hut t.isLt)
    have hcard_le :
        (Finset.univ.filter fun u : Fin xs.length => u.val ≤ t.val).card = t.val + 1 := by
      rw [← Fin.card_Iic t]
      congr 1
      ext u
      simp only [Finset.mem_Iic, Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
    have hq_ge : t.val + 1 ≤ q := by
      calc t.val + 1 =
          (Finset.univ.filter fun u : Fin xs.length => u.val ≤ t.val).card := hcard_le.symm
        _ ≤ qFin.card := Finset.card_le_card hsub
    omega
  -- `BStar` total weight is at most `2 * ∑ j : Fin q, v j.val`.
  have hsum_top_half : ∑ x ∈ BStar, w x ≤ 2 * ∑ j : Fin q, v j.val := by
    have hxs_sum_eq : (xs.map w).sum = ∑ t : Fin xs.length, v t.val := by
      rw [list_map_sum_eq_sum_fin]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp [v, t.isLt]
    have hsplit : ∑ t : Fin xs.length, v t.val =
        (∑ j : Fin q, v j.val) +
          ∑ t ∈ Finset.univ.filter (fun u : Fin xs.length => q ≤ u.val), v t.val := by
      have hpart := (Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin xs.length))
        (fun u : Fin xs.length => u.val < q) (fun u => v u.val)).symm
      rw [hpart]
      congr 1
      · refine Finset.sum_bij (fun u hu => ⟨u.val, (Finset.mem_filter.mp hu).2⟩) ?_ ?_ ?_ ?_
        · intro u _; exact Finset.mem_univ _
        · intro a _ b _ h; exact Fin.ext (by simpa using congrArg Fin.val h)
        · intro j _
          exact ⟨⟨j.val, j.isLt.trans_le hq_le_len⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩, rfl⟩
        · intro _ _; rfl
      · congr 1
        ext u
        simp [not_lt]
    have htail : ∑ t ∈ Finset.univ.filter (fun u : Fin xs.length => q ≤ u.val), v t.val ≤
        ∑ j : Fin q, v j.val := by
      have hcard_tail : (Finset.univ.filter fun u : Fin xs.length => q ≤ u.val).card =
          xs.length - q := card_filter_fin_ge xs.length q hq_le_len
      have hstep : ∑ t ∈ Finset.univ.filter (fun u : Fin xs.length => q ≤ u.val), v t.val ≤
          ((xs.length - q : ℕ) : ℝ) * (w x1 / (k : ℝ)) := by
        calc ∑ t ∈ Finset.univ.filter (fun u : Fin xs.length => q ≤ u.val), v t.val
            ≤ ∑ _t ∈ Finset.univ.filter (fun u : Fin xs.length => q ≤ u.val), (w x1 / (k : ℝ)) :=
              Finset.sum_le_sum fun t ht => (hge_q_lt t (Finset.mem_filter.mp ht).2).le
          _ = ((xs.length - q : ℕ) : ℝ) * (w x1 / (k : ℝ)) := by
              rw [Finset.sum_const, hcard_tail, nsmul_eq_mul]
      have hcard_mul : ((xs.length - q : ℕ) : ℝ) * (w x1 / (k : ℝ)) ≤ w x1 := by
        have hk_real : (0 : ℝ) < k := by exact_mod_cast hk_pos
        calc ((xs.length - q : ℕ) : ℝ) * (w x1 / (k : ℝ))
            ≤ (k : ℝ) * (w x1 / (k : ℝ)) := by gcongr; omega
          _ = w x1 := mul_div_cancel₀ _ hk_real.ne'
      have hv0_le : w x1 ≤ ∑ j : Fin q, v j.val := by
        calc w x1 = v 0 := by
              dsimp only [v, x1]
              simp only [hxs_len_pos, ↓reduceDIte]
          _ = v (⟨0, hq_pos⟩ : Fin q).val := rfl
          _ ≤ ∑ j : Fin q, v j.val :=
            Finset.single_le_sum (f := fun j : Fin q => v j.val) (fun j _ => hv_nonneg _)
              (Finset.mem_univ (⟨0, hq_pos⟩ : Fin q))
      exact hstep.trans (hcard_mul.trans hv0_le)
    rw [hBStar_sum, hxs_sum_eq, hsplit]
    linarith
  -- Layer expectation bound: for every `i : Fin q`, `((i.val + 1 : ℕ) : ℝ)` is at most
  -- `8 * (d + 1) * E[countGE (v i.val / 2) B]`.
  let μσ := uniformOfFintype (Fin n ≃ α)
  let μj := uniformOfFintype (Fin (d + 1))
  have hlayer_prob : ∀ i : Fin q,
      ((i.val + 1 : ℕ) : ℝ) ≤
        8 * ((d + 1 : ℕ) : ℝ) *
          ∑ σ : Fin n ≃ α, ∑ j : Fin (d + 1), (μσ σ).toReal * (μj j).toReal *
            ((((thresholdPriceRun M w σ j).filter fun y => v i.val / 2 ≤ w y).card : ℕ) : ℝ) := by
    intro i
    have hi_len : i.val < xs.length := i.isLt.trans_le hq_le_len
    have hcard_perm : (Fintype.card (Fin n ≃ α) : ℝ) = ((Nat.factorial n : ℕ) : ℝ) := by
      rw [Fintype.card_equiv (Fintype.equivFin α).symm, Fintype.card_fin]
    have hμσ_eq : ∀ σ, (μσ σ).toReal = ((Nat.factorial n : ℕ) : ℝ)⁻¹ := fun σ => by
      simp [μσ, uniformOfFintype_apply, hcard_perm]
    have hμj_eq : ∀ j, (μj j).toReal = ((d + 1 : ℕ) : ℝ)⁻¹ := fun j => by
      simp only [μj, uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv]
      norm_cast
    have hd_pos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
    have hfact_pos : (0 : ℝ) < ((Nat.factorial n : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos n
    rcases Nat.eq_zero_or_pos i.val with hi0 | hipos
    · -- Case `i = 0`: split `x2 ∈ S` and `x1 ∉ S`, with `j = 0`.
      have hne_erase : (Finset.univ.erase x1).Nonempty := Finset.card_pos.mp <| by
        rw [Finset.card_erase_of_mem (Finset.mem_univ x1), Finset.card_univ]; omega
      obtain ⟨x2, hx2_mem, hx2_max⟩ := (Finset.univ.erase x1).exists_max_image w hne_erase
      have hx2_ne : x2 ≠ x1 := (Finset.mem_erase.mp hx2_mem).1
      have hprob_split := one_fourth_le_prob_split hx2_ne hn
      have hpick_x1 : ∀ σ : Fin n ≃ α, x2 ∈ sampleSet σ s → x1 ∉ sampleSet σ s →
          1 ≤ (((thresholdPriceRun M w σ 0).filter fun y => v i.val / 2 ≤ w y).card : ℕ) := by
        intro σ hx2S hx1NS
        have hSmax : sampleMax w (sampleSet σ s) = w x2 := by
          apply le_antisymm
          · refine sampleMax_le ⟨x2, hx2S⟩ fun y hy => ?_
            have hy_ne : y ≠ x1 := fun h => hx1NS (h ▸ hy)
            exact hx2_max y (Finset.mem_erase.mpr ⟨hy_ne, Finset.mem_univ y⟩)
          · exact le_sampleMax_of_mem hx2S
        let Lpost := (postSampleList σ s).filter fun x =>
          decide (0 < w x ∧ sampleMax w (sampleSet σ s) / (2 : ℝ) ^ ((0 : Fin (d + 1)) : ℕ) ≤ w x)
        have hLpost_sub : ∀ y ∈ Lpost, y = x1 := by
          intro y hy
          have hy' := List.mem_filter.mp hy
          simp only [decide_eq_true_eq, Fin.val_zero, pow_zero, div_one, hSmax] at hy'
          by_contra hy_ne
          have hwy_le : w y ≤ w x2 := hx2_max y (Finset.mem_erase.mpr ⟨hy_ne, Finset.mem_univ y⟩)
          have hwy_eq : w y = w x2 := le_antisymm hwy_le hy'.2.2
          have hy_eq_x2 : y = x2 := by
            by_contra hy_ne2
            exact hy'.2.1.ne (hwb y x2 hy_ne2 hwy_eq).symm
          rw [hy_eq_x2] at hy'
          exact (mem_postSampleList_iff_notMem_sampleSet σ s x2).mp hy'.1 hx2S
        have hx1_in_Lpost : x1 ∈ Lpost := by
          refine List.mem_filter.mpr ⟨(mem_postSampleList_iff_notMem_sampleSet σ s x1).mpr hx1NS,
            decide_eq_true ⟨hv1_pos, ?_⟩⟩
          simp only [Fin.val_zero, pow_zero, div_one, hSmax]
          exact hx1_max x2
        have hLpost_nodup : Lpost.Nodup := (postSampleList_nodup σ s).filter _
        have hLpost_eq : Lpost = [x1] := by
          rcases Lpost with _ | ⟨a, r⟩
          · simp at hx1_in_Lpost
          · have ha : a = x1 := hLpost_sub a (List.mem_cons_self ..)
            subst ha
            have hr_nil : r = [] := by
              by_contra hr_ne
              obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil r hr_ne
              have hb_eq : b = x1 := hLpost_sub b (List.mem_cons_of_mem _ hb)
              subst hb_eq
              exact (List.nodup_cons.mp hLpost_nodup).1 hb
            simp [hr_nil]
        have hx1_sel : x1 ∈ thresholdPriceRun M w σ 0 := by
          change x1 ∈ greedySelect indepB Lpost
          rw [hLpost_eq]
          simp only [greedySelect, List.foldl_cons, List.foldl_nil, greedyStep]
          have hind : indepB (insert x1 (∅ : Finset α)) = true :=
            decide_eq_true (by simpa using hnl x1)
          simp only [hind, ite_true]
          exact Finset.mem_singleton_self x1
        have hx1_ge : v i.val / 2 ≤ w x1 := by
          simp only [hi0, v, hxs_len_pos, ↓reduceDIte]
          change w x1 / 2 ≤ w x1
          linarith
        exact Finset.card_pos.mpr ⟨x1, Finset.mem_filter.mpr ⟨hx1_sel, hx1_ge⟩⟩
      have hprob_sum_ge : (1 / 4 : ℝ) ≤
          ∑ σ : Fin n ≃ α, (μσ σ).toReal *
            ((((thresholdPriceRun M w σ 0).filter fun y => v i.val / 2 ≤ w y).card : ℕ) : ℝ) := by
        have hprob_eq : ((μσ.toOuterMeasure {σ | x2 ∈ sampleSet σ s ∧ x1 ∉ sampleSet σ s}).toReal) =
            ∑ σ : Fin n ≃ α, (μσ σ).toReal *
              if x2 ∈ sampleSet σ s ∧ x1 ∉ sampleSet σ s then (1 : ℝ) else 0 := by
          rw [toOuterMeasure_uniformOfFintype_toReal, hcard_perm]
          simp only [hμσ_eq, ← Finset.mul_sum, Set.mem_ofPred_eq, Finset.sum_boole,
            div_eq_inv_mul]
        refine hprob_split.trans (hprob_eq.le.trans (Finset.sum_le_sum fun σ _ => ?_))
        refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
        split_ifs with hs
        · exact_mod_cast hpick_x1 σ hs.1 hs.2
        · positivity
      have hsingle_j : (1 / 4 : ℝ) * (μj 0).toReal ≤
          ∑ σ : Fin n ≃ α, ∑ j : Fin (d + 1), (μσ σ).toReal * (μj j).toReal *
            ((((thresholdPriceRun M w σ j).filter fun y => v i.val / 2 ≤ w y).card : ℕ) : ℝ) := by
        calc (1 / 4 : ℝ) * (μj 0).toReal
            ≤ (∑ σ : Fin n ≃ α, (μσ σ).toReal *
                ((((thresholdPriceRun M w σ 0).filter fun y =>
                  v i.val / 2 ≤ w y).card : ℕ) : ℝ)) * (μj 0).toReal :=
              mul_le_mul_of_nonneg_right hprob_sum_ge ENNReal.toReal_nonneg
          _ = ∑ σ : Fin n ≃ α, (μσ σ).toReal * (μj 0).toReal *
                ((((thresholdPriceRun M w σ 0).filter fun y =>
                  v i.val / 2 ≤ w y).card : ℕ) : ℝ) := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun σ _ => by ring
          _ ≤ ∑ σ : Fin n ≃ α, ∑ j : Fin (d + 1), (μσ σ).toReal * (μj j).toReal *
                ((((thresholdPriceRun M w σ j).filter fun y =>
                  v i.val / 2 ≤ w y).card : ℕ) : ℝ) := by
              refine Finset.sum_le_sum fun σ _ => Finset.single_le_sum (f := fun j : Fin (d + 1) =>
                (μσ σ).toReal * (μj j).toReal *
                  ((((thresholdPriceRun M w σ j).filter fun y => v i.val / 2 ≤ w y).card : ℕ) : ℝ))
                (fun j _ => by positivity) (Finset.mem_univ (0 : Fin (d + 1)))
      have hi_eq : ((i.val + 1 : ℕ) : ℝ) = 1 := by simp [hi0]
      rw [hi_eq]
      rw [hμj_eq 0] at hsingle_j
      calc (1 : ℝ) = 4 * ((d + 1 : ℕ) : ℝ) * ((1 / 4 : ℝ) * ((d + 1 : ℕ) : ℝ)⁻¹) := by
            field_simp
        _ ≤ 8 * ((d + 1 : ℕ) : ℝ) * ((1 / 4 : ℝ) * ((d + 1 : ℕ) : ℝ)⁻¹) := by
            gcongr; norm_num
        _ ≤ _ := mul_le_mul_of_nonneg_left hsingle_j (by positivity)
    · -- Case `0 < i.val`: find bucket `j_i` for `v i.val`, compare against `A ∩ (U \ S)`.
      have hk_pow : k ≤ 2 ^ d := Nat.le_pow_clog (by decide : 1 < 2) k
      have hlow : w x1 / (2 : ℝ) ^ d ≤ v i.val := by
        have hk_le_pow : (k : ℝ) ≤ (2 : ℝ) ^ d := by exact_mod_cast hk_pow
        calc w x1 / (2 : ℝ) ^ d ≤ w x1 / (k : ℝ) :=
              div_le_div_of_nonneg_left hv1_pos.le (by exact_mod_cast hk_pos) hk_le_pow
          _ ≤ v i.val := hlt_q_ge i
      have hupper : v i.val ≤ w x1 := by
        simp only [v, hi_len, ↓reduceDIte]
        exact hx1_max _
      obtain ⟨j0, hj0_half, hj0_le⟩ := le_half_pow_clog_find hv1_pos hlow hupper
      let AList := xs.take (i.val + 1)
      have hAList_len : AList.length = i.val + 1 := List.length_take_of_le (by omega)
      have hAList_nodup : AList.Nodup := hxs_nodup.take
      have hA_indep : M.Indep ((AList.toFinset : Finset α) : Set α) := by
        refine hBStar_indep.subset ?_
        intro x hx
        have hx' : x ∈ xs := List.mem_of_mem_take (List.mem_toFinset.mp hx)
        exact Finset.mem_toList.mp (hperm.mem_iff.mp hx')
      have hcond_card : ∀ σ : Fin n ≃ α, x1 ∈ sampleSet σ s →
          (AList.toFinset.filter fun y => y ∉ sampleSet σ s).card ≤
            ((thresholdPriceRun M w σ j0).filter fun y => v i.val / 2 ≤ w y).card := by
        intro σ hx1S
        have hSmax : sampleMax w (sampleSet σ s) = w x1 :=
          le_antisymm (sampleMax_le ⟨x1, hx1S⟩ fun y _ => hx1_max y) (le_sampleMax_of_mem hx1S)
        set τ := sampleMax w (sampleSet σ s) / (2 : ℝ) ^ (j0 : ℕ)
        have hτ_eq : τ = w x1 / (2 : ℝ) ^ (j0 : ℕ) := by simp [τ, hSmax]
        have hτ_pos : 0 < τ := by rw [hτ_eq]; positivity
        have hτ_ge_half : v i.val / 2 ≤ τ := hτ_eq ▸ hj0_half
        have hτ_le_vi : τ ≤ v i.val := hτ_eq ▸ hj0_le
        let T := AList.toFinset.filter fun y => y ∉ sampleSet σ s
        have hT_indep : M.Indep (T : Set α) :=
          hA_indep.subset (Finset.coe_subset.mpr (Finset.filter_subset _ _))
        have hB_indep : M.Indep ((thresholdPriceRun M w σ j0 : Finset α) : Set α) :=
          thresholdPriceRun_indep M w σ j0
        have hT_ge_tau : ∀ t ∈ T, τ ≤ w t := by
          intro t ht
          have htA : t ∈ AList := List.mem_toFinset.mp (Finset.mem_filter.mp ht).1
          obtain ⟨r, hr, hget⟩ := List.mem_iff_getElem.mp htA
          rw [hAList_len] at hr
          have hget_xs : xs[r]'(hr.trans_le hi_len) = t := by
            dsimp only [AList] at hget
            rw [List.getElem_take] at hget
            exact hget
          have hwr : v i.val ≤ w t := by
            have hr_le : r ≤ i.val := by omega
            have hle_v := hv_anti hr_le hi_len
            simpa only [v, hr.trans_le hi_len, hi_len, ↓reduceDIte, hget_xs] using hle_v
          exact hτ_le_vi.trans hwr
        have hblock : ∀ t ∈ T, t ∉ thresholdPriceRun M w σ j0 →
            ¬ M.Indep ((insert t (thresholdPriceRun M w σ j0) : Finset α) : Set α) := by
          intro t ht ht_not
          have ht_post : t ∈ postSampleList σ s :=
            (mem_postSampleList_iff_notMem_sampleSet σ s t).mpr (Finset.mem_filter.mp ht).2
          have ht_tau : τ ≤ w t := hT_ge_tau t ht
          exact thresholdPriceRun_blocked M w σ j0 ht_post (hτ_pos.trans_le ht_tau) ht_tau ht_not
        have hT_le_B : T.card ≤ (thresholdPriceRun M w σ j0).card := by
          simpa using (isPSystem_matroid M).card_le_mul_card_of_blocked hB_indep hT_indep hblock
        rwa [Finset.filter_true_of_mem fun y hy =>
          hτ_ge_half.trans (thresholdPriceRun_subset_post M w σ j0 hy).2.2]
      have hcount_sum :
          (i.val : ℝ) * (((Nat.factorial n : ℕ) : ℝ) / 4) ≤
            ∑ σ : Fin n ≃ α, (if x1 ∈ sampleSet σ s then (1 : ℝ) else 0) *
              (((AList.toFinset.filter fun y => y ∉ sampleSet σ s).card : ℕ) : ℝ) := by
        have hT_ge_tail : ∀ σ : Fin n ≃ α,
            (∑ r : Fin i.val,
              if AList[r.val + 1]'(by rw [hAList_len]; omega) ∉ sampleSet σ s then (1 : ℝ) else 0) ≤
              (((AList.toFinset.filter fun y => y ∉ sampleSet σ s).card : ℕ) : ℝ) := by
          intro σ
          have hsub : (Finset.univ.filter fun r : Fin i.val =>
              AList[r.val + 1]'(by rw [hAList_len]; omega) ∉ sampleSet σ s).image
              (fun r : Fin i.val => AList[r.val + 1]'(by rw [hAList_len]; omega)) ⊆
              AList.toFinset.filter fun y => y ∉ sampleSet σ s := by
            intro y hy
            obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hy
            exact Finset.mem_filter.mpr
              ⟨List.mem_toFinset.mpr (List.getElem_mem _), (Finset.mem_filter.mp hr).2⟩
          have hinj : Set.InjOn
              (fun r : Fin i.val => AList[r.val + 1]'(by rw [hAList_len]; omega))
              (Finset.univ.filter fun r : Fin i.val =>
                AList[r.val + 1]'(by rw [hAList_len]; omega) ∉ sampleSet σ s) := by
            intro r₁ _ r₂ _ heq
            have hidx := (hAList_nodup.getElem_inj_iff).mp heq
            exact Fin.ext (by omega)
          have hcard_le := Finset.card_le_card hsub
          rw [Finset.card_image_of_injOn hinj, Finset.card_filter] at hcard_le
          exact_mod_cast hcard_le
        have hstep1 : ∑ r : Fin i.val, ∑ σ : Fin n ≃ α,
            (if x1 ∈ sampleSet σ s ∧
                AList[r.val + 1]'(by rw [hAList_len]; omega) ∉ sampleSet σ s
              then (1 : ℝ) else 0) ≤
            ∑ σ : Fin n ≃ α, (if x1 ∈ sampleSet σ s then (1 : ℝ) else 0) *
              (((AList.toFinset.filter fun y => y ∉ sampleSet σ s).card : ℕ) : ℝ) := by
          rw [Finset.sum_comm]
          refine Finset.sum_le_sum fun σ _ => ?_
          by_cases hx1S : x1 ∈ sampleSet σ s
          · simp only [hx1S, true_and, ↓reduceIte, one_mul]
            exact hT_ge_tail σ
          · simp [hx1S]
        have hsplit_r : ∀ r : Fin i.val,
            (((Nat.factorial n : ℕ) : ℝ) / 4) ≤
              ∑ σ : Fin n ≃ α, (if x1 ∈ sampleSet σ s ∧
                  AList[r.val + 1]'(by rw [hAList_len]; omega) ∉ sampleSet σ s
                then (1 : ℝ) else 0) := by
          intro r
          have hne_xr : x1 ≠ AList[r.val + 1]'(by rw [hAList_len]; omega) := by
            intro h
            have h0 : AList[0]'(by rw [hAList_len]; omega) = x1 := List.getElem_take
            rw [← h0] at h
            have heq := (hAList_nodup.getElem_inj_iff).mp h
            omega
          have hprob := one_fourth_le_prob_split hne_xr hn
          have hprob_eq : ((μσ.toOuterMeasure
              {σ | x1 ∈ sampleSet σ s ∧
                AList[r.val + 1]'(by rw [hAList_len]; omega) ∉ sampleSet σ s}).toReal) =
              ((Nat.factorial n : ℕ) : ℝ)⁻¹ * ∑ σ : Fin n ≃ α,
                (if x1 ∈ sampleSet σ s ∧
                    AList[r.val + 1]'(by rw [hAList_len]; omega) ∉ sampleSet σ s
                  then (1 : ℝ) else 0) := by
            rw [toOuterMeasure_uniformOfFintype_toReal, hcard_perm]
            simp only [Set.mem_ofPred_eq, Finset.sum_boole, div_eq_inv_mul]
          rw [hprob_eq] at hprob
          have hmul := mul_le_mul_of_nonneg_left hprob hfact_pos.le
          rw [← mul_assoc, mul_inv_cancel₀ hfact_pos.ne', one_mul] at hmul
          linarith
        have hsum_r : (i.val : ℝ) * (((Nat.factorial n : ℕ) : ℝ) / 4) ≤
            ∑ r : Fin i.val, ∑ σ : Fin n ≃ α,
              (if x1 ∈ sampleSet σ s ∧
                  AList[r.val + 1]'(by rw [hAList_len]; omega) ∉ sampleSet σ s
                then (1 : ℝ) else 0) := by
          calc (i.val : ℝ) * (((Nat.factorial n : ℕ) : ℝ) / 4)
              = ∑ _r : Fin i.val, (((Nat.factorial n : ℕ) : ℝ) / 4) := by
                simp [Finset.sum_const, nsmul_eq_mul]
            _ ≤ _ := Finset.sum_le_sum fun r _ => hsplit_r r
        exact hsum_r.trans hstep1
      have hsingle_j0 :
          (i.val : ℝ) / (4 * ((d + 1 : ℕ) : ℝ)) ≤
            ∑ σ : Fin n ≃ α, (μσ σ).toReal * (μj j0).toReal *
              ((((thresholdPriceRun M w σ j0).filter fun y =>
                v i.val / 2 ≤ w y).card : ℕ) : ℝ) := by
        have hstep_sum :
            ∑ σ : Fin n ≃ α, (if x1 ∈ sampleSet σ s then (1 : ℝ) else 0) *
              (((AList.toFinset.filter fun y => y ∉ sampleSet σ s).card : ℕ) : ℝ) ≤
            ∑ σ : Fin n ≃ α,
              ((((thresholdPriceRun M w σ j0).filter fun y =>
                v i.val / 2 ≤ w y).card : ℕ) : ℝ) := by
          refine Finset.sum_le_sum fun σ _ => ?_
          by_cases hx1S : x1 ∈ sampleSet σ s
          · simp only [hx1S, ↓reduceIte, one_mul]
            exact_mod_cast hcond_card σ hx1S
          · simp only [hx1S, ↓reduceIte, zero_mul]
            positivity
        have hcomb := hcount_sum.trans hstep_sum
        have hfactor : ∑ σ : Fin n ≃ α, (μσ σ).toReal * (μj j0).toReal *
            ((((thresholdPriceRun M w σ j0).filter fun y =>
              v i.val / 2 ≤ w y).card : ℕ) : ℝ) =
            ((Nat.factorial n : ℕ) : ℝ)⁻¹ * ((d + 1 : ℕ) : ℝ)⁻¹ *
              ∑ σ : Fin n ≃ α, ((((thresholdPriceRun M w σ j0).filter fun y =>
                v i.val / 2 ≤ w y).card : ℕ) : ℝ) := by
          simp only [hμσ_eq, hμj_eq, Finset.mul_sum]
        rw [hfactor]
        have hmul := mul_le_mul_of_nonneg_left hcomb (by positivity :
          0 ≤ ((Nat.factorial n : ℕ) : ℝ)⁻¹ * ((d + 1 : ℕ) : ℝ)⁻¹)
        have hl : ((Nat.factorial n : ℕ) : ℝ)⁻¹ * ((d + 1 : ℕ) : ℝ)⁻¹ *
            ((i.val : ℝ) * (((Nat.factorial n : ℕ) : ℝ) / 4)) =
            (i.val : ℝ) / (4 * ((d + 1 : ℕ) : ℝ)) := by
          field_simp
        nlinarith
      have hfull_j : (i.val : ℝ) / (4 * ((d + 1 : ℕ) : ℝ)) ≤
          ∑ σ : Fin n ≃ α, ∑ j : Fin (d + 1), (μσ σ).toReal * (μj j).toReal *
            ((((thresholdPriceRun M w σ j).filter fun y => v i.val / 2 ≤ w y).card : ℕ) : ℝ) := by
        refine hsingle_j0.trans (Finset.sum_le_sum fun σ _ => ?_)
        exact Finset.single_le_sum (f := fun j : Fin (d + 1) =>
          (μσ σ).toReal * (μj j).toReal *
            ((((thresholdPriceRun M w σ j).filter fun y => v i.val / 2 ≤ w y).card : ℕ) : ℝ))
          (fun j _ => by positivity) (Finset.mem_univ j0)
      calc ((i.val + 1 : ℕ) : ℝ) ≤ 2 * (i.val : ℝ) := by
            exact_mod_cast show i.val + 1 ≤ 2 * i.val by omega
        _ = 8 * ((d + 1 : ℕ) : ℝ) * ((i.val : ℝ) / (4 * ((d + 1 : ℕ) : ℝ))) := by
            field_simp; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hfull_j (by positivity)
  have hgap_nonneg : ∀ i : Fin q, 0 ≤ layerGap v q i := by
    intro i
    unfold layerGap
    split_ifs with hi
    · exact sub_nonneg.mpr (hv_anti (by omega) (hi.trans_le hq_le_len))
    · rw [sub_zero]
      exact hv_nonneg _
  have hv_anti_q : ∀ ⦃a b : ℕ⦄, a ≤ b → b < q → v b ≤ v a := fun _ _ hab hb =>
    hv_anti hab (hb.trans_le hq_le_len)
  have hswap :
      2 * ∑ i : Fin q, layerGap v q i * (8 * ((d + 1 : ℕ) : ℝ) *
          ∑ σ : Fin n ≃ α, ∑ j : Fin (d + 1), (μσ σ).toReal * (μj j).toReal *
            ((((thresholdPriceRun M w σ j).filter fun y =>
              v i.val / 2 ≤ w y).card : ℕ) : ℝ)) =
        16 * ((d + 1 : ℕ) : ℝ) *
          ∑ σ : Fin n ≃ α, ∑ j : Fin (d + 1), (μσ σ).toReal * (μj j).toReal *
            ∑ i : Fin q, layerGap v q i *
              ((((thresholdPriceRun M w σ j).filter fun y =>
                v i.val / 2 ≤ w y).card : ℕ) : ℝ) := by
    have h1 : ∀ i : Fin q,
        layerGap v q i * (8 * ((d + 1 : ℕ) : ℝ) *
          ∑ σ : Fin n ≃ α, ∑ j : Fin (d + 1), (μσ σ).toReal * (μj j).toReal *
            ((((thresholdPriceRun M w σ j).filter fun y =>
              v i.val / 2 ≤ w y).card : ℕ) : ℝ)) =
        8 * ((d + 1 : ℕ) : ℝ) * ∑ σ : Fin n ≃ α, ∑ j : Fin (d + 1),
          (μσ σ).toReal * (μj j).toReal * (layerGap v q i *
            ((((thresholdPriceRun M w σ j).filter fun y =>
              v i.val / 2 ≤ w y).card : ℕ) : ℝ)) := by
      intro i
      rw [mul_left_comm (layerGap v q i), Finset.mul_sum]
      refine congrArg (8 * ((d + 1 : ℕ) : ℝ) * ·) (Finset.sum_congr rfl fun σ _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    simp_rw [h1]
    rw [← Finset.mul_sum, ← mul_assoc, show (2 : ℝ) * (8 * ((d + 1 : ℕ) : ℝ)) =
      16 * ((d + 1 : ℕ) : ℝ) by ring, Finset.sum_comm]
    refine congrArg (16 * ((d + 1 : ℕ) : ℝ) * ·) (Finset.sum_congr rfl fun σ _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
  calc ∑ x ∈ I, w x ≤ ∑ x ∈ BStar, w x := hI_le_BStar
    _ ≤ 2 * ∑ j : Fin q, v j.val := hsum_top_half
    _ = 2 * ∑ i : Fin q, layerGap v q i * ((i.val + 1 : ℕ) : ℝ) := by rw [sum_layerGap_mul_succ]
    _ ≤ 2 * ∑ i : Fin q, layerGap v q i *
          (8 * ((d + 1 : ℕ) : ℝ) *
            ∑ σ : Fin n ≃ α, ∑ j : Fin (d + 1), (μσ σ).toReal * (μj j).toReal *
              ((((thresholdPriceRun M w σ j).filter fun y =>
                v i.val / 2 ≤ w y).card : ℕ) : ℝ)) := by
          gcongr with i
          · exact hgap_nonneg i
          · exact hlayer_prob i
    _ = 16 * ((d + 1 : ℕ) : ℝ) *
          ∑ σ : Fin n ≃ α, ∑ j : Fin (d + 1), (μσ σ).toReal * (μj j).toReal *
            ∑ i : Fin q, layerGap v q i *
              ((((thresholdPriceRun M w σ j).filter fun y =>
                v i.val / 2 ≤ w y).card : ℕ) : ℝ) := hswap
    _ ≤ 16 * ((d + 1 : ℕ) : ℝ) *
          ∑ σ : Fin n ≃ α, ∑ j : Fin (d + 1), (μσ σ).toReal * (μj j).toReal *
            (2 * ∑ y ∈ thresholdPriceRun M w σ j, w y) := by
          gcongr with σ _ j
          exact sum_layerGap_mul_countHalf w hv_anti_q fun y _ => hw y
    _ = 32 * ((d + 1 : ℕ) : ℝ) * expectedThresholdPrice M w := by
          have h2 : (∑ σ : Fin n ≃ α, ∑ j : Fin (d + 1), (μσ σ).toReal * (μj j).toReal *
              (2 * ∑ y ∈ thresholdPriceRun M w σ j, w y)) = 2 * expectedThresholdPrice M w := by
            have hpull : ∀ σ j,
                (μσ σ).toReal * (μj j).toReal * (2 * ∑ y ∈ thresholdPriceRun M w σ j, w y) =
                  2 * ((μσ σ).toReal * (μj j).toReal * ∑ y ∈ thresholdPriceRun M w σ j, w y) :=
              fun σ j => by ring
            simp_rw [hpull, ← Finset.mul_sum]
            rfl
          rw [h2]
          ring

/-- `O(log k)` form of **Theorem 3.2** for rank `k = M.eRank.toNat ≥ 2`: since
`⌈log₂ k⌉ + 1 ≤ 2 * ⌈log₂ k⌉`, `Threshold Price` is `(64 * ⌈log₂ k⌉)`-competitive. -/
theorem sum_le_sixtyFour_clog_mul_expectedThresholdPrice (M : Matroid α)
    [DecidablePred fun S : Finset α => M.Indep (S : Set α)]
    (w : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hwb : ∀ x y, x ≠ y → w x = w y → w x = 0)
    (hnl : ∀ x, M.Indep ({x} : Set α))
    (hn : 2 ≤ Fintype.card α) (hr : 2 ≤ M.eRank.toNat)
    {I : Finset α} (hI : M.Indep (I : Set α)) :
    ∑ x ∈ I, w x ≤
      64 * (Nat.clog 2 M.eRank.toNat : ℝ) * expectedThresholdPrice M w := by
  have hclog : 1 ≤ Nat.clog 2 M.eRank.toNat := Nat.clog_pos (by decide) hr
  have hbase := sum_le_mul_expectedThresholdPrice M w hw hwb hnl hn hI
  have hexp_nonneg := expectedThresholdPrice_nonneg M hw
  have hcoef : ((Nat.clog 2 M.eRank.toNat + 1 : ℕ) : ℝ) ≤ 2 * (Nat.clog 2 M.eRank.toNat : ℝ) := by
    exact_mod_cast show Nat.clog 2 M.eRank.toNat + 1 ≤ 2 * Nat.clog 2 M.eRank.toNat by omega
  calc ∑ x ∈ I, w x
      ≤ 32 * ((Nat.clog 2 M.eRank.toNat + 1 : ℕ) : ℝ) * expectedThresholdPrice M w := hbase
    _ ≤ 32 * (2 * (Nat.clog 2 M.eRank.toNat : ℝ)) * expectedThresholdPrice M w := by
        gcongr
    _ = 64 * (Nat.clog 2 M.eRank.toNat : ℝ) * expectedThresholdPrice M w := by ring

end ThresholdPrice

end Cslib.Probability.OptimalStopping.MatroidSecretary
