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
  exact ⟨fun ⟨_, ht, h⟩ => h ▸ by simpa using ht, fun h => ⟨σ.symm x, h, by simp⟩⟩

omit [DecidableEq α] in
@[simp]
theorem mem_postSampleList_iff (σ : Fin (Fintype.card α) ≃ α) (s : ℕ) (x : α) :
    x ∈ postSampleList σ s ↔ s ≤ (σ.symm x).val := by
  simp only [postSampleList, List.mem_map]
  constructor
  · rintro ⟨_, ht, rfl⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ht
    simp only [List.length_drop, List.length_finRange, List.getElem_drop, List.getElem_finRange,
      Equiv.symm_apply_apply, Fin.val_cast] at hk ⊢
    omega
  · intro h
    refine ⟨σ.symm x, List.mem_iff_getElem.mpr ⟨(σ.symm x).val - s, ?_, ?_⟩, by simp⟩
    · simp only [List.length_drop, List.length_finRange]; omega
    · rw [List.getElem_drop, List.getElem_finRange]; ext; simp only [Fin.val_cast]; omega

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

private theorem card_fin_equiv (β : Type*) [Fintype β] [DecidableEq β] :
    Fintype.card (Fin (Fintype.card β) ≃ β) = Nat.factorial (Fintype.card β) := by
  have he : (Fin (Fintype.card β) ≃ β) ≃ Equiv.Perm (Fin (Fintype.card β)) :=
    Equiv.equivCongr (Equiv.refl (Fin (Fintype.card β))) (Fintype.equivFin β)
  rw [Fintype.card_congr he, Fintype.card_perm, Fintype.card_fin]

private theorem card_filter_perm_eq_two {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {p q : Fin n} (hpq : p ≠ q) :
    (Finset.univ.filter fun τ : Equiv.Perm (Fin n) => τ i = p ∧ τ j = q).card =
      Nat.factorial (n - 2) := by
  let U : Finset (Fin n) := {i, j}
  let f : Fin n → Fin n := fun x => if x = i then p else q
  have hf : Set.InjOn f U := by
    intro a ha b hb hab
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, U] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp only [f, ↓reduceIte, hij.symm] at hab
    · rfl
    · exact absurd hab hpq
    · exact absurd hab.symm hpq
    · rfl
  have hset : (Finset.univ.filter fun τ : Equiv.Perm (Fin n) => τ i = p ∧ τ j = q) =
      Finset.univ.filter fun τ : Equiv.Perm (Fin n) => ∀ u ∈ U, τ u = f u := by
    ext τ; simp [U, f, hij.symm]
  rw [hset]
  have hres := Equiv.Perm.card_filter_forall_eq_of_injOn U f hf
  rw [Fintype.card_fin, Finset.card_pair hij] at hres
  convert hres

private theorem card_filter_fin_lt (n s : ℕ) (hs : s ≤ n) :
    (Finset.univ.filter fun p : Fin n => p.val < s).card = s := by
  calc (Finset.univ.filter fun p : Fin n => p.val < s).card
      = (Finset.univ : Finset (Fin s)).card :=
        Finset.card_bij (fun p hp => ⟨p.val, (Finset.mem_filter.mp hp).2⟩)
          (fun _ _ => Finset.mem_univ _)
          (fun _ _ _ _ h => Fin.ext (by simpa using congrArg Fin.val h))
          fun k _ => ⟨⟨k.val, k.isLt.trans_le hs⟩, by simp, rfl⟩
    _ = s := by simp

private theorem card_filter_fin_ge (n s : ℕ) (hs : s ≤ n) :
    (Finset.univ.filter fun q : Fin n => s ≤ q.val).card = n - s := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (p := fun q : Fin n => q.val < s)
  simp only [Finset.card_univ, Fintype.card_fin, card_filter_fin_lt n s hs, not_lt] at h
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
        (τ (e a)).val < s ∧ s ≤ (τ (e b)).val).card :=
    Finset.card_bij (fun σ _ => conv σ)
      (fun σ hσ => by simpa [conv, not_lt] using hσ)
      (fun _ _ _ _ h => conv.injective h)
      fun τ hτ => ⟨conv.symm τ, by simpa [conv, not_lt] using hτ, conv.apply_symm_apply τ⟩
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
    exact ⟨fun h => ⟨(τ (e a), τ (e b)), h, rfl, rfl⟩, fun ⟨_, h, h1, h2⟩ => h1 ▸ h2 ▸ h⟩
  have hdisj : ((P ×ˢ Q : Finset (Fin n × Fin n)) : Set (Fin n × Fin n)).PairwiseDisjoint F := by
    rintro ⟨p₁, q₁⟩ _ ⟨p₂, q₂⟩ _ hne
    refine Finset.disjoint_left.mpr fun τ h₁ h₂ => hne ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, F] at h₁ h₂
    exact Prod.ext (h₁.1.symm.trans h₂.1) (h₁.2.symm.trans h₂.2)
  rw [hcover, Finset.card_biUnion hdisj]
  have hfib : ∀ pq ∈ P ×ˢ Q, (F pq).card = Nat.factorial (n - 2) := by
    rintro ⟨p, q⟩ hpq
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, P, Q] at hpq
    exact card_filter_perm_eq_two (e.injective.ne hab) fun h => by
      have hv : p.val = q.val := congrArg Fin.val h; omega
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
  rw [toOuterMeasure_uniformOfFintype_toReal]
  have hfact : Nat.factorial n = n * (n - 1) * Nat.factorial (n - 2) := by
    have h1 := (Nat.mul_factorial_pred (show n ≠ 0 by omega)).symm
    have h2 := (Nat.mul_factorial_pred (show n - 1 ≠ 0 by omega)).symm
    rw [show n - 1 - 1 = n - 2 by omega] at h2
    rw [h1, h2, mul_assoc]
  have hnum : n * (n - 1) ≤ 4 * (s * (n - s)) := by
    rcases Nat.even_or_odd' n with ⟨m, hm | hm⟩
    · have : s = m := by omega
      rw [this, hm, show 2 * m - m = m by omega]
      nlinarith [Nat.sub_le (2 * m) 1]
    · have : s = m + 1 := by omega
      rw [this, hm, show 2 * m + 1 - 1 = 2 * m by omega, show 2 * m + 1 - (m + 1) = m by omega]
      nlinarith
  have hle_nat : Fintype.card (Fin n ≃ α) ≤
      4 * (Finset.univ.filter fun σ : Fin n ≃ α =>
        a ∈ sampleSet σ s ∧ b ∉ sampleSet σ s).card := by
    rw [card_fin_equiv, card_filter_mem_sample_not_mem_sample hab (by omega), hfact]
    simpa [mul_assoc] using Nat.mul_le_mul_right (Nat.factorial (n - 2)) hnum
  have hden : (0 : ℝ) < (Fintype.card (Fin n ≃ α) : ℝ) := by
    rw [card_fin_equiv]; exact_mod_cast Nat.factorial_pos n
  have hle_real : (Fintype.card (Fin n ≃ α) : ℝ) ≤
      4 * ((Finset.univ.filter fun σ : Fin n ≃ α =>
        a ∈ sampleSet σ s ∧ b ∉ sampleSet σ s).card : ℝ) := by exact_mod_cast hle_nat
  simp only [Set.mem_ofPred_eq]
  rw [le_div_iff₀ hden]
  linarith

private theorem factorial_div_four_le_sum_split {a b : α} (hab : a ≠ b)
    (hn : 2 ≤ Fintype.card α) :
    ((Nat.factorial (Fintype.card α) : ℕ) : ℝ) / 4 ≤
      ∑ σ : Fin (Fintype.card α) ≃ α,
        if a ∈ sampleSet σ ((Fintype.card α + 1) / 2) ∧
          b ∉ sampleSet σ ((Fintype.card α + 1) / 2) then (1 : ℝ) else 0 := by
  classical
  have hprob := one_fourth_le_prob_split hab hn
  rw [toOuterMeasure_uniformOfFintype_toReal, card_fin_equiv] at hprob
  have hpos : (0 : ℝ) < (Nat.factorial (Fintype.card α) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  simp only [Set.mem_ofPred_eq, le_div_iff₀ hpos] at hprob
  rw [Finset.sum_boole]
  linarith

end Sampling

/-! ### Lower bound for optimal classical secretary cutoff -/

section OptimalCutoff

open Cslib.Probability.OptimalStopping.Secretary

private theorem cutoffValue_eq_zero (n : ℕ) : cutoffValue n 0 = 1 / (n : ℝ) := by
  rw [← successProb_cutoffRule_succ 0 n, zero_add, successProb_cutoffRule_one]

private theorem cutoffValue_eq_of_pos {n s : ℕ} (hs : 0 < s) :
    cutoffValue n s = (s : ℝ) / n * ∑ i ∈ Finset.Ico s n, (1 : ℝ) / i := by
  have h := successProb_cutoffRule (r := s + 1) (n := n) (by omega)
  rw [successProb_cutoffRule_succ s n] at h
  rw [h]
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
  have hc_le : c ≤ n := by
    have := optimalCutoff_le (by omega : 1 ≤ n + 1)
      (by simp : ∑ i ∈ Finset.Ico (n + 1) (n + 1), (1 : ℝ) / i ≤ 1)
    omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  rcases Nat.eq_zero_or_pos c with hc0 | hcpos
  · rw [hc0]
    have hstep : cutoffValue (n + 1) 0 ≤ cutoffValue n 0 := by
      rw [cutoffValue_eq_zero, cutoffValue_eq_zero]; gcongr; exact_mod_cast Nat.le_succ n
    have hsp := successProb_le_successProb_optimalCutoff (cutoffRule 1) n
    rw [successProb_cutoffRule_succ 0 n] at hsp
    exact hstep.trans hsp
  · set S := ∑ i ∈ Finset.Ico c n, (1 : ℝ) / i
    by_cases hS1 : 1 ≤ S
    · have hcv : cutoffValue (n + 1) c ≤ cutoffValue n c := by
        rw [cutoffValue_eq_of_pos hcpos, cutoffValue_eq_of_pos hcpos, Finset.sum_Ico_succ_top hc_le]
        rw [← sub_nonneg]
        have hdiff : (c : ℝ) / n * S - (c : ℝ) / ((n + 1 : ℕ) : ℝ) * (S + 1 / n) =
            (c : ℝ) * (S - 1) / ((n : ℝ) * ((n + 1 : ℕ) : ℝ)) := by
          push_cast; field_simp; ring
        rw [hdiff]
        exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hS1)) (by positivity)
      have hsp := successProb_le_successProb_optimalCutoff (cutoffRule (c + 1)) n
      rw [successProb_cutoffRule_succ c n] at hsp
      exact hcv.trans hsp
    · push Not at hS1
      have hcv : cutoffValue (n + 1) c ≤ cutoffValue n (c - 1) := by
        rcases eq_or_lt_of_le (Nat.succ_le_of_lt hcpos) with h1 | hc2
        · have hce : c = 1 := h1.symm
          have hn_eq : n = 1 := by
            by_contra hne
            have hge : (1 : ℝ) ≤ S := by
              have h1' : (1 : ℝ) = 1 / ((1 : ℕ) : ℝ) := by norm_num
              rw [h1']
              exact Finset.single_le_sum (f := fun i : ℕ => (1 : ℝ) / i)
                (fun _ _ => by positivity) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
            linarith
          subst hn_eq; rw [hce, cutoffValue_eq_of_pos one_pos, cutoffValue_eq_zero]
          norm_num [Finset.sum_Ico_succ_top]
        · have hcm : 1 ≤ c - 1 := by omega
          have hS_eq : ∑ i ∈ Finset.Ico (c - 1) n, (1 : ℝ) / i = 1 / ((c - 1 : ℕ) : ℝ) + S := by
            rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), show c - 1 + 1 = c by omega]
          rw [cutoffValue_eq_of_pos hcpos, cutoffValue_eq_of_pos hcm,
            Finset.sum_Ico_succ_top hc_le, hS_eq, ← sub_nonneg]
          have hcm_cast : ((c - 1 : ℕ) : ℝ) + 1 = (c : ℝ) := by
            exact_mod_cast show c - 1 + 1 = c by omega
          have hcmr : (0 : ℝ) < ((c - 1 : ℕ) : ℝ) := by exact_mod_cast hcm
          have hdiff : ((c - 1 : ℕ) : ℝ) / n * (1 / ((c - 1 : ℕ) : ℝ) + S) -
              (c : ℝ) / ((n + 1 : ℕ) : ℝ) * (S + 1 / n) =
              ((n : ℝ) + 1 - (c : ℝ)) * (1 - S) / ((n : ℝ) * ((n + 1 : ℕ) : ℝ)) := by
            rw [← hcm_cast]; push_cast; field_simp; ring
          rw [hdiff]
          have hle : (c : ℝ) ≤ n := by exact_mod_cast hc_le
          exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
      have hsp := successProb_le_successProb_optimalCutoff (cutoffRule c) n
      rw [← show c - 1 + 1 = c by omega, successProb_cutoffRule_succ (c - 1) n] at hsp
      exact hcv.trans hsp

/-- **Non-asymptotic `1/e` bound for the optimal secretary cutoff**: for every `n ≥ 1`, the
optimal cutoff rule selects the best of `n` candidates with probability at least `1/e` (without an
`O(1/n)` slack, because the optimal success probability decreases monotonically to `1/e`). -/
theorem exp_neg_one_le_successProb_optimalCutoff {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-1) ≤ successProb (cutoffRule (optimalCutoff n)) n := by
  have hle_all : ∀ k, successProb (cutoffRule (optimalCutoff (n + k))) (n + k) ≤
      successProb (cutoffRule (optimalCutoff n)) n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 := one_le_optimalCutoff (n + k + 1)
      have hstep := cutoffValue_antitone_step (n := n + k) (by omega)
      rw [← successProb_cutoffRule_succ (optimalCutoff (n + k + 1) - 1) (n + k + 1),
        show optimalCutoff (n + k + 1) - 1 + 1 = optimalCutoff (n + k + 1) by omega] at hstep
      exact hstep.trans ih
  exact le_of_tendsto
    (by simpa [Function.comp_def, Nat.add_comm] using
      tendsto_successProb_optimalCutoff.comp (Filter.tendsto_add_atTop_nat n))
    (Filter.Eventually.of_forall hle_all)

end OptimalCutoff

/-! ### Partition matroids: `e`-competitive independent secretary copies -/

section PartitionMatroid

open Cslib.Probability.OptimalStopping.Secretary

local instance instNonemptyEquivPartition (α : Type*) [Fintype α] :
    Nonempty (Fin (Fintype.card α) ≃ α) :=
  ⟨(Fintype.equivFin α).symm⟩

private def blockKey {α : Type*} (w : α → ℝ) (a : α) : ℝ ×ₗ α := toLex (w a, a)

private theorem blockKey_injective {α : Type*} (w : α → ℝ) : Function.Injective (blockKey w) :=
  fun _ _ h => (Prod.ext_iff.mp (ofLex.injective h)).2

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
  congr 1; ext a; simp [mem_blockArrivalList_iff]

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
  simp only [hab] at hk₁_stop
  have hk_val : k₁.val = k₂.val := Option.some.inj (hk₁_stop.symm.trans hk₂_stop)
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
      (Finset.univ.filter fun y : B => blockKey w y.1 < blockKey w b.1) :=
  Finset.ssubset_iff_of_subset
    (fun _ hy => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2.trans h⟩)
    |>.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩,
      fun ha => lt_irrefl _ (Finset.mem_filter.mp ha).2⟩

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
private theorem blockOrderEquiv_lt_iff {α : Type*} [LinearOrder α]
    (w : α → ℝ) (B : Finset α) (a b : B) :
    blockOrderEquiv w B a < blockOrderEquiv w B b ↔ blockKey w a.1 < blockKey w b.1 := by
  have hfwd : ∀ x y : B, blockKey w x.1 < blockKey w y.1 →
      blockOrderEquiv w B x < blockOrderEquiv w B y :=
    fun _ _ h => Finset.card_lt_card (blockKeyFilter_ssubset w B h)
  refine ⟨fun h => ?_, hfwd a b⟩
  by_contra hge
  rcases eq_or_lt_of_le (not_lt.mp hge) with heq | hgt
  · exact lt_irrefl _ (Subtype.ext (blockKey_injective w heq.symm) ▸ h)
  · exact lt_asymm h (hfwd b a hgt)

omit [LinearOrder α] in
private theorem perm_ofSubtype_preserves_block (part : α → ι) (i : ι)
    (τ : Equiv.Perm {a : α // a ∈ Finset.univ.filter fun x => part x = i}) (a : α) :
    part ((Equiv.Perm.ofSubtype τ) a) = i ↔ part a = i := by
  by_cases ha : part a = i
  · have hm : a ∈ Finset.univ.filter fun x => part x = i :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
    rw [Equiv.Perm.ofSubtype_apply_of_mem τ hm]
    exact ⟨fun _ => ha, fun _ => (Finset.mem_filter.mp (τ ⟨a, hm⟩).2).2⟩
  · rw [Equiv.Perm.ofSubtype_apply_of_not_mem τ (by simpa using ha)]

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
      fun a => decide (part a = i) :=
    funext fun a => by simp [Function.comp_apply, perm_ofSubtype_preserves_block]
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

private theorem toOuterMeasure_eq_tsum_mul {β : Type*} (p : PMF β) (s : Set β) :
    p.toOuterMeasure s = ∑' x, p x * s.indicator 1 x := by
  rw [PMF.toOuterMeasure_apply]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ s <;> simp [Set.indicator, hx]

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
  let q := blockOrderEquiv w B
  have htop : ∀ y : B, q y ≤ q xStar := fun y => by
    change (q y).val ≤ (q xStar).val
    have hxq : (q xStar).val = m - 1 := by simp [xStar, q, m]
    rw [hxq]; exact Nat.le_pred_of_lt (q y).isLt
  have hunif : uniformOfFintype (Fin (Fintype.card α) ≃ α) =
      (uniformOfFintype (Fin (Fintype.card α) ≃ α)).bind fun σ =>
        (uniformOfFintype (Equiv.Perm B)).map fun τ => σ.trans (Equiv.Perm.ofSubtype τ) := by
    simp_rw [← PMF.bind_pure_comp]
    rw [PMF.bind_comm]
    refine Eq.symm (Eq.trans ?_ (PMF.bind_const (uniformOfFintype (Equiv.Perm B)) _))
    congr 1 with τ : 1
    change (uniformOfFintype (Fin (Fintype.card α) ≃ α)).bind
      (PMF.pure ∘ fun σ : Fin (Fintype.card α) ≃ α => σ.trans (Equiv.Perm.ofSubtype τ)) = _
    rw [PMF.bind_pure_comp]
    exact uniformOfFintype_map_equiv
      (Equiv.equivCongr (Equiv.refl _) (Equiv.Perm.ofSubtype τ))
  rw [hunif, toOuterMeasure_eq_tsum_mul, tsum_bind_mul]
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
          seq'[k]'(by rw [hlen']; exact hk) = (τ (pσ ⟨k, hk⟩)).1 := fun k hk => by
        simp only [seq', hseq_eq, List.getElem_map]
        exact Equiv.Perm.ofSubtype_apply_of_mem τ (pσ ⟨k, hk⟩).2
      have hranks_eq : (List.ofFn fun k : Fin seq'.length =>
            ((seq'.take k.val).filter fun y =>
              decide (blockKey w seq'[k.val] < blockKey w y)).length) =
          Secretary.relRanks (eτ τ) := by
        rw [Secretary.relRanks, List.ext_getElem_iff]
        refine ⟨by simp [hlen'], fun k hk₁ _ => ?_⟩
        simp only [List.length_ofFn, hlen'] at hk₁
        have hlen_filt : ∀ (l : List α) (p : α → Bool), (l.filter p).length =
            (Finset.univ.filter fun j : Fin l.length => p l[j.val] = true).card := by
          intro l p; induction l with
          | nil => simp
          | cons a t ih =>
            simp only [List.filter_cons]
            change (if p a = true then a :: t.filter p else t.filter p).length =
              (Finset.univ.filter fun i : Fin (t.length + 1) => p (a :: t)[i.val] = true).card
            rw [Finset.card_filter, Fin.sum_univ_succ]
            rw [Finset.card_filter] at ih
            cases hpa : p a <;> simp [hpa, ih]; ring
        simp only [List.getElem_ofFn, Secretary.relRank, hlen_filt, decide_eq_true_eq]
        have hlt_take : (seq'.take k).length = k :=
          List.length_take_of_le (by rw [hlen']; exact hk₁.le)
        refine Finset.card_bij (fun j _ => ⟨j.val, by omega⟩) ?_
          (fun _ _ _ _ h => Fin.ext (by simpa using congrArg Fin.val h)) ?_
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.getElem_take] at hj ⊢
          refine ⟨by change j.val < k; omega, ?_⟩
          rw [hget' k hk₁, hget' j.val (by omega)] at hj
          exact (blockOrderEquiv_lt_iff w B _ _).mpr hj
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          have hj_lt : j.val < k := hj.1
          refine ⟨⟨j.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Fin.ext rfl⟩
          rw [List.getElem_take, hget' k hk₁, hget' j.val j.isLt]
          exact (blockOrderEquiv_lt_iff w B _ _).mp hj.2
      have hxStar_part : part xStar.1 = i := (Finset.mem_filter.mp xStar.2).2
      have hxStar_mem_iff : xStar.1 ∈ partitionSelect part w σ' ↔
          ∃ k : Fin m, seq'[k.val]'(by rw [hlen']; exact k.isLt) = xStar.1 ∧
            stopIndex (cutoffRule (optimalCutoff m)) [] (Secretary.relRanks (eτ τ)) =
              some k.val := by
        have hpart : ∀ seq, blockArrivalList part σ' (part xStar.1) = seq →
            (xStar.1 ∈ partitionSelect part w σ' ↔
              ∃ k : Fin seq.length, seq[k.val] = xStar.1 ∧
                stopIndex (cutoffRule (optimalCutoff seq.length)) []
                  (List.ofFn fun k : Fin seq.length =>
                    ((seq.take k.val).filter fun y =>
                      decide (blockKey w seq[k.val] < blockKey w y)).length) = some k.val) := by
          rintro seq rfl; simp [partitionSelect]
        have hlen_cut : optimalCutoff seq'.length = optimalCutoff m := by rw [hlen']
        rw [hpart seq' (by rw [hxStar_part]), hranks_eq, hlen_cut]
        exact ⟨fun ⟨k, h1, h2⟩ => ⟨⟨k.val, hlen' ▸ k.isLt⟩, h1, h2⟩,
          fun ⟨k, h1, h2⟩ => ⟨⟨k.val, by rw [hlen']; exact k.isLt⟩, h1, h2⟩⟩
      rw [hxStar_mem_iff, Secretary.Wins]
      constructor
      · rintro ⟨k, hkq, hstop⟩
        refine ⟨k, hstop, fun j => ?_⟩
        have hxk : τ (pσ k) = xStar := Subtype.ext ((hget' k.val k.isLt).symm.trans hkq)
        change q (τ (pσ j)) ≤ q (τ (pσ k))
        rw [hxk]; exact htop _
      · rintro ⟨k, hstop, hmax⟩
        refine ⟨k, ?_, hstop⟩
        rw [hget' k.val k.isLt]
        have hmax' := hmax ((eτ τ).symm (q xStar))
        simp only [Equiv.apply_symm_apply] at hmax'
        exact congrArg Subtype.val (q.injective (le_antisymm (htop _) hmax'))
    have hcongr : ∀ τ : Equiv.Perm B,
        ({σ' | xStar.1 ∈ partitionSelect part w σ'} : Set _).indicator
          (1 : (Fin (Fintype.card α) ≃ α) → ℝ≥0∞) (σ.trans (Equiv.Perm.ofSubtype τ)) =
        ({π | Secretary.Wins (cutoffRule (optimalCutoff m)) π} : Set _).indicator 1 (eτ τ) := by
      intro τ
      by_cases h : xStar.1 ∈ partitionSelect part w (σ.trans (Equiv.Perm.ofSubtype τ))
      · simp [Set.indicator, h, (hiff τ).mp h]
      · simp [Set.indicator, h, mt (hiff τ).mpr h]
    simp_rw [hcongr]
    rw [← tsum_map_mul, uniformOfFintype_map_equiv eτ, ← toOuterMeasure_eq_tsum_mul]
  simp_rw [hinner, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
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
  have hq : (q xStar).val < (q ⟨a, ha⟩).val :=
    (blockOrderEquiv_lt_iff w B xStar ⟨a, ha⟩).mpr ((Prod.Lex.toLex_lt_toLex).mpr (Or.inl hlt))
  have hx : (q xStar).val = B.card - 1 := by simp [xStar, q]
  have ha_lt := (q ⟨a, ha⟩).isLt
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
    exact Finset.sum_nonneg fun _ _ =>
      mul_nonneg ENNReal.toReal_nonneg (Finset.sum_nonneg fun x _ => hw x)
  have hinj : Set.InjOn part (I : Set α) := unitPartitionMatroid_indep_iff.mp hI
  let J : Finset ι := I.image part
  let B : ι → Finset α := fun i => Finset.univ.filter fun a : α => part a = i
  let blkW : ι → ℝ := fun i => if h : (B i).Nonempty then w (blockMaxElem part w i h) else 0
  have hI_bound : ∑ x ∈ I, w x ≤ ∑ i ∈ J, blkW i := by
    rw [Finset.sum_image (fun x hx y hy h => hinj hx hy h)]
    refine Finset.sum_le_sum fun x _ => ?_
    have hmem : x ∈ B (part x) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    have hne : (B (part x)).Nonempty := ⟨x, hmem⟩
    simp only [blkW, hne, ↓reduceDIte]
    exact mem_block_le_blockMaxElem part w (part x) hne hmem
  let μ := uniformOfFintype (Fin (Fintype.card α) ≃ α)
  have hstep : ∀ i ∈ J, Real.exp (-1) * blkW i ≤
      ∑ σ : Fin (Fintype.card α) ≃ α, (μ σ).toReal *
        ∑ x ∈ partitionSelect part w σ ∩ B i, w x := by
    intro i _
    dsimp only [blkW]
    split_ifs with hne
    · set xStar := blockMaxElem part w i hne
      have hxStar_mem : xStar ∈ B i := Subtype.prop _
      have hprob_eq : (μ.toOuterMeasure {σ | xStar ∈ partitionSelect part w σ}).toReal =
          Secretary.successProb (cutoffRule (optimalCutoff (B i).card)) (B i).card :=
        block_prob_max_eq_successProb part w i hne
      have hexp_le : Real.exp (-1) ≤
          (μ.toOuterMeasure {σ | xStar ∈ partitionSelect part w σ}).toReal := by
        rw [hprob_eq]; exact exp_neg_one_le_successProb_optimalCutoff hne.card_pos
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
            exact Finset.sum_congr rfl fun σ _ => by split_ifs <;> ring
        _ ≤ ∑ σ : Fin (Fintype.card α) ≃ α, (μ σ).toReal *
              ∑ x ∈ partitionSelect part w σ ∩ B i, w x := by
            refine Finset.sum_le_sum fun σ _ =>
              mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
            split_ifs with hs
            · exact Finset.single_le_sum (fun x _ => hw x) (Finset.mem_inter.mpr ⟨hs, hxStar_mem⟩)
            · exact Finset.sum_nonneg fun x _ => hw x
    · rw [mul_zero]
      exact Finset.sum_nonneg fun _ _ =>
        mul_nonneg ENNReal.toReal_nonneg (Finset.sum_nonneg fun x _ => hw x)
  calc Real.exp (-1) * ∑ x ∈ I, w x
      ≤ ∑ i ∈ J, Real.exp (-1) * blkW i := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left hI_bound (Real.exp_pos (-1)).le
    _ ≤ ∑ i ∈ J, ∑ σ : Fin (Fintype.card α) ≃ α, (μ σ).toReal *
          ∑ x ∈ partitionSelect part w σ ∩ B i, w x := Finset.sum_le_sum hstep
    _ = ∑ σ : Fin (Fintype.card α) ≃ α, (μ σ).toReal *
          ∑ i ∈ J, ∑ x ∈ partitionSelect part w σ ∩ B i, w x := by
        rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
    _ ≤ expectedPartitionSecretary part w := by
        refine Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
        have hdisj : (J : Set ι).PairwiseDisjoint fun i => partitionSelect part w σ ∩ B i :=
          fun _ _ _ _ hne => Finset.disjoint_left.mpr fun _ h₁ h₂ => hne <|
            (Finset.mem_filter.mp (Finset.mem_inter.mp h₁).2).2.symm.trans
              (Finset.mem_filter.mp (Finset.mem_inter.mp h₂).2).2
        rw [← Finset.sum_biUnion hdisj]
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) (fun x _ _ => hw x)
        obtain ⟨_, _, hx'⟩ := Finset.mem_biUnion.mp hx
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
  have htop : M.eRank ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top (Fintype.card α)) <|
    (M.eRank_def ▸ M.eRk_le_encard _).trans <| (Set.encard_mono (Set.subset_univ _)).trans
      (by rw [Set.encard_univ, ENat.card_eq_coe_fintype_card])
  have hc : (I.card : ℕ∞) ≤ M.eRank := (Set.encard_coe_eq_coe_finsetCard I).symm.trans_le
    (hI.eRk_eq_encard.symm.trans_le (M.eRk_le_eRank _))
  exact_mod_cast (ENat.natCast_toNat htop ▸ hc)

private def layerGap (v : ℕ → ℝ) (q : ℕ) (i : Fin q) : ℝ :=
  v i.val - if i.val + 1 < q then v (i.val + 1) else 0

private theorem sum_Ico_sub_succ (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ k ∈ Finset.Ico a b, (f k - f (k + 1)) = f a - f b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih => rw [Finset.sum_Ico_succ_top hab, ih]; ring

private theorem sum_layerGap_ge {v : ℕ → ℝ} {q : ℕ} (j : Fin q) :
    ∑ i : Fin q, (if j ≤ i then layerGap v q i else 0) = v j.val := by
  let f : ℕ → ℝ := fun k => if k < q then v k else 0
  have hfilter : ∑ i : Fin q, (if j ≤ i then layerGap v q i else 0) =
      ∑ k ∈ Finset.Ico j.val q, (f k - f (k + 1)) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun i _ => i.val)
      (fun i hi => Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp hi).2, i.isLt⟩)
      (fun _ _ _ _ h => Fin.ext h)
      (fun k hk => ⟨⟨k, (Finset.mem_Ico.mp hk).2⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_Ico.mp hk).1⟩, rfl⟩)
      fun i _ => by simp [layerGap, f, i.isLt]
  rw [hfilter, sum_Ico_sub_succ f j.isLt.le]
  simp [f, j.isLt]

private theorem sum_layerGap_mul_succ {v : ℕ → ℝ} {q : ℕ} :
    ∑ i : Fin q, layerGap v q i * ((i.val + 1 : ℕ) : ℝ) = ∑ j : Fin q, v j.val := by
  have hcard : ∀ i : Fin q, ((i.val + 1 : ℕ) : ℝ) = ∑ j : Fin q, if j ≤ i then (1 : ℝ) else 0 :=
    fun i => by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
        show (Finset.univ.filter fun j : Fin q => j ≤ i) = Finset.Iic i by ext; simp, Fin.card_Iic]
  simp_rw [hcard, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simpa [mul_ite] using sum_layerGap_ge (v := v) j

open scoped Classical in
private theorem sum_layerGap_mul_countHalf {α : Type*} (w : α → ℝ) {v : ℕ → ℝ} {q : ℕ}
    (hv_anti : ∀ ⦃a b : ℕ⦄, a ≤ b → b < q → v b ≤ v a)
    {S : Finset α} (hS : ∀ y ∈ S, 0 ≤ w y) :
    ∑ i : Fin q, layerGap v q i *
        (((S.filter fun y => v i.val / 2 ≤ w y).card : ℕ) : ℝ) ≤
      2 * ∑ y ∈ S, w y := by
  have hcard : ∀ i : Fin q, (((S.filter fun y => v i.val / 2 ≤ w y).card : ℕ) : ℝ) =
      ∑ y ∈ S, if v i.val / 2 ≤ w y then (1 : ℝ) else 0 := fun i => by
    rw [Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_congr rfl fun _ _ => by split_ifs <;> simp
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
    have hsum :
        ∑ i : Fin q, layerGap v q i * (if v i.val / 2 ≤ w y then (1 : ℝ) else 0) = v i0.val := by
      simpa [hiff, mul_ite] using sum_layerGap_ge (v := v) i0
    linarith
  · push Not at hex
    have hzero : ∑ i : Fin q, layerGap v q i * (if v i.val / 2 ≤ w y then (1 : ℝ) else 0) = 0 :=
      Finset.sum_eq_zero fun i _ => by simp [not_le.mpr (hex i)]
    linarith [hS y hy]

private theorem list_map_sum_eq_sum_fin {α : Type*} (w : α → ℝ) (xs : List α) :
    (xs.map w).sum = ∑ t : Fin xs.length, w xs[t.val] := by
  induction xs with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, ih]
    change w a + ∑ k : Fin t.length, w t[k.val] = ∑ k : Fin (t.length + 1), w (a :: t)[k.val]
    rw [Fin.sum_univ_succ]; simp

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
    [DecidablePred fun S : Finset α => M.Indep (S : Set α)]
    (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) : 0 ≤ expectedThresholdPrice M w :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (Finset.sum_nonneg fun x _ => hw x)

theorem expectedThresholdPrice_eq_tsum (M : Matroid α)
    [DecidablePred fun S : Finset α => M.Indep (S : Set α)] (w : α → ℝ) :
    expectedThresholdPrice M w =
      ∑ B : Finset α, ((thresholdPricePMF M w B).toReal) * ∑ x ∈ B, w x := by
  classical
  have hne : ∀ (p : Prop) [Decidable p] (σ : Fin (Fintype.card α) ≃ α)
      (j : Fin (Nat.clog 2 M.eRank.toNat + 1)),
      uniformOfFintype (Fin (Fintype.card α) ≃ α) σ *
        (if p then uniformOfFintype (Fin (Nat.clog 2 M.eRank.toNat + 1)) j else 0) ≠ ⊤ := by
    intro p _ _ _
    split_ifs
    · exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)
    · simp
  have hpmf : ∀ B : Finset α, (thresholdPricePMF M w B).toReal =
      ∑ σ : Fin (Fintype.card α) ≃ α, ∑ j : Fin (Nat.clog 2 M.eRank.toNat + 1),
        ((uniformOfFintype (Fin (Fintype.card α) ≃ α) σ).toReal) *
          ((uniformOfFintype (Fin (Nat.clog 2 M.eRank.toNat + 1)) j).toReal) *
          (if B = thresholdPriceRun M w σ j then (1 : ℝ) else 0) := fun B => by
    unfold thresholdPricePMF
    rw [PMF.bind_apply, tsum_fintype]
    simp_rw [PMF.map_apply, tsum_fintype, Finset.mul_sum]
    rw [ENNReal.toReal_sum]
    · refine Finset.sum_congr rfl fun σ _ => ?_
      rw [ENNReal.toReal_sum]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [ENNReal.toReal_mul]; split_ifs <;> simp
      · exact fun j _ => @hne _ (Classical.propDecidable _) σ j
    · exact fun σ _ => ENNReal.sum_ne_top.mpr fun j _ => @hne _ (Classical.propDecidable _) σ j
  unfold expectedThresholdPrice
  simp_rw [hpmf, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [mul_assoc, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    one_mul, zero_mul, ite_mul]

/-- Every element chosen by `thresholdPriceRun` arrived after the sample, has strictly positive
weight, and exceeds or equals the sampled threshold `τ = sampleMax w S / 2 ^ j`. -/
theorem thresholdPriceRun_subset_post (M : Matroid α)
    [DecidablePred fun S : Finset α => M.Indep (S : Set α)]
    (w : α → ℝ) (σ : Fin (Fintype.card α) ≃ α)
    (j : Fin (Nat.clog 2 M.eRank.toNat + 1)) {x : α}
    (hx : x ∈ thresholdPriceRun M w σ j) :
    x ∈ postSampleList σ ((Fintype.card α + 1) / 2) ∧ 0 < w x ∧
      sampleMax w (sampleSet σ ((Fintype.card α + 1) / 2)) / (2 : ℝ) ^ (j : ℕ) ≤ w x := by
  simpa only [List.mem_filter, decide_eq_true_eq] using mem_of_mem_greedySelect hx

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
  intro hins
  dsimp only [thresholdPriceRun] at ht_not hins
  rw [Finset.coe_insert] at hins
  exact hbas.insert_not_indep
    ⟨List.mem_filter.mpr ⟨ht_post, decide_eq_true ⟨ht_pos, ht_tau⟩⟩, ht_not⟩ hins

private theorem exists_best_weight_mem_greedyMaxBasis (M : Matroid α)
    [DecidablePred fun S : Finset α => M.Indep (S : Set α)]
    (w : α → ℝ) (hnl : ∀ x, M.Indep ({x} : Set α)) (hn : 1 ≤ Fintype.card α) :
    let BStar := greedyMaxBasis (fun S => decide (M.Indep (S : Set α))) w Finset.univ.toList
    ∃ x0 ∈ BStar, ∀ y : α, w y ≤ w x0 := by
  intro BStar
  let L := Finset.univ.toList.mergeSort (fun a b => decide (w b ≤ w a))
  have hperm := List.mergeSort_perm Finset.univ.toList (fun a b => decide (w b ≤ w a))
  have hsorted : L.Pairwise (fun a b => w b ≤ w a) := by
    simpa [L] using List.pairwise_mergeSort (le := fun a b => decide (w b ≤ w a))
      (fun _ _ _ h₁ h₂ => decide_eq_true (le_trans (of_decide_eq_true h₂) (of_decide_eq_true h₁)))
      (fun a b => by rcases le_total (w b) (w a) with h | h <;> simp [h])
      Finset.univ.toList
  cases hL : L with
  | nil =>
    have hlen : L.length = Fintype.card α := by
      rw [hperm.length_eq, Finset.length_toList, Finset.card_univ]
    rw [hL, List.length_nil] at hlen; omega
  | cons u rest =>
    rw [hL] at hsorted
    have hmono : ∀ (l : List α) (acc : Finset α), acc ⊆ l.foldl
        (greedyStep fun S => decide (M.Indep (S : Set α))) acc := fun l => by
      induction l with
      | nil => exact fun _ => Finset.Subset.rfl
      | cons z zs ih =>
        intro acc
        refine Finset.Subset.trans ?_ (ih _)
        unfold greedyStep
        split_ifs
        · exact Finset.subset_insert _ _
        · exact Finset.Subset.rfl
    have hu_mem : u ∈ BStar := by
      change u ∈ greedySelect (fun S => decide (M.Indep (S : Set α))) L
      rw [hL, greedySelect, List.foldl_cons]
      have hu0 : greedyStep (fun S => decide (M.Indep (S : Set α))) ∅ u = {u} := by
        simp [greedyStep, hnl u]
      rw [hu0]; exact hmono rest {u} (Finset.mem_singleton_self u)
    refine ⟨u, hu_mem, fun y => ?_⟩
    have hy : y ∈ u :: rest := hL ▸ hperm.mem_iff.mpr (Finset.mem_toList.mpr (Finset.mem_univ y))
    rcases List.mem_cons.mp hy with rfl | hy_rest
    · exact le_rfl
    · exact (List.pairwise_cons.mp hsorted).1 y hy_rest

private theorem le_half_pow_clog_find {v₁ vi : ℝ} (hv₁ : 0 < v₁) {k : ℕ}
    (hlow : v₁ / (2 : ℝ) ^ Nat.clog 2 k ≤ vi) (hupper : vi ≤ v₁) :
    ∃ j : Fin (Nat.clog 2 k + 1), vi / 2 ≤ v₁ / (2 : ℝ) ^ (j : ℕ) ∧
      v₁ / (2 : ℝ) ^ (j : ℕ) ≤ vi := by
  classical
  have hex : ∃ j : ℕ, v₁ / (2 : ℝ) ^ j ≤ vi := ⟨Nat.clog 2 k, hlow⟩
  let j0 := Nat.find hex
  refine ⟨⟨j0, Nat.lt_succ_of_le (Nat.find_min' hex hlow)⟩, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos j0 with hj0 | hj0pos
  · simp only [hj0, pow_zero, div_one]; linarith
  · have hlt := not_le.mp (Nat.find_min hex (show j0 - 1 < j0 by omega))
    have hpow : (2 : ℝ) ^ j0 = 2 * (2 : ℝ) ^ (j0 - 1) := by
      conv_lhs => rw [show j0 = j0 - 1 + 1 by omega, pow_succ']
    rw [hpow, show v₁ / (2 * (2 : ℝ) ^ (j0 - 1)) = (v₁ / (2 : ℝ) ^ (j0 - 1)) / 2 by ring]
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
  · exact (hzero ▸ hI_le_BStar).trans
      (mul_nonneg (by positivity) (expectedThresholdPrice_nonneg M w hw))
  -- `xs`: elements of `BStar` sorted descending by `w`.
  let xs : List α := BStar.toList.mergeSort (fun a b => decide (w b ≤ w a))
  have hperm : xs.Perm BStar.toList := List.mergeSort_perm BStar.toList _
  have hxs_nodup : xs.Nodup := hperm.nodup_iff.mpr BStar.nodup_toList
  have hxs_sorted : xs.Pairwise (fun a b => w b ≤ w a) := by
    simpa [xs] using List.pairwise_mergeSort (le := fun a b => decide (w b ≤ w a))
      (fun _ _ _ h₁ h₂ => decide_eq_true (le_trans (of_decide_eq_true h₂) (of_decide_eq_true h₁)))
      (fun a b => by rcases le_total (w b) (w a) with h | h <;> simp [h])
      BStar.toList
  have hBStar_sum : ∑ x ∈ BStar, w x = (xs.map w).sum := by rw [(hperm.map w).sum_eq]; simp
  have hxs_len_pos : 0 < xs.length :=
    List.length_pos_of_ne_nil fun h => hzero (by simp [hBStar_sum, h])
  have hxs_len_le_k : xs.length ≤ k := by
    rw [hperm.length_eq, Finset.length_toList]; exact card_indep_le_eRank_toNat M hBStar_indep
  have hk_pos : 1 ≤ k := Nat.le_trans hxs_len_pos hxs_len_le_k
  let x1 : α := xs[0]'hxs_len_pos
  have hx1_max : ∀ y : α, w y ≤ w x1 := by
    obtain ⟨u, hu_mem, hu_max⟩ := exists_best_weight_mem_greedyMaxBasis M w hnl (by omega)
    obtain ⟨idx, hidx, hget⟩ :=
      List.mem_iff_getElem.mp (hperm.mem_iff.mpr (Finset.mem_toList.mpr hu_mem))
    intro y
    refine (hu_max y).trans (hget ▸ ?_)
    rcases Nat.eq_zero_or_pos idx with rfl | hpos
    · exact le_rfl
    · exact (List.pairwise_iff_getElem.mp hxs_sorted) 0 idx hxs_len_pos hidx hpos
  have hv1_pos : 0 < w x1 := by
    by_contra hle
    exact hzero <| Finset.sum_eq_zero fun y _ =>
      le_antisymm ((hx1_max y).trans (not_lt.mp hle)) (hw y)
  -- Define `v : ℕ → ℝ` with `v t = w xs[t]` for `t < xs.length`, and `q = #{t | w x1 / k ≤ v t}`.
  let v : ℕ → ℝ := fun t => if h : t < xs.length then w (xs[t]'h) else 0
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
    exact div_le_self hv1_pos.le (by exact_mod_cast hk_pos)
  set q := qFin.card
  have hq_pos : 1 ≤ q := Finset.card_pos.mpr ⟨_, hq0⟩
  have hq_le_len : q ≤ xs.length :=
    (Finset.card_filter_le _ _).trans (Fintype.card_fin _).le
  -- Since `v` is antitone, indices `< q` are precisely those with `w x1 / k ≤ v t`.
  have hlt_q_ge : ∀ t : Fin q, w x1 / (k : ℝ) ≤ v t.val := fun t => by
    by_contra hlt
    have hsub : qFin ⊆ Finset.univ.filter fun u : Fin xs.length => u.val < t.val := fun u hu =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        by_contra hge
        linarith [(Finset.mem_filter.mp hu).2, hv_anti (not_lt.mp hge) u.isLt]⟩
    have hcard : q ≤ t.val := (Finset.card_le_card hsub).trans_eq
      (card_filter_fin_lt xs.length t.val (t.isLt.le.trans hq_le_len))
    exact absurd t.isLt (not_lt.mpr hcard)
  have hge_q_lt : ∀ t : Fin xs.length, q ≤ t.val → v t.val < w x1 / (k : ℝ) := fun t ht => by
    by_contra hge
    have hsub : Finset.Iic t ⊆ qFin := fun u hu =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (not_lt.mp hge).trans (hv_anti (Fin.le_def.mp (Finset.mem_Iic.mp hu)) t.isLt)⟩
    have hq_ge : t.val + 1 ≤ q := (Fin.card_Iic t).symm.trans_le (Finset.card_le_card hsub)
    omega
  -- `BStar` total weight is at most `2 * ∑ j : Fin q, v j.val`.
  have hsum_top_half : ∑ x ∈ BStar, w x ≤ 2 * ∑ j : Fin q, v j.val := by
    have hsplit : ∑ x ∈ BStar, w x = (∑ j : Fin q, v j.val) +
        ∑ t ∈ Finset.univ.filter (fun u : Fin xs.length => q ≤ u.val), v t.val := by
      rw [hBStar_sum, list_map_sum_eq_sum_fin,
        show (∑ t : Fin xs.length, w xs[t.val]) = ∑ t : Fin xs.length, v t.val from
          Finset.sum_congr rfl fun t _ => by simp [v, t.isLt],
        ← Finset.sum_filter_add_sum_filter_not _ (fun u : Fin xs.length => u.val < q)]
      congr 1
      · exact Finset.sum_bij (fun u hu => ⟨u.val, (Finset.mem_filter.mp hu).2⟩)
          (fun _ _ => Finset.mem_univ _)
          (fun _ _ _ _ h => Fin.ext (by simpa using congrArg Fin.val h))
          (fun j _ => ⟨⟨j.val, j.isLt.trans_le hq_le_len⟩, by simp, rfl⟩) fun _ _ => rfl
      · congr 1; ext; simp [not_lt]
    have htail : ∑ t ∈ Finset.univ.filter (fun u : Fin xs.length => q ≤ u.val), v t.val ≤
        ∑ j : Fin q, v j.val := by
      have hk_real : (0 : ℝ) < k := by exact_mod_cast hk_pos
      have hsub_le : ((xs.length - q : ℕ) : ℝ) ≤ k := by
        exact_mod_cast show xs.length - q ≤ k by omega
      calc ∑ t ∈ Finset.univ.filter (fun u : Fin xs.length => q ≤ u.val), v t.val
          ≤ ∑ _t ∈ Finset.univ.filter (fun u : Fin xs.length => q ≤ u.val), (w x1 / (k : ℝ)) :=
            Finset.sum_le_sum fun t ht => (hge_q_lt t (Finset.mem_filter.mp ht).2).le
        _ = ((xs.length - q : ℕ) : ℝ) * (w x1 / (k : ℝ)) := by
            rw [Finset.sum_const, card_filter_fin_ge xs.length q hq_le_len, nsmul_eq_mul]
        _ ≤ (k : ℝ) * (w x1 / (k : ℝ)) := mul_le_mul_of_nonneg_right hsub_le (by positivity)
        _ = v (⟨0, hq_pos⟩ : Fin q).val := by
            rw [mul_div_cancel₀ _ hk_real.ne']; simp [v, x1, hxs_len_pos]
        _ ≤ ∑ j : Fin q, v j.val :=
            Finset.single_le_sum (f := fun j : Fin q => v j.val)
              (fun j _ => by simp only [v, j.isLt.trans_le hq_le_len, ↓reduceDIte]; exact hw _)
              (Finset.mem_univ _)
    linarith
  -- Layer expectation bound: for every `i : Fin q`, `((i.val + 1 : ℕ) : ℝ)` is at most
  -- `8 * (d + 1) * E[countGE (v i.val / 2) B]`.
  let μσ := uniformOfFintype (Fin n ≃ α)
  let μj := uniformOfFintype (Fin (d + 1))
  have hμσ_eq : ∀ σ, (μσ σ).toReal = ((Nat.factorial n : ℕ) : ℝ)⁻¹ := fun σ => by
    have hc : Fintype.card (Fin n ≃ α) = Nat.factorial n := card_fin_equiv α
    simp [μσ, uniformOfFintype_apply, hc]
  have hμj_eq : ∀ j, (μj j).toReal = ((d + 1 : ℕ) : ℝ)⁻¹ := fun j => by
    simp only [μj, uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv]; norm_cast
  have hd_pos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
  have hfact_pos : (0 : ℝ) < ((Nat.factorial n : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hlayer_prob : ∀ i : Fin q,
      ((i.val + 1 : ℕ) : ℝ) ≤
        8 * ((d + 1 : ℕ) : ℝ) *
          ∑ σ : Fin n ≃ α, ∑ j : Fin (d + 1), (μσ σ).toReal * (μj j).toReal *
            ((((thresholdPriceRun M w σ j).filter fun y => v i.val / 2 ≤ w y).card : ℕ) : ℝ) := by
    intro i
    have hi_len : i.val < xs.length := i.isLt.trans_le hq_le_len
    have hsingle : ∀ (j0 : Fin (d + 1)) (c : ℝ),
        c * ((Nat.factorial n : ℕ) : ℝ) ≤
          ∑ σ : Fin n ≃ α,
            ((((thresholdPriceRun M w σ j0).filter fun y => v i.val / 2 ≤ w y).card : ℕ) : ℝ) →
        c / ((d + 1 : ℕ) : ℝ) ≤
          ∑ σ : Fin n ≃ α, ∑ j : Fin (d + 1), (μσ σ).toReal * (μj j).toReal *
            ((((thresholdPriceRun M w σ j).filter fun y => v i.val / 2 ≤ w y).card : ℕ) : ℝ) := by
      intro j0 c hc
      have hfactor : ∑ σ : Fin n ≃ α, (μσ σ).toReal * (μj j0).toReal *
          ((((thresholdPriceRun M w σ j0).filter fun y => v i.val / 2 ≤ w y).card : ℕ) : ℝ) =
          ((Nat.factorial n : ℕ) : ℝ)⁻¹ * ((d + 1 : ℕ) : ℝ)⁻¹ *
            ∑ σ : Fin n ≃ α, ((((thresholdPriceRun M w σ j0).filter fun y =>
              v i.val / 2 ≤ w y).card : ℕ) : ℝ) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun σ _ => by rw [hμσ_eq, hμj_eq]
      have hle_j0 : c / ((d + 1 : ℕ) : ℝ) ≤ ∑ σ : Fin n ≃ α, (μσ σ).toReal * (μj j0).toReal *
          ((((thresholdPriceRun M w σ j0).filter fun y => v i.val / 2 ≤ w y).card : ℕ) : ℝ) := by
        rw [hfactor]
        have hmul := mul_le_mul_of_nonneg_left hc
          (by positivity : 0 ≤ ((Nat.factorial n : ℕ) : ℝ)⁻¹ * ((d + 1 : ℕ) : ℝ)⁻¹)
        have hl : ((Nat.factorial n : ℕ) : ℝ)⁻¹ * ((d + 1 : ℕ) : ℝ)⁻¹ *
            (c * ((Nat.factorial n : ℕ) : ℝ)) = c / ((d + 1 : ℕ) : ℝ) := by field_simp
        linarith
      exact hle_j0.trans <| Finset.sum_le_sum fun σ _ =>
        Finset.single_le_sum (f := fun j : Fin (d + 1) => (μσ σ).toReal * (μj j).toReal *
            ((((thresholdPriceRun M w σ j).filter fun y => v i.val / 2 ≤ w y).card : ℕ) : ℝ))
          (fun _ _ => mul_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
            (Nat.cast_nonneg _)) (Finset.mem_univ j0)
    rcases Nat.eq_zero_or_pos i.val with hi0 | hipos
    · -- Case `i = 0`: split `x2 ∈ S` and `x1 ∉ S`, with `j = 0`.
      have hne_erase : (Finset.univ.erase x1).Nonempty := Finset.card_pos.mp <| by
        rw [Finset.card_erase_of_mem (Finset.mem_univ x1), Finset.card_univ]; omega
      obtain ⟨x2, hx2_mem, hx2_max⟩ := (Finset.univ.erase x1).exists_max_image w hne_erase
      have hx2_ne : x2 ≠ x1 := (Finset.mem_erase.mp hx2_mem).1
      have hpick_x1 : ∀ σ : Fin n ≃ α, x2 ∈ sampleSet σ s → x1 ∉ sampleSet σ s →
          1 ≤ ((thresholdPriceRun M w σ 0).filter fun y => v i.val / 2 ≤ w y).card := by
        intro σ hx2S hx1NS
        have hSmax : sampleMax w (sampleSet σ s) = w x2 := le_antisymm
          (sampleMax_le ⟨x2, hx2S⟩ fun y hy =>
            hx2_max y (Finset.mem_erase.mpr ⟨fun h => hx1NS (h ▸ hy), Finset.mem_univ y⟩))
          (le_sampleMax_of_mem hx2S)
        let Lpost := (postSampleList σ s).filter fun x =>
          decide (0 < w x ∧ sampleMax w (sampleSet σ s) / (2 : ℝ) ^ ((0 : Fin (d + 1)) : ℕ) ≤ w x)
        have hLpost_sub : ∀ y ∈ Lpost, y = x1 := fun y hy => by
          have hy' := List.mem_filter.mp hy
          simp only [decide_eq_true_eq, Fin.val_zero, pow_zero, div_one, hSmax] at hy'
          by_contra hy_ne
          have hwy_eq : w y = w x2 :=
            le_antisymm (hx2_max y (Finset.mem_erase.mpr ⟨hy_ne, Finset.mem_univ y⟩)) hy'.2.2
          have hy_eq_x2 : y = x2 := by_contra fun h => hy'.2.1.ne (hwb y x2 h hwy_eq).symm
          exact (mem_postSampleList_iff_notMem_sampleSet σ s x2).mp (hy_eq_x2 ▸ hy'.1) hx2S
        have hx1_in : x1 ∈ Lpost := List.mem_filter.mpr
          ⟨(mem_postSampleList_iff_notMem_sampleSet σ s x1).mpr hx1NS,
            decide_eq_true ⟨hv1_pos, by simpa [hSmax] using hx1_max x2⟩⟩
        have hLpost_eq : Lpost = [x1] := by
          have hnd : Lpost.Nodup := (postSampleList_nodup σ s).filter _
          rcases Lpost with _ | ⟨a, r⟩
          · simp at hx1_in
          · obtain rfl : a = x1 := hLpost_sub a List.mem_cons_self
            have hr : r = [] := List.eq_nil_iff_forall_not_mem.mpr fun b hb =>
              (List.nodup_cons.mp hnd).1 (hLpost_sub b (List.mem_cons_of_mem _ hb) ▸ hb)
            rw [hr]
        have hx1_sel : x1 ∈ thresholdPriceRun M w σ 0 := by
          change x1 ∈ greedySelect indepB Lpost
          rw [hLpost_eq]; simp [greedySelect, greedyStep, indepB, hnl x1]
        have hx1_ge : v i.val / 2 ≤ w x1 := by
          simp only [hi0, v, hxs_len_pos, ↓reduceDIte]; change w x1 / 2 ≤ w x1; linarith
        exact Finset.card_pos.mpr ⟨x1, Finset.mem_filter.mpr ⟨hx1_sel, hx1_ge⟩⟩
      have hcount : (1 / 4 : ℝ) * ((Nat.factorial n : ℕ) : ℝ) ≤
          ∑ σ : Fin n ≃ α,
            ((((thresholdPriceRun M w σ 0).filter fun y => v i.val / 2 ≤ w y).card : ℕ) : ℝ) := by
        have hsplit := factorial_div_four_le_sum_split hx2_ne hn
        refine (by linarith : (1 / 4 : ℝ) * ((Nat.factorial n : ℕ) : ℝ) ≤
            ((Nat.factorial n : ℕ) : ℝ) / 4).trans (hsplit.trans (Finset.sum_le_sum fun σ _ => ?_))
        split_ifs with hs
        · exact_mod_cast hpick_x1 σ hs.1 hs.2
        · positivity
      have hbound := hsingle 0 (1 / 4) hcount
      rw [show ((i.val + 1 : ℕ) : ℝ) = 1 by simp [hi0]]
      calc (1 : ℝ) ≤ 8 * ((d + 1 : ℕ) : ℝ) * ((1 / 4 : ℝ) / ((d + 1 : ℕ) : ℝ)) := by
            rw [show 8 * ((d + 1 : ℕ) : ℝ) * ((1 / 4 : ℝ) / ((d + 1 : ℕ) : ℝ)) = 2 by
              field_simp; ring]
            norm_num
        _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by positivity)
    · -- Case `0 < i.val`: find bucket `j0` for `v i.val`, compare against `A ∩ (U \ S)`.
      have hlow : w x1 / (2 : ℝ) ^ d ≤ v i.val :=
        (div_le_div_of_nonneg_left hv1_pos.le (by exact_mod_cast hk_pos)
          (by exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) k)).trans (hlt_q_ge i)
      obtain ⟨j0, hj0_half, hj0_le⟩ :=
        le_half_pow_clog_find hv1_pos hlow (by simp only [v, hi_len, ↓reduceDIte]; exact hx1_max _)
      let AList := xs.take (i.val + 1)
      have hAList_len : AList.length = i.val + 1 := List.length_take_of_le (by omega)
      have hAList_nodup : AList.Nodup := hxs_nodup.take
      have hA_indep : M.Indep ((AList.toFinset : Finset α) : Set α) :=
        hBStar_indep.subset fun x hx =>
          Finset.mem_toList.mp (hperm.mem_iff.mp (List.mem_of_mem_take (List.mem_toFinset.mp hx)))
      have hcond_card : ∀ σ : Fin n ≃ α, x1 ∈ sampleSet σ s →
          (AList.toFinset.filter fun y => y ∉ sampleSet σ s).card ≤
            ((thresholdPriceRun M w σ j0).filter fun y => v i.val / 2 ≤ w y).card := by
        intro σ hx1S
        have hSmax : sampleMax w (sampleSet σ s) = w x1 :=
          le_antisymm (sampleMax_le ⟨x1, hx1S⟩ fun y _ => hx1_max y) (le_sampleMax_of_mem hx1S)
        set τ := sampleMax w (sampleSet σ s) / (2 : ℝ) ^ (j0 : ℕ)
        have hτ_eq : τ = w x1 / (2 : ℝ) ^ (j0 : ℕ) := by simp [τ, hSmax]
        let T := AList.toFinset.filter fun y => y ∉ sampleSet σ s
        have hblock : ∀ t ∈ T, t ∉ thresholdPriceRun M w σ j0 →
            ¬ M.Indep ((insert t (thresholdPriceRun M w σ j0) : Finset α) : Set α) := by
          intro t ht ht_not
          obtain ⟨r, hr, hget⟩ :=
            List.mem_iff_getElem.mp (List.mem_toFinset.mp (Finset.mem_filter.mp ht).1)
          rw [hAList_len] at hr
          have hwr : v i.val ≤ w t := by
            have hget_xs : xs[r]'(hr.trans_le hi_len) = t := by simpa [AList] using hget
            simpa only [v, hr.trans_le hi_len, hi_len, ↓reduceDIte, hget_xs] using
              hv_anti (by omega : r ≤ i.val) hi_len
          have ht_tau : τ ≤ w t := (hτ_eq ▸ hj0_le).trans hwr
          exact thresholdPriceRun_blocked M w σ j0
            ((mem_postSampleList_iff_notMem_sampleSet σ s t).mpr (Finset.mem_filter.mp ht).2)
            ((show 0 < τ by rw [hτ_eq]; positivity).trans_le ht_tau) ht_tau ht_not
        have hB_eq : (thresholdPriceRun M w σ j0).filter (fun y => v i.val / 2 ≤ w y) =
            thresholdPriceRun M w σ j0 := Finset.filter_true_of_mem fun y hy =>
          (hτ_eq ▸ hj0_half).trans (thresholdPriceRun_subset_post M w σ j0 hy).2.2
        rw [hB_eq]
        simpa using (isPSystem_matroid M).card_le_mul_card_of_blocked
          (thresholdPriceRun_indep M w σ j0)
          (hA_indep.subset (Finset.coe_subset.mpr (Finset.filter_subset _ _))) hblock
      have hcount : ((i.val : ℝ) / 4) * ((Nat.factorial n : ℕ) : ℝ) ≤
          ∑ σ : Fin n ≃ α,
            ((((thresholdPriceRun M w σ j0).filter fun y => v i.val / 2 ≤ w y).card : ℕ) : ℝ) := by
        have hT_ge_tail : ∀ σ : Fin n ≃ α,
            (∑ r : Fin i.val,
              if AList[r.val + 1]'(by rw [hAList_len]; omega) ∉ sampleSet σ s then (1 : ℝ) else 0) ≤
              (((AList.toFinset.filter fun y => y ∉ sampleSet σ s).card : ℕ) : ℝ) := fun σ => by
          let f : Fin i.val → α := fun r => AList[r.val + 1]'(by rw [hAList_len]; omega)
          have hcard_le := Finset.card_le_card (s := (Finset.univ.filter fun r : Fin i.val =>
              f r ∉ sampleSet σ s).image f) (t := AList.toFinset.filter fun y => y ∉ sampleSet σ s)
            fun y hy => by
              obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hy
              exact Finset.mem_filter.mpr
                ⟨List.mem_toFinset.mpr (List.getElem_mem _), (Finset.mem_filter.mp hr).2⟩
          rw [Finset.card_image_of_injOn (fun _ _ _ _ h =>
              Fin.ext (by have := hAList_nodup.getElem_inj_iff.mp h; omega)),
            Finset.card_filter] at hcard_le
          exact_mod_cast hcard_le
        calc ((i.val : ℝ) / 4) * ((Nat.factorial n : ℕ) : ℝ)
            = ∑ _r : Fin i.val, (((Nat.factorial n : ℕ) : ℝ) / 4) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
          _ ≤ ∑ r : Fin i.val, ∑ σ : Fin n ≃ α,
                (if x1 ∈ sampleSet σ s ∧
                    AList[r.val + 1]'(by rw [hAList_len]; omega) ∉ sampleSet σ s
                  then (1 : ℝ) else 0) := by
              refine Finset.sum_le_sum fun r _ => factorial_div_four_le_sum_split (fun h => ?_) hn
              have h0 : AList[0]'(by rw [hAList_len]; omega) = x1 := List.getElem_take
              have := hAList_nodup.getElem_inj_iff.mp (h0.trans h); omega
          _ = ∑ σ : Fin n ≃ α, ∑ r : Fin i.val,
                (if x1 ∈ sampleSet σ s ∧
                    AList[r.val + 1]'(by rw [hAList_len]; omega) ∉ sampleSet σ s
                  then (1 : ℝ) else 0) := Finset.sum_comm
          _ ≤ ∑ σ : Fin n ≃ α, ((((thresholdPriceRun M w σ j0).filter
                fun y => v i.val / 2 ≤ w y).card : ℕ) : ℝ) := by
              refine Finset.sum_le_sum fun σ _ => ?_
              by_cases hx1S : x1 ∈ sampleSet σ s
              · simp only [hx1S, true_and]
                exact (hT_ge_tail σ).trans (by exact_mod_cast hcond_card σ hx1S)
              · simp [hx1S]
      have hbound := hsingle j0 ((i.val : ℝ) / 4) hcount
      have hi_le_2 : ((i.val + 1 : ℕ) : ℝ) ≤ 2 * (i.val : ℝ) := by
        exact_mod_cast show i.val + 1 ≤ 2 * i.val by omega
      calc ((i.val + 1 : ℕ) : ℝ) ≤ 2 * (i.val : ℝ) := hi_le_2
        _ = 8 * ((d + 1 : ℕ) : ℝ) * (((i.val : ℝ) / 4) / ((d + 1 : ℕ) : ℝ)) := by field_simp; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by positivity)
  have hgap_nonneg : ∀ i : Fin q, 0 ≤ layerGap v q i := fun i => by
    unfold layerGap
    split_ifs with hi
    · exact sub_nonneg.mpr (hv_anti (by omega) (hi.trans_le hq_le_len))
    · simp only [sub_zero, v, i.isLt.trans_le hq_le_len, ↓reduceDIte]; exact hw _
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
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
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
          exact sum_layerGap_mul_countHalf w (fun _ _ hab hb => hv_anti hab (hb.trans_le hq_le_len))
            fun y _ => hw y
    _ = 32 * ((d + 1 : ℕ) : ℝ) * expectedThresholdPrice M w := by
          unfold expectedThresholdPrice
          dsimp only [μσ, μj]
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring

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
  have hexp_nonneg := expectedThresholdPrice_nonneg M w hw
  have hcoef : ((Nat.clog 2 M.eRank.toNat + 1 : ℕ) : ℝ) ≤ 2 * (Nat.clog 2 M.eRank.toNat : ℝ) := by
    exact_mod_cast show Nat.clog 2 M.eRank.toNat + 1 ≤ 2 * Nat.clog 2 M.eRank.toNat by omega
  calc ∑ x ∈ I, w x
      ≤ 32 * ((Nat.clog 2 M.eRank.toNat + 1 : ℕ) : ℝ) * expectedThresholdPrice M w :=
        sum_le_mul_expectedThresholdPrice M w hw hwb hnl hn hI
    _ ≤ 32 * (2 * (Nat.clog 2 M.eRank.toNat : ℝ)) * expectedThresholdPrice M w := by gcongr
    _ = 64 * (Nat.clog 2 M.eRank.toNat : ℝ) * expectedThresholdPrice M w := by ring

end ThresholdPrice

end Cslib.Probability.OptimalStopping.MatroidSecretary
