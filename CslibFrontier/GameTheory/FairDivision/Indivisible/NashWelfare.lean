/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.FairDivision.Indivisible.Basic
public import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Unreasonable Fairness of Maximum Nash Welfare (`MNW → EF1 ∧ PO`)

While Round-Robin (`AdditiveValuation.roundRobin`) and Lipton–Markakis–Mossel–Saberi envy-cycle
elimination (`MonotoneValuation.lmmsAllocate`) guarantee `EF1`, neither guarantees Pareto
optimality (`IsParetoOptimal`). Caragiannis, Kurokawa, Moulin, Procaccia, Shah, and Wang
([CaragiannisKurokawaMoulinProcacciaShahWang2019]) proved that **every Maximum Nash Welfare (`MNW`)
allocation simultaneously satisfies `EF1` and Pareto optimality** for nonnegative additive
valuations.

To handle degenerate instances where no allocation gives every agent strictly positive utility (so
the full product `∏ i, u_i(A_i)` vanishes identically),
[CaragiannisKurokawaMoulinProcacciaShahWang2019] defines an `MNW` allocation
(`AdditiveValuation.IsMaxNashWelfare`) in two lexicographic stages:

1. Maximize the number `(W.posAgents A).card` of agents receiving strictly positive utility.
2. Subject to maximum `(W.posAgents A).card`, maximize the Nash product
   `W.nashProduct A = ∏ i ∈ W.posAgents A, W.bundleVal i (A.bundle i)`.

Because every inequality in the proof can be cleared of denominators and logarithms, all definitions
and theorems hold over any strict linear ordered commutative ring `R` (`ℤ`, `ℚ`, `ℝ`), and are
computable (`Decidable`) when `R` has decidable order (`ℤ`, `ℚ`).

## Main definitions

* `Cslib.GameTheory.FairDivision.Indivisible.AdditiveValuation.posAgents`,
  `nashProduct`, `IsMaxNashWelfare`: positive-utility agent set, Nash product over positive agents,
  and two-stage Maximum Nash Welfare optimality predicate.
* `Cslib.GameTheory.FairDivision.Indivisible.MNWState`,
  `Cslib.GameTheory.FairDivision.Indivisible.AdditiveValuation.maxNashWelfareAllocation`:
  memoized candidate state and computable selector returning an `MNW` complete allocation when
  `0 < n`.

## Main results

* `AdditiveValuation.isMaxNashWelfare_maxNashWelfareAllocation`,
  `AdditiveValuation.exists_isMaxNashWelfare`: existence and computability of `MNW` allocations.
* `AdditiveValuation.IsMaxNashWelfare.isParetoOptimal`:
  every `MNW` allocation is Pareto optimal.
* `AdditiveValuation.IsMaxNashWelfare.isEF1`:
  every `MNW` allocation is envy-free up to one good (`EF1`).
* `AdditiveValuation.isEF1_and_isParetoOptimal_maxNashWelfareAllocation`:
  `W.maxNashWelfareAllocation hn` is simultaneously `EF1` and Pareto optimal
  ([CaragiannisKurokawaMoulinProcacciaShahWang2019]).

## References

* [CaragiannisKurokawaMoulinProcacciaShahWang2019]
* [Budish2011]
-/

public section

namespace Cslib.GameTheory.FairDivision.Indivisible

/-- Memoized candidate state for linear-time reduction during Maximum Nash Welfare search. -/
structure MNWState (n m : ℕ) (R : Type*) where
  /-- Candidate complete allocation. -/
  alloc : BundleAllocation n m
  /-- Cached count `(W.posAgents alloc).card`. -/
  posCard : ℕ
  /-- Cached Nash product `W.nashProduct alloc`. -/
  prod : R

namespace AdditiveValuation

section Defs

variable {n m : ℕ} {R : Type*} [CommRing R] [LinearOrder R]
  (W : AdditiveValuation n m R)

/-- Set of agents receiving strictly positive bundle utility under `A`. -/
@[expose] def posAgents (A : BundleAllocation n m) : Finset (Fin n) :=
  Finset.univ.filter fun i => 0 < W.bundleVal i (A.bundle i)

@[simp] theorem mem_posAgents {A : BundleAllocation n m} {i : Fin n} :
    i ∈ W.posAgents A ↔ 0 < W.bundleVal i (A.bundle i) := by
  simp [posAgents]

/-- Product of utilities across all agents with strictly positive bundle utility in `A`. -/
@[expose] def nashProduct (A : BundleAllocation n m) : R :=
  ∏ i ∈ W.posAgents A, W.bundleVal i (A.bundle i)

theorem nashProduct_eq_prod_univ {A : BundleAllocation n m}
    (hpos : ∀ i : Fin n, 0 < W.bundleVal i (A.bundle i)) :
    W.nashProduct A = ∏ i : Fin n, W.bundleVal i (A.bundle i) := by
  have huniv : W.posAgents A = Finset.univ := Finset.ext fun i => by simp [hpos i]
  rw [nashProduct, huniv]

/-- Two-stage Maximum Nash Welfare (`MNW`) optimality
([CaragiannisKurokawaMoulinProcacciaShahWang2019]): `A` is a complete allocation that maximizes
`(W.posAgents A).card`, and among complete allocations with maximum `(W.posAgents A).card` maximizes
`W.nashProduct A`. -/
@[expose] def IsMaxNashWelfare (A : BundleAllocation n m) : Prop :=
  A.IsComplete ∧
    (∀ B : BundleAllocation n m, B.IsComplete → (W.posAgents B).card ≤ (W.posAgents A).card) ∧
    (∀ B : BundleAllocation n m, B.IsComplete →
      (W.posAgents B).card = (W.posAgents A).card → W.nashProduct B ≤ W.nashProduct A)

instance instDecidableIsMaxNashWelfare (A : BundleAllocation n m) :
    Decidable (W.IsMaxNashWelfare A) := by
  have hiff : W.IsMaxNashWelfare A ↔
      A.IsComplete ∧
        (∀ B ∈ BundleAllocation.completeAllocationList n m,
          (W.posAgents B).card ≤ (W.posAgents A).card) ∧
        (∀ B ∈ BundleAllocation.completeAllocationList n m,
          (W.posAgents B).card = (W.posAgents A).card → W.nashProduct B ≤ W.nashProduct A) := by
    simp only [IsMaxNashWelfare, BundleAllocation.mem_completeAllocationList_iff]
  exact decidable_of_iff' _ hiff

/-- Builds a memoized `MNWState` for allocation `A`. -/
@[expose] def mkMNWState (A : BundleAllocation n m) : MNWState n m R where
  alloc := A
  posCard := (W.posAgents A).card
  prod := W.nashProduct A

/-- Structural scan over candidate allocations, matching on each recursive `MNWState` so kernel
reduction evaluates each candidate once. -/
@[expose] def bestMNWState (hn : 0 < n) : List (BundleAllocation n m) → MNWState n m R
  | [] => W.mkMNWState (BundleAllocation.ofAssignment fun _ : Fin m => ⟨0, hn⟩)
  | B :: rest =>
    match bestMNWState hn rest with
    | ⟨bestA, bestC, bestP⟩ =>
      let cB := (W.posAgents B).card
      let pB := W.nashProduct B
      if bestC < cB then ⟨B, cB, pB⟩
      else if bestC = cB ∧ bestP < pB then ⟨B, cB, pB⟩
      else ⟨bestA, bestC, bestP⟩

/-- Computable Maximum Nash Welfare complete allocation via lexicographic maximization over
`BundleAllocation.completeAllocationList n m`. -/
@[expose] def maxNashWelfareAllocation (hn : 0 < n) : BundleAllocation n m :=
  (W.bestMNWState hn (BundleAllocation.completeAllocationList n m)).alloc

private def leMNW (A B : BundleAllocation n m) : Prop :=
  (W.posAgents A).card < (W.posAgents B).card ∨
    ((W.posAgents A).card = (W.posAgents B).card ∧ W.nashProduct A ≤ W.nashProduct B)

private theorem leMNW_refl (A : BundleAllocation n m) : W.leMNW A A :=
  Or.inr ⟨rfl, le_rfl⟩

private theorem leMNW_trans {A B C : BundleAllocation n m}
    (hAB : W.leMNW A B) (hBC : W.leMNW B C) : W.leMNW A C := by
  rcases hAB with hlt₁ | ⟨heq₁, hle₁⟩ <;> rcases hBC with hlt₂ | ⟨heq₂, hle₂⟩
  · exact Or.inl (hlt₁.trans hlt₂)
  · exact Or.inl (heq₂ ▸ hlt₁)
  · exact Or.inl (heq₁.symm ▸ hlt₂)
  · exact Or.inr ⟨heq₁.trans heq₂, hle₁.trans hle₂⟩

private theorem bestMNWState_spec (hn : 0 < n) :
    ∀ (xs : List (BundleAllocation n m)),
      (∀ B ∈ xs, B.IsComplete) →
      let s := W.bestMNWState hn xs
      s.alloc.IsComplete ∧
        s.posCard = (W.posAgents s.alloc).card ∧
        s.prod = W.nashProduct s.alloc ∧
        ∀ B ∈ xs, W.leMNW B s.alloc
  | [], _ =>
    ⟨BundleAllocation.isComplete_ofAssignment _, rfl, rfl,
      fun _ h => absurd h List.not_mem_nil⟩
  | B :: rest, hxs => by
    have hB_comp : B.IsComplete := hxs B List.mem_cons_self
    have ih := bestMNWState_spec hn rest (fun X hX => hxs X (List.mem_cons_of_mem B hX))
    dsimp only [bestMNWState]
    rcases hrest : W.bestMNWState hn rest with ⟨bestA, bestC, bestP⟩
    rw [hrest] at ih
    obtain ⟨hA_comp, hC_eq, hP_eq, hall_rest⟩ := ih
    dsimp only at hA_comp hC_eq hP_eq hall_rest ⊢
    let cB := (W.posAgents B).card
    let pB := W.nashProduct B
    split_ifs with h₁ h₂
    · refine ⟨hB_comp, rfl, rfl, fun X hX => ?_⟩
      rcases List.mem_cons.1 hX with rfl | hmem
      · exact W.leMNW_refl X
      · exact W.leMNW_trans (hall_rest X hmem) (Or.inl (hC_eq ▸ h₁))
    · refine ⟨hB_comp, rfl, rfl, fun X hX => ?_⟩
      rcases List.mem_cons.1 hX with rfl | hmem
      · exact W.leMNW_refl X
      · exact W.leMNW_trans (hall_rest X hmem)
          (Or.inr ⟨hC_eq ▸ h₂.1, (hP_eq ▸ h₂.2).le⟩)
    · refine ⟨hA_comp, hC_eq, hP_eq, fun X hX => ?_⟩
      rcases List.mem_cons.1 hX with rfl | hmem
      · rcases lt_trichotomy cB bestC with hlt | heq | hgt
        · exact Or.inl (hC_eq ▸ hlt)
        · have hleP : pB ≤ bestP := not_lt.1 fun hltP => h₂ ⟨heq.symm, hltP⟩
          exact Or.inr ⟨hC_eq ▸ heq, hP_eq ▸ hleP⟩
        · exact absurd hgt h₁
      · exact hall_rest X hmem

/-- `W.maxNashWelfareAllocation hn` satisfies `W.IsMaxNashWelfare`. -/
theorem isMaxNashWelfare_maxNashWelfareAllocation (hn : 0 < n) :
    W.IsMaxNashWelfare (W.maxNashWelfareAllocation hn) := by
  let xs := BundleAllocation.completeAllocationList n m
  have hxs : ∀ B ∈ xs, B.IsComplete :=
    fun _ hB => BundleAllocation.mem_completeAllocationList_iff.1 hB
  obtain ⟨hcomp, -, -, hall⟩ := W.bestMNWState_spec hn xs hxs
  refine ⟨hcomp, fun B hB => ?_, fun B hB hcard => ?_⟩
  · exact (hall B (BundleAllocation.mem_completeAllocationList_iff.2 hB)).elim (·.le) (·.1.le)
  · exact (hall B (BundleAllocation.mem_completeAllocationList_iff.2 hB)).elim
      (fun hlt => absurd hcard hlt.ne) And.right

/-- Every instance with `0 < n` (or `m = 0`) admits a Maximum Nash Welfare allocation. -/
theorem exists_isMaxNashWelfare (h : 0 < n ∨ m = 0) :
    ∃ A : BundleAllocation n m, W.IsMaxNashWelfare A := by
  rcases h with hn | rfl
  · exact ⟨W.maxNashWelfareAllocation hn, W.isMaxNashWelfare_maxNashWelfareAllocation hn⟩
  · have hemp (B : BundleAllocation n 0) : W.posAgents B = ∅ := by
      ext i
      simp [Finset.eq_empty_of_forall_notMem fun g : Fin 0 => g.elim0]
    exact ⟨BundleAllocation.empty, fun g => g.elim0,
      fun B _ => by simp [hemp B],
      fun B _ _ => by simp [nashProduct, hemp]⟩

end Defs

section FairnessAndEfficiency

variable {n m : ℕ} {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  {W : AdditiveValuation n m R}

omit [IsStrictOrderedRing R] in
private theorem bundleVal_sdiff_singleton (W : AdditiveValuation n m R) {i : Fin n} {g : Fin m}
    {S : Finset (Fin m)} (hg : g ∈ S) :
    W.bundleVal i (S \ {g}) = W.bundleVal i S - W.weight i g :=
  eq_sub_of_add_eq (W.bundleVal_sdiff_singleton_add hg)

omit [IsStrictOrderedRing R] in
private theorem bundleVal_transfer_target (W : AdditiveValuation n m R) {A : BundleAllocation n m}
    {j i : Fin n} (hji : j ≠ i) {g : Fin m} (hg : g ∈ A.bundle j) :
    W.bundleVal i ((A.transferGood j i g hg).bundle i) =
      W.bundleVal i (A.bundle i) + W.weight i g := by
  have hg_not : g ∉ A.bundle i := fun hgi => hji (A.eq_of_mem_bundle hg hgi)
  rw [BundleAllocation.transferGood_bundle_target, W.bundleVal_insert hg_not]

omit [IsStrictOrderedRing R] in
private theorem bundleVal_transfer_source (W : AdditiveValuation n m R) {A : BundleAllocation n m}
    {j i : Fin n} (hji : j ≠ i) {g : Fin m} (hg : g ∈ A.bundle j) :
    W.bundleVal j ((A.transferGood j i g hg).bundle j) =
      W.bundleVal j (A.bundle j) - W.weight j g := by
  rw [BundleAllocation.transferGood_bundle_source A g hg hji, W.bundleVal_sdiff_singleton hg]

private theorem nashProduct_lt_of_pair_lt {A B : BundleAllocation n m} {i j : Fin n}
    (hji : j ≠ i) (hi : i ∈ W.posAgents A) (hj : j ∈ W.posAgents A)
    (hpos_eq : W.posAgents B = W.posAgents A)
    (hother : ∀ k : Fin n, k ≠ i → k ≠ j → B.bundle k = A.bundle k)
    (hpair : W.bundleVal i (A.bundle i) * W.bundleVal j (A.bundle j) <
      W.bundleVal i (B.bundle i) * W.bundleVal j (B.bundle j)) :
    W.nashProduct A < W.nashProduct B := by
  set S := W.posAgents A
  have hj_er : j ∈ S.erase i := Finset.mem_erase.2 ⟨hji, hj⟩
  have hexp (C : BundleAllocation n m) (hC : W.posAgents C = S) :
      W.nashProduct C = (W.bundleVal i (C.bundle i) * W.bundleVal j (C.bundle j)) *
        ∏ k ∈ (S.erase i).erase j, W.bundleVal k (C.bundle k) := by
    rw [nashProduct, hC, ← Finset.mul_prod_erase S _ hi,
      ← Finset.mul_prod_erase (S.erase i) _ hj_er, mul_assoc]
  have hrest_eq : ∏ k ∈ (S.erase i).erase j, W.bundleVal k (B.bundle k) =
      ∏ k ∈ (S.erase i).erase j, W.bundleVal k (A.bundle k) :=
    Finset.prod_congr rfl fun k hk => by
      rw [hother k (Finset.mem_erase.1 (Finset.mem_erase.1 hk).2).1 (Finset.mem_erase.1 hk).1]
  rw [hexp A rfl, hexp B hpos_eq, hrest_eq]
  exact mul_lt_mul_of_pos_right hpair
    (Finset.prod_pos fun k hk =>
      W.mem_posAgents.1 (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk)))

/-- **Every Maximum Nash Welfare allocation is Pareto optimal**
([CaragiannisKurokawaMoulinProcacciaShahWang2019]). -/
theorem IsMaxNashWelfare.isParetoOptimal {A : BundleAllocation n m}
    (hMNW : W.IsMaxNashWelfare A) : W.toMonotoneValuation.IsParetoOptimal A := by
  obtain ⟨hcompA, hcard_max, hprod_max⟩ := hMNW
  refine ⟨hcompA, ?_⟩
  rintro ⟨B, hcompB, hle, i₀, hlt₀⟩
  simp only [toMonotoneValuation_val] at hle hlt₀
  have hsub : W.posAgents A ⊆ W.posAgents B := fun i hi =>
    W.mem_posAgents.2 (lt_of_lt_of_le (W.mem_posAgents.1 hi) (hle i))
  have hcard_eq : (W.posAgents B).card = (W.posAgents A).card :=
    le_antisymm (hcard_max B hcompB) (Finset.card_le_card hsub)
  have hpos_eq : W.posAgents B = W.posAgents A :=
    (Finset.eq_of_subset_of_card_le hsub hcard_eq.le).symm
  have hi₀B : i₀ ∈ W.posAgents B :=
    W.mem_posAgents.2 (lt_of_le_of_lt (W.toMonotoneValuation.mono i₀ (Finset.empty_subset _)) hlt₀)
  have hi₀A : i₀ ∈ W.posAgents A := hpos_eq ▸ hi₀B
  have hprod_lt : W.nashProduct A < W.nashProduct B := by
    rw [nashProduct, nashProduct, hpos_eq]
    exact Finset.prod_lt_prod₀ (fun i hi => W.mem_posAgents.1 hi) (fun i _ => hle i)
      ⟨i₀, hi₀A, hlt₀⟩
  exact not_lt_of_ge (hprod_max B hcompB hcard_eq) hprod_lt

/-- **The Unreasonable Fairness of Maximum Nash Welfare (`MNW → EF1`)**
([CaragiannisKurokawaMoulinProcacciaShahWang2019]): every Maximum Nash Welfare allocation is
envy-free up to one good (`IsEF1`). -/
theorem IsMaxNashWelfare.isEF1 {A : BundleAllocation n m}
    (hMNW : W.IsMaxNashWelfare A) : W.toMonotoneValuation.IsEF1 A := by
  have hPO := hMNW.isParetoOptimal
  obtain ⟨hcompA, hcard_max, hprod_max⟩ := hMNW
  intro i j
  simp only [toMonotoneValuation_val]
  by_contra! hnot
  obtain ⟨henv, hno_ef1⟩ := hnot
  have hji : j ≠ i := fun hEq => lt_irrefl _ (hEq ▸ henv)
  -- Since `u_i(A_i) < u_i(A_j)`, `A_j` contains some good `g₁` with `0 < W.weight i g₁`.
  have hex_good {S : Finset (Fin m)} (hS : 0 < W.bundleVal i S) :
      ∃ g ∈ S, 0 < W.weight i g := by
    by_contra! hall
    exact hS.ne' (Finset.sum_eq_zero fun g hg => le_antisymm (hall g hg) (W.weight_nonneg i g))
  obtain ⟨g₁, hg₁, hwg₁_pos⟩ := hex_good ((W.bundleVal_nonneg i _).trans_lt henv)
  -- Case split on whether `j` has positive utility (`j ∈ W.posAgents A`).
  by_cases hj_pos : 0 < W.bundleVal j (A.bundle j)
  · -- Subcase split on whether `i` has positive utility (`i ∈ W.posAgents A`).
    by_cases hi_pos : 0 < W.bundleVal i (A.bundle i)
    · -- Both `i, j ∈ W.posAgents A`: pick `g* ∈ A_j` with `0 < w_i(g*)` and
      -- `w_j(g*) * u_i(A_j) ≤ u_j(A_j) * w_i(g*)`.
      let Spos := (A.bundle j).filter fun g => 0 < W.weight i g
      have hSpos_ne : Spos.Nonempty := ⟨g₁, Finset.mem_filter.2 ⟨hg₁, hwg₁_pos⟩⟩
      obtain ⟨g, hgS, hratio⟩ : ∃ g ∈ Spos,
          W.weight j g * W.bundleVal i (A.bundle j) ≤
            W.bundleVal j (A.bundle j) * W.weight i g := by
        by_contra! hall_gt
        have hsum_lt := Finset.sum_lt_sum_of_nonempty hSpos_ne fun g hg => hall_gt g hg
        have hsum_i_eq : ∑ g ∈ Spos, W.weight i g = W.bundleVal i (A.bundle j) := by
          rw [bundleVal, ← Finset.sum_filter_add_sum_filter_not (A.bundle j)
            (fun g => 0 < W.weight i g),
            Finset.sum_eq_zero fun g hg =>
              le_antisymm (not_lt.1 (Finset.mem_filter.1 hg).2) (W.weight_nonneg i g),
            add_zero]
        have hsum_j_le : ∑ g ∈ Spos, W.weight j g ≤ W.bundleVal j (A.bundle j) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun g _ _ => W.weight_nonneg j g
        rw [← Finset.mul_sum, hsum_i_eq, ← Finset.sum_mul] at hsum_lt
        exact not_lt_of_ge (mul_le_mul_of_nonneg_right hsum_j_le (W.bundleVal_nonneg i _)) hsum_lt
      obtain ⟨hg, hw_ig_pos⟩ := Finset.mem_filter.1 hgS
      have hrem_i : W.bundleVal i (A.bundle i) + W.weight i g < W.bundleVal i (A.bundle j) := by
        linarith [hno_ef1 g hg, W.bundleVal_sdiff_singleton (i := i) hg]
      have hrem_j_pos : 0 < W.bundleVal j (A.bundle j) - W.weight j g := by
        have hw_jg_le : W.weight j g ≤ W.bundleVal j (A.bundle j) := by
          linarith [W.bundleVal_sdiff_singleton_add (i := j) hg,
            W.bundleVal_nonneg j (A.bundle j \ {g})]
        by_contra hle0
        have hw_jg_eq : W.weight j g = W.bundleVal j (A.bundle j) := by linarith
        linarith [le_of_mul_le_mul_left (hw_jg_eq ▸ hratio) hj_pos]
      let B := A.transferGood j i g hg
      have hcompB : B.IsComplete := BundleAllocation.isComplete_transferGood j i g hg hcompA
      have huBi : W.bundleVal i (B.bundle i) = W.bundleVal i (A.bundle i) + W.weight i g :=
        W.bundleVal_transfer_target hji hg
      have huBj : W.bundleVal j (B.bundle j) = W.bundleVal j (A.bundle j) - W.weight j g :=
        W.bundleVal_transfer_source hji hg
      have hpos_eq : W.posAgents B = W.posAgents A := by
        ext k
        simp only [mem_posAgents]
        rcases eq_or_ne k i with rfl | hki
        · simp [huBi, hi_pos, show 0 < W.bundleVal k (A.bundle k) + W.weight k g by linarith]
        · rcases eq_or_ne k j with rfl | hkj
          · simp [huBj, hj_pos, hrem_j_pos]
          · rw [BundleAllocation.transferGood_bundle_other A g hg hki hkj]
      have hpair_lt : W.bundleVal i (A.bundle i) * W.bundleVal j (A.bundle j) <
          W.bundleVal i (B.bundle i) * W.bundleVal j (B.bundle j) := by
        rw [huBi, huBj]
        rcases (W.weight_nonneg j g).eq_or_lt with hw0 | hw_pos
        · rw [← hw0, sub_zero, add_mul]
          linarith [mul_pos hj_pos hw_ig_pos]
        · linarith [mul_lt_mul_of_pos_left hrem_i hw_pos,
            show (W.bundleVal i (A.bundle i) + W.weight i g) *
                (W.bundleVal j (A.bundle j) - W.weight j g) -
              W.bundleVal i (A.bundle i) * W.bundleVal j (A.bundle j) =
            W.bundleVal j (A.bundle j) * W.weight i g -
              W.weight j g * (W.bundleVal i (A.bundle i) + W.weight i g) by ring]
      exact not_lt_of_ge (hprod_max B hcompB (congrArg Finset.card hpos_eq))
        (nashProduct_lt_of_pair_lt hji (W.mem_posAgents.2 hi_pos) (W.mem_posAgents.2 hj_pos)
          hpos_eq (fun k hki hkj => BundleAllocation.transferGood_bundle_other A g hg hki hkj)
          hpair_lt)
    · -- `u_i(A_i) = 0` and `u_j(A_j) > 0`: `A_j` contains two distinct goods valued positively by
      -- `i`, at least one of which leaves `j` with strictly positive utility, increasing
      -- `|posAgents|`.
      have hui0 : W.bundleVal i (A.bundle i) = 0 :=
        le_antisymm (not_lt.1 hi_pos) (W.bundleVal_nonneg i _)
      obtain ⟨g₂, hg₂_sdiff, hwg₂_pos⟩ := hex_good (by simpa only [hui0] using hno_ef1 g₁ hg₁)
      obtain ⟨hg₂, hg₂_ne_singleton⟩ := Finset.mem_sdiff.1 hg₂_sdiff
      have hsum_two : W.weight j g₁ + W.weight j g₂ ≤ W.bundleVal j (A.bundle j) := by
        rw [← Finset.sum_pair (Finset.notMem_singleton.1 hg₂_ne_singleton).symm]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.insert_subset_iff.2 ⟨hg₁, Finset.singleton_subset_iff.2 hg₂⟩)
          fun x _ _ => W.weight_nonneg j x
      obtain ⟨g, hg, hwig, hwjg_lt⟩ : ∃ g ∈ A.bundle j, 0 < W.weight i g ∧
          W.weight j g < W.bundleVal j (A.bundle j) := by
        by_cases h₁ : W.weight j g₁ < W.bundleVal j (A.bundle j)
        · exact ⟨g₁, hg₁, hwg₁_pos, h₁⟩
        · exact ⟨g₂, hg₂, hwg₂_pos, by linarith⟩
      let B := A.transferGood j i g hg
      have hcompB : B.IsComplete := BundleAllocation.isComplete_transferGood j i g hg hcompA
      have huBi : W.bundleVal i (B.bundle i) = W.weight i g := by
        rw [W.bundleVal_transfer_target hji hg, hui0, zero_add]
      have huBj : W.bundleVal j (B.bundle j) = W.bundleVal j (A.bundle j) - W.weight j g :=
        W.bundleVal_transfer_source hji hg
      have hsub_pos : Insert.insert i (W.posAgents A) ⊆ W.posAgents B := fun k hk => by
        rw [mem_posAgents]
        rcases Finset.mem_insert.1 hk with rfl | hkA
        · rwa [huBi]
        · have hk_pos : 0 < W.bundleVal k (A.bundle k) := W.mem_posAgents.1 hkA
          have hki : k ≠ i := fun hEq => absurd (hEq ▸ hui0) hk_pos.ne'
          rcases eq_or_ne k j with rfl | hkj
          · rw [huBj]
            linarith
          · rwa [BundleAllocation.transferGood_bundle_other A g hg hki hkj]
      have hi_notA : i ∉ W.posAgents A := by simp [hui0]
      have hcard_gt : (W.posAgents A).card < (W.posAgents B).card := by
        calc (W.posAgents A).card
            < (insert i (W.posAgents A)).card := by simp [Finset.card_insert_of_notMem hi_notA]
          _ ≤ (W.posAgents B).card := Finset.card_le_card hsub_pos
      exact not_lt_of_ge (hcard_max B hcompB) hcard_gt
  · -- `u_j(A_j) = 0`: transferring `g₁` (`0 < w_i(g₁)`, `w_j(g₁) = 0`) from `j` to `i`
    -- Pareto-dominates `A`, contradicting `hPO`.
    have huj0 : W.bundleVal j (A.bundle j) = 0 :=
      le_antisymm (not_lt.1 hj_pos) (W.bundleVal_nonneg j _)
    have hwjg₁ : W.weight j g₁ = 0 := by
      linarith [W.bundleVal_sdiff_singleton_add (i := j) hg₁,
        W.bundleVal_nonneg j (A.bundle j \ {g₁}), W.weight_nonneg j g₁]
    refine hPO.2 ⟨A.transferGood j i g₁ hg₁,
      BundleAllocation.isComplete_transferGood j i g₁ hg₁ hcompA, fun k => ?_, i, ?_⟩
    · simp only [toMonotoneValuation_val]
      rcases eq_or_ne k i with rfl | hki
      · rw [W.bundleVal_transfer_target hji hg₁]
        linarith
      · rcases eq_or_ne k j with rfl | hkj
        · rw [W.bundleVal_transfer_source hji hg₁, huj0, hwjg₁, sub_zero]
        · rw [BundleAllocation.transferGood_bundle_other A g₁ hg₁ hki hkj]
    · simp only [toMonotoneValuation_val, W.bundleVal_transfer_target hji hg₁]
      linarith

/-- **Maximum Nash Welfare simultaneously achieves `EF1` and Pareto optimality**
([CaragiannisKurokawaMoulinProcacciaShahWang2019]): for any `0 < n` and any nonnegative additive
valuation profile `W`, `W.maxNashWelfareAllocation hn` is complete, `EF1`, and Pareto optimal. -/
theorem isEF1_and_isParetoOptimal_maxNashWelfareAllocation (W : AdditiveValuation n m R)
    (hn : 0 < n) :
    (W.maxNashWelfareAllocation hn).IsComplete ∧
      W.toMonotoneValuation.IsEF1 (W.maxNashWelfareAllocation hn) ∧
      W.toMonotoneValuation.IsParetoOptimal (W.maxNashWelfareAllocation hn) := by
  have hMNW := W.isMaxNashWelfare_maxNashWelfareAllocation hn
  exact ⟨hMNW.1, hMNW.isEF1, hMNW.isParetoOptimal⟩

end FairnessAndEfficiency

end AdditiveValuation

end Cslib.GameTheory.FairDivision.Indivisible
