/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.Analysis.Brouwer.KKMS
public import CslibFrontier.GameTheory.Cooperative.Scarf
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.Real

/-!
# KKM, KKMS, and Scarf's theorem for NTU cooperative games

Checked witnesses and counterexamples exercising
`CslibFrontier/Foundations/Analysis/Brouwer/KKMS.lean` and
`CslibFrontier/GameTheory/Cooperative/Scarf.lean`:

* **Classical KKM lemma and strict KKMS generalization** (`Cslib.Brouwer`):
  - `kkmThreeCover`: closed simplex cover on `Fin 3` with nonempty triple intersection.
  - `kkmsCoalitionalCover`: coalitional KKMS cover on `Fin 3` whose singleton intersection is
    empty, while KKMS exhibits a balanced intersection point.
* **Balanced non-TU 3-player utility and cost-sharing games**:
  - `nonTUThreePlayer`: strictly non-TU utility game satisfying `IsBounded` and `IsBalanced`,
    giving `NonemptyCore` via Scarf's theorem, together with the explicit NTU core allocation
    `![3 / 2, 3 / 2, 0]` that is blocked in the corresponding TU game `tuThreePlayer`.
  - `nonTUCostThreePlayer`: non-TU cost-sharing game satisfying `IsBounded` and `IsBalanced`,
    giving `NonemptyCore` via `NTUCostSharingGame.nonemptyCore_of_isBalanced`, with explicit core
    allocation `fun _ => 2 / 3`.
* **Necessity counterexamples**:
  - `majorityGame`: 3-player simple majority game failing both balancedness and core
    nonemptiness.
  - `unboundedTwoPlayer`: balanced 2-player NTU game with empty core, showing `IsBounded` is
    necessary in Scarf's theorem.
* **TU-to-NTU bridges**: checking `FacilityLocationInstance.example15_2` through
  `CostSharingGame.toNTUCostSharingGame`.
-/

public section

namespace CslibFrontierTests.GameTheory.Scarf

open Cslib.Brouwer Cslib.GameTheory Finset Set

private theorem isClosed_forall_le {n : ℕ} (S : Finset (Fin n)) (c : ℝ) :
    IsClosed {x : Fin n → ℝ | ∀ i ∈ S, x i ≤ c} := by
  have h : {x : Fin n → ℝ | ∀ i ∈ S, x i ≤ c} = ⋂ i ∈ S, {x : Fin n → ℝ | x i ≤ c} := by
    ext x
    simp
  rw [h]
  exact isClosed_biInter fun i _ => isClosed_le (continuous_apply i) continuous_const

private theorem isClosed_forall_ge {n : ℕ} (S : Finset (Fin n)) (c : ℝ) :
    IsClosed {x : Fin n → ℝ | ∀ i ∈ S, c ≤ x i} := by
  have h : {x : Fin n → ℝ | ∀ i ∈ S, c ≤ x i} = ⋂ i ∈ S, {x : Fin n → ℝ | c ≤ x i} := by
    ext x
    simp
  rw [h]
  exact isClosed_biInter fun i _ => isClosed_le continuous_const (continuous_apply i)

/-! ### KKM and KKMS witnesses on `Fin 3` -/

/-- Closed cover on the 2-simplex assigning `F i = {q | 1 / 3 ≤ q i}`. -/
def kkmThreeCover (i : Fin 3) : Set (Fin 3 → ℝ) :=
  {q | (1 / 3 : ℝ) ≤ q i}

theorem kkmThreeCover_exists_inter :
    ∃ q : Fin 3 → ℝ, ((∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1) ∧ ∀ i : Fin 3, q ∈ kkmThreeCover i := by
  refine exists_mem_iInter_of_kkmCover kkmThreeCover
    (fun i => isClosed_le continuous_const (continuous_apply i)) fun T hT q _ hq1 hqout => ?_
  by_contra hnone
  push Not at hnone
  have hsumT : ∑ i ∈ T, q i = 1 := by
    rw [← hq1]
    exact Finset.sum_subset (Finset.subset_univ T) fun i _ hiT => hqout i hiT
  have hlt : ∑ i ∈ T, q i < ∑ _ ∈ T, (1 / 3 : ℝ) :=
    Finset.sum_lt_sum_of_nonempty hT fun i hi => not_le.1 (hnone i hi)
  rw [Finset.sum_const, nsmul_eq_mul] at hlt
  have hcard : (T.card : ℝ) ≤ 3 := by
    exact_mod_cast (Finset.card_le_univ T).trans_eq (Fintype.card_fin 3)
  linarith

/-- Coalitional KKMS cover on `Fin 3`: singletons require `2 / 3 ≤ q i`, pairs require
`1 / 3 ≤ q i` on both members, and `univ` accepts all points. -/
def kkmsCoalitionalCover (S : Finset (Fin 3)) : Set (Fin 3 → ℝ) :=
  if S.card = 1 then {q | ∀ i ∈ S, (2 / 3 : ℝ) ≤ q i}
  else if S.card = 2 then {q | ∀ i ∈ S, (1 / 3 : ℝ) ≤ q i}
  else if S = Finset.univ then Set.univ
  else ∅

theorem kkmsCoalitionalCover_no_singleton_inter :
    ¬ ∃ q : Fin 3 → ℝ, (∑ i : Fin 3, q i = 1) ∧
      ∀ i : Fin 3, q ∈ kkmsCoalitionalCover {i} := by
  rintro ⟨q, hq1, hq⟩
  have hge : ∀ i : Fin 3, (2 / 3 : ℝ) ≤ q i := fun i => by
    have hi := hq i
    have hcard1 : ({i} : Finset (Fin 3)).card = 1 := Finset.card_singleton i
    simp only [kkmsCoalitionalCover, hcard1, ↓reduceIte, mem_ofPred_eq] at hi
    exact hi i (Finset.mem_singleton_self i)
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hge i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hq1] at hsum
  norm_num at hsum

theorem kkmsCoalitionalCover_exists_balanced :
    ∃ q : Fin 3 → ℝ, ((∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1) ∧
      ∃ w : Finset (Fin 3) → ℝ,
        (∀ S, 0 ≤ w S) ∧ w ∅ = 0 ∧ (∀ i : Fin 3, (∑ S with i ∈ S, w S) = 1) ∧
          ∀ S, 0 < w S → q ∈ kkmsCoalitionalCover S := by
  refine exists_balanced_inter_of_kkmCover kkmsCoalitionalCover ?_ ?_
  · intro S _
    dsimp only [kkmsCoalitionalCover]
    split_ifs
    · exact isClosed_forall_ge S (2 / 3)
    · exact isClosed_forall_ge S (1 / 3)
    · exact isClosed_univ
    · exact isClosed_empty
  · intro T hT q _ hq1 hqout
    by_cases hex : ∃ i ∈ T, (2 / 3 : ℝ) ≤ q i
    · obtain ⟨i, hiT, hqi⟩ := hex
      refine ⟨{i}, Finset.singleton_subset_iff.2 hiT, Finset.singleton_nonempty i, ?_⟩
      have hcard1 : ({i} : Finset (Fin 3)).card = 1 := Finset.card_singleton i
      simp only [kkmsCoalitionalCover, hcard1, ↓reduceIte, mem_ofPred_eq]
      intro j hj
      rwa [Finset.mem_singleton.1 hj]
    · push Not at hex
      have hsumT : ∑ i ∈ T, q i = 1 := by
        rw [← hq1]
        exact Finset.sum_subset (Finset.subset_univ T) fun i _ hiT => hqout i hiT
      by_cases hU : T = Finset.univ
      · subst hU
        refine ⟨Finset.univ, Finset.Subset.rfl, Finset.univ_nonempty, ?_⟩
        have h3 : (Finset.univ : Finset (Fin 3)).card = 3 := Fintype.card_fin 3
        simp [kkmsCoalitionalCover, h3]
      · have hlt3 : T.card < 3 := lt_of_le_of_ne
          ((Finset.card_le_univ T).trans_eq (Fintype.card_fin 3))
          fun heq => hU (Finset.eq_univ_of_card T (heq.trans (Fintype.card_fin 3).symm))
        have hne1 : T.card ≠ 1 := by
          intro h1
          obtain ⟨i, hiT⟩ := Finset.card_eq_one.1 h1
          subst hiT
          simp only [Finset.sum_singleton] at hsumT
          linarith [hex i (Finset.mem_singleton_self i)]
        have h2 : T.card = 2 := by
          have hpos : 0 < T.card := Finset.card_pos.2 hT
          omega
        refine ⟨T, Finset.Subset.rfl, hT, ?_⟩
        simp only [kkmsCoalitionalCover, h2, ↓reduceIte]
        intro i hiT
        have hsplit := Finset.add_sum_erase T q hiT
        have hcard1 : (T.erase i).card = 1 := by
          rw [Finset.card_erase_of_mem hiT, h2]
        obtain ⟨j, hj⟩ := Finset.card_eq_one.1 hcard1
        have hjT : j ∈ T := (Finset.mem_erase.1 (hj ▸ Finset.mem_singleton_self j)).2
        rw [hj, Finset.sum_singleton] at hsplit
        linarith [hex j hjT]

/-! ### Non-TU 3-player cooperative game and Scarf's theorem -/

/-- A balanced, bounded 3-player non-TU utility game: singletons earn at most `0`, pairs have
total utility at most `2` with an individual cap of `3 / 2`, and the grand coalition can divide `3`
freely. -/
def nonTUThreePlayer : NTUGame (Fin 3) where
  feasible S :=
    if S.card = 1 then {x | ∑ i ∈ S, x i ≤ 0}
    else if S.card = 2 then {x | ∑ i ∈ S, x i ≤ 2} ∩ {x | ∀ i ∈ S, x i ≤ 3 / 2}
    else {x | ∑ i ∈ S, x i ≤ 3}
  isCylinder S _ x y hxy hx := by
    have hsum : ∑ i ∈ S, x i = ∑ i ∈ S, y i := Finset.sum_congr rfl hxy
    split_ifs at hx ⊢
    · rw [mem_ofPred_eq] at hx ⊢; linarith
    · rw [mem_inter_iff, mem_ofPred_eq, mem_ofPred_eq] at hx ⊢
      exact ⟨by linarith [hx.1], fun i hi => by simpa only [hxy i hi] using hx.2 i hi⟩
    · rw [mem_ofPred_eq] at hx ⊢; linarith
  isClosed S _ := by
    split_ifs
    · exact isClosed_le (continuous_finsetSum S fun i _ => continuous_apply i) continuous_const
    · exact (isClosed_le (continuous_finsetSum S fun i _ => continuous_apply i)
        continuous_const).inter (isClosed_forall_le S (3 / 2))
    · exact isClosed_le (continuous_finsetSum S fun i _ => continuous_apply i) continuous_const
  isComprehensive S _ x y hx hle := by
    have hsum : ∑ i ∈ S, y i ≤ ∑ i ∈ S, x i := Finset.sum_le_sum hle
    split_ifs at hx ⊢
    · exact hsum.trans hx
    · exact ⟨hsum.trans hx.1, fun i hi => (hle i hi).trans (hx.2 i hi)⟩
    · exact hsum.trans hx
  nonempty S _ := by
    refine ⟨0, ?_⟩
    split_ifs
    · simp
    · refine ⟨?_, fun _ _ => by norm_num⟩
      simp
    · simp

private theorem nonTUThreePlayer_sum_le_card (S : Finset (Fin 3)) (x : Fin 3 → ℝ)
    (hx : x ∈ nonTUThreePlayer.feasible S) : ∑ i ∈ S, x i ≤ S.card := by
  dsimp only [nonTUThreePlayer] at hx
  split_ifs at hx with h1 h2
  · rw [h1]; exact hx.trans (by norm_num)
  · rw [h2]; exact hx.1.trans (by norm_num)
  · by_cases hS : S.Nonempty
    · have hcard : S.card = 3 := by
        have hle := (Finset.card_le_univ S).trans_eq (Fintype.card_fin 3)
        have hpos := Finset.card_pos.2 hS
        omega
      rw [hcard]
      exact hx.trans (by norm_num)
    · rw [Finset.not_nonempty_iff_eq_empty.1 hS]
      simp

theorem nonTUThreePlayer_individualValue (i : Fin 3) :
    nonTUThreePlayer.individualValue i = 0 := by
  have hbdd : BddAbove ((fun x : Fin 3 → ℝ => x i) '' nonTUThreePlayer.feasible {i}) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hcard1 : ({i} : Finset (Fin 3)).card = 1 := Finset.card_singleton i
    simpa only [nonTUThreePlayer, hcard1, ↓reduceIte, mem_ofPred_eq, Finset.sum_singleton] using hx
  refine le_antisymm ?_ ?_
  · have hmem := (nonTUThreePlayer.mem_feasible_singleton_iff i hbdd
      (fun _ => nonTUThreePlayer.individualValue i)).2 le_rfl
    have hcard1 : ({i} : Finset (Fin 3)).card = 1 := Finset.card_singleton i
    simpa only [nonTUThreePlayer, hcard1, ↓reduceIte, mem_ofPred_eq,
      Finset.sum_singleton] using hmem
  · refine (nonTUThreePlayer.mem_feasible_singleton_iff i hbdd (fun _ => 0)).1 ?_
    have hcard1 : ({i} : Finset (Fin 3)).card = 1 := Finset.card_singleton i
    simp [nonTUThreePlayer, hcard1]

theorem nonTUThreePlayer_isBounded : nonTUThreePlayer.IsBounded := by
  refine ⟨fun i => ⟨0, ?_⟩, ⟨3, fun S _ x hx hir i hi => ?_⟩⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hcard1 : ({i} : Finset (Fin 3)).card = 1 := Finset.card_singleton i
    simpa only [nonTUThreePlayer, hcard1, ↓reduceIte, mem_ofPred_eq, Finset.sum_singleton] using hx
  · have hnonneg : ∀ j ∈ S, 0 ≤ x j := fun j hj => by
      have hjv := hir j hj
      rwa [nonTUThreePlayer_individualValue j] at hjv
    have hxi : x i ≤ ∑ j ∈ S, x j := Finset.single_le_sum hnonneg hi
    have hcard : (S.card : ℝ) ≤ 3 := by
      exact_mod_cast (Finset.card_le_univ S).trans_eq (Fintype.card_fin 3)
    exact hxi.trans ((nonTUThreePlayer_sum_le_card S x hx).trans hcard)

theorem nonTUThreePlayer_isBalanced : nonTUThreePlayer.IsBalanced := by
  intro w hw x hx
  have h3 : (Finset.univ : Finset (Fin 3)).card = 3 := Fintype.card_fin 3
  have hcard_sum : ∑ S : Finset (Fin 3), w S * (S.card : ℝ) = 3 := by
    have h1 := hw.sum_mul_sum_eq (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin] at h1
    norm_num at h1
    exact h1
  have hsum : ∑ i, x i ≤ 3 := by
    rw [← hw.sum_mul_sum_eq x]
    refine (Finset.sum_le_sum fun S _ => ?_).trans hcard_sum.le
    by_cases hS : S.Nonempty
    · rcases (hw.1 S).lt_or_eq with hwpos | hw0
      · exact mul_le_mul_of_nonneg_left (nonTUThreePlayer_sum_le_card S x (hx S hS hwpos)) (hw.1 S)
      · simp [← hw0]
    · rw [Finset.not_nonempty_iff_eq_empty.1 hS]
      simp
  simpa [nonTUThreePlayer, h3] using hsum

theorem nonTUThreePlayer_nonemptyCore : nonTUThreePlayer.NonemptyCore :=
  nonTUThreePlayer.nonemptyCore_of_isBalanced nonTUThreePlayer_isBounded nonTUThreePlayer_isBalanced

/-- `![3 / 2, 3 / 2, 0]` lies in the NTU core of `nonTUThreePlayer`: the cap `x i ≤ 3 / 2` on pairs
prevents `{0, 2}` and `{1, 2}` from strictly improving both members, even though `3 / 2 + 0 < 2`. -/
theorem nonTUThreePlayer_inCore_threeHalves :
    nonTUThreePlayer.InCore ![3 / 2, 3 / 2, 0] := by
  have h3 : (Finset.univ : Finset (Fin 3)).card = 3 := Fintype.card_fin 3
  refine ⟨?_, ?_⟩
  · simp only [nonTUThreePlayer, h3]
    change ∑ i : Fin 3, (![3 / 2, 3 / 2, 0] : Fin 3 → ℝ) i ≤ 3
    norm_num [Fin.sum_univ_three]
  · rintro S hS ⟨y, hy, hlt⟩
    have hcard_le : S.card ≤ 3 := (Finset.card_le_univ S).trans_eq (Fintype.card_fin 3)
    have hcard_pos : 0 < S.card := Finset.card_pos.2 hS
    rcases Nat.lt_trichotomy S.card 2 with hlt2 | h2 | hgt2
    · have h1 : S.card = 1 := by omega
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 h1
      have hcard1 : ({i} : Finset (Fin 3)).card = 1 := Finset.card_singleton i
      simp only [nonTUThreePlayer, hcard1, ↓reduceIte, mem_ofPred_eq, Finset.sum_singleton] at hy
      have hi := hlt i (Finset.mem_singleton_self i)
      fin_cases i <;> simp at hy hi <;> linarith
    · simp only [nonTUThreePlayer, h2, ↓reduceIte] at hy
      by_cases h0 : (0 : Fin 3) ∈ S
      · have h0lt := hlt 0 h0
        norm_num at h0lt
        linarith [hy.2 0 h0]
      · by_cases h1 : (1 : Fin 3) ∈ S
        · have h1lt := hlt 1 h1
          norm_num at h1lt
          linarith [hy.2 1 h1]
        · have hsub : S ⊆ ({2} : Finset (Fin 3)) := fun i hi => by
            fin_cases i
            · exact False.elim (h0 hi)
            · exact False.elim (h1 hi)
            · exact Finset.mem_singleton_self 2
          have hle1 : S.card ≤ 1 := (Finset.card_le_card hsub).trans_eq (Finset.card_singleton 2)
          omega
    · have hcard3 : S.card = 3 := by omega
      have hSu : S = Finset.univ :=
        Finset.eq_univ_of_card S (hcard3.trans (Fintype.card_fin 3).symm)
      subst hSu
      have hsum_le : ∑ i : Fin 3, y i ≤ 3 := by
        simpa [nonTUThreePlayer, h3] using hy
      have hsum_lt := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ =>
        hlt i (Finset.mem_univ i)
      norm_num [Fin.sum_univ_three] at hsum_lt hsum_le
      linarith

/-- Checking `inCore_iff_notMem_interior`: `![3 / 2, 3 / 2, 0]` avoids the interior of every
nonempty coalition's feasible set. -/
theorem nonTUThreePlayer_notMem_interior (S : Finset (Fin 3)) (hS : S.Nonempty) :
    (![3 / 2, 3 / 2, 0] : Fin 3 → ℝ) ∉ interior (nonTUThreePlayer.feasible S) :=
  ((nonTUThreePlayer.inCore_iff_notMem_interior _).1 nonTUThreePlayer_inCore_threeHalves).2 S hS

/-- Corresponding TU cooperative game matching `nonTUThreePlayer`'s coalitional sums (`0` on
singletons, `S.card` otherwise). Unlike `nonTUThreePlayer`, it excludes `![3 / 2, 3 / 2, 0]` from
the core. -/
def tuThreePlayer : CooperativeGame (Fin 3) where
  val S := if S.card = 1 then 0 else S.card
  val_empty := by simp

theorem tuThreePlayer_not_inCore_threeHalves :
    ¬ tuThreePlayer.toNTUGame.InCore ![3 / 2, 3 / 2, 0] := by
  rw [tuThreePlayer.inCore_toNTUGame_iff]
  rintro ⟨_, hS⟩
  have h02 := hS {0, 2}
  have hcard : ({0, 2} : Finset (Fin 3)).card = 2 := by decide
  simp only [tuThreePlayer, hcard] at h02
  rw [Finset.sum_pair (by decide)] at h02
  norm_num at h02

/-! ### Non-TU 3-player cost-sharing game and Scarf's theorem -/

/-- A balanced, bounded 3-player non-TU cost-sharing game: singletons must cover `1`, pairs must
cover at least `3 / 2` in total with each member paying at least `1 / 2`, and `univ` must cover
total cost `2`. -/
def nonTUCostThreePlayer : NTUCostSharingGame (Fin 3) where
  feasible S :=
    if S.card = 1 then {α | 1 ≤ ∑ i ∈ S, α i}
    else if S.card = 2 then {α | 3 / 2 ≤ ∑ i ∈ S, α i} ∩ {α | ∀ i ∈ S, 1 / 2 ≤ α i}
    else {α | 2 ≤ ∑ i ∈ S, α i}
  isCylinder S _ α β hαβ hα := by
    have hsum : ∑ i ∈ S, α i = ∑ i ∈ S, β i := Finset.sum_congr rfl hαβ
    split_ifs at hα ⊢
    · rw [mem_ofPred_eq] at hα ⊢; linarith
    · rw [mem_inter_iff, mem_ofPred_eq, mem_ofPred_eq] at hα ⊢
      exact ⟨by linarith [hα.1], fun i hi => by simpa only [hαβ i hi] using hα.2 i hi⟩
    · rw [mem_ofPred_eq] at hα ⊢; linarith
  isClosed S _ := by
    split_ifs
    · exact isClosed_le continuous_const (continuous_finsetSum S fun i _ => continuous_apply i)
    · exact (isClosed_le continuous_const
        (continuous_finsetSum S fun i _ => continuous_apply i)).inter (isClosed_forall_ge S (1 / 2))
    · exact isClosed_le continuous_const (continuous_finsetSum S fun i _ => continuous_apply i)
  isComprehensive S _ α β hα hle := by
    have hsum : ∑ i ∈ S, α i ≤ ∑ i ∈ S, β i := Finset.sum_le_sum hle
    split_ifs at hα ⊢
    · exact hα.trans hsum
    · exact ⟨hα.1.trans hsum, fun i hi => (hα.2 i hi).trans (hle i hi)⟩
    · exact hα.trans hsum
  nonempty S _ := by
    refine ⟨fun _ => 1, ?_⟩
    split_ifs with h1 h2
    · change (1 : ℝ) ≤ ∑ _ ∈ S, 1
      rw [Finset.sum_const, nsmul_eq_mul, h1]
      norm_num
    · refine ⟨?_, fun _ _ => by norm_num⟩
      change (3 / 2 : ℝ) ≤ ∑ _ ∈ S, 1
      rw [Finset.sum_const, nsmul_eq_mul, h2]
      norm_num
    · have hne_card : 1 ≤ S.card := by
        rcases Finset.eq_empty_or_nonempty S with rfl | hSne
        · contradiction
        · exact Finset.one_le_card.2 hSne
      have hcard3 : S.card = 3 := by
        have hle := (Finset.card_le_univ S).trans_eq (Fintype.card_fin 3)
        omega
      change (2 : ℝ) ≤ ∑ _ ∈ S, 1
      rw [Finset.sum_const, nsmul_eq_mul, hcard3]
      norm_num

private theorem nonTUCostThreePlayer_card_le_sum {S : Finset (Fin 3)} (hS : S.Nonempty)
    (α : Fin 3 → ℝ) (hα : α ∈ nonTUCostThreePlayer.feasible S) :
    (2 / 3 : ℝ) * S.card ≤ ∑ i ∈ S, α i := by
  dsimp only [nonTUCostThreePlayer] at hα
  split_ifs at hα with h1 h2
  · rw [mem_ofPred_eq] at hα
    rw [h1]
    norm_num
    linarith
  · rw [mem_inter_iff, mem_ofPred_eq] at hα
    rw [h2]
    norm_num
    linarith [hα.1]
  · rw [mem_ofPred_eq] at hα
    have hcard : S.card = 3 := by
      have hle := (Finset.card_le_univ S).trans_eq (Fintype.card_fin 3)
      have hpos := Finset.card_pos.2 hS
      omega
    rw [hcard]
    norm_num
    exact hα

theorem nonTUCostThreePlayer_individualCost (i : Fin 3) :
    nonTUCostThreePlayer.individualCost i = 1 := by
  have hbdd : BddBelow ((fun α : Fin 3 → ℝ => α i) '' nonTUCostThreePlayer.feasible {i}) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨α, hα, rfl⟩
    have hcard1 : ({i} : Finset (Fin 3)).card = 1 := Finset.card_singleton i
    simpa only [nonTUCostThreePlayer, hcard1, ↓reduceIte, mem_ofPred_eq, Finset.sum_singleton]
      using hα
  refine le_antisymm ?_ ?_
  · refine (nonTUCostThreePlayer.mem_feasible_singleton_iff i hbdd (fun _ => 1)).1 ?_
    have hcard1 : ({i} : Finset (Fin 3)).card = 1 := Finset.card_singleton i
    simp [nonTUCostThreePlayer, hcard1]
  · have hmem := (nonTUCostThreePlayer.mem_feasible_singleton_iff i hbdd
      (fun _ => nonTUCostThreePlayer.individualCost i)).2 le_rfl
    have hcard1 : ({i} : Finset (Fin 3)).card = 1 := Finset.card_singleton i
    simpa only [nonTUCostThreePlayer, hcard1, ↓reduceIte, mem_ofPred_eq, Finset.sum_singleton]
      using hmem

theorem nonTUCostThreePlayer_isBounded : nonTUCostThreePlayer.IsBounded := by
  refine ⟨fun i => ⟨1, ?_⟩, ⟨0, fun S hS α hα hir i hi => ?_⟩⟩
  · rintro _ ⟨α, hα, rfl⟩
    have hcard1 : ({i} : Finset (Fin 3)).card = 1 := Finset.card_singleton i
    simpa only [nonTUCostThreePlayer, hcard1, ↓reduceIte, mem_ofPred_eq, Finset.sum_singleton]
      using hα
  · have hsum_lb := nonTUCostThreePlayer_card_le_sum hS α hα
    have hle1 : ∀ j ∈ S, α j ≤ 1 := fun j hj => by
      have hjc := hir j hj
      rwa [nonTUCostThreePlayer_individualCost j] at hjc
    have herase : ∑ j ∈ S.erase i, α j ≤ (S.card : ℝ) - 1 := by
      have hcard_e : ((S.erase i).card : ℝ) = (S.card : ℝ) - 1 := by
        have h1 : 1 ≤ S.card := Finset.one_le_card.2 hS
        rw [Finset.card_erase_of_mem hi, Nat.cast_sub h1, Nat.cast_one]
      have hle_sum : ∑ j ∈ S.erase i, α j ≤ ∑ _ ∈ S.erase i, (1 : ℝ) :=
        Finset.sum_le_sum fun j hj => hle1 j (Finset.mem_erase.1 hj).2
      rw [Finset.sum_const, nsmul_eq_mul, mul_one, hcard_e] at hle_sum
      exact hle_sum
    have hsplit := Finset.add_sum_erase S α hi
    have hcard_le : (S.card : ℝ) ≤ 3 := by
      exact_mod_cast (Finset.card_le_univ S).trans_eq (Fintype.card_fin 3)
    linarith

theorem nonTUCostThreePlayer_isBalanced : nonTUCostThreePlayer.IsBalanced := by
  intro w hw α hα
  have h3 : (Finset.univ : Finset (Fin 3)).card = 3 := Fintype.card_fin 3
  have hcard_sum : ∑ S : Finset (Fin 3), w S * ((2 / 3 : ℝ) * S.card) = 2 := by
    have h1 := hw.sum_mul_sum_eq (fun _ => (2 / 3 : ℝ))
    have hmul : ∀ S : Finset (Fin 3),
        w S * (∑ _ ∈ S, (2 / 3 : ℝ)) = w S * ((2 / 3 : ℝ) * S.card) := fun S => by
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm (S.card : ℝ)]
    simp_rw [hmul] at h1
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin] at h1
    norm_num at h1
    exact h1
  have hsum : 2 ≤ ∑ i, α i := by
    rw [← hw.sum_mul_sum_eq α]
    refine hcard_sum.ge.trans (Finset.sum_le_sum fun S _ => ?_)
    by_cases hS : S.Nonempty
    · rcases (hw.1 S).lt_or_eq with hwpos | hw0
      · exact mul_le_mul_of_nonneg_left (nonTUCostThreePlayer_card_le_sum hS α (hα S hS hwpos))
          (hw.1 S)
      · simp [← hw0]
    · rw [Finset.not_nonempty_iff_eq_empty.1 hS]
      simp
  simpa [nonTUCostThreePlayer, h3] using hsum

theorem nonTUCostThreePlayer_nonemptyCore : nonTUCostThreePlayer.NonemptyCore :=
  nonTUCostThreePlayer.nonemptyCore_of_isBalanced nonTUCostThreePlayer_isBounded
    nonTUCostThreePlayer_isBalanced

theorem nonTUCostThreePlayer_inCore_twoThirds :
    nonTUCostThreePlayer.InCore (fun _ => 2 / 3) := by
  have h3 : (Finset.univ : Finset (Fin 3)).card = 3 := Fintype.card_fin 3
  refine ⟨?_, ?_⟩
  · simp only [nonTUCostThreePlayer, h3]
    change (2 : ℝ) ≤ ∑ _ : Fin 3, (2 / 3 : ℝ)
    norm_num [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  · rintro S hS ⟨β, hβ, hlt⟩
    have hlb := nonTUCostThreePlayer_card_le_sum hS β hβ
    have hsum_lt : ∑ i ∈ S, β i < ∑ _ ∈ S, (2 / 3 : ℝ) :=
      Finset.sum_lt_sum_of_nonempty hS fun i hi => hlt i hi
    rw [Finset.sum_const, nsmul_eq_mul] at hsum_lt
    linarith

theorem nonTUCostThreePlayer_pair_nonTU :
    ¬ (![3 / 2, 0, 0] : Fin 3 → ℝ) ∈ nonTUCostThreePlayer.feasible {0, 1} := by
  have hcard : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
  simp only [nonTUCostThreePlayer, hcard]
  intro ⟨_, hmin⟩
  have h1 := hmin 1 (by decide)
  norm_num at h1

/-! ### Counterexamples: unbalanced games and failure of boundedness -/

/-- 3-player simple majority game: `v(S) = 1` for `|S| ≥ 2` and `0` otherwise. -/
def majorityGame : CooperativeGame (Fin 3) where
  val S := if 2 ≤ S.card then 1 else 0
  val_empty := by simp

theorem majorityGame_not_isBalanced : ¬ majorityGame.toNTUGame.IsBalanced := by
  intro hbal
  let w : Finset (Fin 3) → ℝ := fun S => if S.card = 2 then 1 / 2 else 0
  have hw : IsBalancedWeights w := by
    refine ⟨fun S => by dsimp only [w]; split_ifs <;> norm_num, fun i => ?_⟩
    have hsum : (∑ S with i ∈ S, w S) =
        ∑ _ ∈ Finset.univ.filter (fun S : Finset (Fin 3) => i ∈ S ∧ S.card = 2), (1 / 2 : ℝ) := by
      simp only [Finset.sum_filter]
      refine Finset.sum_congr rfl fun S _ => ?_
      dsimp only [w]
      by_cases hi : i ∈ S <;> by_cases h2 : S.card = 2 <;> simp [hi, h2]
    have hcard : (Finset.univ.filter fun S : Finset (Fin 3) => i ∈ S ∧ S.card = 2).card = 2 := by
      fin_cases i <;> decide
    rw [hsum, Finset.sum_const, nsmul_eq_mul, hcard]
    norm_num
  have hx : ∀ S : Finset (Fin 3), S.Nonempty → 0 < w S →
      (fun _ : Fin 3 => (1 / 2 : ℝ)) ∈ majorityGame.toNTUGame.feasible S := by
    intro S _ hwS
    dsimp only [w] at hwS
    split_ifs at hwS with h2
    · simp only [CooperativeGame.mem_toNTUGame_feasible, majorityGame, h2, le_refl, ↓reduceIte,
        Finset.sum_const, nsmul_eq_mul]
      norm_num
    · linarith
  have huniv := hbal w hw (fun _ => 1 / 2) hx
  simp only [CooperativeGame.mem_toNTUGame_feasible, majorityGame, Finset.card_univ,
    Fintype.card_fin, Finset.sum_const, nsmul_eq_mul] at huniv
  norm_num at huniv

theorem majorityGame_not_nonemptyCore : ¬ majorityGame.toNTUGame.NonemptyCore := by
  rintro ⟨x, hx⟩
  rw [majorityGame.inCore_toNTUGame_iff] at hx
  obtain ⟨hbal, hS⟩ := hx
  have h01 := hS {0, 1}
  have h12 := hS {1, 2}
  have h02 := hS {0, 2}
  have c01 : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
  have c12 : ({1, 2} : Finset (Fin 3)).card = 2 := by decide
  have c02 : ({0, 2} : Finset (Fin 3)).card = 2 := by decide
  simp only [majorityGame, c01, c12, c02, le_refl, ↓reduceIte, Finset.card_univ,
    Fintype.card_fin] at hbal h01 h12 h02
  norm_num at hbal h01 h12 h02
  rw [Fin.sum_univ_three] at hbal
  linarith

/-- Balanced 2-player NTU game with `feasible {i} = {x | x i ≤ 0}` and `feasible univ = Set.univ`.
It satisfies every hypothesis of Scarf's theorem except `IsBounded`, yet has an empty core. -/
def unboundedTwoPlayer : NTUGame (Fin 2) where
  feasible S :=
    if S = {0} then {x | x 0 ≤ 0}
    else if S = {1} then {x | x 1 ≤ 0}
    else Set.univ
  isCylinder S _ x y hxy hx := by
    split_ifs at hx ⊢ with h0 h1
    · subst h0; simpa only [mem_ofPred_eq, ← hxy 0 (Finset.mem_singleton_self 0)] using hx
    · subst h1; simpa only [mem_ofPred_eq, ← hxy 1 (Finset.mem_singleton_self 1)] using hx
    · exact Set.mem_univ _
  isClosed S _ := by
    split_ifs
    · exact isClosed_le (continuous_apply 0) continuous_const
    · exact isClosed_le (continuous_apply 1) continuous_const
    · exact isClosed_univ
  isComprehensive S _ x y hx hle := by
    split_ifs at hx ⊢ with h0 h1
    · subst h0; exact (hle 0 (Finset.mem_singleton_self 0)).trans hx
    · subst h1; exact (hle 1 (Finset.mem_singleton_self 1)).trans hx
    · exact Set.mem_univ _
  nonempty S _ := by
    refine ⟨0, ?_⟩
    split_ifs <;> simp

theorem unboundedTwoPlayer_isBalanced : unboundedTwoPlayer.IsBalanced := by
  intro w _ x _
  have h0 : (Finset.univ : Finset (Fin 2)) ≠ {0} := by decide
  have h1 : (Finset.univ : Finset (Fin 2)) ≠ {1} := by decide
  simp [unboundedTwoPlayer, h0, h1]

theorem unboundedTwoPlayer_not_isBounded : ¬ unboundedTwoPlayer.IsBounded := by
  rintro ⟨hbdd, ⟨B, hB⟩⟩
  have hind : ∀ i : Fin 2, unboundedTwoPlayer.individualValue i = 0 := fun i => by
    have h10 : ({1} : Finset (Fin 2)) ≠ {0} := by decide
    fin_cases i
    · refine le_antisymm ?_ ?_
      · have hmem := (unboundedTwoPlayer.mem_feasible_singleton_iff 0 (hbdd 0)
          (fun _ => unboundedTwoPlayer.individualValue 0)).2 le_rfl
        simpa [unboundedTwoPlayer] using hmem
      · refine (unboundedTwoPlayer.mem_feasible_singleton_iff 0 (hbdd 0) (fun _ => 0)).1 ?_
        simp [unboundedTwoPlayer]
    · refine le_antisymm ?_ ?_
      · have hmem := (unboundedTwoPlayer.mem_feasible_singleton_iff 1 (hbdd 1)
          (fun _ => unboundedTwoPlayer.individualValue 1)).2 le_rfl
        simpa [unboundedTwoPlayer, h10] using hmem
      · refine (unboundedTwoPlayer.mem_feasible_singleton_iff 1 (hbdd 1) (fun _ => 0)).1 ?_
        simp [unboundedTwoPlayer, h10]
  have h0 : (Finset.univ : Finset (Fin 2)) ≠ {0} := by decide
  have h1 : (Finset.univ : Finset (Fin 2)) ≠ {1} := by decide
  let x : Fin 2 → ℝ := fun _ => max B 0 + 1
  have hmem : x ∈ unboundedTwoPlayer.feasible Finset.univ := by
    simp [unboundedTwoPlayer, h0, h1]
  have hir : ∀ i ∈ (Finset.univ : Finset (Fin 2)), unboundedTwoPlayer.individualValue i ≤ x i := by
    intro i _
    rw [hind i]
    exact le_trans (le_max_right B 0) (by linarith)
  have hleB := hB Finset.univ_nonempty hmem hir 0 (Finset.mem_univ 0)
  dsimp only [x] at hleB
  linarith [le_max_left B 0]

theorem unboundedTwoPlayer_not_nonemptyCore : ¬ unboundedTwoPlayer.NonemptyCore := by
  rintro ⟨x, hx⟩
  have h0 : (Finset.univ : Finset (Fin 2)) ≠ {0} := by decide
  have h1 : (Finset.univ : Finset (Fin 2)) ≠ {1} := by decide
  refine hx.2 Finset.univ Finset.univ_nonempty ⟨fun i => x i + 1, ?_, fun i _ => by linarith⟩
  simp [unboundedTwoPlayer, h0, h1]

/-! ### TU-to-NTU bridge on facility location Example 15.2 -/

theorem example15_2_ntu_core_and_balanced :
    FacilityLocationInstance.example15_2.toCostSharingGame.toNTUCostSharingGame.InCore ![4, 2, 2] ∧
    FacilityLocationInstance.example15_2.toCostSharingGame.toNTUCostSharingGame.IsBalanced ∧
    FacilityLocationInstance.example15_2.toCostSharingGame.toNTUCostSharingGame.IsBounded := by
  refine ⟨?_, ?_, ?_⟩
  · exact (CostSharingGame.inCore_toNTUCostSharingGame_iff _ _).2
      FacilityLocationInstance.example15_2_inCore_four_two_two
  · rw [CostSharingGame.toNTUCostSharingGame_isBalanced_iff]
    exact (CostSharingGame.nonemptyCore_iff_balanced _).1
      ⟨![4, 2, 2], FacilityLocationInstance.example15_2_inCore_four_two_two⟩
  · exact CostSharingGame.toNTUCostSharingGame_isBounded _

end CslibFrontierTests.GameTheory.Scarf
