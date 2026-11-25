/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.RandomAssignment.Basic

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Random Serial Dictatorship (RSD)

Formalizes the deterministic **serial dictatorship** mechanism `serialDictatorship p σ` for a
priority ordering `σ : Equiv.Perm (Fin n)` (agents pick in the order `σ 0, σ 1, …, σ (n - 1)`),
and **random serial dictatorship (RSD)** `rsd p` — the uniform lottery over all `n!` priority
orderings.

## Main definitions

* `Cslib.GameTheory.RandomAssignment.serialDictatorship`: bijection `Equiv.Perm (Fin n)` returned
  by deterministic serial dictatorship under priority order `σ`.
* `Cslib.GameTheory.RandomAssignment.rsd`: random serial dictatorship `AssignmentRule n`.

## Main results

* `Cslib.GameTheory.RandomAssignment.serialDictatorship_isParetoEfficient`: deterministic serial
  dictatorship is always Pareto efficient.
* `Cslib.GameTheory.RandomAssignment.serialDictatorship_strategyProof`: deterministic serial
  dictatorship is strategy-proof.
* `Cslib.GameTheory.RandomAssignment.rsd_mem_doublyStochastic`: `rsd p` is doubly stochastic.
* `Cslib.GameTheory.RandomAssignment.rsd_isExPostEfficient`: `rsd p` is ex-post efficient.
* `Cslib.GameTheory.RandomAssignment.rsd_isAnonymous` / `rsd_isEqualTreatmentOfEquals`: `rsd` is
  anonymous and satisfies equal treatment of equals (`ETE`).
* `Cslib.GameTheory.RandomAssignment.rsd_isSDStrategyProof`: `rsd` is strongly
  `sd`-strategy-proof.
* `Cslib.GameTheory.RandomAssignment.rsd_isSDEfficient_of_le_three`: for `n ≤ 3`, `rsd p` is
  always `sd`-efficient (sharp threshold).
* `Cslib.GameTheory.RandomAssignment.not_isSDEnvyFree_rsd_three`: for `n = 3`, `rsd` fails
  `sd`-envy-freeness.
* `Cslib.GameTheory.RandomAssignment.not_isSDEfficient_rsd_four` /
  `rsd_ineffProfileFour_strictly_dominated`: for `n = 4` (and `not_isSDEfficient_rsd_of_four_le`
  for every `n ≥ 4`), `rsd` is **not** `sd`-efficient (witnessed on `p₄ = (abcd, abcd, badc, badc)`
  where `rsd` yields `(5/12, 1/12, 5/12, 1/12)` and `(1/12, 5/12, 1/12, 5/12)`, strictly
  `sd`-dominated for all four agents by `(1/2, 0, 1/2, 0)` and `(0, 1/2, 0, 1/2)`).

## References

* [BogomolnaiaMoulin2001] (primary article PDF not consulted; section/theorem locators
  unverified).
-/

public section

namespace Cslib.GameTheory.RandomAssignment

open Finset Matrix

/-- Internal step picking the best remaining object from `Fin n` avoiding `taken`. -/
private def bestRemaining {n : ℕ} (π : Equiv.Perm (Fin n)) (taken : Finset (Fin n))
    (hne : (Finset.univ.filter fun r : Fin n => π r ∉ taken).Nonempty) : Fin n :=
  π ((Finset.univ.filter fun r : Fin n => π r ∉ taken).min' hne)

private lemma bestRemaining_not_mem {n : ℕ} (π : Equiv.Perm (Fin n)) (taken : Finset (Fin n))
    (hne : (Finset.univ.filter fun r : Fin n => π r ∉ taken).Nonempty) :
    bestRemaining π taken hne ∉ taken := by
  exact (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2

private lemma bestRemaining_rank_le {n : ℕ} (π : Equiv.Perm (Fin n)) (taken : Finset (Fin n))
    (hne : (Finset.univ.filter fun r : Fin n => π r ∉ taken).Nonempty)
    {o : Fin n} (ho : o ∉ taken) :
    π.symm (bestRemaining π taken hne) ≤ π.symm o := by
  unfold bestRemaining
  rw [Equiv.symm_apply_apply]
  refine Finset.min'_le _ (π.symm o) ?_
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, by simpa using ho⟩

private lemma exists_avail_of_card_lt {n : ℕ} (π : Equiv.Perm (Fin n)) (taken : Finset (Fin n))
    (hcard : taken.card < n) :
    (Finset.univ.filter fun r : Fin n => π r ∉ taken).Nonempty := by
  have hsub : (Finset.univ \ taken).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff]
    have hle : (taken ∩ Finset.univ).card = taken.card := by simp
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨o, ho⟩ := hsub
  rw [Finset.mem_sdiff] at ho
  exact ⟨π.symm o, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using ho.2⟩⟩

/-- Prefix state after the first `t` dictators (`σ 0, …, σ (t - 1)`) have chosen. -/
private def sdPrefix {n : ℕ} (p : Profile n) (σ : Equiv.Perm (Fin n)) :
    (t : ℕ) → t ≤ n → {s : Finset (Fin n) // s.card = t}
  | 0, _ => ⟨∅, by simp⟩
  | t + 1, ht =>
    let prev := sdPrefix p σ t (by omega)
    let hne := exists_avail_of_card_lt (p (σ ⟨t, by omega⟩)) prev.1 (by rw [prev.2]; omega)
    let o := bestRemaining (p (σ ⟨t, by omega⟩)) prev.1 hne
    ⟨insert o prev.1, by
      rw [Finset.card_insert_of_notMem (bestRemaining_not_mem _ _ hne), prev.2]⟩

/-- The object picked at turn `t : Fin n` (by agent `σ t`). -/
private def serialDictPick {n : ℕ} (p : Profile n) (σ : Equiv.Perm (Fin n)) (t : Fin n) : Fin n :=
  let prev := sdPrefix p σ t.val (by omega)
  bestRemaining (p (σ t)) prev.1
    (exists_avail_of_card_lt (p (σ t)) prev.1 (by rw [prev.2]; exact t.isLt))

/-- The set of objects already claimed strictly before turn `t : Fin n`. -/
private def serialDictTaken {n : ℕ} (p : Profile n) (σ : Equiv.Perm (Fin n)) (t : ℕ)
    (ht : t ≤ n) : Finset (Fin n) :=
  (sdPrefix p σ t ht).1

private lemma serialDictTaken_succ {n : ℕ} (p : Profile n) (σ : Equiv.Perm (Fin n))
    (t : ℕ) (ht : t < n) :
    serialDictTaken p σ (t + 1) (by omega) =
      insert (serialDictPick p σ ⟨t, ht⟩) (serialDictTaken p σ t (by omega)) :=
  rfl

private lemma mem_serialDictTaken_iff {n : ℕ} (p : Profile n) (σ : Equiv.Perm (Fin n))
    (t : ℕ) (ht : t ≤ n) (o : Fin n) :
    o ∈ serialDictTaken p σ t ht ↔ ∃ s : Fin n, s.val < t ∧ serialDictPick p σ s = o := by
  induction t with
  | zero =>
    simp [serialDictTaken, sdPrefix]
  | succ t ih =>
    rw [serialDictTaken_succ p σ t (by omega), Finset.mem_insert, ih (by omega)]
    constructor
    · rintro (rfl | ⟨s, hs, rfl⟩)
      · exact ⟨⟨t, by omega⟩, by simp, rfl⟩
      · exact ⟨s, by omega, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hs) with hlt | heq
      · exact Or.inr ⟨s, hlt, rfl⟩
      · left; congr 1; exact Fin.ext heq

private lemma serialDictPick_not_mem_taken {n : ℕ} (p : Profile n) (σ : Equiv.Perm (Fin n))
    (t : Fin n) : serialDictPick p σ t ∉ serialDictTaken p σ t.val (by omega) :=
  bestRemaining_not_mem _ _ _

private lemma serialDictPick_optimal {n : ℕ} (p : Profile n) (σ : Equiv.Perm (Fin n))
    (t : Fin n) {o : Fin n} (ho : o ∉ serialDictTaken p σ t.val (by omega)) :
    (p (σ t)).symm (serialDictPick p σ t) ≤ (p (σ t)).symm o :=
  bestRemaining_rank_le _ _ _ ho

private lemma serialDictPick_injective {n : ℕ} (p : Profile n) (σ : Equiv.Perm (Fin n)) :
    Function.Injective (serialDictPick p σ) := by
  intro s t hst
  by_contra hne
  have hord : ∀ a b : Fin n, serialDictPick p σ a = serialDictPick p σ b → a.val < b.val → False :=
    fun a b hab hlt =>
      serialDictPick_not_mem_taken p σ b ((mem_serialDictTaken_iff p σ b.val (by omega) _).mpr
        ⟨a, hlt, hab⟩)
  rcases Nat.lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hgt
  · exact hord s t hst hlt
  · exact hord t s hst.symm hgt

/-- Computable serial dictatorship assignment mapping each agent `i` to the object she picks when
agents choose in order `σ 0, σ 1, …, σ (n - 1)`. -/
private def serialDictFun {n : ℕ} (p : Profile n) (σ : Equiv.Perm (Fin n)) (i : Fin n) : Fin n :=
  serialDictPick p σ (σ.symm i)

private lemma serialDictFun_bijective {n : ℕ} (p : Profile n) (σ : Equiv.Perm (Fin n)) :
    Function.Bijective (serialDictFun p σ) := by
  rw [Finite.injective_iff_bijective.symm]
  intro i j hij
  exact σ.symm.injective (serialDictPick_injective p σ hij)

/-- Serial dictatorship as a permutation of `Fin n`: agent `i` receives her top available object
when agents choose in priority order `σ 0, σ 1, …, σ (n - 1)`. -/
noncomputable def serialDictatorship {n : ℕ} (p : Profile n) (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n) :=
  Equiv.ofBijective (serialDictFun p σ) (serialDictFun_bijective p σ)

private lemma serialDictatorship_apply {n : ℕ} (p : Profile n) (σ : Equiv.Perm (Fin n))
    (i : Fin n) : serialDictatorship p σ i = serialDictFun p σ i :=
  Equiv.ofBijective_apply _ _ i

/-- If `i` prefers `o` strictly over what she receives in `serialDictatorship p σ`, then some
earlier agent `j` (`σ.symm j < σ.symm i`) takes `o`. -/
lemma serialDictatorship_taken_before {n : ℕ} (p : Profile n) (σ : Equiv.Perm (Fin n))
    {i o : Fin n} (hlt : (p i).symm o < (p i).symm (serialDictatorship p σ i)) :
    ∃ j : Fin n, (σ.symm j).val < (σ.symm i).val ∧ serialDictatorship p σ j = o := by
  have hmem : o ∈ serialDictTaken p σ (σ.symm i).val (by omega) := by
    by_contra hnot
    have hle := serialDictPick_optimal p σ (σ.symm i) hnot
    rw [Equiv.apply_symm_apply] at hle
    rw [serialDictatorship_apply] at hlt
    exact (lt_of_lt_of_le hlt hle).false
  rw [mem_serialDictTaken_iff] at hmem
  obtain ⟨s, hs, rfl⟩ := hmem
  exact ⟨σ s, by simpa using hs, by rw [serialDictatorship_apply]; simp [serialDictFun]⟩

/-- When `j` picks strictly before `i`, `j` weakly prefers her own object over `i`'s object. -/
lemma serialDictatorship_rank_le_of_lt {n : ℕ} (p : Profile n) (σ : Equiv.Perm (Fin n))
    {j i : Fin n} (hlt : (σ.symm j).val < (σ.symm i).val) :
    (p j).symm (serialDictatorship p σ j) ≤ (p j).symm (serialDictatorship p σ i) := by
  have hnot : serialDictatorship p σ i ∉ serialDictTaken p σ (σ.symm j).val (by omega) := by
    rw [mem_serialDictTaken_iff]
    rintro ⟨s, hs, heq⟩
    rw [serialDictatorship_apply] at heq
    have hinj : s = σ.symm i := serialDictPick_injective p σ heq
    have : s.val = (σ.symm i).val := congrArg Fin.val hinj
    omega
  rw [serialDictatorship_apply]
  have hle := serialDictPick_optimal p σ (σ.symm j) hnot
  simpa only [serialDictFun, Equiv.apply_symm_apply] using hle

/-- When `j` picks `a` strictly before `i` picks `b ≠ a`, `j` strictly prefers `a` over `b`. -/
private lemma serialDictatorship_rank_lt_of_lt {n : ℕ} (p : Profile n) (σ : Equiv.Perm (Fin n))
    {j i a b : Fin n} (hlt : (σ.symm j).val < (σ.symm i).val)
    (ha : serialDictatorship p σ j = a) (hb : serialDictatorship p σ i = b) (hab : a ≠ b) :
    (p j).symm a < (p j).symm b := by
  subst ha hb
  exact (serialDictatorship_rank_le_of_lt p σ hlt).lt_of_ne fun h => hab ((p j).symm.injective h)

/-- Deterministic serial dictatorship is Pareto efficient for every priority order `σ`. -/
theorem serialDictatorship_isParetoEfficient {n : ℕ} (p : Profile n) (σ : Equiv.Perm (Fin n)) :
    IsParetoEfficientPerm p (serialDictatorship p σ) := by
  rintro ⟨ν, hweak, i₀, hstrict⟩
  have heq : ∀ t : ℕ, (ht : t < n) →
      ν (σ ⟨t, ht⟩) = serialDictatorship p σ (σ ⟨t, ht⟩) := by
    intro t
    induction t using Nat.strongRecOn with
    | ind t ih =>
      intro ht
      set i := σ ⟨t, ht⟩
      have hnot : ν i ∉ serialDictTaken p σ t (by omega) := by
        rw [mem_serialDictTaken_iff]
        rintro ⟨s, hs, hs_eq⟩
        have hprev := ih s.val hs s.isLt
        have hi_ne : i ≠ σ s := fun h => by
          have : (⟨t, ht⟩ : Fin n) = s := σ.injective h
          have hv : t = s.val := congrArg Fin.val this
          omega
        have hν : ν i = ν (σ s) := by
          rw [hprev, serialDictatorship_apply]
          simp only [serialDictFun, Equiv.symm_apply_apply]
          exact hs_eq.symm
        exact hi_ne (ν.injective hν)
      have hopt : (p i).symm (serialDictPick p σ ⟨t, ht⟩) ≤ (p i).symm (ν i) :=
        serialDictPick_optimal p σ ⟨t, ht⟩ hnot
      have hsd : serialDictatorship p σ i = serialDictPick p σ ⟨t, ht⟩ := by
        rw [serialDictatorship_apply, serialDictFun, Equiv.symm_apply_apply]
      have hle : (p i).symm (ν i) ≤ (p i).symm (serialDictatorship p σ i) := hweak i
      rw [hsd] at hle
      exact ((p i).symm.injective (le_antisymm hle hopt)).trans hsd.symm
  have hi₀ := heq (σ.symm i₀).val (σ.symm i₀).isLt
  have hinv : σ ⟨(σ.symm i₀).val, (σ.symm i₀).isLt⟩ = i₀ := by
    have : (⟨(σ.symm i₀).val, (σ.symm i₀).isLt⟩ : Fin n) = σ.symm i₀ := rfl
    rw [this, Equiv.apply_symm_apply]
  rw [hinv] at hi₀
  rw [hi₀] at hstrict
  exact lt_irrefl _ hstrict

private lemma sdPrefix_update_of_le {n : ℕ} (p : Profile n) (σ : Equiv.Perm (Fin n))
    (i : Fin n) (π' : Equiv.Perm (Fin n)) (t : ℕ) (ht : t ≤ (σ.symm i).val) :
    serialDictTaken (Function.update p i π') σ t (by omega) =
      serialDictTaken p σ t (by omega) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hprev := ih (by omega)
    have hne : σ ⟨t, by omega⟩ ≠ i := fun h => by
      have heq : (⟨t, by omega⟩ : Fin n) = σ.symm i :=
        (σ.eq_symm_apply.mpr h)
      have hv := congrArg Fin.val heq
      dsimp at hv
      omega
    have hpick : serialDictPick (Function.update p i π') σ ⟨t, by omega⟩ =
        serialDictPick p σ ⟨t, by omega⟩ := by
      unfold serialDictPick
      have hset : (sdPrefix (Function.update p i π') σ t (by omega)).1 =
          (sdPrefix p σ t (by omega)).1 := hprev
      simp only [Function.update_of_ne hne, hset]
    rw [serialDictTaken_succ _ σ t (by omega), serialDictTaken_succ _ σ t (by omega),
      hpick, hprev]

/-- Deterministic serial dictatorship is strategy-proof: no agent can gain a strictly better
object by misreporting her preference ranking. -/
theorem serialDictatorship_strategyProof {n : ℕ} (p : Profile n) (σ : Equiv.Perm (Fin n))
    (i : Fin n) (π' : Equiv.Perm (Fin n)) :
    (p i).symm (serialDictatorship p σ i) ≤
      (p i).symm (serialDictatorship (Function.update p i π') σ i) := by
  have hnot' : serialDictPick (Function.update p i π') σ (σ.symm i) ∉
      serialDictTaken p σ (σ.symm i).val (by omega) := by
    rw [← sdPrefix_update_of_le p σ i π' (σ.symm i).val le_rfl]
    exact serialDictPick_not_mem_taken (Function.update p i π') σ (σ.symm i)
  rw [serialDictatorship_apply, serialDictatorship_apply]
  have hle := serialDictPick_optimal p σ (σ.symm i) hnot'
  simpa only [serialDictFun, Equiv.apply_symm_apply] using hle

/-- Relabeling agents equivariance for `sdPrefix`. -/
private lemma serialDictTaken_comp {n : ℕ} (p : Profile n) (τ σ : Equiv.Perm (Fin n))
    (t : ℕ) (ht : t ≤ n) :
    serialDictTaken (p ∘ τ) (τ⁻¹ * σ) t ht = serialDictTaken p σ t ht := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hprev := ih (by omega)
    have hcomp : (p ∘ τ) ((τ⁻¹ * σ) ⟨t, by omega⟩) = p (σ ⟨t, by omega⟩) := by
      simp [Function.comp_apply, Equiv.Perm.mul_apply]
    have hpick : serialDictPick (p ∘ τ) (τ⁻¹ * σ) ⟨t, by omega⟩ =
        serialDictPick p σ ⟨t, by omega⟩ := by
      unfold serialDictPick
      have hset : (sdPrefix (p ∘ τ) (τ⁻¹ * σ) t (by omega)).1 =
          (sdPrefix p σ t (by omega)).1 := hprev
      simp only [hcomp, hset]
    rw [serialDictTaken_succ _ _ t (by omega), serialDictTaken_succ _ _ t (by omega),
      hpick, hprev]

lemma serialDictatorship_comp {n : ℕ} (p : Profile n) (τ σ : Equiv.Perm (Fin n)) (i : Fin n) :
    serialDictatorship (p ∘ τ) (τ⁻¹ * σ) i = serialDictatorship p σ (τ i) := by
  rw [serialDictatorship_apply, serialDictatorship_apply]
  have hidx : (τ⁻¹ * σ).symm i = σ.symm (τ i) := by
    rw [Equiv.symm_apply_eq]
    simp [Equiv.Perm.mul_apply]
  have hset : (sdPrefix (p ∘ τ) (τ⁻¹ * σ) (σ.symm (τ i)).val (by omega)).1 =
      (sdPrefix p σ (σ.symm (τ i)).val (by omega)).1 :=
    serialDictTaken_comp p τ σ (σ.symm (τ i)).val (by omega)
  have hpref : (p ∘ τ) ((τ⁻¹ * σ) (σ.symm (τ i))) = p (σ (σ.symm (τ i))) := by
    simp [Function.comp_apply, Equiv.Perm.mul_apply]
  unfold serialDictFun serialDictPick
  rw [hidx]
  simp only [hpref, hset]

/-- **Random Serial Dictatorship (RSD):** the uniform convex combination of the `n!` deterministic
serial dictatorship matchings. -/
noncomputable def rsd {n : ℕ} : AssignmentRule n := fun p =>
  (Nat.factorial n : ℝ)⁻¹ •
    ∑ σ : Equiv.Perm (Fin n), (serialDictatorship p σ).permMatrix ℝ

lemma rsd_apply {n : ℕ} (p : Profile n) (i o : Fin n) :
    rsd p i o = (Nat.factorial n : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin n), if serialDictatorship p σ i = o then (1 : ℝ) else 0 := by
  simp only [rsd, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases h : serialDictatorship p σ i = o
  · subst h
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, h]

lemma rsd_apply_pos_iff {n : ℕ} (p : Profile n) (i o : Fin n) :
    0 < rsd p i o ↔ ∃ σ : Equiv.Perm (Fin n), serialDictatorship p σ i = o := by
  rw [rsd_apply, mul_pos_iff_of_pos_left (by positivity),
    Finset.sum_pos_iff_of_nonneg fun σ _ => by split_ifs <;> norm_num]
  simp only [Finset.mem_univ, true_and]
  exact exists_congr fun σ => by split_ifs with h <;> simp [h]

/-- Every `rsd p` is doubly stochastic. -/
theorem rsd_mem_doublyStochastic {n : ℕ} (p : Profile n) :
    rsd p ∈ doublyStochastic ℝ (Fin n) := by
  rw [mem_doublyStochastic_iff_sum]
  have hfac : (Nat.factorial n : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (Nat.factorial_pos n)).ne'
  have hcard : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) = Nat.factorial n := by
    simp [Fintype.card_perm]
  refine ⟨fun i o => ?_, fun i => ?_, fun o => ?_⟩
  · rw [rsd_apply]
    refine mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) ?_
    exact Finset.sum_nonneg fun σ _ => by split_ifs <;> norm_num
  · simp_rw [rsd_apply, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    have hrow : ∀ σ : Equiv.Perm (Fin n),
        ∑ o : Fin n, (if serialDictatorship p σ i = o then (1 : ℝ) else 0) = 1 := by simp
    simp only [hrow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard]
    exact inv_mul_cancel₀ hfac
  · simp_rw [rsd_apply, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    have hcol : ∀ σ : Equiv.Perm (Fin n),
        ∑ i : Fin n, (if serialDictatorship p σ i = o then (1 : ℝ) else 0) = 1 := fun σ =>
      (Equiv.sum_comp (serialDictatorship p σ) fun x => if x = o then (1 : ℝ) else 0).trans
        (by simp)
    simp only [hcol, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard]
    exact inv_mul_cancel₀ hfac

/-- `rsd` is ex-post efficient: it assigns positive weight only to Pareto-efficient deterministic
matchings. -/
theorem rsd_isExPostEfficient {n : ℕ} (p : Profile n) : IsExPostEfficient p (rsd p) := by
  let w : Equiv.Perm (Fin n) → ℝ := fun μ =>
    (Nat.factorial n : ℝ)⁻¹ *
      ((Finset.univ.filter fun σ : Equiv.Perm (Fin n) => serialDictatorship p σ = μ).card : ℝ)
  have hfac_pos : (0 : ℝ) < (Nat.factorial n : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  refine ⟨w, fun μ => mul_nonneg (inv_nonneg.mpr hfac_pos.le) (Nat.cast_nonneg _), ?_, ?_, ?_⟩
  · have hsum_card : ∑ μ : Equiv.Perm (Fin n),
        (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => serialDictatorship p σ = μ).card =
        Nat.factorial n :=
      (Finset.card_eq_sum_card_fiberwise (f := serialDictatorship p) (s := Finset.univ)
        (t := Finset.univ) fun _ _ => Finset.mem_univ _).symm.trans (by simp [Fintype.card_perm])
    simp only [w, ← Finset.mul_sum, ← Nat.cast_sum, hsum_card]
    exact inv_mul_cancel₀ hfac_pos.ne'
  · intro μ hpos
    have hcard_pos : 0 <
        (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => serialDictatorship p σ = μ).card :=
      Nat.pos_of_ne_zero fun h0 => by simp [w, h0] at hpos
    obtain ⟨σ, hσ⟩ := Finset.card_pos.mp hcard_pos
    rw [← (Finset.mem_filter.mp hσ).2]
    exact serialDictatorship_isParetoEfficient p σ
  · ext i o
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, rsd, w, mul_assoc,
      ← Finset.mul_sum]
    congr 1
    have hsplit : ∑ μ : Equiv.Perm (Fin n),
        ((Finset.univ.filter fun σ => serialDictatorship p σ = μ).card : ℝ) *
          μ.permMatrix ℝ i o =
        ∑ μ : Equiv.Perm (Fin n),
          ∑ σ ∈ Finset.univ.filter (fun σ => serialDictatorship p σ = μ),
            (serialDictatorship p σ).permMatrix ℝ i o := by
      refine Finset.sum_congr rfl fun μ _ => ?_
      have hc : ∀ σ ∈ Finset.univ.filter (fun σ => serialDictatorship p σ = μ),
          (serialDictatorship p σ).permMatrix ℝ i o = μ.permMatrix ℝ i o := by
        intro σ hσ; rw [(Finset.mem_filter.mp hσ).2]
      rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
    rw [hsplit]
    exact Finset.sum_fiberwise (s := (Finset.univ : Finset (Equiv.Perm (Fin n))))
      (g := fun σ => serialDictatorship p σ)
      (f := fun σ => (serialDictatorship p σ).permMatrix ℝ i o)

/-- `rsd` is anonymous: permuting agent labels via `τ` permutes the rows of `rsd` by `τ`. -/
theorem rsd_isAnonymous {n : ℕ} (p : Profile n) (τ : Equiv.Perm (Fin n)) (i o : Fin n) :
    rsd (p ∘ τ) i o = rsd p (τ i) o := by
  rw [rsd_apply, rsd_apply]
  congr 1
  refine (Equiv.sum_comp (Equiv.mulLeft τ⁻¹)
    (fun σ => if serialDictatorship (p ∘ τ) σ i = o then (1 : ℝ) else 0)).symm.trans ?_
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Equiv.coe_mulLeft, serialDictatorship_comp]

/-- `rsd` satisfies equal treatment of equals (ETE). -/
theorem rsd_isEqualTreatmentOfEquals {n : ℕ} (p : Profile n) :
    IsEqualTreatmentOfEquals p (rsd p) := by
  intro i j hij
  funext o
  have hprof : p ∘ Equiv.swap i j = p := by
    funext k
    simp only [Function.comp_apply]
    by_cases h1 : k = i
    · subst h1; simp [hij]
    · by_cases h2 : k = j
      · subst h2; simp [hij]
      · simp [Equiv.swap_apply_of_ne_of_ne h1 h2]
  have h := rsd_isAnonymous p (Equiv.swap i j) i o
  rw [hprof, Equiv.swap_apply_left] at h
  exact h

/-- `rsd` is strongly `sd`-strategy-proof. -/
theorem rsd_isSDStrategyProof {n : ℕ} : IsSDStrategyProof (rsd (n := n)) := by
  intro p i π' k
  have heval : ∀ (q : Profile n),
      upperContourSum (p i) (rsd q i) k =
        (Nat.factorial n : ℝ)⁻¹ *
          ∑ σ : Equiv.Perm (Fin n),
            if (p i).symm (serialDictatorship q σ i) ≤ k then (1 : ℝ) else 0 := by
    intro q
    rw [upperContourSum_eq_sum_filter]
    simp_rw [rsd_apply, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    by_cases hk : (p i).symm (serialDictatorship q σ i) ≤ k
    · simp only [hk, ↓reduceIte]
      rw [Finset.sum_eq_single (serialDictatorship q σ i)]
      · simp
      · intro o _ ho; simp [ho.symm]
      · intro hm
        exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ (serialDictatorship q σ i), hk⟩) hm
    · simp only [hk, ↓reduceIte]
      refine Finset.sum_eq_zero fun o ho => ?_
      have ho' := (Finset.mem_filter.mp ho).2
      have hne : serialDictatorship q σ i ≠ o := fun heq => hk (heq ▸ ho')
      simp [hne]
  rw [heval p, heval (Function.update p i π')]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => ?_)
    (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hle := serialDictatorship_strategyProof p σ i π'
  by_cases h : (p i).symm (serialDictatorship (Function.update p i π') σ i) ≤ k
  · simp [h, hle.trans h]
  · simp only [h, ↓reduceIte]; split_ifs <;> norm_num

/-- `rsd` never produces a 2-cycle in the trade relation when `n ≤ 3`. -/
private lemma rsd_no_twoCycle_of_le_three {n : ℕ} (hn : n ≤ 3) (p : Profile n)
    {a b : Fin n} (hab : tradeRel p (rsd p) a b) (hba : tradeRel p (rsd p) b a) : False := by
  obtain ⟨i₁, hpos₁, hpref₁⟩ := hab
  obtain ⟨i₂, hpos₂, hpref₂⟩ := hba
  have hi_ne : i₁ ≠ i₂ := by
    rintro rfl
    exact lt_asymm hpref₁ hpref₂
  obtain ⟨σ₁, hσ₁⟩ := (rsd_apply_pos_iff p i₁ b).mp hpos₁
  obtain ⟨σ₂, hσ₂⟩ := (rsd_apply_pos_iff p i₂ a).mp hpos₂
  obtain ⟨j₁, hj₁_lt, hj₁_eq⟩ :=
    serialDictatorship_taken_before p σ₁ (o := a) (by rwa [hσ₁])
  obtain ⟨j₂, hj₂_lt, hj₂_eq⟩ :=
    serialDictatorship_taken_before p σ₂ (o := b) (by rwa [hσ₂])
  have hab : a ≠ b := by rintro rfl; exact lt_irrefl _ hpref₁
  have hj₁_pref := serialDictatorship_rank_lt_of_lt p σ₁ hj₁_lt hj₁_eq hσ₁ hab
  have hj₂_pref := serialDictatorship_rank_lt_of_lt p σ₂ hj₂_lt hj₂_eq hσ₂ hab.symm
  have hj₁_ne_i₁ : j₁ ≠ i₁ := fun h => by subst h; omega
  have hj₁_ne_i₂ : j₁ ≠ i₂ := fun h => by subst h; exact lt_asymm hj₁_pref hpref₂
  have hj₂_ne_i₁ : j₂ ≠ i₁ := fun h => by subst h; exact lt_asymm hj₂_pref hpref₁
  have hj₂_ne_i₂ : j₂ ≠ i₂ := fun h => by subst h; omega
  obtain rfl : j₁ = j₂ := by omega
  exact lt_asymm hj₁_pref hj₂_pref

/-- In `Fin 3`, an element other than `i₁` is one of the two other distinct elements. -/
private lemma fin3_eq_or_eq {i₁ i₂ i₃ j : Fin 3} (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃)
    (hj : j ≠ i₁) : j = i₂ ∨ j = i₃ := by
  revert i₁ i₂ i₃ j; decide

/-- On a 3-cycle in `Fin 3`, helper forcing `i₂` to prefer `a` over `b` whenever `i₁` gets `b`
(`a > b`), `i₂` prefers `b > c`, and `i₃` prefers `c > a`. -/
private lemma rsd_threeCycle_force (p : Profile 3)
    {i₁ i₂ i₃ a b c : Fin 3}
    (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃)
    (hab : a ≠ b) (hbc : b ≠ c)
    (h1 : (p i₁).symm a < (p i₁).symm b)
    (h2 : (p i₂).symm b < (p i₂).symm c)
    (h3 : (p i₃).symm c < (p i₃).symm a)
    (hσ : ∃ σ : Equiv.Perm (Fin 3), serialDictatorship p σ i₁ = b) :
    (p i₂).symm a < (p i₂).symm b := by
  obtain ⟨σ, hσ_eq⟩ := hσ
  obtain ⟨j, hj_lt, hj_eq⟩ :=
    serialDictatorship_taken_before p σ (o := a) (by rwa [hσ_eq])
  have hj_ne1 : j ≠ i₁ := fun h => by subst h; omega
  obtain rfl | rfl := fin3_eq_or_eq h12 h13 h23 hj_ne1
  · exact serialDictatorship_rank_lt_of_lt p σ hj_lt hj_eq hσ_eq hab
  · -- `j = i₃` took `a` before `i₁` took `b`, so `c` must have been taken before `j`.
    obtain ⟨k, hk_lt, hk_eq⟩ :=
      serialDictatorship_taken_before p σ (o := c) (by rwa [hj_eq])
    have hk_ne3 : k ≠ j := fun h => by subst h; omega
    have hk_ne1 : k ≠ i₁ := fun h => by subst h; exact hbc (hσ_eq.symm.trans hk_eq)
    obtain rfl := (fin3_eq_or_eq h12 h13 h23 hk_ne1).resolve_right hk_ne3
    have hle := serialDictatorship_rank_le_of_lt p σ (lt_trans hk_lt hj_lt)
    rw [hk_eq, hσ_eq] at hle
    exact absurd (lt_of_lt_of_le h2 hle) (lt_irrefl _)

/-- **Sharp positive efficiency bound:** for `n ≤ 3`, Random Serial Dictatorship is `sd`-efficient
for every strict preference profile `p`. -/
theorem rsd_isSDEfficient_of_le_three {n : ℕ} (hn : n ≤ 3) (p : Profile n) :
    IsSDEfficient p (rsd p) := by
  rw [isSDEfficient_iff_isAcyclicTrade]
  refine ⟨rsd_mem_doublyStochastic p, ⟨fun x hx => ?_⟩⟩
  have hstep : ∀ m : ℕ, 2 ≤ m → m ≤ n →
      ∀ c : Fin m → Fin n, Function.Injective c →
        (∀ j : Fin m, tradeRel p (rsd p)
      (c ⟨(j.val + 1) % m, Nat.mod_lt _ (Nat.zero_lt_of_lt j.isLt)⟩) (c j)) →
        False := by
    intro m hm2 hmn c hc_inj hcyc
    obtain rfl | rfl : m = 2 ∨ m = 3 := by omega
    · have h01 : tradeRel p (rsd p) (c ⟨1, by omega⟩) (c ⟨0, by omega⟩) := hcyc ⟨0, by omega⟩
      have h10 : tradeRel p (rsd p) (c ⟨0, by omega⟩) (c ⟨1, by omega⟩) := by
        simpa [show (⟨(1 + 1) % 2, Nat.mod_lt _ (by omega)⟩ : Fin 2) = ⟨0, by omega⟩ from rfl]
          using hcyc ⟨1, by omega⟩
      exact rsd_no_twoCycle_of_le_three hn p h01 h10
    · obtain rfl : n = 3 := by omega
      let a := c ⟨0, by omega⟩
      let b := c ⟨1, by omega⟩
      let d := c ⟨2, by omega⟩
      have hab : a ≠ b := fun h => by simpa using hc_inj h
      have had : a ≠ d := fun h => by simpa using hc_inj h
      have hbd : b ≠ d := fun h => by simpa using hc_inj h
      have hba : tradeRel p (rsd p) b a := hcyc ⟨0, by omega⟩
      have hdb : tradeRel p (rsd p) d b := hcyc ⟨1, by omega⟩
      have had_e : tradeRel p (rsd p) a d := by
        simpa [a, d,
          show (⟨(2 + 1) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = ⟨0, by omega⟩ from rfl] using
          hcyc ⟨2, by omega⟩
      obtain ⟨i₁, hpos₁, hpref₁⟩ := hba
      obtain ⟨i₂, hpos₂, hpref₂⟩ := hdb
      obtain ⟨i₃, hpos₃, hpref₃⟩ := had_e
      have h12 : i₁ ≠ i₂ := by
        rintro rfl
        have htr : tradeRel p (rsd p) d a := ⟨i₁, hpos₁, lt_trans hpref₂ hpref₁⟩
        exact rsd_no_twoCycle_of_le_three le_rfl p htr ⟨i₃, hpos₃, hpref₃⟩
      have h23 : i₂ ≠ i₃ := by
        rintro rfl
        have htr : tradeRel p (rsd p) a b := ⟨i₂, hpos₂, lt_trans hpref₃ hpref₂⟩
        exact rsd_no_twoCycle_of_le_three le_rfl p htr ⟨i₁, hpos₁, hpref₁⟩
      have h13 : i₁ ≠ i₃ := by
        rintro rfl
        have htr : tradeRel p (rsd p) b d := ⟨i₁, hpos₃, lt_trans hpref₁ hpref₃⟩
        exact rsd_no_twoCycle_of_le_three le_rfl p htr ⟨i₂, hpos₂, hpref₂⟩
      have hσ₁ := (rsd_apply_pos_iff p i₁ a).mp hpos₁
      have hσ₂ := (rsd_apply_pos_iff p i₂ b).mp hpos₂
      have hσ₃ := (rsd_apply_pos_iff p i₃ d).mp hpos₃
      have hf₂ : (p i₁).symm d < (p i₁).symm b :=
        rsd_threeCycle_force p h12.symm h23 h13 hbd.symm hab.symm
          hpref₂ hpref₁ hpref₃ hσ₂
      have hf₃ : (p i₂).symm a < (p i₂).symm d :=
        rsd_threeCycle_force p h23.symm h13.symm h12.symm had hbd.symm
          hpref₃ hpref₂ hpref₁ hσ₃
      -- Now inside `σ₁` where `i₁` picks `a`: `i₁` prefers `d > b > a` (`hf₂` and `hpref₁`).
      obtain ⟨σ₁, hσ₁_eq⟩ := hσ₁
      -- `d` must be taken by `i₂` or `i₃` strictly before `i₁` takes `a`.
      obtain ⟨jd, hjd_lt, hjd_eq⟩ :=
        serialDictatorship_taken_before p σ₁ (o := d) (by
          rw [hσ₁_eq]; exact lt_trans hf₂ hpref₁)
      have hjd_ne1 : jd ≠ i₁ := fun h => by subst h; omega
      obtain rfl | rfl := fin3_eq_or_eq h12 h13 h23 hjd_ne1
      · -- `i₂` picked `d` while `a` was free, contradicting `i₂` prefers `a > d` (`hf₃`).
        exact lt_asymm hf₃ (serialDictatorship_rank_lt_of_lt p σ₁ hjd_lt hjd_eq hσ₁_eq had.symm)
      · -- `i₃` picked `d` while `a` was free, contradicting `i₃` prefers `a > d`.
        exact lt_asymm hpref₃
          (serialDictatorship_rank_lt_of_lt p σ₁ hjd_lt hjd_eq hσ₁_eq had.symm)
  -- Reduce `TransGen` to a shortest simple cycle and apply `hstep`.
  obtain ⟨m, hm2, c, hc_inj, hcyc⟩ := exists_simple_tradeCycle hx
  have hm_le_n : m ≤ n := by
    simpa using Fintype.card_le_of_injective c hc_inj
  exact hstep m hm2 hm_le_n c hc_inj hcyc

/-- Canonical 3-agent strict profile `(a b c, a c b, b a c)` separating `RSD` and `PS` and showing
that `RSD` is not `sd`-envy-free. -/
def profileThree : Profile 3 :=
  ![Equiv.refl (Fin 3), Equiv.swap (1 : Fin 3) 2, Equiv.swap (0 : Fin 3) 1]

/-- Canonical 4-agent strict profile `(a b c d, a b c d, b a d c, b a d c)` showing that `RSD` is
not `sd`-efficient for `n = 4`. -/
def rsdIneffProfileFour : Profile 4 :=
  ![Equiv.refl (Fin 4),
    Equiv.refl (Fin 4),
    Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3,
    Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3]

/-- Embedding of `rsdIneffProfileFour` into `Fin n` for every `n ≥ 4`: dummy agents `k ≥ 4` rank
object `k` first and swap it with `0`, keeping objects `{0, 1, 2, 3}` on the top four ranks of
agents `0, 1, 2, 3`. -/
def rsdIneffProfile {n : ℕ} (hn : 4 ≤ n) : Profile n := fun i =>
  if h0 : i.val < 2 then
    Equiv.refl (Fin n)
  else if h1 : i.val < 4 then
    Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ * Equiv.swap ⟨2, by omega⟩ ⟨3, by omega⟩
  else
    Equiv.swap ⟨0, by omega⟩ i

/-- If the first two dictators `σ 0` and `σ 1` both rank `o₀` first, and `σ 1` ranks `o₁` second,
then `σ 1` picks `o₁`. -/
private lemma serialDictatorship_second_eq {n : ℕ} (hn : 2 ≤ n) (p : Profile n)
    (σ : Equiv.Perm (Fin n)) (i₀ i₁ o₀ o₁ : Fin n) (hne : o₀ ≠ o₁)
    (hσ0 : σ ⟨0, by omega⟩ = i₀) (hσ1 : σ ⟨1, by omega⟩ = i₁)
    (hr0 : (p i₀).symm o₀ = ⟨0, by omega⟩) (hr1_0 : (p i₁).symm o₀ = ⟨0, by omega⟩)
    (hr1_1 : (p i₁).symm o₁ = ⟨1, by omega⟩) :
    serialDictatorship p σ i₁ = o₁ := by
  have hpick0 : serialDictPick p σ ⟨0, by omega⟩ = o₀ := by
    have hmem : o₀ ∉ serialDictTaken p σ 0 (by omega) := by simp [serialDictTaken, sdPrefix]
    have hle := serialDictPick_optimal p σ ⟨0, by omega⟩ hmem
    rw [hσ0, hr0] at hle
    exact (p i₀).symm.injective (Fin.ext (Nat.eq_zero_of_le_zero hle) |>.trans hr0.symm)
  have ht1 : serialDictTaken p σ 1 (by omega) = {o₀} := by
    rw [serialDictTaken_succ p σ 0 (by omega), hpick0]
    simp [serialDictTaken, sdPrefix]
  have hpick1 : serialDictPick p σ ⟨1, by omega⟩ = o₁ := by
    have hnot1 : o₁ ∉ serialDictTaken p σ 1 (by omega) := by
      rw [ht1, Finset.mem_singleton]; exact hne.symm
    have hnot0 : serialDictPick p σ ⟨1, by omega⟩ ≠ o₀ := by
      simpa [ht1] using serialDictPick_not_mem_taken p σ ⟨1, by omega⟩
    have hle := serialDictPick_optimal p σ ⟨1, by omega⟩ hnot1
    rw [hσ1, hr1_1] at hle
    have hval : ((p i₁).symm (serialDictPick p σ ⟨1, by omega⟩)).val ≤ 1 := hle
    have hne0 : ((p i₁).symm (serialDictPick p σ ⟨1, by omega⟩)).val ≠ 0 := fun hz =>
      hnot0 ((p i₁).symm.injective ((Fin.ext hz).trans hr1_0.symm))
    have heq : (p i₁).symm (serialDictPick p σ ⟨1, by omega⟩) = (p i₁).symm o₁ := by
      rw [hr1_1]; exact Fin.ext (by change _ = (1 : ℕ); omega)
    exact (p i₁).symm.injective heq
  rw [serialDictatorship_apply, serialDictFun,
    show σ.symm i₁ = ⟨1, by omega⟩ from (Equiv.symm_apply_eq σ).mpr hσ1.symm, hpick1]

private lemma rsd_ineff_entry_one {n : ℕ} (hn : 4 ≤ n) :
    0 < rsd (rsdIneffProfile hn) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  rw [rsd_apply_pos_iff]
  refine ⟨Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩,
    serialDictatorship_second_eq (by omega) (rsdIneffProfile hn) _
      ⟨1, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.ext_iff])
      (by simp) (by simp) ?_ ?_ ?_⟩ <;> simp [rsdIneffProfile]

private lemma rsd_ineff_entry_two {n : ℕ} (hn : 4 ≤ n) :
    0 < rsd (rsdIneffProfile hn) ⟨2, by omega⟩ ⟨0, by omega⟩ := by
  rw [rsd_apply_pos_iff]
  refine ⟨Equiv.swap ⟨0, by omega⟩ ⟨3, by omega⟩ * Equiv.swap ⟨1, by omega⟩ ⟨2, by omega⟩,
    serialDictatorship_second_eq (by omega) (rsdIneffProfile hn) _
      ⟨3, by omega⟩ ⟨2, by omega⟩ ⟨1, by omega⟩ ⟨0, by omega⟩ (by simp [Fin.ext_iff])
      ?_ ?_ ?_ ?_ ?_⟩
  · simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne, Fin.ext_iff]
  · simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne, Fin.ext_iff]
  all_goals
    simp [rsdIneffProfile, Equiv.symm_apply_eq, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne, Fin.ext_iff]

/-- For every `n ≥ 4`, Random Serial Dictatorship fails `sd`-efficiency. -/
theorem not_isSDEfficient_rsd_of_four_le {n : ℕ} (hn : 4 ≤ n) :
    ¬ IsSDEfficient (rsdIneffProfile hn) (rsd (rsdIneffProfile hn)) := by
  intro heff
  have h01 : 0 < rsd (rsdIneffProfile hn) ⟨0, by omega⟩ ⟨1, by omega⟩ :=
    rsd_ineff_entry_one hn
  have h20 : 0 < rsd (rsdIneffProfile hn) ⟨2, by omega⟩ ⟨0, by omega⟩ :=
    rsd_ineff_entry_two hn
  have hpref0 : (rsdIneffProfile hn ⟨0, by omega⟩).symm ⟨0, by omega⟩ <
      (rsdIneffProfile hn ⟨0, by omega⟩).symm ⟨1, by omega⟩ := by
    simp [rsdIneffProfile]
  have hpref2 : (rsdIneffProfile hn ⟨2, by omega⟩).symm ⟨1, by omega⟩ <
      (rsdIneffProfile hn ⟨2, by omega⟩).symm ⟨0, by omega⟩ := by
    have hp2 : rsdIneffProfile hn ⟨2, by omega⟩ =
        Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ * Equiv.swap ⟨2, by omega⟩ ⟨3, by omega⟩ := by
      simp [rsdIneffProfile]
    rw [hp2]
    have ha : (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ *
        Equiv.swap (⟨2, by omega⟩ : Fin n) ⟨3, by omega⟩).symm ⟨1, by omega⟩ =
          ⟨0, by omega⟩ := by
      rw [Equiv.symm_apply_eq]
      simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne, Fin.ext_iff]
    have hb : (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ *
        Equiv.swap (⟨2, by omega⟩ : Fin n) ⟨3, by omega⟩).symm ⟨0, by omega⟩ =
          ⟨1, by omega⟩ := by
      rw [Equiv.symm_apply_eq]
      simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne, Fin.ext_iff]
    rw [ha, hb]
    change (0 : ℕ) < 1
    omega
  exact heff.not_twoCycle h01 hpref0 h20 hpref2

/-- The exact 4-agent `rsd` profile agrees with `rsdIneffProfile (le_refl 4)`. -/
private lemma rsdIneffProfileFour_eq :
    rsdIneffProfileFour = rsdIneffProfile (le_refl 4) := by
  funext i
  fin_cases i <;> simp [rsdIneffProfileFour, rsdIneffProfile]

/-- On `n = 4`, `rsd rsdIneffProfileFour` is strictly `sd`-inefficient. -/
theorem not_isSDEfficient_rsd_four :
    ¬ IsSDEfficient rsdIneffProfileFour (rsd rsdIneffProfileFour) := by
  rw [rsdIneffProfileFour_eq]
  exact not_isSDEfficient_rsd_of_four_le (le_refl 4)

private lemma rsd_eq_inv_fac_mul_card {n : ℕ} (p : Profile n) (i o : Fin n) :
    rsd p i o = (Nat.factorial n : ℝ)⁻¹ *
      ((∑ σ : Equiv.Perm (Fin n), if serialDictFun p σ i = o then (1 : ℕ) else 0 : ℕ) : ℝ) := by
  rw [rsd_apply, Nat.cast_sum]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp [serialDictatorship_apply]

private lemma rsd_profileThree_counts (i o : Fin 3) :
    (∑ σ : Equiv.Perm (Fin 3), if serialDictFun profileThree σ i = o then (1 : ℕ) else 0) =
      (if i = 0 then ![3, 1, 2] o else if i = 1 then ![3, 0, 3] o else ![0, 5, 1] o) := by
  decide +revert

/-- Exact `rsd` assignment probabilities for agent `0` on `profileThree`: `(1/2, 1/6, 1/3)`. -/
theorem rsd_profileThree_row0 :
    rsd profileThree 0 0 = 1 / 2 ∧ rsd profileThree 0 1 = 1 / 6 ∧
    rsd profileThree 0 2 = 1 / 3 := by
  simp only [rsd_eq_inv_fac_mul_card, rsd_profileThree_counts]
  norm_num [Nat.factorial]

/-- Exact `rsd` assignment probabilities for agent `2` on `profileThree`: `(0, 5/6, 1/6)`. -/
theorem rsd_profileThree_row2 :
    rsd profileThree 2 0 = 0 ∧ rsd profileThree 2 1 = 5 / 6 ∧
    rsd profileThree 2 2 = 1 / 6 := by
  simp only [rsd_eq_inv_fac_mul_card, rsd_profileThree_counts]
  norm_num [Nat.factorial]

/-- `rsd` is **not** `sd`-envy-free at `n = 3`: on `profileThree = (a b c, a c b, b a c)`, agent
`0` (`a > b > c`) gets `a + b` weight `1/2 + 1/6 = 2/3`, strictly less than agent `2`'s `a + b`
weight `0 + 5/6 = 5/6`. -/
theorem not_isSDEnvyFree_rsd_three :
    ¬ IsSDEnvyFree profileThree (rsd profileThree) := by
  intro hef
  have h02 := hef 0 2 1
  obtain ⟨r00, r01, _⟩ := rsd_profileThree_row0
  obtain ⟨r20, r21, _⟩ := rsd_profileThree_row2
  have hs : ∀ x : Fin 3 → ℝ,
      upperContourSum (profileThree 0) x 1 = x 0 + x 1 := by
    intro x
    simp only [upperContourSum, profileThree, Matrix.cons_val_zero, Equiv.refl_apply]
    have hiic : Finset.Iic (1 : Fin 3) = {0, 1} := by decide
    rw [hiic, Finset.sum_pair (by decide)]
  rw [hs, hs, r00, r01, r20, r21] at h02
  linarith

/-- Exact `rsd` matrix on `rsdIneffProfileFour`: rows `0, 1` are `(5/12, 1/12, 5/12, 1/12)` and
rows `2, 3` are `(1/12, 5/12, 1/12, 5/12)`. -/
theorem rsd_ineffProfileFour_apply (i o : Fin 4) :
    rsd rsdIneffProfileFour i o =
      if i.val < 2 then
        if o.val = 0 ∨ o.val = 2 then 5 / 12 else 1 / 12
      else
        if o.val = 1 ∨ o.val = 3 then 5 / 12 else 1 / 12 := by
  have hc : ∀ (i o : Fin 4),
      (∑ σ : Equiv.Perm (Fin 4),
          if serialDictFun rsdIneffProfileFour σ i = o then (1 : ℕ) else 0) =
        if i.val < 2 then
          if o.val = 0 ∨ o.val = 2 then 10 else 2
        else
          if o.val = 1 ∨ o.val = 3 then 10 else 2 := by
    decide
  rw [rsd_eq_inv_fac_mul_card, hc i o]
  have hfac : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hfac]
  split_ifs <;> norm_num

/-- Explicit doubly stochastic matrix `(1/2, 0, 1/2, 0)` / `(0, 1/2, 0, 1/2)` that strictly
`sd`-dominates `rsd rsdIneffProfileFour` for **every** one of the four agents. -/
theorem rsd_ineffProfileFour_strictly_dominated :
    let Q : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun i o =>
      if i.val < 2 then (if o.val = 0 ∨ o.val = 2 then 1 / 2 else 0)
      else (if o.val = 1 ∨ o.val = 3 then 1 / 2 else 0)
    Q ∈ doublyStochastic ℝ (Fin 4) ∧
      ∀ i : Fin 4, SDDominatesStrict (rsdIneffProfileFour i) (Q i)
        (rsd rsdIneffProfileFour i) := by
  intro Q
  refine ⟨?_, ?_⟩
  · rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun i o => by simp only [Q, Matrix.of_apply]; split_ifs <;> norm_num,
      fun i => ?_, fun o => ?_⟩
    · fin_cases i <;> simp [Q, Fin.sum_univ_four] <;> norm_num
    · fin_cases o <;> simp [Q, Fin.sum_univ_four] <;> norm_num
  · intro i
    have hsum0 : ∀ (π : Equiv.Perm (Fin 4)) (x : Fin 4 → ℝ),
        upperContourSum π x 0 = x (π 0) := fun π x => by
      simp [upperContourSum, show Finset.Iic (0 : Fin 4) = {0} by decide]
    have hdom_row : ∀ (i k : Fin 4),
        upperContourSum (rsdIneffProfileFour i) (rsd rsdIneffProfileFour i) k ≤
          upperContourSum (rsdIneffProfileFour i) (Q i) k := by
      intro i k
      have hval : ∀ (j k : Fin 4),
          (rsdIneffProfileFour j k).val =
            (if j.val < 2 then k.val
             else ![1, 0, 3, 2] k) := by decide
      have heval : ∀ (x : Fin 4 → ℝ),
          upperContourSum (rsdIneffProfileFour i) x k =
            (if (0 : Fin 4) ≤ k then x (rsdIneffProfileFour i 0) else 0) +
            (if (1 : Fin 4) ≤ k then x (rsdIneffProfileFour i 1) else 0) +
            (if (2 : Fin 4) ≤ k then x (rsdIneffProfileFour i 2) else 0) +
            (if (3 : Fin 4) ≤ k then x (rsdIneffProfileFour i 3) else 0) := by
        intro x
        have hf : Finset.Iic k = Finset.univ.filter fun r : Fin 4 => r ≤ k := by
          ext r; simp
        rw [upperContourSum, hf, Finset.sum_filter, Fin.sum_univ_four]
      have hQ : ∀ j o : Fin 4, Q j o =
          if j.val < 2 then (if o.val = 0 ∨ o.val = 2 then 1 / 2 else 0)
          else (if o.val = 1 ∨ o.val = 3 then 1 / 2 else 0) := fun _ _ => rfl
      rw [heval, heval]
      simp_rw [hQ, rsd_ineffProfileFour_apply, hval]
      fin_cases i <;> fin_cases k <;> norm_num
    have hstrict_row : ∀ i : Fin 4,
        upperContourSum (rsdIneffProfileFour i) (rsd rsdIneffProfileFour i) 0 <
          upperContourSum (rsdIneffProfileFour i) (Q i) 0 := by
      intro i
      rw [hsum0, hsum0]
      have hQ : ∀ j o : Fin 4, Q j o =
          if j.val < 2 then (if o.val = 0 ∨ o.val = 2 then 1 / 2 else 0)
          else (if o.val = 1 ∨ o.val = 3 then 1 / 2 else 0) := fun _ _ => rfl
      have hval0 : ∀ j : Fin 4, (rsdIneffProfileFour j 0).val = if j.val < 2 then 0 else 1 := by
        decide
      rw [hQ, rsd_ineffProfileFour_apply, hval0]
      fin_cases i <;> norm_num
    exact ⟨hdom_row i, 0, hstrict_row i⟩

end Cslib.GameTheory.RandomAssignment
