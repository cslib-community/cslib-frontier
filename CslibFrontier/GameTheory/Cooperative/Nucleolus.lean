/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Cooperative.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Order.PiLex
import CslibFrontier.Foundations.LinearAlgebra.Matrix.LinearProgramming
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Sum
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The nucleolus, prenucleolus, and Kohlberg's balanced-collection theorem

This module formalizes the **nucleolus** and **prenucleolus** of finite transferable-utility
cooperative games ([Schmeidler1969], [Kohlberg1971]):

1. **Descending order statistics (`sortDesc`)**: characterizes the nonincreasingly sorted tuple
   of any finite real vector `u : κ → ℝ` via the minimax order-statistic formula
   `max_{|T| = k + 1} min_{s ∈ T} u s`, proving continuity in `u`, antitone ordering
   (`sortDesc_antitone`), list-permutation equivalence (`sortDesc_perm_list`), threshold counting
   (`le_sortDesc_iff`, `sortDesc_lex_lt_iff_countGe`), and Schmeidler's midpoint descent lemma
   (`sortDesc_midpoint_lt_of_ne`).
2. **Schmeidler's existence and uniqueness theorems ([Schmeidler1969])**:
   * General lexicographic minimization (`CooperativeGame.IsLexMinimizerOn`) exists over every
     nonempty compact payoff set `K : Set (A → ℝ)`
     (`CooperativeGame.exists_isLexMinimizerOn_of_isCompact`) and is unique over every convex set
     (`CooperativeGame.unique_isLexMinimizerOn_of_convex`).
   * **Nucleolus** (`CooperativeGame.nucleolus`, `CooperativeGame.existsUnique_nucleolus`): exists
     and is unique whenever the imputation set `imputations G` is nonempty
     (`∑ i, G.val {i} ≤ G.val univ`), and always lies in the core when `G.NonemptyCore`
     (`CooperativeGame.IsNucleolus.inCore`).
   * **Prenucleolus** (`CooperativeGame.prenucleolus`, `CooperativeGame.existsUnique_prenucleolus`):
     exists and is unique for *every* `CooperativeGame A` without hypotheses, and equals
     `G.nucleolus` whenever it is individually rational
     (`CooperativeGame.prenucleolus_eq_nucleolus_of_mem_imputations`).
   * Proper nonempty coalitions `properNonemptyCoalitions A` induce the exact same lexicographic
     comparison on `preimputations G` (`CooperativeGame.sortExcess_lex_lt_iff_proper`).
3. **Kohlberg's balanced-collection criterion ([Kohlberg1971])**:
   Using the affine Farkas lemma (`Matrix.exists_dual_le_of_forall_le`), proves exact
   balanced-family characterizations for both the prenucleolus
   (`CooperativeGame.isPrenucleolus_iff_kohlberg`) and the nucleolus
   (`CooperativeGame.isNucleolus_iff_kohlberg`).
4. **Axiomatic properties and cost-sharing dual**: anonymity (`perm`), symmetry (`AreSymmetric`),
   strategic-equivalence covariance (`mapAffine`), dummy player zero payoff (`IsDummyAgent`), and
   the dual `CostSharingGame.nucleolus` / `CostSharingGame.prenucleolus`.

## Main definitions

* `Cslib.GameTheory.sortDesc`: descendingly sorted order-statistic vector of `u : κ → ℝ`.
* `Cslib.GameTheory.countGe`: number of coordinates of `u : κ → ℝ` at least `r`.
* `Cslib.GameTheory.CooperativeGame.excess`: coalition excess `G.val S - ∑ i ∈ S, x i`.
* `Cslib.GameTheory.CooperativeGame.properNonemptyCoalitions`: nonempty proper coalitions
  `S ⊊ univ`.
* `Cslib.GameTheory.CooperativeGame.sortExcess`: descendingly sorted excess vector over `Finset A`.
* `Cslib.GameTheory.CooperativeGame.sortProperExcess`: descendingly sorted excess vector over
  `properNonemptyCoalitions A`.
* `Cslib.GameTheory.CooperativeGame.preimputations`,
  `Cslib.GameTheory.CooperativeGame.imputations`: efficient and individually rational payoff sets.
* `Cslib.GameTheory.CooperativeGame.IsLexMinimizerOn`,
  `Cslib.GameTheory.CooperativeGame.IsNucleolus`,
  `Cslib.GameTheory.CooperativeGame.IsPrenucleolus`,
  `Cslib.GameTheory.CooperativeGame.nucleolus`,
  `Cslib.GameTheory.CooperativeGame.prenucleolus`: nucleolus and prenucleolus predicates and
  selected allocations.
* `Cslib.GameTheory.CooperativeGame.IsPositiveBalancedOn`,
  `Cslib.GameTheory.CooperativeGame.IsImputationBalancedAt`,
  `Cslib.GameTheory.CooperativeGame.upperLevel`: Kohlberg balanced-collection predicates.
* `Cslib.GameTheory.CooperativeGame.perm`, `Cslib.GameTheory.CooperativeGame.mapAffine`,
  `Cslib.GameTheory.CooperativeGame.AreSymmetric`,
  `Cslib.GameTheory.CooperativeGame.IsDummyAgent`: permutation pushforward, positive affine
  rescaling, symmetric players, and dummy players.
* `Cslib.GameTheory.CostSharingGame.nucleolus`,
  `Cslib.GameTheory.CostSharingGame.prenucleolus`: dual nucleolus and prenucleolus for
  cost-sharing games.

## Main results

* `Cslib.GameTheory.sortDesc_antitone`, `Cslib.GameTheory.sortDesc_perm_list`,
  `Cslib.GameTheory.sortDesc_lex_lt_iff_countGe`,
  `Cslib.GameTheory.sortDesc_midpoint_lt_of_ne`: order-statistic, permutation, threshold, and
  strict-midpoint descent properties of `sortDesc`.
* `Cslib.GameTheory.CooperativeGame.exists_isLexMinimizerOn_of_isCompact`,
  `Cslib.GameTheory.CooperativeGame.unique_isLexMinimizerOn_of_convex`,
  `Cslib.GameTheory.CooperativeGame.existsUnique_isLexMinimizerOn`: Schmeidler's general
  existence and uniqueness theorems over compact convex payoff sets ([Schmeidler1969]).
* `Cslib.GameTheory.CooperativeGame.existsUnique_nucleolus`,
  `Cslib.GameTheory.CooperativeGame.existsUnique_prenucleolus`,
  `Cslib.GameTheory.CooperativeGame.IsNucleolus.inCore`,
  `Cslib.GameTheory.CooperativeGame.prenucleolus_eq_nucleolus_of_mem_imputations`: existence,
  uniqueness, and core containment of the nucleolus and prenucleolus ([Schmeidler1969]).
* `Cslib.GameTheory.CooperativeGame.isPrenucleolus_iff_kohlberg`,
  `Cslib.GameTheory.CooperativeGame.isNucleolus_iff_kohlberg`: Kohlberg's balanced-collection
  characterizations ([Kohlberg1971]).
* `Cslib.GameTheory.CooperativeGame.nucleolus_perm`,
  `Cslib.GameTheory.CooperativeGame.nucleolus_eq_of_areSymmetric`,
  `Cslib.GameTheory.CooperativeGame.nucleolus_mapAffine`,
  `Cslib.GameTheory.CooperativeGame.nucleolus_isDummyAgent`: anonymity, symmetry, covariance, and
  dummy-player properties.

## References

* [Kohlberg1971]
* [Schmeidler1969]
-/

public section

namespace Cslib.GameTheory

/-! ## Descending order statistics and lexicographic comparison -/

section OrderStatistics

private theorem powersetCard_univ_nonempty_aux {κ : Type*} [Fintype κ] (k : Fin (Fintype.card κ)) :
    ((Finset.univ : Finset κ).powersetCard (k.1 + 1)).Nonempty := by
  obtain ⟨T, -, hT⟩ := Finset.exists_subset_card_eq (n := k.1 + 1) (s := (Finset.univ : Finset κ))
    (by simp only [Finset.card_univ]; exact k.2)
  exact ⟨T, Finset.mem_powersetCard.2 ⟨Finset.subset_univ T, hT⟩⟩

private theorem mem_powersetCard_nonempty_aux {κ : Type*} [Fintype κ] {k : Fin (Fintype.card κ)}
    {T : Finset κ} (hT : T ∈ (Finset.univ : Finset κ).powersetCard (k.1 + 1)) : T.Nonempty :=
  Finset.card_pos.1 (by rw [(Finset.mem_powersetCard.1 hT).2]; exact Nat.succ_pos _)

/-- The `k`-th largest (0-indexed) entry of `u : κ → ℝ`, defined via the minimax order-statistic
formula `max_{|T| = k + 1} min_{s ∈ T} u s`. -/
@[expose] noncomputable def sortDesc {κ : Type*} [Fintype κ] (u : κ → ℝ)
    (k : Fin (Fintype.card κ)) : ℝ :=
  (((Finset.univ : Finset κ).powersetCard (k.1 + 1)).attach).sup'
    (Finset.attach_nonempty_iff.2 (by
      obtain ⟨T, -, hT⟩ := Finset.exists_subset_card_eq (n := k.1 + 1)
        (s := (Finset.univ : Finset κ)) (by simp only [Finset.card_univ]; exact k.2)
      exact ⟨T, Finset.mem_powersetCard.2 ⟨Finset.subset_univ T, hT⟩⟩))
    fun T => T.1.inf' (Finset.card_pos.1 (by
      rw [(Finset.mem_powersetCard.1 T.2).2]; exact Nat.succ_pos _)) u

/-- Number of coordinates `s : κ` satisfying `r ≤ u s`. -/
@[expose] noncomputable def countGe {κ : Type*} [Fintype κ] (u : κ → ℝ) (r : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun s => r ≤ u s).card

private theorem countGe_eq_filter {κ : Type*} [Fintype κ] (u : κ → ℝ) (r : ℝ)
    [DecidablePred fun s => r ≤ u s] :
    countGe u r = (Finset.univ.filter fun s => r ≤ u s).card := by
  classical
  unfold countGe
  congr 1
  ext s
  simp only [Finset.mem_filter]

private theorem countGe_mono {κ : Type*} [Fintype κ] (u : κ → ℝ) {r₁ r₂ : ℝ} (hr : r₁ ≤ r₂) :
    countGe u r₂ ≤ countGe u r₁ := by
  classical
  unfold countGe
  exact Finset.card_le_card fun s hs =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hr.trans (Finset.mem_filter.1 hs).2⟩

private theorem countGe_le_card {κ : Type*} [Fintype κ] (u : κ → ℝ) (r : ℝ) :
    countGe u r ≤ Fintype.card κ := by
  classical
  unfold countGe
  exact (Finset.card_filter_le _ _).trans_eq Finset.card_univ

/-- `r ≤ sortDesc u k` holds iff at least `k + 1` coordinates of `u` satisfy `r ≤ u s`. -/
theorem le_sortDesc_iff {κ : Type*} [Fintype κ] (u : κ → ℝ) (k : Fin (Fintype.card κ))
    (r : ℝ) :
    r ≤ sortDesc u k ↔ k.1 + 1 ≤ countGe u r := by
  classical
  rw [countGe_eq_filter]
  set P := (Finset.univ : Finset κ).powersetCard (k.1 + 1)
  have hPne : P.attach.Nonempty := Finset.attach_nonempty_iff.2 (powersetCard_univ_nonempty_aux k)
  constructor
  · intro hr
    obtain ⟨T, -, hTeq⟩ := Finset.exists_mem_eq_sup' hPne
      fun T => T.1.inf' (mem_powersetCard_nonempty_aux T.2) u
    have hinf : r ≤ T.1.inf' (mem_powersetCard_nonempty_aux T.2) u := by
      simpa only [sortDesc, P, hTeq] using hr
    have hsub : T.1 ⊆ Finset.univ.filter fun s => r ≤ u s := fun s hs =>
      Finset.mem_filter.2 ⟨Finset.mem_univ s, hinf.trans (Finset.inf'_le u hs)⟩
    have hcard : T.1.card = k.1 + 1 := (Finset.mem_powersetCard.1 T.2).2
    simpa only [hcard] using Finset.card_le_card hsub
  · intro hle
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hle
    have hTP : T ∈ P := Finset.mem_powersetCard.2 ⟨Finset.subset_univ T, hTcard⟩
    have hinf : r ≤ T.inf' (mem_powersetCard_nonempty_aux hTP) u :=
      Finset.le_inf' (mem_powersetCard_nonempty_aux hTP) u fun s hs =>
        (Finset.mem_filter.1 (hTsub hs)).2
    have hmem : (⟨T, hTP⟩ : {T // T ∈ P}) ∈ P.attach := Finset.mem_attach P ⟨T, hTP⟩
    exact hinf.trans (Finset.le_sup' (fun S : {T // T ∈ P} => S.1.inf' _ u) hmem)

theorem sortDesc_lt_iff {κ : Type*} [Fintype κ] (u : κ → ℝ) (k : Fin (Fintype.card κ))
    (r : ℝ) :
    sortDesc u k < r ↔ countGe u r ≤ k.1 := by
  rw [← not_le, le_sortDesc_iff, not_le, Nat.lt_succ_iff]

theorem sortDesc_antitone {κ : Type*} [Fintype κ] (u : κ → ℝ) : Antitone (sortDesc u) := by
  intro i j hij
  have hi : i.1 + 1 ≤ countGe u (sortDesc u j) :=
    (Nat.succ_le_succ hij).trans ((le_sortDesc_iff u j (sortDesc u j)).1 le_rfl)
  exact (le_sortDesc_iff u i (sortDesc u j)).2 hi

theorem sortDesc_mem_range {κ : Type*} [Fintype κ] (u : κ → ℝ) (k : Fin (Fintype.card κ)) :
    ∃ s : κ, sortDesc u k = u s := by
  set P := (Finset.univ : Finset κ).powersetCard (k.1 + 1)
  have hPne : P.attach.Nonempty := Finset.attach_nonempty_iff.2 (powersetCard_univ_nonempty_aux k)
  obtain ⟨T, -, hTeq⟩ :=
    Finset.exists_mem_eq_sup' hPne fun T => T.1.inf' (mem_powersetCard_nonempty_aux T.2) u
  obtain ⟨s, -, hseq⟩ := Finset.exists_mem_eq_inf' (mem_powersetCard_nonempty_aux T.2) u
  exact ⟨s, by dsimp only [sortDesc]; rw [hTeq, hseq]⟩

theorem sortDesc_comp_equiv {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂] (e : κ₁ ≃ κ₂)
    (u : κ₂ → ℝ) (k : Fin (Fintype.card κ₁)) :
    sortDesc (u ∘ e) k = sortDesc u (k.cast (Fintype.card_congr e)) := by
  classical
  have hcount : ∀ r : ℝ, countGe (u ∘ e) r = countGe u r := by
    intro r
    simp only [countGe]
    refine Finset.card_nbij' (fun s => e s) (fun s => e.symm s) ?_ ?_ ?_ ?_ <;>
      intro s hs <;> simp_all
  apply le_antisymm
  · rw [le_sortDesc_iff]
    have hge := (le_sortDesc_iff (u ∘ e) k (sortDesc (u ∘ e) k)).1 le_rfl
    rw [hcount] at hge
    simpa only [Fin.val_cast] using hge
  · have hge := (le_sortDesc_iff u (k.cast (Fintype.card_congr e))
      (sortDesc u (k.cast (Fintype.card_congr e)))).1 le_rfl
    rw [le_sortDesc_iff, hcount]
    simpa only [Fin.val_cast] using hge

theorem sortDesc_scale_add {κ : Type*} [Fintype κ] (u : κ → ℝ) {a : ℝ} (ha : 0 ≤ a) (b : ℝ)
    (k : Fin (Fintype.card κ)) :
    sortDesc (fun s => a * u s + b) k = a * sortDesc u k + b := by
  dsimp only [sortDesc]
  set P := (Finset.univ : Finset κ).powersetCard (k.1 + 1)
  have hPne : P.attach.Nonempty := Finset.attach_nonempty_iff.2 (powersetCard_univ_nonempty_aux k)
  have hinf : ∀ T : {T // T ∈ P},
      T.1.inf' (mem_powersetCard_nonempty_aux T.2) (fun s => a * u s + b) =
        a * T.1.inf' (mem_powersetCard_nonempty_aux T.2) u + b := by
    intro T
    obtain ⟨s₀, hs₀T, hs₀⟩ := Finset.exists_mem_eq_inf' (mem_powersetCard_nonempty_aux T.2) u
    apply le_antisymm
    · exact (Finset.inf'_le (fun s => a * u s + b) hs₀T).trans_eq (by rw [hs₀])
    · refine Finset.le_inf' (mem_powersetCard_nonempty_aux T.2) _ fun s hs => ?_
      exact add_le_add (mul_le_mul_of_nonneg_left (Finset.inf'_le u hs) ha) le_rfl
  simp_rw [hinf]
  obtain ⟨T₀, hT₀, hsup₀⟩ :=
    Finset.exists_mem_eq_sup' hPne fun T => T.1.inf' (mem_powersetCard_nonempty_aux T.2) u
  apply le_antisymm
  · refine Finset.sup'_le hPne _ fun T hT => ?_
    have hle := Finset.le_sup' (fun S : {T // T ∈ P} =>
      S.1.inf' (mem_powersetCard_nonempty_aux S.2) u) hT
    exact add_le_add (mul_le_mul_of_nonneg_left hle ha) le_rfl
  · refine (Finset.le_sup' (fun S : {T // T ∈ P} =>
      a * S.1.inf' (mem_powersetCard_nonempty_aux S.2) u + b) hT₀).trans_eq' ?_
    dsimp only [P] at hsup₀ ⊢
    rw [hsup₀]

private theorem card_filter_le_sortDesc {κ : Type*} [Fintype κ] (u : κ → ℝ) (r : ℝ) :
    (Finset.univ.filter fun k : Fin (Fintype.card κ) => r ≤ sortDesc u k).card =
      countGe u r := by
  have hle : countGe u r ≤ Fintype.card κ := countGe_le_card u r
  have hfilt : (Finset.univ.filter fun k : Fin (Fintype.card κ) => r ≤ sortDesc u k) =
      Finset.univ.filter fun k : Fin (Fintype.card κ) => k.1 + 1 ≤ countGe u r := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, le_sortDesc_iff]
  rw [hfilt]
  refine (Finset.card_bij (s := Finset.univ.filter fun k : Fin (Fintype.card κ) =>
      k.1 + 1 ≤ countGe u r) (t := Finset.range (countGe u r))
      (fun k _ => k.1) ?_ ?_ ?_).trans (Finset.card_range (countGe u r))
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hk ⊢
    omega
  · exact fun _ _ _ _ heq => Fin.ext heq
  · intro i hi
    rw [Finset.mem_range] at hi
    exact ⟨⟨i, hi.trans_le hle⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩, rfl⟩

private theorem card_filter_lt_sortDesc {κ : Type*} [Fintype κ] (u : κ → ℝ) (r : ℝ) :
    (Finset.univ.filter fun k : Fin (Fintype.card κ) => r < sortDesc u k).card =
      (Finset.univ.filter fun s : κ => r < u s).card := by
  set S_lt := Finset.univ.filter fun s : κ => r < u s
  by_cases hne : S_lt.Nonempty
  · set b := S_lt.inf' hne u
    have hrb : r < b := by
      obtain ⟨s, hsS, hseq⟩ := Finset.exists_mem_eq_inf' hne u
      dsimp only [b]
      rw [hseq]
      exact (Finset.mem_filter.1 hsS).2
    have hlt_iff : ∀ y, (∃ s, y = u s) → (r < y ↔ b ≤ y) := by
      rintro y ⟨s, rfl⟩
      refine ⟨fun hy => Finset.inf'_le u (Finset.mem_filter.2 ⟨Finset.mem_univ s, hy⟩),
        fun hb => hrb.trans_le hb⟩
    have hfilt_k : (Finset.univ.filter fun k => r < sortDesc u k) =
        Finset.univ.filter fun k => b ≤ sortDesc u k := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hlt_iff (sortDesc u k) (sortDesc_mem_range u k)
    have hfilt_s : S_lt = Finset.univ.filter fun s => b ≤ u s := by
      ext s
      simp only [S_lt, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hlt_iff (u s) ⟨s, rfl⟩
    rw [hfilt_k, hfilt_s, card_filter_le_sortDesc, countGe_eq_filter]
  · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.card_empty, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff]
    intro k _ hk
    obtain ⟨s, hs⟩ := sortDesc_mem_range u k
    exact hne ⟨s, Finset.mem_filter.2 ⟨Finset.mem_univ s, hs ▸ hk⟩⟩

private theorem card_filter_eq_add_lt {ι : Type*} [Fintype ι] (g : ι → ℝ) (a : ℝ) :
    (Finset.univ.filter fun i => g i = a).card +
      (Finset.univ.filter fun i => a < g i).card =
      (Finset.univ.filter fun i => a ≤ g i).card := by
  classical
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [eq_comm]
    exact le_iff_eq_or_lt.symm
  · exact Finset.disjoint_filter.2 fun _ _ heq hlt => hlt.ne heq.symm

private theorem list_count_map_eq_card_filter {ι : Type*} [Fintype ι]
    (l : List ι) (hl : l.Nodup) (hmem : ∀ i, i ∈ l) (g : ι → ℝ) (a : ℝ) :
    (l.map g).count a = (Finset.univ.filter fun i => g i = a).card := by
  classical
  rw [List.count_eq_countP, List.countP_map, List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup (hl.filter _)]
  congr 1
  ext i
  simp only [List.mem_toFinset, List.mem_filter, Function.comp_apply, beq_iff_eq,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.2, fun h => ⟨hmem i, h⟩⟩

/-- `List.ofFn (sortDesc u)` is a permutation of `(Finset.univ : Finset κ).toList.map u`. -/
theorem sortDesc_perm_list {κ : Type*} [Fintype κ] (u : κ → ℝ) :
    (List.ofFn (sortDesc u)).Perm ((Finset.univ : Finset κ).toList.map u) := by
  classical
  have hcard_eq : ∀ a : ℝ,
      (Finset.univ.filter fun k : Fin (Fintype.card κ) => sortDesc u k = a).card =
        (Finset.univ.filter fun s : κ => u s = a).card := by
    intro a
    have h1 := card_filter_eq_add_lt (sortDesc u) a
    have h2 := card_filter_eq_add_lt u a
    rw [card_filter_le_sortDesc, card_filter_lt_sortDesc, countGe_eq_filter] at h1
    omega
  rw [List.perm_iff_count]
  intro a
  rw [List.ofFn_eq_map,
    list_count_map_eq_card_filter (List.finRange _) (List.nodup_finRange _) List.mem_finRange,
    list_count_map_eq_card_filter Finset.univ.toList (Finset.nodup_toList _)
      (fun s => Finset.mem_toList.2 (Finset.mem_univ s))]
  exact hcard_eq a

/-- Threshold characterization of lexicographic strict inequality between sorted tuples
`sortDesc u` and `sortDesc v`: `sortDesc u` is lexicographically strictly smaller iff at the
highest threshold `r` where their upper-tail counts differ, `u` has strictly fewer entries `≥ r`. -/
theorem sortDesc_lex_lt_iff_countGe {κ : Type*} [Fintype κ] (u v : κ → ℝ) :
    toLex (sortDesc u) < toLex (sortDesc v) ↔
      ∃ r : ℝ, countGe u r < countGe v r ∧ ∀ t : ℝ, r < t → countGe u t = countGe v t := by
  constructor
  · rintro ⟨k, hk_eq, hk_lt⟩
    refine ⟨sortDesc v k, ?_, ?_⟩
    · have h1 : countGe u (sortDesc v k) ≤ k.1 := (sortDesc_lt_iff u k (sortDesc v k)).1 hk_lt
      have h2 : k.1 + 1 ≤ countGe v (sortDesc v k) :=
        (le_sortDesc_iff v k (sortDesc v k)).1 le_rfl
      omega
    · intro t ht
      rw [← card_filter_le_sortDesc u t, ← card_filter_le_sortDesc v t]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases lt_or_ge j k with hjk | hkj
      · rw [show sortDesc u j = sortDesc v j from hk_eq j hjk]
      · exact iff_of_false (not_le.2 ((sortDesc_antitone u hkj).trans_lt (hk_lt.trans ht)))
          (not_le.2 ((sortDesc_antitone v hkj).trans_lt ht))
  · rintro ⟨r, hlt, heqt⟩
    have hlt_card : countGe u r < Fintype.card κ := lt_of_lt_of_le hlt (countGe_le_card v r)
    let k : Fin (Fintype.card κ) := ⟨countGe u r, hlt_card⟩
    refine ⟨k, fun j hj => ?_, ?_⟩
    · change sortDesc u j = sortDesc v j
      refine eq_of_forall_le_iff fun t => ?_
      rw [le_sortDesc_iff, le_sortDesc_iff]
      rcases lt_or_ge r t with hrt | htr
      · rw [heqt t hrt]
      · have hjk : j.1 < countGe u r := hj
        have hu : j.1 + 1 ≤ countGe u t :=
          (Nat.succ_le_of_lt hjk).trans (countGe_mono u htr)
        have hv : j.1 + 1 ≤ countGe v t :=
          (Nat.succ_le_of_lt (hjk.trans hlt)).trans (countGe_mono v htr)
        exact iff_of_true hu hv
    · exact ((sortDesc_lt_iff u k r).2 le_rfl).trans_le ((le_sortDesc_iff v k r).2 hlt)

private theorem sortDesc_lex_lt_of_countGe_lt {κ : Type*} [Fintype κ] {u v : κ → ℝ} (r₀ : ℝ)
    (hlt : countGe u r₀ < countGe v r₀) (hle : ∀ t : ℝ, r₀ ≤ t → countGe u t ≤ countGe v t) :
    toLex (sortDesc u) < toLex (sortDesc v) := by
  classical
  have hk_lt : countGe u r₀ < Fintype.card κ := lt_of_lt_of_le hlt (countGe_le_card v r₀)
  let k : Fin (Fintype.card κ) := ⟨countGe u r₀, hk_lt⟩
  have hr₀_v : r₀ ≤ sortDesc v k := (le_sortDesc_iff v k r₀).2 hlt
  have hlt_k : sortDesc u k < sortDesc v k :=
    ((sortDesc_lt_iff u k r₀).2 le_rfl).trans_le hr₀_v
  have hle_top : ∀ j : Fin (Fintype.card κ), j ≤ k → sortDesc u j ≤ sortDesc v j := by
    intro j hj
    by_contra! hgt
    have hu : j.1 + 1 ≤ countGe u (sortDesc u j) := (le_sortDesc_iff u j _).1 le_rfl
    have hv : countGe v (sortDesc u j) ≤ j.1 := (sortDesc_lt_iff v j _).1 hgt
    have hge := hle (sortDesc u j) ((hr₀_v.trans (sortDesc_antitone v hj)).trans hgt.le)
    omega
  let diff : Finset (Fin (Fintype.card κ)) :=
    Finset.univ.filter fun j => sortDesc u j ≠ sortDesc v j
  have hdiff_ne : diff.Nonempty := ⟨k, Finset.mem_filter.2 ⟨Finset.mem_univ k, hlt_k.ne⟩⟩
  let j₀ := diff.min' hdiff_ne
  have hj₀_mem : j₀ ∈ diff := Finset.min'_mem diff hdiff_ne
  have hj₀_le_k : j₀ ≤ k :=
    Finset.min'_le diff k (Finset.mem_filter.2 ⟨Finset.mem_univ k, hlt_k.ne⟩)
  refine ⟨j₀, fun i hi => ?_, lt_of_le_of_ne (hle_top j₀ hj₀_le_k) (Finset.mem_filter.1 hj₀_mem).2⟩
  by_contra hne_i
  exact absurd (Finset.min'_le diff i (Finset.mem_filter.2 ⟨Finset.mem_univ i, hne_i⟩))
    (not_le.2 hi)

private theorem sortDesc_lex_lt_of_tail_pres {κ : Type*} [Fintype κ] {u' u : κ → ℝ} (r₀ : ℝ)
    (hpres : ∀ t : ℝ, r₀ ≤ t → ∀ s : κ, t ≤ u' s → t ≤ u s)
    {s₀ : κ} (hge : r₀ ≤ u s₀) (hlt : u' s₀ < r₀) :
    toLex (sortDesc u') < toLex (sortDesc u) := by
  refine sortDesc_lex_lt_of_countGe_lt r₀ ?_ fun t ht => ?_
  · simp only [countGe]
    refine Finset.card_lt_card ⟨fun s hs =>
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hpres r₀ le_rfl s (Finset.mem_filter.1 hs).2⟩,
      fun hsub => absurd (Finset.mem_filter.1
        (hsub (Finset.mem_filter.2 ⟨Finset.mem_univ _, hge⟩))).2 (not_le.2 hlt)⟩
  · simp only [countGe]
    exact Finset.card_le_card fun s hs =>
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hpres t ht s (Finset.mem_filter.1 hs).2⟩

private theorem sortDesc_midpoint_lt_aux {κ : Type*} [Fintype κ] {u v : κ → ℝ} (M : ℝ)
    (hD_le : ∀ s, u s ≠ v s → max (u s) (v s) ≤ M)
    (hs₀ : ∃ s, u s ≠ v s ∧ u s = M) :
    toLex (sortDesc fun s => (u s + v s) / 2) < toLex (sortDesc u) := by
  classical
  set w : κ → ℝ := fun s => (u s + v s) / 2
  have hw_lt : ∀ s, u s ≠ v s → w s < M := fun s hs => by
    have hmax := max_le_iff.1 (hD_le s hs)
    rcases lt_or_gt_of_ne hs with h | h <;> dsimp only [w] <;> linarith [hmax.1, hmax.2]
  rw [sortDesc_lex_lt_iff_countGe]
  refine ⟨M, ?_, ?_⟩
  · obtain ⟨s₀, hs₀ne, hs₀eq⟩ := hs₀
    simp only [countGe]
    refine Finset.card_lt_card ⟨fun s hs => ?_, fun hsub => ?_⟩
    · have hMs : M ≤ w s := (Finset.mem_filter.1 hs).2
      by_cases hne : u s = v s
      · refine Finset.mem_filter.2 ⟨Finset.mem_univ s, ?_⟩
        dsimp only [w] at hMs
        linarith
      · exact absurd hMs (not_le.2 (hw_lt s hne))
    · exact absurd (Finset.mem_filter.1 (hsub (Finset.mem_filter.2
        ⟨Finset.mem_univ s₀, hs₀eq.ge⟩))).2 (not_le.2 (hw_lt s₀ hs₀ne))
  · intro t ht
    simp only [countGe]
    congr 1
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hne : u s = v s
    · simp only [w, hne, add_self_div_two]
    · exact iff_of_false (not_le.2 ((hw_lt s hne).trans ht))
        (not_le.2 ((le_trans (le_max_left _ _) (hD_le s hne)).trans_lt ht))

/-- **Schmeidler's midpoint descent lemma** ([Schmeidler1969]): if `u, v : κ → ℝ` are distinct
vectors with identical descendingly sorted tuples `sortDesc u = sortDesc v`, then their midpoint
`(u + v) / 2` has a lexicographically strictly smaller `sortDesc`. -/
theorem sortDesc_midpoint_lt_of_ne {κ : Type*} [Fintype κ] {u v : κ → ℝ}
    (heq : sortDesc u = sortDesc v) (hne : u ≠ v) :
    toLex (sortDesc fun s => (u s + v s) / 2) < toLex (sortDesc u) := by
  classical
  set D := Finset.univ.filter fun s : κ => u s ≠ v s
  have hD : D.Nonempty := by
    by_contra hne_D
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hne_D
    exact hne (funext fun s => not_not.1 fun h => hne_D (Finset.mem_univ s) h)
  set M := D.sup' hD fun s => max (u s) (v s)
  have hD_le : ∀ s, u s ≠ v s → max (u s) (v s) ≤ M := fun s hs =>
    Finset.le_sup' (fun t => max (u t) (v t)) (Finset.mem_filter.2 ⟨Finset.mem_univ s, hs⟩)
  obtain ⟨s₀, hs₀D, hs₀eq⟩ := Finset.exists_mem_eq_sup' hD fun s => max (u s) (v s)
  have hs₀ne : u s₀ ≠ v s₀ := (Finset.mem_filter.1 hs₀D).2
  rcases le_total (u s₀) (v s₀) with huv | hvu
  · have hvM : v s₀ = M := by
      dsimp only [M]
      rw [hs₀eq, max_eq_right huv]
    have hD_le' : ∀ s, v s ≠ u s → max (v s) (u s) ≤ M := fun s hs => by
      simpa only [max_comm] using hD_le s hs.symm
    have hlt := sortDesc_midpoint_lt_aux M hD_le' ⟨s₀, hs₀ne.symm, hvM⟩
    simpa only [add_comm, heq] using hlt
  · have huM : u s₀ = M := by
      dsimp only [M]
      rw [hs₀eq, max_eq_left hvu]
    exact sortDesc_midpoint_lt_aux M hD_le ⟨s₀, hs₀ne, huM⟩

theorem continuous_sortDesc {κ : Type*} [Fintype κ] (k : Fin (Fintype.card κ)) :
    Continuous fun u : κ → ℝ => sortDesc u k := by
  refine Continuous.finset_sup'_apply _ fun T _ => ?_
  exact Continuous.finset_inf'_apply _ fun s _ => continuous_apply s

private theorem exists_lexMin_of_continuous {X : Type*} [TopologicalSpace X] :
    ∀ (m : ℕ) (f : Fin m → X → ℝ), (∀ i, Continuous (f i)) →
      ∀ (K : Set X), K.Nonempty → IsCompact K →
        ∃ x ∈ K, ∀ y ∈ K, toLex (fun i => f i x) ≤ toLex (fun i => f i y)
  | 0, _, _, K, ⟨x₀, hx₀⟩, _ =>
    ⟨x₀, hx₀, fun _ _ => le_of_eq (congrArg toLex (funext fun i => i.elim0))⟩
  | m + 1, f, hf, K, hKne, hKcomp => by
    obtain ⟨x₀, hx₀K, hx₀min⟩ := hKcomp.exists_isMinOn hKne (hf 0).continuousOn
    set v₀ := f 0 x₀
    set K' := K ∩ {x | f 0 x ≤ v₀}
    have hK'ne : K'.Nonempty := ⟨x₀, hx₀K, show f 0 x₀ ≤ v₀ from le_rfl⟩
    have hK'comp : IsCompact K' := hKcomp.inter_right (isClosed_le (hf 0) continuous_const)
    obtain ⟨x, hxK', hxmin⟩ :=
      exists_lexMin_of_continuous m (fun i => f i.succ) (fun i => hf i.succ) K' hK'ne hK'comp
    refine ⟨x, hxK'.1, fun y hy => ?_⟩
    have hx_eq : f 0 x = v₀ := le_antisymm hxK'.2 (isMinOn_iff.1 hx₀min x hxK'.1)
    have hv₀_le_y : v₀ ≤ f 0 y := isMinOn_iff.1 hx₀min y hy
    rcases lt_or_eq_of_le (hx_eq ▸ hv₀_le_y) with hlt | heq
    · exact le_of_lt ⟨0, fun _ hj => absurd hj (Nat.not_lt_zero _), hlt⟩
    · have hyK' : y ∈ K' := ⟨hy, show f 0 y ≤ v₀ from by linarith⟩
      have hsucc := hxmin y hyK'
      rcases eq_or_lt_of_le hsucc with heq_succ | hlt_succ
      · refine le_of_eq (congrArg toLex (funext fun i => Fin.cases heq (fun j => ?_) i))
        exact congr_fun (congrArg ofLex heq_succ) j
      · obtain ⟨j, hj_eq, hj_lt⟩ := hlt_succ
        refine le_of_lt ⟨j.succ, fun i hi => ?_, hj_lt⟩
        cases i using Fin.cases with
        | zero => exact heq
        | succ k => exact hj_eq k (Fin.succ_lt_succ_iff.1 hi)

end OrderStatistics

namespace CooperativeGame

variable {A : Type*}

/-! ## Symmetries, affine rescaling, and dummy players on `CooperativeGame` -/

/-- Pushforward of a cooperative game along a permutation `π` of the agents: coalition `S`
receives the value of its preimage `S.map π.symm.toEmbedding`. -/
@[expose] def perm (π : Equiv.Perm A) (G : CooperativeGame A) : CooperativeGame A where
  val S := G.val (S.map π.symm.toEmbedding)
  val_empty := by simp

@[simp]
theorem perm_val (π : Equiv.Perm A) (G : CooperativeGame A) (S : Finset A) :
    (G.perm π).val S = G.val (S.map π.symm.toEmbedding) :=
  rfl

/-- Positive affine strategic equivalence rescaling
`(G.mapAffine a b).val S = a * G.val S + ∑ i ∈ S, b i` ([Schmeidler1969]; S-equivalence). -/
@[expose] def mapAffine (G : CooperativeGame A) (a : ℝ) (b : A → ℝ) : CooperativeGame A where
  val S := a * G.val S + ∑ i ∈ S, b i
  val_empty := by simp

@[simp]
theorem mapAffine_val (G : CooperativeGame A) (a : ℝ) (b : A → ℝ) (S : Finset A) :
    (G.mapAffine a b).val S = a * G.val S + ∑ i ∈ S, b i :=
  rfl

/-- Two agents `i, j` are **symmetric** in `G` if adding either one to any coalition avoiding both
produces the same value. -/
@[expose] def AreSymmetric [DecidableEq A] (G : CooperativeGame A) (i j : A) : Prop :=
  ∀ S : Finset A, i ∉ S → j ∉ S → G.val (insert i S) = G.val (insert j S)

/-- Agent `i` is a **dummy agent** in `G` if `G.val (insert i S) = G.val S` whenever `i ∉ S`. -/
@[expose] def IsDummyAgent [DecidableEq A] (G : CooperativeGame A) (i : A) : Prop :=
  ∀ S : Finset A, i ∉ S → G.val (insert i S) = G.val S

theorem IsDummyAgent.val_singleton [DecidableEq A] {G : CooperativeGame A} {i : A}
    (hd : G.IsDummyAgent i) : G.val {i} = 0 := by
  simpa using hd ∅ (Finset.notMem_empty i)

theorem AreSymmetric.perm_swap_eq [DecidableEq A] {G : CooperativeGame A} {i j : A}
    (hsym : G.AreSymmetric i j) : G.perm (Equiv.swap i j) = G := by
  ext S
  simp only [perm_val]
  -- Membership in the swapped coalition is membership of the swapped agent.
  have hmem : ∀ x, x ∈ S.map (Equiv.swap i j).symm.toEmbedding ↔ Equiv.swap i j x ∈ S :=
    fun x => by rw [Finset.mem_map_equiv, Equiv.symm_symm]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · congr 1
    ext x
    rw [hmem, Equiv.swap_apply_def]
    split_ifs <;> simp_all
  · have hij : i ≠ j := fun h => hj (h ▸ hi)
    have hsub : S.map (Equiv.swap i j).symm.toEmbedding = insert j (S.erase i) := by
      ext x
      rw [hmem, Equiv.swap_apply_def]
      split_ifs <;> simp_all [eq_comm]
    rw [hsub, ← hsym (S.erase i) (Finset.notMem_erase i S) fun h => hj (Finset.mem_of_mem_erase h),
      Finset.insert_erase hi]
  · have hij : i ≠ j := fun h => hi (h ▸ hj)
    have hsub : S.map (Equiv.swap i j).symm.toEmbedding = insert i (S.erase j) := by
      ext x
      rw [hmem, Equiv.swap_apply_def]
      split_ifs <;> simp_all [eq_comm]
    rw [hsub, hsym (S.erase j) (fun h => hi (Finset.mem_of_mem_erase h)) (Finset.notMem_erase j S),
      Finset.insert_erase hj]
  · congr 1
    ext x
    rw [hmem, Equiv.swap_apply_def]
    split_ifs <;> simp_all

/-! ## Excesses, preimputations, and imputations -/

/-- **Coalition excess** `e(S, x) := G.val S - ∑ i ∈ S, x i` measuring the dissatisfaction of
coalition `S` at payoff allocation `x` ([Schmeidler1969]). -/
@[expose] def excess (G : CooperativeGame A) (S : Finset A) (x : A → ℝ) : ℝ :=
  G.val S - ∑ i ∈ S, x i

@[simp]
theorem excess_empty (G : CooperativeGame A) (x : A → ℝ) : G.excess ∅ x = 0 := by
  simp [excess]

theorem excess_midpoint (G : CooperativeGame A) (S : Finset A) (x y : A → ℝ) :
    G.excess S ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) = (G.excess S x + G.excess S y) / 2 := by
  simp only [excess, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

theorem inCore_iff_excess [Fintype A] (G : CooperativeGame A) (x : A → ℝ) :
    G.InCore x ↔ (∑ i : A, x i = G.val Finset.univ) ∧ ∀ S : Finset A, G.excess S x ≤ 0 := by
  simp only [InCore, excess, sub_nonpos]

/-- The finite set of nonempty proper coalitions `∅ ⊂neq S ⊂neq Finset.univ`. -/
@[expose] def properNonemptyCoalitions (A : Type*) [Fintype A] [DecidableEq A] :
    Finset (Finset A) :=
  Finset.univ.filter fun S : Finset A => S.Nonempty ∧ S ≠ Finset.univ

theorem mem_properNonemptyCoalitions [Fintype A] [DecidableEq A] {S : Finset A} :
    S ∈ properNonemptyCoalitions A ↔ S.Nonempty ∧ S ≠ Finset.univ := by
  simp [properNonemptyCoalitions]

theorem singleton_mem_properNonemptyCoalitions [Fintype A] [DecidableEq A]
    (hA : 2 ≤ Fintype.card A) (i : A) :
    ({i} : Finset A) ∈ properNonemptyCoalitions A := by
  rw [mem_properNonemptyCoalitions]
  refine ⟨Finset.singleton_nonempty i, fun heq => ?_⟩
  have hc : (Finset.univ : Finset A).card = 1 := by rw [← heq, Finset.card_singleton]
  rw [Finset.card_univ] at hc
  omega

/-- Descendingly sorted vector of all `2 ^ |A|` coalition excesses at allocation `x`. -/
@[expose] noncomputable def sortExcess [Fintype A] (G : CooperativeGame A) (x : A → ℝ) :
    Fin (Fintype.card (Finset A)) → ℝ :=
  sortDesc fun S : Finset A => G.excess S x

/-- Descendingly sorted vector of excesses over proper nonempty coalitions `S ⊊ univ`. -/
@[expose] noncomputable def sortProperExcess [Fintype A] [DecidableEq A]
    (G : CooperativeGame A) (x : A → ℝ) :
    Fin (Fintype.card {S : Finset A // S ∈ properNonemptyCoalitions A}) → ℝ :=
  sortDesc fun S : {S : Finset A // S ∈ properNonemptyCoalitions A} => G.excess S.1 x

/-- Set of **preimputations** (efficient payoff vectors) `∑ i, x i = G.val univ`. -/
@[expose] def preimputations [Fintype A] (G : CooperativeGame A) : Set (A → ℝ) :=
  {x : A → ℝ | ∑ i : A, x i = G.val Finset.univ}

/-- Set of **imputations** (efficient and individually rational payoff vectors). -/
@[expose] def imputations [Fintype A] (G : CooperativeGame A) : Set (A → ℝ) :=
  {x : A → ℝ | ∑ i : A, x i = G.val Finset.univ ∧ ∀ i : A, G.val {i} ≤ x i}

private def cappedPreimputations [Fintype A] (G : CooperativeGame A) (lb : A → ℝ) :
    Set (A → ℝ) :=
  {x : A → ℝ | ∑ i : A, x i = G.val Finset.univ ∧ ∀ i : A, lb i ≤ x i}

theorem preimputations_nonempty [Fintype A] (G : CooperativeGame A) :
    G.preimputations.Nonempty := by
  by_cases hA : Nonempty A
  · let a₀ := Classical.arbitrary A
    classical
    refine ⟨fun i => if i = a₀ then G.val Finset.univ else 0, ?_⟩
    simp [preimputations]
  · have : IsEmpty A := not_nonempty_iff.1 hA
    refine ⟨fun _ => 0, ?_⟩
    simp [preimputations, Finset.univ_eq_empty]

theorem nonempty_imputations_iff [Fintype A] (G : CooperativeGame A) :
    G.imputations.Nonempty ↔ ∑ i : A, G.val {i} ≤ G.val Finset.univ := by
  constructor
  · rintro ⟨x, hsum, hir⟩
    rw [← hsum]
    exact Finset.sum_le_sum fun i _ => hir i
  · intro hle
    by_cases hA : Fintype.card A = 0
    · have : IsEmpty A := Fintype.card_eq_zero_iff.1 hA
      exact ⟨fun _ => 0, by simp [Finset.univ_eq_empty], fun i => IsEmpty.elim ‹_› i⟩
    · have hpos : (0 : ℝ) < Fintype.card A := Nat.cast_pos.2 (Nat.pos_of_ne_zero hA)
      let slack := (G.val Finset.univ - ∑ j : A, G.val {j}) / (Fintype.card A : ℝ)
      have hslack : 0 ≤ slack := div_nonneg (sub_nonneg.2 hle) hpos.le
      refine ⟨fun i => G.val {i} + slack, ?_, fun i => le_add_of_nonneg_right hslack⟩
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp only [slack]
      field_simp [hpos.ne']
      ring

theorem core_subset_imputations [Fintype A] (G : CooperativeGame A) {x : A → ℝ}
    (hx : G.InCore x) : x ∈ G.imputations :=
  ⟨hx.1, fun i => by simpa using hx.2 {i}⟩

private theorem isCompact_cappedPreimputations [Fintype A]
    (G : CooperativeGame A) (lb : A → ℝ) :
    IsCompact (G.cappedPreimputations lb) := by
  classical
  let ub : A → ℝ := fun i => G.val Finset.univ - ∑ j ∈ Finset.univ.erase i, lb j
  have hbox : IsCompact (Set.univ.pi fun i : A => Set.Icc (lb i) (ub i)) :=
    isCompact_univ_pi fun i => ConditionallyCompleteLinearOrder.isCompact_Icc (lb i) (ub i)
  have hclosed : IsClosed (G.cappedPreimputations lb) := by
    have hlb : IsClosed {x : A → ℝ | ∀ i, lb i ≤ x i} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    exact (isClosed_eq (continuous_finsetSum Finset.univ fun i _ => continuous_apply i)
      continuous_const).inter hlb
  refine hbox.of_isClosed_subset hclosed fun x hx i _ => ⟨hx.2 i, ?_⟩
  have hsplit : x i + ∑ j ∈ Finset.univ.erase i, x j = G.val Finset.univ := by
    simpa only [Finset.add_sum_erase _ _ (Finset.mem_univ i)] using hx.1
  have hsum_lb : ∑ j ∈ Finset.univ.erase i, lb j ≤ ∑ j ∈ Finset.univ.erase i, x j :=
    Finset.sum_le_sum fun j _ => hx.2 j
  dsimp only [ub]
  linarith

private theorem convex_cappedPreimputations [Fintype A] (G : CooperativeGame A) (lb : A → ℝ) :
    Convex ℝ (G.cappedPreimputations lb) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, fun i => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx.1, hy.1]
    calc
      a * G.val Finset.univ + b * G.val Finset.univ =
          (a + b) * G.val Finset.univ := (add_mul _ _ _).symm
      _ = G.val Finset.univ := by rw [hab, one_mul]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc
      lb i = (a + b) * lb i := by rw [hab, one_mul]
      _ = a * lb i + b * lb i := add_mul _ _ _
      _ ≤ a * x i + b * y i :=
        add_le_add (mul_le_mul_of_nonneg_left (hx.2 i) ha) (mul_le_mul_of_nonneg_left (hy.2 i) hb)

theorem isCompact_imputations [Fintype A] (G : CooperativeGame A) : IsCompact G.imputations := by
  classical
  exact G.isCompact_cappedPreimputations _

theorem convex_imputations [Fintype A] (G : CooperativeGame A) : Convex ℝ G.imputations :=
  G.convex_cappedPreimputations _

theorem convex_preimputations [Fintype A] (G : CooperativeGame A) : Convex ℝ G.preimputations := by
  intro x hx y hy a b _ _ hab
  have hx' : ∑ i : A, x i = G.val Finset.univ := hx
  have hy' : ∑ i : A, y i = G.val Finset.univ := hy
  simp only [preimputations, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, hx', hy']
  calc
    a * G.val Finset.univ + b * G.val Finset.univ =
        (a + b) * G.val Finset.univ := (add_mul _ _ _).symm
    _ = G.val Finset.univ := by rw [hab, one_mul]

/-! ### Equivalence of full-coalition and proper-nonempty-coalition comparisons -/

theorem excess_univ_of_mem_preimputations [Fintype A] {G : CooperativeGame A} {x : A → ℝ}
    (hx : x ∈ G.preimputations) : G.excess Finset.univ x = 0 := by
  have hx' : ∑ i : A, x i = G.val Finset.univ := hx
  simp only [excess, hx', sub_self]

private theorem countGe_all_eq_proper [Fintype A] [DecidableEq A] (G : CooperativeGame A)
    {z : A → ℝ} (hz : z ∈ G.preimputations) (r : ℝ) :
    countGe (fun S : Finset A => G.excess S z) r =
      countGe (fun S : {S : Finset A // S ∈ properNonemptyCoalitions A} => G.excess S.1 z) r +
        (Finset.univ.filter fun S : Finset A =>
          ¬ (S.Nonempty ∧ S ≠ Finset.univ) ∧ r ≤ 0).card := by
  classical
  have hzero : ∀ S : Finset A, ¬ (S.Nonempty ∧ S ≠ Finset.univ) → G.excess S z = 0 := by
    intro S hP
    by_cases hne : S.Nonempty
    · have hu : S = Finset.univ := not_not.1 fun hn => hP ⟨hne, hn⟩
      rw [hu, excess_univ_of_mem_preimputations hz]
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne, excess_empty]
  have hsplit : (Finset.univ.filter fun S : Finset A => r ≤ G.excess S z) =
      (Finset.univ.filter fun S : Finset A =>
        (S.Nonempty ∧ S ≠ Finset.univ) ∧ r ≤ G.excess S z) ∪
      (Finset.univ.filter fun S : Finset A => ¬ (S.Nonempty ∧ S ≠ Finset.univ) ∧ r ≤ 0) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    by_cases hP : S.Nonempty ∧ S ≠ Finset.univ
    · tauto
    · rw [hzero S hP]; tauto
  have hdisj : Disjoint
      (Finset.univ.filter fun S : Finset A => (S.Nonempty ∧ S ≠ Finset.univ) ∧ r ≤ G.excess S z)
      (Finset.univ.filter fun S : Finset A => ¬ (S.Nonempty ∧ S ≠ Finset.univ) ∧ r ≤ 0) :=
    Finset.disjoint_filter.2 fun _ _ h1 h2 => h2.1 h1.1
  have hbij : (Finset.univ.filter fun S : Finset A =>
        (S.Nonempty ∧ S ≠ Finset.univ) ∧ r ≤ G.excess S z).card =
      countGe (fun S : {S : Finset A // S ∈ properNonemptyCoalitions A} => G.excess S.1 z) r := by
    simp only [countGe]
    exact Finset.card_bij
      (fun S hS => ⟨S, mem_properNonemptyCoalitions.2 (Finset.mem_filter.1 hS).2.1⟩)
      (fun S hS => Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hS).2.2⟩)
      (fun _ _ _ _ h => congrArg Subtype.val h) fun S hS => ⟨S.1, Finset.mem_filter.2
        ⟨Finset.mem_univ _, mem_properNonemptyCoalitions.1 S.2, (Finset.mem_filter.1 hS).2⟩, rfl⟩
  rw [countGe_eq_filter, hsplit, Finset.card_union_of_disjoint hdisj, hbij]

theorem sortExcess_lex_lt_iff_proper [Fintype A] [DecidableEq A] (G : CooperativeGame A)
    {x y : A → ℝ} (hx : x ∈ G.preimputations) (hy : y ∈ G.preimputations) :
    toLex (G.sortExcess x) < toLex (G.sortExcess y) ↔
      toLex (G.sortProperExcess x) < toLex (G.sortProperExcess y) := by
  have hcx := countGe_all_eq_proper G hx
  have hcy := countGe_all_eq_proper G hy
  simp only [sortExcess, sortProperExcess, sortDesc_lex_lt_iff_countGe]
  constructor <;> rintro ⟨r, hlt, heq⟩
  all_goals
    refine ⟨r, ?_, fun t ht => ?_⟩
    · have := hcx r
      have := hcy r
      omega
    · have := hcx t
      have := hcy t
      have := heq t ht
      omega

theorem sortExcess_lex_le_iff_proper [Fintype A] [DecidableEq A] (G : CooperativeGame A)
    {x y : A → ℝ} (hx : x ∈ G.preimputations) (hy : y ∈ G.preimputations) :
    toLex (G.sortExcess x) ≤ toLex (G.sortExcess y) ↔
      toLex (G.sortProperExcess x) ≤ toLex (G.sortProperExcess y) := by
  rw [← not_lt, ← not_lt]
  exact not_congr (G.sortExcess_lex_lt_iff_proper hy hx)

/-! ## Schmeidler's existence and uniqueness theorems -/

section Schmeidler

private theorem lex_zero_le_of_le {m : ℕ} (hm : 0 < m) {u v : Fin m → ℝ}
    (hle : toLex u ≤ toLex v) : u ⟨0, hm⟩ ≤ v ⟨0, hm⟩ := by
  rcases eq_or_lt_of_le hle with heq | hlt
  · exact le_of_eq (congr_fun (congrArg ofLex heq) _)
  · obtain ⟨k, hk_eq, hk_lt⟩ := hlt
    by_cases hk0 : k.1 = 0
    · have hk : k = ⟨0, hm⟩ := Fin.ext hk0
      exact hk ▸ hk_lt.le
    · have hkpos : (⟨0, hm⟩ : Fin m) < k := Fin.mk_lt_mk.2 (Nat.pos_of_ne_zero hk0)
      exact le_of_eq (hk_eq ⟨0, hm⟩ hkpos)

private theorem inCore_of_lex_le_core [Fintype A] {G : CooperativeGame A} {x y : A → ℝ}
    (hx_pre : x ∈ G.preimputations) (hy : G.InCore y)
    (hle : toLex (G.sortExcess x) ≤ toLex (G.sortExcess y)) : G.InCore x := by
  have hlex0 : G.sortExcess x ⟨0, Fintype.card_pos⟩ ≤ G.sortExcess y ⟨0, Fintype.card_pos⟩ :=
    lex_zero_le_of_le Fintype.card_pos hle
  have hy0 : G.sortExcess y ⟨0, Fintype.card_pos⟩ ≤ 0 := by
    obtain ⟨S, hS⟩ := sortDesc_mem_range (fun S => G.excess S y) ⟨0, Fintype.card_pos⟩
    change G.sortExcess y ⟨0, Fintype.card_pos⟩ = G.excess S y at hS
    rw [hS]
    exact ((G.inCore_iff_excess y).1 hy).2 S
  rw [G.inCore_iff_excess]
  refine ⟨hx_pre, fun S => ?_⟩
  have hS_le : G.excess S x ≤ G.sortExcess x ⟨0, Fintype.card_pos⟩ := by
    rw [sortExcess, le_sortDesc_iff]
    classical
    rw [countGe_eq_filter]
    exact Finset.card_pos.2 ⟨S, Finset.mem_filter.2 ⟨Finset.mem_univ S, le_rfl⟩⟩
  exact hS_le.trans (hlex0.trans hy0)

/-- `x` is a lexicographic excess minimizer of `G` over the payoff set `K` ([Schmeidler1969]). -/
@[expose] def IsLexMinimizerOn [Fintype A] (G : CooperativeGame A) (K : Set (A → ℝ))
    (x : A → ℝ) : Prop :=
  x ∈ K ∧ ∀ y ∈ K, toLex (G.sortExcess x) ≤ toLex (G.sortExcess y)

/-- **Schmeidler's existence theorem** ([Schmeidler1969]): every nonempty compact payoff
set `K ⊆ (A → ℝ)` contains at least one lexicographic excess minimizer. -/
theorem exists_isLexMinimizerOn_of_isCompact [Fintype A] (G : CooperativeGame A)
    {K : Set (A → ℝ)} (hKne : K.Nonempty) (hKcomp : IsCompact K) :
    ∃ x : A → ℝ, G.IsLexMinimizerOn K x := by
  have hf : ∀ k : Fin (Fintype.card (Finset A)), Continuous fun x : A → ℝ => G.sortExcess x k := by
    intro k
    refine (continuous_sortDesc k).comp (continuous_pi fun S => ?_)
    exact continuous_const.sub (continuous_finsetSum S fun i _ => continuous_apply i)
  exact exists_lexMin_of_continuous (Fintype.card (Finset A))
    (fun k x => G.sortExcess x k) hf K hKne hKcomp

/-- **Schmeidler's uniqueness theorem** ([Schmeidler1969]): every convex payoff set `K`
has at most one lexicographic excess minimizer. -/
theorem unique_isLexMinimizerOn_of_convex [Fintype A] (G : CooperativeGame A) {K : Set (A → ℝ)}
    (hKconv : Convex ℝ K) {x y : A → ℝ}
    (hx : G.IsLexMinimizerOn K x) (hy : G.IsLexMinimizerOn K y) : x = y := by
  classical
  have hlex : sortDesc (fun S => G.excess S x) = sortDesc (fun S => G.excess S y) :=
    congrArg ofLex (le_antisymm (hx.2 y hy.1) (hy.2 x hx.1))
  by_contra hxy
  have hex_ne : (fun S : Finset A => G.excess S x) ≠ (fun S : Finset A => G.excess S y) := by
    intro heq
    apply hxy
    funext i
    have hi := congrFun heq {i}
    simp only [excess, Finset.sum_singleton] at hi
    linarith
  have hlt := sortDesc_midpoint_lt_of_ne hlex hex_ne
  let m : A → ℝ := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y
  have hmK : m ∈ K := hKconv hx.1 hy.1 (by norm_num) (by norm_num) (by norm_num)
  have hex_m : (fun S : Finset A => G.excess S m) =
      fun S => (G.excess S x + G.excess S y) / 2 :=
    funext fun S => G.excess_midpoint S x y
  have hlt' : toLex (G.sortExcess m) < toLex (G.sortExcess x) := by
    simpa only [sortExcess, hex_m] using hlt
  exact absurd (hx.2 m hmK) (not_le.2 hlt')

theorem existsUnique_isLexMinimizerOn [Fintype A] (G : CooperativeGame A) {K : Set (A → ℝ)}
    (hKne : K.Nonempty) (hKcomp : IsCompact K) (hKconv : Convex ℝ K) :
    ∃! x : A → ℝ, G.IsLexMinimizerOn K x := by
  obtain ⟨x, hx⟩ := G.exists_isLexMinimizerOn_of_isCompact hKne hKcomp
  exact ⟨x, hx, fun y hy => (G.unique_isLexMinimizerOn_of_convex hKconv hx hy).symm⟩

/-- Predicate characterizing the **nucleolus** of `G`: lexicographic excess minimizer over
`G.imputations` ([Schmeidler1969]). -/
@[expose] def IsNucleolus [Fintype A] (G : CooperativeGame A) (x : A → ℝ) : Prop :=
  G.IsLexMinimizerOn G.imputations x

/-- Predicate characterizing the **prenucleolus** of `G`: lexicographic excess minimizer over
all preimputations `G.preimputations`. -/
@[expose] def IsPrenucleolus [Fintype A] (G : CooperativeGame A) (x : A → ℝ) : Prop :=
  G.IsLexMinimizerOn G.preimputations x

/-- **Existence and uniqueness of the nucleolus** ([Schmeidler1969]): whenever the imputation set
is nonempty (`∑ i, G.val {i} ≤ G.val Finset.univ`), `G` admits a unique nucleolus. -/
theorem existsUnique_nucleolus [Fintype A] (G : CooperativeGame A)
    (hle : ∑ i : A, G.val {i} ≤ G.val Finset.univ) :
    ∃! x : A → ℝ, G.IsNucleolus x :=
  G.existsUnique_isLexMinimizerOn ((G.nonempty_imputations_iff).2 hle)
    G.isCompact_imputations G.convex_imputations

/-- The **nucleolus** of a TU cooperative game `G` (returning `0` as a total junk value when the
imputation set is empty). -/
noncomputable def nucleolus [Fintype A] (G : CooperativeGame A) : A → ℝ :=
  if h : ∑ i : A, G.val {i} ≤ G.val Finset.univ then
    (G.existsUnique_nucleolus h).choose
  else 0

theorem nucleolus_isNucleolus [Fintype A] (G : CooperativeGame A)
    (hle : ∑ i : A, G.val {i} ≤ G.val Finset.univ) :
    G.IsNucleolus G.nucleolus := by
  simp only [nucleolus, hle, ↓reduceDIte]
  exact (G.existsUnique_nucleolus hle).choose_spec.1

theorem nucleolus_mem_imputations [Fintype A] (G : CooperativeGame A)
    (hle : ∑ i : A, G.val {i} ≤ G.val Finset.univ) :
    G.nucleolus ∈ G.imputations :=
  (G.nucleolus_isNucleolus hle).1

theorem isNucleolus_iff_eq_nucleolus [Fintype A] (G : CooperativeGame A)
    (hle : ∑ i : A, G.val {i} ≤ G.val Finset.univ) {x : A → ℝ} :
    G.IsNucleolus x ↔ x = G.nucleolus :=
  ⟨fun hx => G.unique_isLexMinimizerOn_of_convex G.convex_imputations hx
      (G.nucleolus_isNucleolus hle),
    fun hx => hx ▸ G.nucleolus_isNucleolus hle⟩

/-- **Core containment of the nucleolus** ([Schmeidler1969]): if `G` has a nonempty
core, its nucleolus lies in the core. -/
theorem IsNucleolus.inCore [Fintype A] {G : CooperativeGame A} {x : A → ℝ}
    (hx : G.IsNucleolus x) (hcore : G.NonemptyCore) : G.InCore x := by
  obtain ⟨y, hy⟩ := hcore
  exact inCore_of_lex_le_core hx.1.1 hy (hx.2 y (G.core_subset_imputations hy))

theorem nucleolus_inCore_of_nonemptyCore [Fintype A] (G : CooperativeGame A)
    (hcore : G.NonemptyCore) : G.InCore G.nucleolus := by
  obtain ⟨y, hy⟩ := hcore
  have hle : ∑ i : A, G.val {i} ≤ G.val Finset.univ :=
    ((G.nonempty_imputations_iff).1 ⟨y, G.core_subset_imputations hy⟩)
  exact (G.nucleolus_isNucleolus hle).inCore ⟨y, hy⟩

/-- **Existence and uniqueness of the prenucleolus** (unconditional over arbitrary TU games `G`):
restricting to a compact lower-bounded box around an arbitrary preimputation `x₀` yields a unique
lexicographic minimizer on all of `G.preimputations`. -/
theorem existsUnique_prenucleolus [Fintype A] (G : CooperativeGame A) :
    ∃! x : A → ℝ, G.IsPrenucleolus x := by
  classical
  obtain ⟨x₀, hx₀⟩ := G.preimputations_nonempty
  set M := (Finset.univ : Finset (Finset A)).sup' Finset.univ_nonempty fun S => G.excess S x₀
  set lb : A → ℝ := fun i => G.val {i} - M
  set K := G.cappedPreimputations lb
  have hx₀K : x₀ ∈ K := by
    refine ⟨hx₀, fun i => ?_⟩
    have hle : G.excess {i} x₀ ≤ M := Finset.le_sup' (fun S => G.excess S x₀) (Finset.mem_univ _)
    simp only [excess, Finset.sum_singleton] at hle
    dsimp only [lb]
    linarith
  obtain ⟨x, hxK, hxmin⟩ :=
    G.exists_isLexMinimizerOn_of_isCompact ⟨x₀, hx₀K⟩ (G.isCompact_cappedPreimputations lb)
  have hx_pre : G.IsPrenucleolus x := by
    refine ⟨hxK.1, fun y hy => ?_⟩
    by_cases hyK : y ∈ K
    · exact hxmin y hyK
    · obtain ⟨i, hi_lt⟩ : ∃ i, y i < lb i := by
        by_contra! h
        exact hyK ⟨hy, h⟩
      have hM_lt_ex : M < G.excess {i} y := by
        simp only [excess, Finset.sum_singleton]
        dsimp only [lb] at hi_lt
        linarith
      have hx_le_x₀ : G.sortExcess x ⟨0, Fintype.card_pos⟩ ≤
          G.sortExcess x₀ ⟨0, Fintype.card_pos⟩ :=
        lex_zero_le_of_le Fintype.card_pos (hxmin x₀ hx₀K)
      have hx₀_le_M : G.sortExcess x₀ ⟨0, Fintype.card_pos⟩ ≤ M := by
        obtain ⟨S, hS⟩ := sortDesc_mem_range (fun S => G.excess S x₀) ⟨0, Fintype.card_pos⟩
        change G.sortExcess x₀ ⟨0, Fintype.card_pos⟩ = G.excess S x₀ at hS
        rw [hS]
        exact Finset.le_sup' (fun S => G.excess S x₀) (Finset.mem_univ S)
      have hM_lt_y : M < G.sortExcess y ⟨0, Fintype.card_pos⟩ := by
        refine hM_lt_ex.trans_le ?_
        rw [sortExcess, le_sortDesc_iff, countGe_eq_filter]
        exact Finset.card_pos.2 ⟨{i}, Finset.mem_filter.2 ⟨Finset.mem_univ _, le_rfl⟩⟩
      exact le_of_lt ⟨0, fun _ hj => absurd hj (Nat.not_lt_zero _),
        hx_le_x₀.trans_lt (hx₀_le_M.trans_lt hM_lt_y)⟩
  exact ⟨x, hx_pre, fun y hy =>
    (G.unique_isLexMinimizerOn_of_convex G.convex_preimputations hx_pre hy).symm⟩

/-- The unique **prenucleolus** of a TU cooperative game `G`. -/
noncomputable def prenucleolus [Fintype A] (G : CooperativeGame A) : A → ℝ :=
  G.existsUnique_prenucleolus.choose

theorem prenucleolus_isPrenucleolus [Fintype A] (G : CooperativeGame A) :
    G.IsPrenucleolus G.prenucleolus :=
  G.existsUnique_prenucleolus.choose_spec.1

theorem prenucleolus_mem_preimputations [Fintype A] (G : CooperativeGame A) :
    G.prenucleolus ∈ G.preimputations :=
  G.prenucleolus_isPrenucleolus.1

theorem isPrenucleolus_iff_eq_prenucleolus [Fintype A] (G : CooperativeGame A) {x : A → ℝ} :
    G.IsPrenucleolus x ↔ x = G.prenucleolus :=
  ⟨fun hx => G.unique_isLexMinimizerOn_of_convex G.convex_preimputations hx
    G.prenucleolus_isPrenucleolus,
    fun hx => hx ▸ G.prenucleolus_isPrenucleolus⟩

theorem prenucleolus_eq_nucleolus_of_mem_imputations [Fintype A] (G : CooperativeGame A)
    (hmem : G.prenucleolus ∈ G.imputations) :
    G.prenucleolus = G.nucleolus := by
  have hle : ∑ i : A, G.val {i} ≤ G.val Finset.univ :=
    (G.nonempty_imputations_iff).1 ⟨G.prenucleolus, hmem⟩
  refine (G.isNucleolus_iff_eq_nucleolus hle).1 ⟨hmem, fun y hy => ?_⟩
  exact G.prenucleolus_isPrenucleolus.2 y hy.1

theorem prenucleolus_eq_nucleolus_of_nonemptyCore [Fintype A] (G : CooperativeGame A)
    (hcore : G.NonemptyCore) :
    G.prenucleolus = G.nucleolus := by
  obtain ⟨y, hy⟩ := hcore
  have hp := G.prenucleolus_isPrenucleolus
  have hmem_core : G.InCore G.prenucleolus :=
    inCore_of_lex_le_core hp.1 hy (hp.2 y hy.1)
  exact G.prenucleolus_eq_nucleolus_of_mem_imputations (G.core_subset_imputations hmem_core)

end Schmeidler

/-! ## Kohlberg's balanced-collection theorem -/

section Kohlberg

open Matrix

/-- A coalition family `ℬ : Finset (Finset A)` is **positively balanced** if there exist strictly
positive weights on `ℬ` (zero outside `ℬ`) whose incidence indicators sum to `1` on every agent
`j : A` ([Kohlberg1971]). -/
@[expose] def IsPositiveBalancedOn [Fintype A] [DecidableEq A]
    (ℬ : Finset (Finset A)) : Prop :=
  ∃ w : Finset A → ℝ, (∀ S ∈ ℬ, 0 < w S) ∧ (∀ S ∉ ℬ, w S = 0) ∧
    ∀ j : A, (∑ S with j ∈ S, w S) = 1

theorem IsPositiveBalancedOn.exists_isBalancedWeights [Fintype A] [DecidableEq A]
    {ℬ : Finset (Finset A)} (hℬ : IsPositiveBalancedOn (A := A) ℬ) :
    ∃ w : Finset A → ℝ, IsBalancedWeights w ∧ (∀ S ∈ ℬ, 0 < w S) ∧ ∀ S ∉ ℬ, w S = 0 := by
  obtain ⟨w, hw_pos, hw_zero, hw_sum⟩ := hℬ
  refine ⟨w, ⟨fun S => ?_, hw_sum⟩, hw_pos, hw_zero⟩
  by_cases hS : S ∈ ℬ
  · exact (hw_pos S hS).le
  · rw [hw_zero S hS]

/-- Imputation balancedness at `x` ([Kohlberg1971]): `ℬ` can be balanced using
strictly positive weights on `ℬ` together with nonnegative singleton multipliers `u j ≥ 0`
supported on agents where individual rationality `G.val {j} = x j` is tight. -/
@[expose] def IsImputationBalancedAt [Fintype A] [DecidableEq A]
    (G : CooperativeGame A) (x : A → ℝ) (ℬ : Finset (Finset A)) : Prop :=
  ∃ (w : Finset A → ℝ) (u : A → ℝ),
    (∀ S ∈ ℬ, 0 < w S) ∧ (∀ S ∉ ℬ, w S = 0) ∧
    (∀ j : A, 0 ≤ u j) ∧ (∀ j : A, G.val {j} < x j → u j = 0) ∧
    ∀ j : A, u j + (∑ S with j ∈ S, w S) = 1

/-- Proper nonempty coalitions whose excess at `x` is at least `t`. -/
@[expose] noncomputable def upperLevel [Fintype A] [DecidableEq A] (G : CooperativeGame A)
    (x : A → ℝ) (t : ℝ) : Finset (Finset A) :=
  (properNonemptyCoalitions A).filter fun S => t ≤ G.excess S x

/-- Excess along the ray `x + ε • d`. -/
private theorem excess_add_smul (G : CooperativeGame A) (S : Finset A) (x d : A → ℝ) (ε : ℝ) :
    G.excess S (x + ε • d) = G.excess S x - ε * ∑ j ∈ S, d j := by
  simp only [excess, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

/-- A weight vanishing off `ℬ` has the same sum over `{S | j ∈ S}` and `{S ∈ ℬ | j ∈ S}`. -/
private theorem sum_filter_mem_eq_of_eq_zero [Fintype A] [DecidableEq A]
    {ℬ : Finset (Finset A)} (j : A) {f : Finset A → ℝ} (hf : ∀ S ∉ ℬ, f S = 0) :
    ∑ S ∈ ℬ with j ∈ S, f S = ∑ S with j ∈ S, f S :=
  Finset.sum_subset
    (fun _ hS => Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hS).2⟩)
    fun S hS hnot => hf S fun h => hnot (Finset.mem_filter.2 ⟨h, (Finset.mem_filter.1 hS).2⟩)

private theorem kohlberg_forward [Fintype A] [DecidableEq A] (G : CooperativeGame A)
    {K : Set (A → ℝ)} {x : A → ℝ} (hx_pre : x ∈ G.preimputations)
    (hx_opt : G.IsLexMinimizerOn K x) (I : Finset A)
    (hmove : ∀ d : A → ℝ, (∑ j : A, d j = 0) → (∀ j ∈ I, 0 ≤ d j) →
      ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → x + ε • d ∈ K)
    (hK_pre : K ⊆ G.preimputations)
    {t : ℝ} (hℬ : (G.upperLevel x t).Nonempty) :
    ∃ (w : Finset A → ℝ) (u : A → ℝ),
      (∀ S ∈ G.upperLevel x t, 0 < w S) ∧ (∀ S ∉ G.upperLevel x t, w S = 0) ∧
      (∀ j : A, 0 ≤ u j) ∧ (∀ j ∉ I, u j = 0) ∧
      ∀ j : A, u j + (∑ S with j ∈ S, w S) = 1 := by
  classical
  set ℬ := G.upperLevel x t
  have hℬ_sub : ∀ S ∈ ℬ, S ∈ properNonemptyCoalitions A := fun S hS =>
    (Finset.mem_filter.1 hS).1
  have h_no_strict : ∀ S₀ ∈ ℬ, ∀ d : A → ℝ,
      (∑ j : A, d j = 0) → (∀ j ∈ I, 0 ≤ d j) → (∀ S ∈ ℬ, 0 ≤ ∑ j ∈ S, d j) →
      ∑ j ∈ S₀, d j ≤ 0 := by
    intro S₀ hS₀ d hd_sum hd_I hd_ℬ
    by_contra hpos_nat
    have hd_pos : 0 < ∑ j ∈ S₀, d j := lt_of_not_ge hpos_nat
    obtain ⟨ε₀, hε₀, hε₀_mem⟩ := hmove d hd_sum hd_I
    set t_min := ℬ.inf' hℬ fun S => G.excess S x
    have ht_min_ge : t ≤ t_min := by
      obtain ⟨S, hS, hSeq⟩ := Finset.exists_mem_eq_inf' hℬ fun S => G.excess S x
      dsimp only [t_min]
      rw [hSeq]
      exact (Finset.mem_filter.1 hS).2
    let rem := properNonemptyCoalitions A \ ℬ
    have hgap : ∃ ε₁ > 0, ∀ S ∈ properNonemptyCoalitions A, S ∉ ℬ →
        ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ → G.excess S (x + ε • d) < t_min := by
      by_cases hrem : rem.Nonempty
      · set T_max := rem.sup' hrem fun S => G.excess S x
        have hT_lt : T_max < t_min := by
          obtain ⟨T, hT, hTeq⟩ := Finset.exists_mem_eq_sup' hrem fun S => G.excess S x
          dsimp only [T_max]
          rw [hTeq]
          have hT' := Finset.mem_sdiff.1 hT
          exact (lt_of_not_ge fun h => hT'.2 (Finset.mem_filter.2 ⟨hT'.1, h⟩)).trans_le ht_min_ge
        let den : ℝ := 2 * (1 + ∑ j : A, |d j|)
        have hS_nn : 0 ≤ ∑ j : A, |d j| := Finset.sum_nonneg fun j _ => abs_nonneg _
        have hden_pos : 0 < den := by dsimp only [den]; linarith
        refine ⟨(t_min - T_max) / den, div_pos (sub_pos.2 hT_lt) hden_pos,
          fun S hSP hSℬ ε hε0 hε1 => ?_⟩
        have hST_le : G.excess S x ≤ T_max :=
          Finset.le_sup' (fun S => G.excess S x) (Finset.mem_sdiff.2 ⟨hSP, hSℬ⟩)
        have hsum_abs : -(∑ j : A, |d j|) ≤ ∑ j ∈ S, d j :=
          neg_le_of_abs_le ((Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
              fun j _ _ => abs_nonneg (d j)))
        have hid : ((t_min - T_max) / den) * (1 + ∑ j : A, |d j|) = (t_min - T_max) / 2 := by
          dsimp only [den]
          field_simp [(by linarith : (0 : ℝ) < 1 + ∑ j : A, |d j|).ne']
        rw [G.excess_add_smul]
        nlinarith [mul_le_mul_of_nonneg_left hsum_abs hε0.le,
          mul_le_mul_of_nonneg_right hε1 (by linarith : (0 : ℝ) ≤ 1 + ∑ j : A, |d j|)]
      · exact ⟨1, zero_lt_one, fun S hSP hSℬ => absurd ⟨S, Finset.mem_sdiff.2 ⟨hSP, hSℬ⟩⟩ hrem⟩
    obtain ⟨ε₁, hε₁, hε₁_lt⟩ := hgap
    let ε := min ε₀ ε₁
    have hε0 : 0 < ε := lt_min hε₀ hε₁
    have hx'K : x + ε • d ∈ K := hε₀_mem ε hε0 (min_le_left _ _)
    have hx'_pre : x + ε • d ∈ G.preimputations := hK_pre hx'K
    let r₀ := G.excess S₀ x
    have hr₀_ge : t_min ≤ r₀ := Finset.inf'_le (fun S => G.excess S x) hS₀
    have hlt_S₀ : G.excess S₀ (x + ε • d) < r₀ := by
      rw [G.excess_add_smul]
      nlinarith [mul_pos hε0 hd_pos]
    let u' : {S : Finset A // S ∈ properNonemptyCoalitions A} → ℝ :=
      fun S => G.excess S.1 (x + ε • d)
    let u : {S : Finset A // S ∈ properNonemptyCoalitions A} → ℝ := fun S => G.excess S.1 x
    have hmem_of_ge : ∀ t' : ℝ, t_min ≤ t' →
        ∀ S : {S : Finset A // S ∈ properNonemptyCoalitions A}, t' ≤ u' S → t' ≤ u S := by
      intro t' ht' S hSt'
      by_cases hSℬ : S.1 ∈ ℬ
      · exact hSt'.trans (show G.excess S.1 (x + ε • d) ≤ G.excess S.1 x by
          rw [G.excess_add_smul]; nlinarith [mul_nonneg hε0.le (hd_ℬ S.1 hSℬ)])
      · exact absurd (ht'.trans hSt') (not_le.2 (hε₁_lt S.1 S.2 hSℬ ε hε0 (min_le_right _ _)))
    have hprop_lt : toLex (G.sortProperExcess (x + ε • d)) < toLex (G.sortProperExcess x) :=
      sortDesc_lex_lt_of_tail_pres r₀ (fun t' ht' => hmem_of_ge t' (hr₀_ge.trans ht'))
        (s₀ := ⟨S₀, hℬ_sub S₀ hS₀⟩) le_rfl hlt_S₀
    have hall_lt : toLex (G.sortExcess (x + ε • d)) < toLex (G.sortExcess x) :=
      (G.sortExcess_lex_lt_iff_proper hx'_pre hx_pre).2 hprop_lt
    exact absurd (hx_opt.2 (x + ε • d) hx'K) (not_le.2 hall_lt)
  -- Apply the affine Farkas lemma for each `S₀ ∈ ℬ` and sum over `S₀ ∈ ℬ`.
  let Row := Unit ⊕ Unit ⊕ {j : A // j ∈ I} ⊕ {S : Finset A // S ∈ ℬ}
  let M : Matrix Row A ℝ := fun r i =>
    Sum.elim (fun _ => 1)
      (Sum.elim (fun _ => -1)
        (Sum.elim (fun j : {j : A // j ∈ I} => if i = j.1 then -1 else 0)
          (fun S : {S : Finset A // S ∈ ℬ} => if i ∈ S.1 then -1 else 0))) r
  have hP : ∃ d : A → ℝ, M *ᵥ d ≤ 0 := ⟨0, by simp⟩
  have hsingle : ∀ S₀ ∈ ℬ, ∃ (c : ℝ) (u : A → ℝ) (w : Finset A → ℝ),
      1 ≤ c ∧ (∀ j, 0 ≤ u j) ∧ (∀ j ∉ I, u j = 0) ∧ (∀ S, 0 ≤ w S) ∧ (∀ S ∉ ℬ, w S = 0) ∧
      ∀ j : A, u j + (∑ S with j ∈ S, w S) + (if j ∈ S₀ then 1 else 0) = c := by
    intro S₀ hS₀
    let obj : A → ℝ := fun j => if j ∈ S₀ then 1 else 0
    have hle_M : ∀ d : A → ℝ, M *ᵥ d ≤ 0 → obj ⬝ᵥ d ≤ 0 := by
      intro d hd
      have h1 : ∑ j : A, d j ≤ 0 := by
        simpa [M, Matrix.mulVec, dotProduct] using hd (.inl ())
      have h2 : -(∑ j : A, d j) ≤ 0 := by
        simpa [M, Matrix.mulVec, dotProduct, Finset.sum_neg_distrib] using hd (.inr (.inl ()))
      have hd_sum : ∑ j : A, d j = 0 := le_antisymm h1 (by linarith)
      have hd_I : ∀ j ∈ I, 0 ≤ d j := fun j hj => by
        simpa only [M, Matrix.mulVec, dotProduct, Sum.elim_inr, Sum.elim_inl, Pi.zero_apply,
          ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
          neg_nonpos] using hd (.inr (.inr (.inl ⟨j, hj⟩)))
      have hd_ℬ : ∀ S ∈ ℬ, 0 ≤ ∑ j ∈ S, d j := by
        intro S hS
        have hrow := hd (.inr (.inr (.inr ⟨S, hS⟩)))
        simp only [M, Matrix.mulVec, dotProduct, Sum.elim_inr, Pi.zero_apply, ite_mul, neg_mul,
          one_mul, zero_mul, ← Finset.sum_filter, Finset.sum_neg_distrib, neg_nonpos] at hrow
        simpa [Finset.filter_mem_eq_inter] using hrow
      have hobj : obj ⬝ᵥ d = ∑ j ∈ S₀, d j := by
        simp [obj, dotProduct]
      rw [hobj]
      exact h_no_strict S₀ hS₀ d hd_sum hd_I hd_ℬ
    obtain ⟨y, hy0, hyM, -⟩ := Matrix.exists_dual_le_of_forall_le M 0 obj 0 hP hle_M
    let c : ℝ := y (.inl ()) - y (.inr (.inl ()))
    let u : A → ℝ := fun j => if hj : j ∈ I then y (.inr (.inr (.inl ⟨j, hj⟩))) else 0
    let w : Finset A → ℝ := fun S => if hS : S ∈ ℬ then y (.inr (.inr (.inr ⟨S, hS⟩))) else 0
    have hu_nn : ∀ j, 0 ≤ u j := fun j => by
      dsimp only [u]; split_ifs <;> [exact hy0 _; exact le_rfl]
    have hw_nn : ∀ S, 0 ≤ w S := fun S => by
      dsimp only [w]; split_ifs <;> [exact hy0 _; exact le_rfl]
    have heq_row : ∀ j : A, u j + (∑ S with j ∈ S, w S) + (if j ∈ S₀ then 1 else 0) = c := by
      intro j
      have hyj := congrFun hyM j
      dsimp only [Row] at hyj
      simp only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, Fintype.sum_unique, M,
        Sum.elim_inl, Sum.elim_inr, mul_one, mul_neg, mul_ite, mul_zero] at hyj
      have hsum_I : ∑ a : {a : A // a ∈ I}, (if j = a.1 then -y (.inr (.inr (.inl a))) else 0) =
          -u j := by
        by_cases hjI : j ∈ I
        · rw [Finset.sum_eq_single ⟨j, hjI⟩
            (fun a _ ha => ite_eq_right fun h => ha (Subtype.ext h.symm))
            fun h => absurd (Finset.mem_univ _) h]
          simp [u, hjI]
        · simp only [u, hjI, ↓reduceDIte, neg_zero]
          exact Finset.sum_eq_zero fun a _ => ite_eq_right fun (h : j = a.1) => hjI (h ▸ a.2)
      have hsum_ℬ : ∑ S : {S : Finset A // S ∈ ℬ},
          (if j ∈ S.1 then -y (.inr (.inr (.inr S))) else 0) = -(∑ S with j ∈ S, w S) := by
        have hid : ∑ S : {S : Finset A // S ∈ ℬ},
            (if j ∈ S.1 then y (.inr (.inr (.inr S))) else 0) = ∑ S with j ∈ S, w S := by
          have hsub_w : ∑ S : {S : Finset A // S ∈ ℬ},
              (if j ∈ S.1 then y (.inr (.inr (.inr S))) else 0) =
              ∑ S : {S : Finset A // S ∈ ℬ}, (if j ∈ S.1 then w S.1 else 0) :=
            Finset.sum_congr rfl fun S _ => by simp [w, S.2]
          rw [hsub_w, ← Finset.sum_subtype ℬ (fun _ => Iff.rfl)
            (fun S => if j ∈ S then w S else 0), ← Finset.sum_filter]
          exact sum_filter_mem_eq_of_eq_zero j fun S hSℬ => by simp [w, hSℬ]
        rw [← hid, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun S _ => by split_ifs <;> simp
      rw [hsum_I, hsum_ℬ] at hyj
      dsimp only [c, obj] at hyj ⊢
      linarith
    have hc1 : 1 ≤ c := by
      have hS₀_ne : S₀.Nonempty := (mem_properNonemptyCoalitions.1 (hℬ_sub S₀ hS₀)).1
      obtain ⟨j₀, hj₀⟩ := hS₀_ne
      have hj₀eq := heq_row j₀
      simp only [hj₀, ↓reduceIte] at hj₀eq
      linarith [hu_nn j₀,
        (Finset.sum_nonneg fun S _ => hw_nn S : 0 ≤ ∑ S with j₀ ∈ S, w S)]
    exact ⟨c, u, w, hc1, hu_nn, fun j hj => by simp [u, hj], hw_nn, fun S hS => by simp [w, hS],
      heq_row⟩
  choose cs us ws hcs hus_nn hus_zero hws_nn hws_zero hrow_eq using hsingle
  let C : ℝ := ∑ S₀ ∈ ℬ.attach, cs S₀.1 S₀.2
  have hC_pos : 0 < C := by
    refine Finset.sum_pos (fun S₀ _ => lt_of_lt_of_le zero_lt_one (hcs S₀.1 S₀.2))
      (Finset.attach_nonempty_iff.2 hℬ)
  let w : Finset A → ℝ := fun S =>
    if hS : S ∈ ℬ then (1 + ∑ S₀ ∈ ℬ.attach, ws S₀.1 S₀.2 S) / C else 0
  let u : A → ℝ := fun j => (∑ S₀ ∈ ℬ.attach, us S₀.1 S₀.2 j) / C
  refine ⟨w, u, fun S hS => ?_, fun S hS => by simp [w, hS],
    fun j => ?_, fun j hj => ?_, fun j => ?_⟩
  · simp only [w, hS, ↓reduceDIte]
    refine div_pos ?_ hC_pos
    have hs : 0 ≤ ∑ S₀ ∈ ℬ.attach, ws S₀.1 S₀.2 S :=
      Finset.sum_nonneg fun S₀ _ => hws_nn S₀.1 S₀.2 S
    linarith
  · exact div_nonneg (Finset.sum_nonneg fun S₀ _ => hus_nn S₀.1 S₀.2 j) hC_pos.le
  · simp only [u]
    rw [Finset.sum_eq_zero fun S₀ _ => hus_zero S₀.1 S₀.2 j hj, zero_div]
  · have hw_sum_j : (∑ S with j ∈ S, w S) =
        ((∑ S₀ ∈ ℬ.attach, (if j ∈ S₀.1 then (1 : ℝ) else 0)) +
          ∑ S₀ ∈ ℬ.attach, ∑ S with j ∈ S, ws S₀.1 S₀.2 S) / C := by
      have hw_eq : (∑ S with j ∈ S, w S) =
          ∑ S ∈ ℬ with j ∈ S, (1 + ∑ S₀ ∈ ℬ.attach, ws S₀.1 S₀.2 S) / C :=
        calc (∑ S with j ∈ S, w S)
            = ∑ S ∈ ℬ with j ∈ S, w S :=
              (sum_filter_mem_eq_of_eq_zero j fun S hSℬ => by simp [w, hSℬ]).symm
          _ = ∑ S ∈ ℬ with j ∈ S, (1 + ∑ S₀ ∈ ℬ.attach, ws S₀.1 S₀.2 S) / C :=
              Finset.sum_congr rfl fun S hS => by simp [w, (Finset.mem_filter.1 hS).1]
      rw [hw_eq]
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
      congr 1
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_attach ℬ (fun S => if j ∈ S then (1 : ℝ) else 0), Finset.sum_filter]
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun S₀ _ => sum_filter_mem_eq_of_eq_zero j (hws_zero S₀.1 S₀.2)
    have hsum_row : (∑ S₀ ∈ ℬ.attach, us S₀.1 S₀.2 j) +
        ((∑ S₀ ∈ ℬ.attach, (if j ∈ S₀.1 then (1 : ℝ) else 0)) +
          ∑ S₀ ∈ ℬ.attach, ∑ S with j ∈ S, ws S₀.1 S₀.2 S) = C := by
      calc
        (∑ S₀ ∈ ℬ.attach, us S₀.1 S₀.2 j) +
            ((∑ S₀ ∈ ℬ.attach, (if j ∈ S₀.1 then (1 : ℝ) else 0)) +
              ∑ S₀ ∈ ℬ.attach, ∑ S with j ∈ S, ws S₀.1 S₀.2 S)
            = ∑ S₀ ∈ ℬ.attach, (us S₀.1 S₀.2 j + (∑ S with j ∈ S, ws S₀.1 S₀.2 S) +
                (if j ∈ S₀.1 then (1 : ℝ) else 0)) := by
              simp only [Finset.sum_add_distrib]
              ring
        _ = ∑ S₀ ∈ ℬ.attach, cs S₀.1 S₀.2 :=
              Finset.sum_congr rfl fun S₀ _ => hrow_eq S₀.1 S₀.2 j
    rw [hw_sum_j]
    dsimp only [u]
    simp only [div_eq_mul_inv, ← add_mul, hsum_row, mul_inv_cancel₀ hC_pos.ne']

private theorem kohlberg_backward [Fintype A] [DecidableEq A] (G : CooperativeGame A)
    {K : Set (A → ℝ)} {x : A → ℝ} (hxK : x ∈ K) (hK_pre : K ⊆ G.preimputations)
    (hbal : ∀ t : ℝ, (G.upperLevel x t).Nonempty →
      ∃ (w : Finset A → ℝ) (u : A → ℝ),
        (∀ S ∈ G.upperLevel x t, 0 < w S) ∧ (∀ S ∉ G.upperLevel x t, w S = 0) ∧
        (∀ j : A, 0 ≤ u j) ∧ (∀ y ∈ K, ∀ j : A, 0 ≤ u j * (y j - x j)) ∧
        ∀ j : A, u j + (∑ S with j ∈ S, w S) = 1) :
    G.IsLexMinimizerOn K x := by
  refine ⟨hxK, fun y hyK => ?_⟩
  have hx_pre : x ∈ G.preimputations := hK_pre hxK
  have hy_pre : y ∈ G.preimputations := hK_pre hyK
  by_cases hA : Fintype.card A < 2
  · have hsub : Subsingleton A := Fintype.card_le_one_iff_subsingleton.1 (Nat.lt_succ_iff.1 hA)
    have hyx : y = x := by
      funext i
      have huniv : (Finset.univ : Finset A) = {i} := by
        ext j
        simp [Subsingleton.elim j i]
      have hx_i : x i = G.val Finset.univ := by simpa [preimputations, huniv] using hx_pre
      have hy_i : y i = G.val Finset.univ := by simpa [preimputations, huniv] using hy_pre
      exact hy_i.trans hx_i.symm
    rw [hyx]
  · have hA2 : 2 ≤ Fintype.card A := le_of_not_gt hA
    let d : A → ℝ := fun j => y j - x j
    have hd_sum : ∑ j : A, d j = 0 := by
      simp only [d, Finset.sum_sub_distrib, sub_eq_zero]
      exact (hy_pre : ∑ j, y j = _).trans (hx_pre : ∑ j, x j = _).symm
    let D : Finset (Finset A) := (properNonemptyCoalitions A).filter fun S => ∑ j ∈ S, d j ≠ 0
    by_cases hD : D.Nonempty
    · let r : ℝ := D.sup' hD fun S => G.excess S x
      obtain ⟨S₀, hS₀D, hS₀eq⟩ := Finset.exists_mem_eq_sup' hD fun S => G.excess S x
      have hS₀_prop : S₀ ∈ properNonemptyCoalitions A := (Finset.mem_filter.1 hS₀D).1
      have hS₀_ne : ∑ j ∈ S₀, d j ≠ 0 := (Finset.mem_filter.1 hS₀D).2
      let ℬ := G.upperLevel x r
      have hS₀ℬ : S₀ ∈ ℬ := Finset.mem_filter.2 ⟨hS₀_prop, hS₀eq.symm.ge⟩
      obtain ⟨w, u, hw_pos, hw_zero, hu_nn, hu_move, hrow⟩ := hbal r ⟨S₀, hS₀ℬ⟩
      have hidentity : (∑ j : A, u j * d j) + ∑ S ∈ ℬ, w S * (∑ j ∈ S, d j) = 0 := by
        have hws_all : ∑ S ∈ ℬ, w S * (∑ j ∈ S, d j) = ∑ S : Finset A, w S * (∑ j ∈ S, d j) :=
          Finset.sum_subset (Finset.subset_univ ℬ) fun S _ hSℬ => by rw [hw_zero S hSℬ, zero_mul]
        have hswap : (∑ S : Finset A, w S * (∑ j ∈ S, d j)) =
            ∑ j : A, (∑ S with j ∈ S, w S) * d j := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_comm' fun S j => by simp
        rw [hws_all, hswap, ← Finset.sum_add_distrib]
        calc
          ∑ j : A, (u j * d j + (∑ S with j ∈ S, w S) * d j)
              = ∑ j : A, (u j + ∑ S with j ∈ S, w S) * d j :=
                Finset.sum_congr rfl fun j _ => by ring
          _ = ∑ j : A, d j := Finset.sum_congr rfl fun j _ => by rw [hrow j, one_mul]
          _ = 0 := hd_sum
      have hu_nonneg : 0 ≤ ∑ j : A, u j * d j :=
        Finset.sum_nonneg fun j _ => hu_move y hyK j
      have hw_nonpos : ∑ S ∈ ℬ, w S * (∑ j ∈ S, d j) ≤ 0 := by linarith
      -- Coalitions with excess above `r = max_D excess` do not change total payoff.
      have hd0_of_lt : ∀ S ∈ properNonemptyCoalitions A, r < G.excess S x → ∑ j ∈ S, d j = 0 :=
        fun S hS hr => not_not.1 fun hne => not_le.2 hr
          (Finset.le_sup' (fun T => G.excess T x) (Finset.mem_filter.2 ⟨hS, hne⟩))
      let ℬeq : Finset (Finset A) := ℬ.filter fun S => G.excess S x = r
      have hℬeq_sum : ∑ S ∈ ℬeq, w S * (∑ j ∈ S, d j) = ∑ S ∈ ℬ, w S * (∑ j ∈ S, d j) := by
        refine Finset.sum_subset (Finset.filter_subset _ _) fun S hSℬ hnot => ?_
        rw [hd0_of_lt S (Finset.mem_filter.1 hSℬ).1 (lt_of_le_of_ne (Finset.mem_filter.1 hSℬ).2
          fun heq => hnot (Finset.mem_filter.2 ⟨hSℬ, heq.symm⟩)), mul_zero]
      have hex_neg : ∃ S' ∈ ℬeq, ∑ j ∈ S', d j < 0 := by
        by_contra! hnone
        have hall_nn : ∀ S ∈ ℬeq, 0 ≤ w S * (∑ j ∈ S, d j) := fun S hS =>
          mul_nonneg (hw_pos S (Finset.mem_filter.1 hS).1).le (hnone S hS)
        exact mul_ne_zero (hw_pos S₀ hS₀ℬ).ne' hS₀_ne ((Finset.sum_eq_zero_iff_of_nonneg hall_nn).1
          (le_antisymm (by rwa [hℬeq_sum]) (Finset.sum_nonneg hall_nn)) S₀
          (Finset.mem_filter.2 ⟨hS₀ℬ, hS₀eq.symm⟩))
      obtain ⟨S', hS'eq, hd_lt⟩ := hex_neg
      have hS'ℬ : S' ∈ ℬ := (Finset.mem_filter.1 hS'eq).1
      have hS'prop : S' ∈ properNonemptyCoalitions A := (Finset.mem_filter.1 hS'ℬ).1
      have hS'ex : G.excess S' x = r := (Finset.mem_filter.1 hS'eq).2
      let r₀ : ℝ := G.excess S' y
      have hr_lt_r₀ : r < r₀ := by
        have hex_diff : G.excess S' y = G.excess S' x - ∑ j ∈ S', d j := by
          simp only [excess, d, Finset.sum_sub_distrib]
          ring
        dsimp only [r₀]
        linarith
      let u_prop : {S : Finset A // S ∈ properNonemptyCoalitions A} → ℝ :=
        fun S => G.excess S.1 x
      let v_prop : {S : Finset A // S ∈ properNonemptyCoalitions A} → ℝ :=
        fun S => G.excess S.1 y
      have hmem_of_ge : ∀ t : ℝ, r₀ ≤ t →
          ∀ S : {S : Finset A // S ∈ properNonemptyCoalitions A},
            t ≤ u_prop S → t ≤ v_prop S := by
        intro t ht S hSt
        have hd0 := hd0_of_lt S.1 S.2 (hr_lt_r₀.trans_le (ht.trans hSt))
        simp only [d, Finset.sum_sub_distrib, sub_eq_zero] at hd0
        simpa only [u_prop, v_prop, excess, hd0] using hSt
      have hprop_lt : toLex (G.sortProperExcess x) < toLex (G.sortProperExcess y) :=
        sortDesc_lex_lt_of_tail_pres r₀ hmem_of_ge (s₀ := ⟨S', hS'prop⟩) le_rfl
          (by dsimp only [u_prop]; rwa [hS'ex])
      exact le_of_lt ((G.sortExcess_lex_lt_iff_proper hx_pre hy_pre).2 hprop_lt)
    · have hyx : y = x := by
        funext i
        have hnotD : ({i} : Finset A) ∉ D := fun hmem => hD ⟨{i}, hmem⟩
        have hsingle : ∑ j ∈ ({i} : Finset A), d j = 0 := not_not.1 fun hne =>
          hnotD (Finset.mem_filter.2 ⟨singleton_mem_properNonemptyCoalitions hA2 i, hne⟩)
        simpa only [Finset.sum_singleton, d, sub_eq_zero] using hsingle
      rw [hyx]

/-- **Kohlberg's balanced-collection theorem for the prenucleolus** ([Kohlberg1971]): a
preimputation `x ∈ G.preimputations` is the prenucleolus of `G` iff every nonempty upper-level
coalition family `G.upperLevel x t` (`t ≤ G.excess S x` for proper nonempty `S`) is positively
balanced. -/
theorem isPrenucleolus_iff_kohlberg [Fintype A] [DecidableEq A] (G : CooperativeGame A)
    {x : A → ℝ} (hx : x ∈ G.preimputations) :
    G.IsPrenucleolus x ↔
      ∀ t : ℝ, (G.upperLevel x t).Nonempty → IsPositiveBalancedOn (G.upperLevel x t) := by
  constructor
  · intro hx_opt t hℬ
    have hmove : ∀ d : A → ℝ, (∑ j : A, d j = 0) → (∀ j ∈ (∅ : Finset A), 0 ≤ d j) →
        ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → x + ε • d ∈ G.preimputations := by
      intro d hd_sum _
      refine ⟨1, zero_lt_one, fun ε _ _ => ?_⟩
      simp only [preimputations, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_add_distrib, ← Finset.mul_sum, hd_sum, mul_zero, add_zero]
      exact hx
    obtain ⟨w, u, hw_pos, hw_zero, _, hu_zero, hrow⟩ :=
      kohlberg_forward G hx hx_opt ∅ hmove (Set.Subset.refl _) hℬ
    refine ⟨w, hw_pos, hw_zero, fun j => ?_⟩
    have hj : u j = 0 := hu_zero j (Finset.notMem_empty j)
    simpa only [hj, zero_add] using hrow j
  · intro hbal
    refine kohlberg_backward G hx (Set.Subset.refl _) fun t hℬ => ?_
    obtain ⟨w, hw_pos, hw_zero, hw_sum⟩ := hbal t hℬ
    exact ⟨w, 0, hw_pos, hw_zero, fun _ => le_rfl, fun _ _ _ => by simp,
      fun j => by simpa only [Pi.zero_apply, zero_add] using hw_sum j⟩

/-- **Kohlberg's balanced-collection theorem for the nucleolus** ([Kohlberg1971]): an imputation
`x ∈ G.imputations` is the nucleolus of `G` iff every nonempty upper-level coalition family
`G.upperLevel x t` is imputation-balanced at `x` (`IsImputationBalancedAt`). -/
theorem isNucleolus_iff_kohlberg [Fintype A] [DecidableEq A] (G : CooperativeGame A)
    {x : A → ℝ} (hx : x ∈ G.imputations) :
    G.IsNucleolus x ↔
      ∀ t : ℝ, (G.upperLevel x t).Nonempty → G.IsImputationBalancedAt x (G.upperLevel x t) := by
  constructor
  · intro hx_opt t hℬ
    let I : Finset A := Finset.univ.filter fun j => x j = G.val {j}
    have hmove : ∀ d : A → ℝ, (∑ j : A, d j = 0) → (∀ j ∈ I, 0 ≤ d j) →
        ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → x + ε • d ∈ G.imputations := by
      intro d hd_sum hd_I
      let J : Finset A := Finset.univ.filter fun j => G.val {j} < x j ∧ d j < 0
      have hε : ∃ ε₀ > 0, ∀ j ∈ J, ε₀ ≤ (x j - G.val {j}) / (-d j) := by
        by_cases hJ : J.Nonempty
        · let ε₀ := J.inf' hJ fun j => (x j - G.val {j}) / (-d j)
          refine ⟨ε₀, ?_, fun j hj => Finset.inf'_le (fun j => (x j - G.val {j}) / (-d j)) hj⟩
          obtain ⟨j, hjJ, hj_eq⟩ := Finset.exists_mem_eq_inf' hJ
            fun j => (x j - G.val {j}) / (-d j)
          dsimp only [ε₀]
          rw [hj_eq]
          exact div_pos (sub_pos.2 (Finset.mem_filter.1 hjJ).2.1)
            (neg_pos.2 (Finset.mem_filter.1 hjJ).2.2)
        · refine ⟨1, zero_lt_one, fun j hj => absurd ⟨j, hj⟩ hJ⟩
      obtain ⟨ε₀, hε₀, hε₀_le⟩ := hε
      refine ⟨ε₀, hε₀, fun ε hε_pos hε_le => ⟨?_, fun j => ?_⟩⟩
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum, hd_sum, mul_zero, add_zero]
        exact hx.1
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        by_cases hdj : 0 ≤ d j
        · exact le_add_of_le_of_nonneg (hx.2 j) (mul_nonneg hε_pos.le hdj)
        · have hdj_lt : d j < 0 := lt_of_not_ge hdj
          have hlt : G.val {j} < x j := lt_of_le_of_ne (hx.2 j) fun heq =>
            hdj (hd_I j (Finset.mem_filter.2 ⟨Finset.mem_univ _, heq.symm⟩))
          have hmul : ε * (-d j) ≤ x j - G.val {j} := (le_div_iff₀ (neg_pos.2 hdj_lt)).1
            (hε_le.trans (hε₀_le j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hlt, hdj_lt⟩)))
          linarith
    obtain ⟨w, u, hw_pos, hw_zero, hu_nn, hu_zero, hrow⟩ :=
      kohlberg_forward G hx.1 hx_opt I hmove (fun _ hy => hy.1) hℬ
    exact ⟨w, u, hw_pos, hw_zero, hu_nn,
      fun j hj => hu_zero j fun hjI => hj.ne' (Finset.mem_filter.1 hjI).2, hrow⟩
  · intro hbal
    refine kohlberg_backward G hx (fun _ hy => hy.1) fun t hℬ => ?_
    obtain ⟨w, u, hw_pos, hw_zero, hu_nn, hu_slack, hrow⟩ := hbal t hℬ
    refine ⟨w, u, hw_pos, hw_zero, hu_nn, fun y hy j => ?_, hrow⟩
    by_cases hlt : G.val {j} < x j
    · rw [hu_slack j hlt, zero_mul]
    · exact mul_nonneg (hu_nn j) (sub_nonneg.2 ((le_of_not_gt hlt).trans (hy.2 j)))

end Kohlberg

/-! ## Axiomatic properties: anonymity, symmetry, covariance, and dummy players -/

section Axioms

private def finsetPermEquiv (π : Equiv.Perm A) : Equiv.Perm (Finset A) where
  toFun S := S.map π.symm.toEmbedding
  invFun S := S.map π.toEmbedding
  left_inv S := by
    ext a
    simp
  right_inv S := by
    ext a
    simp

theorem excess_perm (π : Equiv.Perm A) (G : CooperativeGame A) (S : Finset A) (x : A → ℝ) :
    (G.perm π).excess S (x ∘ π.symm) = G.excess (S.map π.symm.toEmbedding) x := by
  simp only [excess, perm_val, Function.comp_apply, Finset.sum_map, Equiv.coe_toEmbedding]

theorem sortExcess_perm [Fintype A] (π : Equiv.Perm A) (G : CooperativeGame A) (x : A → ℝ) :
    (G.perm π).sortExcess (x ∘ π.symm) = G.sortExcess x := by
  ext k
  have hfun : (fun S : Finset A => (G.perm π).excess S (x ∘ π.symm)) =
      (fun S : Finset A => G.excess S x) ∘ finsetPermEquiv π :=
    funext fun S => excess_perm π G S x
  simp only [sortExcess, hfun]
  simpa using sortDesc_comp_equiv (finsetPermEquiv π) (fun S : Finset A => G.excess S x) k

theorem mem_preimputations_perm_iff [Fintype A] (π : Equiv.Perm A) (G : CooperativeGame A)
    (x : A → ℝ) :
    x ∘ π.symm ∈ (G.perm π).preimputations ↔ x ∈ G.preimputations := by
  simp only [preimputations, Set.mem_ofPred_eq, perm_val, Function.comp_apply]
  have hsum : ∑ i : A, x (π.symm i) = ∑ i : A, x i := Equiv.sum_comp π.symm x
  have hmap : (Finset.univ : Finset A).map π.symm.toEmbedding = Finset.univ := by
    ext i
    simp
  rw [hsum, hmap]

theorem mem_imputations_perm_iff [Fintype A] (π : Equiv.Perm A) (G : CooperativeGame A)
    (x : A → ℝ) :
    x ∘ π.symm ∈ (G.perm π).imputations ↔ x ∈ G.imputations := by
  simp only [imputations, Set.mem_ofPred_eq, perm_val, Finset.map_singleton, Equiv.coe_toEmbedding,
    Function.comp_apply]
  have hsum : ∑ i : A, x (π.symm i) = ∑ i : A, x i := Equiv.sum_comp π.symm x
  have hmap : (Finset.univ : Finset A).map π.symm.toEmbedding = Finset.univ := by
    ext i
    simp
  rw [hsum, hmap]
  exact and_congr Iff.rfl
    ⟨fun h i => by simpa using h (π i), fun h i => h (π.symm i)⟩

private theorem isLexMinimizerOn_perm [Fintype A] (π : Equiv.Perm A) (G : CooperativeGame A)
    {K K' : Set (A → ℝ)} (hK : ∀ z : A → ℝ, z ∘ π.symm ∈ K' ↔ z ∈ K) (x : A → ℝ) :
    (G.perm π).IsLexMinimizerOn K' (x ∘ π.symm) ↔ G.IsLexMinimizerOn K x := by
  constructor
  · intro h
    refine ⟨(hK x).1 h.1, fun y hy => ?_⟩
    have hlex := h.2 (y ∘ π.symm) ((hK y).2 hy)
    rwa [G.sortExcess_perm π x, G.sortExcess_perm π y] at hlex
  · intro h
    refine ⟨(hK x).2 h.1, fun y hy => ?_⟩
    have hcomp : (y ∘ π) ∘ π.symm = y := by ext i; simp
    have hy' : y ∘ π ∈ K := (hK (y ∘ π)).1 (hcomp.symm ▸ hy)
    have hlex := h.2 (y ∘ π) hy'
    have hpy : (G.perm π).sortExcess y = G.sortExcess (y ∘ π) := by
      have := G.sortExcess_perm π (y ∘ π)
      rwa [hcomp] at this
    rwa [G.sortExcess_perm π x, hpy]

theorem isPrenucleolus_perm [Fintype A] (π : Equiv.Perm A) (G : CooperativeGame A) (x : A → ℝ) :
    (G.perm π).IsPrenucleolus (x ∘ π.symm) ↔ G.IsPrenucleolus x :=
  isLexMinimizerOn_perm π G (fun z => G.mem_preimputations_perm_iff π z) x

theorem isNucleolus_perm [Fintype A] (π : Equiv.Perm A) (G : CooperativeGame A) (x : A → ℝ) :
    (G.perm π).IsNucleolus (x ∘ π.symm) ↔ G.IsNucleolus x :=
  isLexMinimizerOn_perm π G (fun z => G.mem_imputations_perm_iff π z) x

/-- **Anonymity (equivariance) of the prenucleolus** ([Schmeidler1969]): permuting agent names by
`π` permutes the prenucleolus allocation accordingly. -/
theorem prenucleolus_perm [Fintype A] (π : Equiv.Perm A) (G : CooperativeGame A) :
    (G.perm π).prenucleolus = G.prenucleolus ∘ π.symm :=
  ((G.perm π).isPrenucleolus_iff_eq_prenucleolus.1
    ((G.isPrenucleolus_perm π G.prenucleolus).2 G.prenucleolus_isPrenucleolus)).symm

/-- **Anonymity (equivariance) of the nucleolus** ([Schmeidler1969]). -/
theorem nucleolus_perm [Fintype A] (π : Equiv.Perm A) (G : CooperativeGame A)
    (hle : ∑ i : A, G.val {i} ≤ G.val Finset.univ) :
    (G.perm π).nucleolus = G.nucleolus ∘ π.symm := by
  have hle' : ∑ i : A, (G.perm π).val {i} ≤ (G.perm π).val Finset.univ := by
    simp only [perm_val, Finset.map_singleton, Equiv.coe_toEmbedding]
    rw [Equiv.sum_comp π.symm fun i => G.val {i}]
    have hmap : (Finset.univ : Finset A).map π.symm.toEmbedding = Finset.univ := by
      ext i
      simp
    rwa [hmap]
  exact (((G.perm π).isNucleolus_iff_eq_nucleolus hle').1
    ((G.isNucleolus_perm π G.nucleolus).2 (G.nucleolus_isNucleolus hle))).symm

/-- **Symmetry of the prenucleolus**: symmetric agents `i, j` receive identical payoffs in
`G.prenucleolus`. -/
theorem prenucleolus_eq_of_areSymmetric [Fintype A] [DecidableEq A] {G : CooperativeGame A}
    {i j : A} (hsym : G.AreSymmetric i j) : G.prenucleolus i = G.prenucleolus j := by
  have hperm := G.prenucleolus_perm (Equiv.swap i j)
  rw [hsym.perm_swap_eq] at hperm
  have hi := congr_fun hperm i
  simpa only [Function.comp_apply, Equiv.symm_swap, Equiv.swap_apply_left] using hi

/-- **Symmetry of the nucleolus**: symmetric agents `i, j` receive identical payoffs in
`G.nucleolus`. -/
theorem nucleolus_eq_of_areSymmetric [Fintype A] [DecidableEq A] {G : CooperativeGame A}
    {i j : A} (hsym : G.AreSymmetric i j) : G.nucleolus i = G.nucleolus j := by
  by_cases hle : ∑ k : A, G.val {k} ≤ G.val Finset.univ
  · have hperm := G.nucleolus_perm (Equiv.swap i j) hle
    rw [hsym.perm_swap_eq] at hperm
    have hi := congr_fun hperm i
    simpa only [Function.comp_apply, Equiv.symm_swap, Equiv.swap_apply_left] using hi
  · simp [nucleolus, hle]

theorem excess_mapAffine (G : CooperativeGame A) (a : ℝ) (b : A → ℝ) (S : Finset A) (x : A → ℝ) :
    (G.mapAffine a b).excess S (fun i => a * x i + b i) = a * G.excess S x := by
  simp only [excess, mapAffine_val, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem sortExcess_mapAffine [Fintype A] (G : CooperativeGame A) {a : ℝ} (ha : 0 ≤ a)
    (b : A → ℝ) (x : A → ℝ) :
    (G.mapAffine a b).sortExcess (fun i => a * x i + b i) = fun k => a * G.sortExcess x k := by
  ext k
  have hfun : (fun S : Finset A => (G.mapAffine a b).excess S (fun i => a * x i + b i)) =
      fun S => a * G.excess S x + 0 :=
    funext fun S => by rw [G.excess_mapAffine a b S x, add_zero]
  simp only [sortExcess, hfun]
  simpa only [add_zero] using sortDesc_scale_add (fun S : Finset A => G.excess S x) ha 0 k

private theorem lex_scale_le_iff {m : ℕ} {a : ℝ} (ha : 0 < a) (u v : Fin m → ℝ) :
    toLex (fun k => a * u k) ≤ toLex (fun k => a * v k) ↔ toLex u ≤ toLex v := by
  have hlt : ∀ p q : Fin m → ℝ,
      (toLex (fun k => a * p k) < toLex (fun k => a * q k)) ↔ (toLex p < toLex q) := by
    intro p q
    constructor <;> rintro ⟨k, hk_eq, hk_lt⟩ <;> refine ⟨k, fun j hj => ?_, ?_⟩
    · exact mul_left_cancel₀ ha.ne' (hk_eq j hj)
    · exact lt_of_mul_lt_mul_left hk_lt ha.le
    · exact congrArg (a * ·) (hk_eq j hj)
    · exact mul_lt_mul_of_pos_left hk_lt ha
  rw [← not_lt, ← not_lt]
  exact not_congr (hlt v u)

private theorem mem_preimputations_mapAffine_iff [Fintype A] (G : CooperativeGame A)
    {a : ℝ} (ha : 0 < a) (b : A → ℝ) (z : A → ℝ) :
    (fun i => a * z i + b i) ∈ (G.mapAffine a b).preimputations ↔ z ∈ G.preimputations := by
  simp only [preimputations, Set.mem_ofPred_eq, mapAffine_val, Finset.sum_add_distrib,
    ← Finset.mul_sum, add_left_inj]
  exact ⟨fun h => mul_left_cancel₀ ha.ne' h, fun h => by rw [h]⟩

private theorem mem_imputations_mapAffine_iff [Fintype A] (G : CooperativeGame A)
    {a : ℝ} (ha : 0 < a) (b : A → ℝ) (z : A → ℝ) :
    (fun i => a * z i + b i) ∈ (G.mapAffine a b).imputations ↔ z ∈ G.imputations := by
  simp only [imputations, Set.mem_ofPred_eq, mapAffine_val, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_singleton, add_left_inj, add_le_add_iff_right]
  exact and_congr ⟨fun h => mul_left_cancel₀ ha.ne' h, fun h => by rw [h]⟩
    (forall_congr' fun i => mul_le_mul_iff_right₀ ha)

private theorem isLexMinimizerOn_mapAffine [Fintype A] (G : CooperativeGame A) {a : ℝ}
    (ha : 0 < a) (b : A → ℝ) {K K' : Set (A → ℝ)}
    (hK : ∀ z : A → ℝ, (fun i => a * z i + b i) ∈ K' ↔ z ∈ K) (x : A → ℝ) :
    (G.mapAffine a b).IsLexMinimizerOn K' (fun i => a * x i + b i) ↔ G.IsLexMinimizerOn K x := by
  constructor
  · intro h
    refine ⟨(hK x).1 h.1, fun y hy => ?_⟩
    have hlex := h.2 (fun i => a * y i + b i) ((hK y).2 hy)
    rwa [G.sortExcess_mapAffine ha.le b x, G.sortExcess_mapAffine ha.le b y,
      lex_scale_le_iff ha] at hlex
  · intro h
    refine ⟨(hK x).2 h.1, fun y hy => ?_⟩
    let y' : A → ℝ := fun i => a⁻¹ * (y i - b i)
    have hy_eq : y = fun i => a * y' i + b i := by
      funext i
      dsimp only [y']
      field_simp [ha.ne']
      ring
    have hy' : y' ∈ K := (hK y').1 (hy_eq ▸ hy)
    rw [hy_eq, G.sortExcess_mapAffine ha.le b x, G.sortExcess_mapAffine ha.le b y',
      lex_scale_le_iff ha]
    exact h.2 y' hy'

theorem isPrenucleolus_mapAffine [Fintype A] (G : CooperativeGame A) {a : ℝ} (ha : 0 < a)
    (b : A → ℝ) (x : A → ℝ) :
    (G.mapAffine a b).IsPrenucleolus (fun i => a * x i + b i) ↔ G.IsPrenucleolus x :=
  isLexMinimizerOn_mapAffine G ha b (fun z => G.mem_preimputations_mapAffine_iff ha b z) x

theorem isNucleolus_mapAffine [Fintype A] (G : CooperativeGame A) {a : ℝ} (ha : 0 < a)
    (b : A → ℝ) (x : A → ℝ) :
    (G.mapAffine a b).IsNucleolus (fun i => a * x i + b i) ↔ G.IsNucleolus x :=
  isLexMinimizerOn_mapAffine G ha b (fun z => G.mem_imputations_mapAffine_iff ha b z) x

/-- **Covariance (S-equivalence) of the prenucleolus** ([Schmeidler1969]): positive affine
rescaling `a * v(S) + ∑_{i ∈ S} b_i` (`0 < a`) rescales the prenucleolus by `a * x_i + b_i`. -/
theorem prenucleolus_mapAffine [Fintype A] (G : CooperativeGame A) {a : ℝ} (ha : 0 < a)
    (b : A → ℝ) :
    (G.mapAffine a b).prenucleolus = fun i => a * G.prenucleolus i + b i :=
  ((G.mapAffine a b).isPrenucleolus_iff_eq_prenucleolus.1
    ((G.isPrenucleolus_mapAffine ha b G.prenucleolus).2 G.prenucleolus_isPrenucleolus)).symm

/-- **Covariance (S-equivalence) of the nucleolus** ([Schmeidler1969]). -/
theorem nucleolus_mapAffine [Fintype A] (G : CooperativeGame A) {a : ℝ} (ha : 0 < a)
    (b : A → ℝ) (hle : ∑ i : A, G.val {i} ≤ G.val Finset.univ) :
    (G.mapAffine a b).nucleolus = fun i => a * G.nucleolus i + b i := by
  have hle' : ∑ i : A, (G.mapAffine a b).val {i} ≤ (G.mapAffine a b).val Finset.univ := by
    simp only [mapAffine_val, Finset.sum_singleton, Finset.sum_add_distrib, ← Finset.mul_sum,
      add_le_add_iff_right]
    exact mul_le_mul_of_nonneg_left hle ha.le
  exact (((G.mapAffine a b).isNucleolus_iff_eq_nucleolus hle').1
    ((G.isNucleolus_mapAffine ha b G.nucleolus).2 (G.nucleolus_isNucleolus hle))).symm

private theorem erase_univ_mem_without [Fintype A] [DecidableEq A]
    (hA2 : 2 ≤ Fintype.card A) (i : A) :
    Finset.univ.erase i ∈ (properNonemptyCoalitions A).filter fun S => i ∉ S := by
  refine Finset.mem_filter.2 ⟨mem_properNonemptyCoalitions.2 ⟨?_, ?_⟩, Finset.notMem_erase i _⟩
  · refine Finset.card_pos.1 ?_
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
    omega
  · exact fun heq => Finset.notMem_erase i Finset.univ (heq.symm ▸ Finset.mem_univ i)

private theorem dummy_eq_zero_of_card_lt_two [Fintype A] [DecidableEq A] {G : CooperativeGame A}
    {i : A} (hd : G.IsDummyAgent i) (hA : Fintype.card A < 2) {x : A → ℝ}
    (hx_pre : x ∈ G.preimputations) : x i = 0 := by
  have hsub : Subsingleton A := Fintype.card_le_one_iff_subsingleton.1 (Nat.lt_succ_iff.1 hA)
  have huniv : (Finset.univ : Finset A) = {i} := by
    ext j
    simp [Subsingleton.elim j i]
  have hsum : ∑ j : A, x j = G.val Finset.univ := hx_pre
  have hx_eff : x i = G.val {i} := by
    simpa only [huniv, Finset.sum_singleton] using hsum
  exact hx_eff.trans hd.val_singleton

private theorem dummy_excess_erase_univ [Fintype A] [DecidableEq A] {G : CooperativeGame A}
    {i : A} (hd : G.IsDummyAgent i) {x : A → ℝ} (hx_pre : x ∈ G.preimputations) :
    G.excess (Finset.univ.erase i) x = x i := by
  have huniv_eq : insert i (Finset.univ.erase i) = Finset.univ :=
    Finset.insert_erase (Finset.mem_univ i)
  have hval_er : G.val (Finset.univ.erase i) = G.val Finset.univ := by
    rw [← hd (Finset.univ.erase i) (Finset.notMem_erase i _), huniv_eq]
  have hx_eff : ∑ j : A, x j = G.val Finset.univ := hx_pre
  have hsum_er : x i + ∑ j ∈ Finset.univ.erase i, x j = G.val Finset.univ := by
    simpa only [Finset.add_sum_erase _ _ (Finset.mem_univ i)] using hx_eff
  simp only [excess, hval_er]
  linarith

private theorem dummy_pos_contradiction [Fintype A] [DecidableEq A] {G : CooperativeGame A}
    {i : A} (hd : G.IsDummyAgent i) (hA2 : 2 ≤ Fintype.card A) {x : A → ℝ}
    (hx_pre : x ∈ G.preimputations) (hxi_pos : 0 < x i)
    (hbal : ∃ (w : Finset A → ℝ) (u : A → ℝ),
      (∀ S ∉ G.upperLevel x
        (((properNonemptyCoalitions A).filter fun S => i ∉ S).sup'
          ⟨Finset.univ.erase i, erase_univ_mem_without hA2 i⟩
          fun S => G.excess S x), w S = 0) ∧
      u i = 0 ∧ u i + (∑ S with i ∈ S, w S) = 1) : False := by
  let P_without := (properNonemptyCoalitions A).filter fun S => i ∉ S
  have hPw : P_without.Nonempty := ⟨Finset.univ.erase i, erase_univ_mem_without hA2 i⟩
  set M := P_without.sup' hPw fun S => G.excess S x
  have hlt_M : ∀ T ∈ properNonemptyCoalitions A, i ∈ T → G.excess T x < M := by
    intro T hT hiT
    by_cases hsingle : T = {i}
    · have hex_er_le : G.excess (Finset.univ.erase i) x ≤ M :=
        Finset.le_sup' (fun S => G.excess S x) (erase_univ_mem_without hA2 i)
      have hex_er : G.excess (Finset.univ.erase i) x = x i :=
        dummy_excess_erase_univ hd hx_pre
      have hex_single : G.excess T x = -x i := by
        simp only [excess, hsingle, Finset.sum_singleton, hd.val_singleton, zero_sub]
      linarith
    · let S := T.erase i
      have hS_ne : S.Nonempty :=
        (Finset.erase_nonempty hiT).2 ((Finset.nontrivial_iff_ne_singleton hiT).2 hsingle)
      have hS_Pw : S ∈ P_without := Finset.mem_filter.2
        ⟨mem_properNonemptyCoalitions.2
          ⟨hS_ne, fun heq => Finset.notMem_erase i T (show i ∈ S from heq ▸ Finset.mem_univ i)⟩,
          Finset.notMem_erase i T⟩
      have hS_le : G.excess S x ≤ M := Finset.le_sup' (fun S => G.excess S x) hS_Pw
      have hex_T : G.excess T x = G.excess S x - x i := by
        conv_lhs => rw [← Finset.insert_erase hiT]
        simp only [S, excess, hd (T.erase i) (Finset.notMem_erase i T),
          Finset.sum_insert (Finset.notMem_erase i T)]
        ring
      linarith
  obtain ⟨w, u, hw_zero, hu0, hrow⟩ := hbal
  have hsum_zero : ∑ S with i ∈ S, w S = 0 :=
    Finset.sum_eq_zero fun S hS => hw_zero S fun hSℬ =>
      (hlt_M S (Finset.mem_filter.1 hSℬ).1 (Finset.mem_filter.1 hS).2).not_ge
        (Finset.mem_filter.1 hSℬ).2
  linarith

/-- **Dummy-player property of the nucleolus**: a dummy agent receives zero payoff in
`G.nucleolus` (assuming imputations exist). -/
theorem nucleolus_isDummyAgent [Fintype A] [DecidableEq A] {G : CooperativeGame A} {i : A}
    (hle : ∑ k : A, G.val {k} ≤ G.val Finset.univ) (hd : G.IsDummyAgent i) :
    G.nucleolus i = 0 := by
  let x := G.nucleolus
  have hx : G.IsNucleolus x := G.nucleolus_isNucleolus hle
  by_cases hA : Fintype.card A < 2
  · exact dummy_eq_zero_of_card_lt_two hd hA hx.1.1
  · have hA2 : 2 ≤ Fintype.card A := le_of_not_gt hA
    have hir : 0 ≤ x i := by
      simpa only [hd.val_singleton] using hx.1.2 i
    by_contra hne0
    have hxi_pos : 0 < x i := lt_of_le_of_ne hir (Ne.symm hne0)
    have hkohl := (G.isNucleolus_iff_kohlberg hx.1).1 hx
    let P_without := (properNonemptyCoalitions A).filter fun S => i ∉ S
    have hPw : P_without.Nonempty := ⟨Finset.univ.erase i, erase_univ_mem_without hA2 i⟩
    obtain ⟨S₀, hS₀Pw, hS₀eq⟩ := Finset.exists_mem_eq_sup' hPw fun S => G.excess S x
    set M := P_without.sup' hPw fun S => G.excess S x
    have hℬne : (G.upperLevel x M).Nonempty :=
      ⟨S₀, Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hS₀Pw).1, hS₀eq.symm.ge⟩⟩
    obtain ⟨w, u, _, hw_zero, _, hu_slack, hrow⟩ := hkohl M hℬne
    have hu0 : u i = 0 := hu_slack i (by simpa only [hd.val_singleton] using hxi_pos)
    exact dummy_pos_contradiction hd hA2 hx.1.1 hxi_pos ⟨w, u, hw_zero, hu0, hrow i⟩

/-- **Dummy-player property of the prenucleolus**: a dummy agent receives zero payoff in
`G.prenucleolus`. -/
theorem prenucleolus_isDummyAgent [Fintype A] [DecidableEq A] {G : CooperativeGame A} {i : A}
    (hd : G.IsDummyAgent i) : G.prenucleolus i = 0 := by
  let x := G.prenucleolus
  have hx : G.IsPrenucleolus x := G.prenucleolus_isPrenucleolus
  by_cases hA : Fintype.card A < 2
  · exact dummy_eq_zero_of_card_lt_two hd hA hx.1
  · have hA2 : 2 ≤ Fintype.card A := le_of_not_gt hA
    have hkohl := (G.isPrenucleolus_iff_kohlberg hx.1).1 hx
    let P_without := (properNonemptyCoalitions A).filter fun S => i ∉ S
    have hPw : P_without.Nonempty := ⟨Finset.univ.erase i, erase_univ_mem_without hA2 i⟩
    rcases lt_trichotomy (x i) 0 with hxi_neg | hxi_zero | hxi_pos
    · obtain ⟨S₀, hS₀Pw, hS₀eq⟩ := Finset.exists_mem_eq_sup' hPw fun S => G.excess S x
      set M := P_without.sup' hPw fun S => G.excess S x
      have hi_not_S₀ : i ∉ S₀ := (Finset.mem_filter.1 hS₀Pw).2
      have hex_above : ∃ T₀ ∈ properNonemptyCoalitions A, M < G.excess T₀ x := by
        by_cases hfull : insert i S₀ = Finset.univ
        · refine ⟨{i}, singleton_mem_properNonemptyCoalitions hA2 i, ?_⟩
          have hS₀_er : S₀ = Finset.univ.erase i := by
            rw [← hfull, Finset.erase_insert hi_not_S₀]
          have hex_S₀ : G.excess S₀ x = x i := hS₀_er ▸ dummy_excess_erase_univ hd hx.1
          have hex_single : G.excess ({i} : Finset A) x = -x i := by
            simp only [excess, Finset.sum_singleton, hd.val_singleton, zero_sub]
          linarith
        · refine ⟨insert i S₀, mem_properNonemptyCoalitions.2
            ⟨Finset.insert_nonempty i S₀, hfull⟩, ?_⟩
          have hex_ins : G.excess (insert i S₀) x = G.excess S₀ x - x i := by
            simp only [excess, hd S₀ hi_not_S₀, Finset.sum_insert hi_not_S₀]
            ring
          linarith
      obtain ⟨T₀, hT₀prop, hM_lt_T₀⟩ := hex_above
      set t := G.excess T₀ x
      have hℬne : (G.upperLevel x t).Nonempty := ⟨T₀, Finset.mem_filter.2 ⟨hT₀prop, le_rfl⟩⟩
      obtain ⟨w, hw_pos, hw_zero, hw_sum⟩ := hkohl t hℬne
      have hi_mem_all : ∀ S ∈ G.upperLevel x t, i ∈ S := fun S hSℬ => by
        by_contra hiS
        exact hM_lt_T₀.not_ge ((Finset.mem_filter.1 hSℬ).2.trans (Finset.le_sup'
          (fun S => G.excess S x) (Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hSℬ).1, hiS⟩)))
      have hsum_all : (∑ S : Finset A, w S) = 1 := by
        rw [← hw_sum i]
        refine (Finset.sum_subset (Finset.filter_subset _ _) fun S _ hnot => ?_).symm
        exact hw_zero S fun hSℬ =>
          hnot (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi_mem_all S hSℬ⟩)
      obtain ⟨j, hjT₀⟩ : ∃ j : A, j ∉ T₀ := by
        by_contra! hall
        exact (mem_properNonemptyCoalitions.1 hT₀prop).2 (Finset.eq_univ_iff_forall.2 hall)
      have hw_nn : ∀ S : Finset A, 0 ≤ w S := fun S =>
        (em _).elim (fun hS => (hw_pos S hS).le) fun hS => (hw_zero S hS).ge
      have hmiss_zero : (∑ S with j ∉ S, w S) = 0 := by
        linarith [hw_sum j, Finset.sum_filter_add_sum_filter_not Finset.univ (fun S => j ∈ S) w]
      have hwT₀_zero : w T₀ = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun S _ => hw_nn S).1
        hmiss_zero T₀ (Finset.mem_filter.2 ⟨Finset.mem_univ T₀, hjT₀⟩)
      exact absurd (hw_pos T₀ (Finset.mem_filter.2 ⟨hT₀prop, le_rfl⟩)) (by linarith)
    · exact hxi_zero
    · obtain ⟨S₀, hS₀Pw, hS₀eq⟩ := Finset.exists_mem_eq_sup' hPw fun S => G.excess S x
      set M := P_without.sup' hPw fun S => G.excess S x
      have hℬne : (G.upperLevel x M).Nonempty :=
        ⟨S₀, Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hS₀Pw).1, hS₀eq.symm.ge⟩⟩
      obtain ⟨w, _, hw_zero, hw_sum⟩ := hkohl M hℬne
      exact False.elim (dummy_pos_contradiction hd hA2 hx.1 hxi_pos
        ⟨w, 0, hw_zero, rfl, by simpa using hw_sum i⟩)

end Axioms

end CooperativeGame

namespace CostSharingGame

variable {A : Type*}

/-- The **nucleolus** cost allocation of a cost-sharing game `C`, defined via the dual
cooperative surplus game `C.toCooperativeGame` (`α = -x`) whenever imputations exist
(`C.cost Finset.univ ≤ ∑ i, C.cost {i}`). -/
noncomputable def nucleolus [Fintype A] (C : CostSharingGame A) : A → ℝ :=
  -C.toCooperativeGame.nucleolus

theorem nucleolus_eq [Fintype A] (C : CostSharingGame A) :
    C.nucleolus = -C.toCooperativeGame.nucleolus := by
  unfold nucleolus
  rfl

/-- The **prenucleolus** cost allocation of a cost-sharing game `C`. -/
noncomputable def prenucleolus [Fintype A] (C : CostSharingGame A) : A → ℝ :=
  -C.toCooperativeGame.prenucleolus

theorem prenucleolus_eq [Fintype A] (C : CostSharingGame A) :
    C.prenucleolus = -C.toCooperativeGame.prenucleolus := by
  unfold prenucleolus
  rfl

theorem sum_nucleolus [Fintype A] (C : CostSharingGame A)
    (hle : C.cost Finset.univ ≤ ∑ i : A, C.cost {i}) :
    ∑ i : A, C.nucleolus i = C.cost Finset.univ := by
  have hle' : ∑ i : A, C.toCooperativeGame.val {i} ≤ C.toCooperativeGame.val Finset.univ := by
    simp only [toCooperativeGame_val, Finset.sum_neg_distrib, neg_le_neg_iff]
    exact hle
  have hsum : ∑ i : A, C.toCooperativeGame.nucleolus i = C.toCooperativeGame.val Finset.univ :=
    (C.toCooperativeGame.nucleolus_mem_imputations hle').1
  rw [C.toCooperativeGame_val Finset.univ] at hsum
  simp only [nucleolus, Pi.neg_apply, Finset.sum_neg_distrib, hsum, neg_neg]

theorem nucleolus_le_singleton [Fintype A] (C : CostSharingGame A)
    (hle : C.cost Finset.univ ≤ ∑ i : A, C.cost {i}) (i : A) :
    C.nucleolus i ≤ C.cost {i} := by
  have hle' : ∑ j : A, C.toCooperativeGame.val {j} ≤ C.toCooperativeGame.val Finset.univ := by
    simp only [toCooperativeGame_val, Finset.sum_neg_distrib, neg_le_neg_iff]
    exact hle
  have hir := (C.toCooperativeGame.nucleolus_mem_imputations hle').2 i
  simp only [toCooperativeGame_val] at hir
  simp only [nucleolus, Pi.neg_apply]
  linarith

theorem sum_prenucleolus [Fintype A] (C : CostSharingGame A) :
    ∑ i : A, C.prenucleolus i = C.cost Finset.univ := by
  have hsum : ∑ i : A, C.toCooperativeGame.prenucleolus i = C.toCooperativeGame.val Finset.univ :=
    C.toCooperativeGame.prenucleolus_mem_preimputations
  rw [C.toCooperativeGame_val Finset.univ] at hsum
  simp only [prenucleolus, Pi.neg_apply, Finset.sum_neg_distrib, hsum, neg_neg]

/-- Whenever a cost-sharing game `C` has a nonempty core, `C.nucleolus` lies in `C.InCore`. -/
theorem nucleolus_inCore_of_nonemptyCore [Fintype A] (C : CostSharingGame A)
    (hcore : C.NonemptyCore) : C.InCore C.nucleolus := by
  rw [← C.inCore_toCooperativeGame_iff, nucleolus, neg_neg]
  exact C.toCooperativeGame.nucleolus_inCore_of_nonemptyCore
    ((C.nonemptyCore_toCooperativeGame_iff).2 hcore)

theorem prenucleolus_eq_nucleolus_of_nonemptyCore [Fintype A] (C : CostSharingGame A)
    (hcore : C.NonemptyCore) : C.prenucleolus = C.nucleolus := by
  simp only [prenucleolus, nucleolus]
  rw [C.toCooperativeGame.prenucleolus_eq_nucleolus_of_nonemptyCore
    ((C.nonemptyCore_toCooperativeGame_iff).2 hcore)]

end CostSharingGame

end Cslib.GameTheory
