/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Fintype.OrderStatistic
public import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Interval
public import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith

/-!
# Phantom-voter median mechanisms on closed real intervals

This module formalizes the anonymous `(n - 1)`-phantom-voter median characterization of
[Moulin1980] and [SchummerVohra2007] (§10.2.1, Theorem 10.2, pp. 247–250; Exercise 10.2, p. 264)
on a closed real interval `Set.Icc a b` (`a ≤ b`).

Given `n - 1` fixed phantom points `y : Fin (Fintype.card ι - 1) → Set.Icc a b`, the rule
`phantomMedian y` takes `n` reported peaks `x : ι → Set.Icc a b` and returns the median of the
`2n - 1` points `{x i | i : ι} ∪ {y j | j : Fin (n - 1)}`. For sorted phantoms `Monotone y`, this
coincides pointwise with the generalized median voter scheme `MoulinScheme.ofPhantoms` whose
coalition parameters are `α_∅ = b`, `α_univ = a`, and `α_S = y (n - 1 - |S|)` for
`1 ≤ |S| ≤ n - 1` (Exercise 10.2; equivalently `β_S = α_{Sᶜ} = y (|S| - 1)` in the monotone
convention of [SchummerVohra2007], Definition 10.3).

## Main definitions

* `Cslib.GameTheory.FacilityLocation.IsAnonymous`: permutation invariance of a deterministic rule.
* `Cslib.GameTheory.FacilityLocation.phantomMedian`: the `(n - 1)`-phantom median rule on
  `Set.Icc a b`.
* `Cslib.GameTheory.FacilityLocation.MoulinScheme.ofPhantoms`: explicit `MoulinScheme` realizing
  `phantomMedian y` for monotone phantoms `y` ([SchummerVohra2007], Exercise 10.2, p. 264).

## Main results

* `Cslib.GameTheory.FacilityLocation.MoulinScheme.eval_extremeProfile`: evaluating a `MoulinScheme`
  at the extreme profile with `S` at `b` and `Sᶜ` at `a` yields `E.alpha Sᶜ`
  ([SchummerVohra2007], p. 250).
* `Cslib.GameTheory.FacilityLocation.MoulinScheme.ofPhantoms_eval_eq_phantomMedian`:
  **Exercise 10.2** ([SchummerVohra2007], p. 264).
* `Cslib.GameTheory.FacilityLocation.phantomMedian_isGroupStrategyProof`,
  `phantomMedian_surjective`, `phantomMedian_isAnonymous`: every phantom median rule is strongly
  group strategy-proof, surjective, and anonymous.
* `Cslib.GameTheory.FacilityLocation.MoulinScheme.exists_phantomMedian_of_isAnonymous`: every
  anonymous `MoulinScheme` is a monotone-phantom median rule.
* `Cslib.GameTheory.FacilityLocation.isStrategyProof_surjective_anonymous_iff_phantomMedian`:
  **Theorem 10.2** on symmetric single-peaked preferences ([Moulin1980]; [SchummerVohra2007],
  pp. 247–250).

## References

* [H. Moulin, *On Strategy-Proofness and Single Peakedness*][Moulin1980]
* [J. Schummer and R. V. Vohra, *Mechanism Design without Money*][SchummerVohra2007]
-/

public section

namespace Cslib.GameTheory.FacilityLocation

/-- A deterministic rule `f : (ι → G) → G` is **anonymous** if permuting the agents leaves the
outcome unchanged ([SchummerVohra2007], §10.2.1, p. 247). -/
@[expose] def IsAnonymous {ι G : Type*} (f : (ι → G) → G) : Prop :=
  ∀ (σ : Equiv.Perm ι) (x : ι → G), f (x ∘ σ) = f x

private lemma exists_perm_image_eq_of_card_eq {α : Type*} [Finite α] {S T : Finset α}
    (hcard : S.card = T.card) :
    ∃ σ : Equiv.Perm α, ∀ i, σ i ∈ S ↔ i ∈ T := by
  classical
  let _ := Fintype.ofFinite α
  have h1 : Fintype.card {i : α // i ∈ T} = Fintype.card {i : α // i ∈ S} := by
    simp only [Fintype.card_coe, hcard]
  have h2 : Fintype.card {i : α // i ∉ T} = Fintype.card {i : α // i ∉ S} := by
    have hT : Fintype.card {i : α // i ∉ T} = (Tᶜ : Finset α).card := by
      rw [Fintype.card_subtype]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
    have hS : Fintype.card {i : α // i ∉ S} = (Sᶜ : Finset α).card := by
      rw [Fintype.card_subtype]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
    rw [hT, hS, Finset.card_compl, Finset.card_compl, hcard]
  let e1 : {i : α // i ∈ T} ≃ {i : α // i ∈ S} := Fintype.equivOfCardEq h1
  let e2 : {i : α // i ∉ T} ≃ {i : α // i ∉ S} := Fintype.equivOfCardEq h2
  let σ : Equiv.Perm α :=
    (Equiv.sumCompl (· ∈ T)).symm.trans ((Equiv.sumCongr e1 e2).trans (Equiv.sumCompl (· ∈ S)))
  refine ⟨σ, fun i => ?_⟩
  by_cases hi : i ∈ T
  · have hσ : σ i = (e1 ⟨i, hi⟩).1 := by
      simp only [σ, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos hi, Equiv.sumCongr_apply,
        Sum.map_inl, Equiv.sumCompl_apply_inl]
    rw [hσ]
    exact iff_of_true (e1 ⟨i, hi⟩).2 hi
  · have hσ : σ i = (e2 ⟨i, hi⟩).1 := by
      simp only [σ, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg hi, Equiv.sumCongr_apply,
        Sum.map_inr, Equiv.sumCompl_apply_inr]
    rw [hσ]
    exact iff_of_false (e2 ⟨i, hi⟩).2 hi

/-- An anonymous rule assigns the same outcome to any two two-valued profiles whose first-value
coalitions `S` and `T` have equal cardinality. -/
theorem IsAnonymous.apply_ite_eq_of_card_eq {ι G : Type*} [Finite ι] {f : (ι → G) → G}
    (hf : IsAnonymous f) {S T : Finset ι} [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (hcard : S.card = T.card) (u v : G) :
    f (fun i => if i ∈ S then u else v) = f (fun i => if i ∈ T then u else v) := by
  obtain ⟨σ, hσ⟩ := exists_perm_image_eq_of_card_eq hcard
  have hcomp : (fun i => if i ∈ S then u else v) ∘ σ = fun i => if i ∈ T then u else v := by
    funext i
    simp only [Function.comp_apply]
    by_cases hi : i ∈ T
    · rw [ite_eq_left ((hσ i).mpr hi), ite_eq_left hi]
    · rw [ite_eq_right (mt (hσ i).mp hi), ite_eq_right hi]
  rw [← hcomp, hf σ]

/-! ### Phantom-voter median rule and Exercise 10.2 -/

section PhantomMedian

variable {ι : Type*} [Fintype ι] [Nonempty ι] {a b : ℝ}

/-- The **`(n - 1)`-phantom-voter median rule** on `Set.Icc a b` ([Moulin1980];
[SchummerVohra2007], Theorem 10.2, Eq. (10.1), p. 247): given `n - 1` fixed phantom locations
`y : Fin (Fintype.card ι - 1) → Set.Icc a b`, output the median of the `2n - 1` points consisting
of the `n` agent reports `x` and the `n - 1` phantoms `y`. -/
noncomputable def phantomMedian (y : Fin (Fintype.card ι - 1) → Set.Icc a b)
    (x : ι → Set.Icc a b) : Set.Icc a b :=
  Fintype.lowerMedian (Sum.elim x y)

private lemma card_sum_phantoms :
    Fintype.card (ι ⊕ Fin (Fintype.card ι - 1)) = 2 * Fintype.card ι - 1 := by
  rw [Fintype.card_sum, Fintype.card_fin]
  have hpos := Fintype.card_pos (α := ι)
  omega

private lemma phantomMedian_eq_orderStatistic (y : Fin (Fintype.card ι - 1) → Set.Icc a b)
    (x : ι → Set.Icc a b) :
    phantomMedian y x = Fintype.orderStatistic (Sum.elim x y) (Fintype.card ι - 1) := by
  rw [phantomMedian, Fintype.lowerMedian_def, card_sum_phantoms]
  have hpos := Fintype.card_pos (α := ι)
  have hdiv : (2 * Fintype.card ι - 1 - 1) / 2 = Fintype.card ι - 1 := by omega
  rw [hdiv]

theorem phantomMedian_isAnonymous (y : Fin (Fintype.card ι - 1) → Set.Icc a b) :
    IsAnonymous (phantomMedian y) := by
  intro σ x
  rw [phantomMedian_eq_orderStatistic, phantomMedian_eq_orderStatistic]
  have hcomp : Sum.elim (x ∘ σ) y = Sum.elim x y ∘ Equiv.sumCongr σ (Equiv.refl _) := by
    funext u
    cases u <;> rfl
  rw [hcomp]
  exact Fintype.orderStatistic_comp_equiv (Equiv.sumCongr σ (Equiv.refl _)) (Sum.elim x y) _

theorem phantomMedian_comp_perm (y : Fin (Fintype.card ι - 1) → Set.Icc a b)
    (τ : Equiv.Perm (Fin (Fintype.card ι - 1))) (x : ι → Set.Icc a b) :
    phantomMedian (y ∘ τ) x = phantomMedian y x := by
  rw [phantomMedian_eq_orderStatistic, phantomMedian_eq_orderStatistic]
  have hcomp : Sum.elim x (y ∘ τ) = Sum.elim x y ∘ Equiv.sumCongr (Equiv.refl _) τ := by
    funext u
    cases u <;> rfl
  rw [hcomp]
  exact Fintype.orderStatistic_comp_equiv (Equiv.sumCongr (Equiv.refl _) τ) (Sum.elim x y) _

omit [Nonempty ι] in
/-- At the extreme profile where agents in `S` report `b` and agents outside `S` report `a`,
`E.eval` outputs `E.alpha Sᶜ` ([SchummerVohra2007], §10.2.1, p. 250). -/
theorem MoulinScheme.eval_extremeProfile [DecidableEq ι] {a b : ℝ} (E : MoulinScheme ι a b)
    (S : Finset ι) :
    (E.eval (fun i =>
      if i ∈ S then ⟨b, (E.mem_Icc ∅).1.trans (E.mem_Icc ∅).2, le_rfl⟩
      else ⟨a, le_rfl, (E.mem_Icc ∅).1.trans (E.mem_Icc ∅).2⟩) : ℝ) = E.alpha Sᶜ := by
  classical
  let hab : a ≤ b := (E.mem_Icc ∅).1.trans (E.mem_Icc ∅).2
  let x : ι → Set.Icc a b := fun i => if i ∈ S then ⟨b, hab, le_rfl⟩ else ⟨a, le_rfl, hab⟩
  let y : Set.Icc a b := ⟨E.alpha Sᶜ, E.mem_Icc Sᶜ⟩
  refine le_antisymm ?_ ?_
  · by_contra hgt
    have hlt : (y : ℝ) < E.eval x := lt_of_not_ge hgt
    have hα := (E.lt_eval_iff x y).mp hlt
    have hsub : Sᶜ ⊆ Finset.univ.filter fun i => (x i : ℝ) ≤ y := by
      intro i hi
      rw [Finset.mem_compl] at hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
      simp only [x, hi, ↓reduceIte]
      exact y.2.1
    exact hα.not_ge (E.antitone hsub)
  · by_contra hlt
    have hlt' : (E.eval x : ℝ) < y := lt_of_not_ge hlt
    have hα := (E.eval_lt_iff x y).mp hlt'
    have hsub : (Finset.univ.filter fun i => (x i : ℝ) < y) ⊆ Sᶜ := by
      intro i hi
      rw [Finset.mem_compl]
      intro hiS
      have hxi := (Finset.mem_filter.mp hi).2
      simp only [x, hiS, ↓reduceIte] at hxi
      exact hxi.not_ge y.2.2
    exact hα.not_ge (E.antitone hsub)

/-- Explicit `MoulinScheme` realizing the anonymous `(n - 1)`-phantom-voter median rule for sorted
phantoms `y : Fin (Fintype.card ι - 1) → Set.Icc a b` ([SchummerVohra2007], Exercise 10.2, p. 264):
`α_∅ = b`, `α_univ = a`, and `α_S = y (n - 1 - |S|)` for `1 ≤ |S| ≤ n - 1` (equivalently
`β_S = α_{Sᶜ} = y (|S| - 1)` in the monotone convention of Definition 10.3). -/
noncomputable def MoulinScheme.ofPhantoms (hab : a ≤ b)
    (y : Fin (Fintype.card ι - 1) → Set.Icc a b) (hy : Monotone y) :
    MoulinScheme ι a b where
  alpha S :=
    if h0 : S.card = 0 then b
    else if hn : S.card = Fintype.card ι then a
    else (y ⟨Fintype.card ι - 1 - S.card, by
      have hle := Finset.card_le_univ S
      omega⟩ : ℝ)
  mem_Icc S := by
    split_ifs
    · exact ⟨hab, le_rfl⟩
    · exact ⟨le_rfl, hab⟩
    · exact (y _).2
  antitone S T hST := by
    have hcard : S.card ≤ T.card := Finset.card_le_card hST
    have hTle : T.card ≤ Fintype.card ι := Finset.card_le_univ T
    by_cases hT0 : T.card = 0
    · have hS0 : S.card = 0 := by omega
      simp only [hT0, hS0, ↓reduceDIte, le_rfl]
    · by_cases hTn : T.card = Fintype.card ι
      · simp only [hTn, Fintype.card_ne_zero, ↓reduceDIte]
        by_cases hS0 : S.card = 0
        · simp only [hS0, ↓reduceDIte, hab]
        · by_cases hSn : S.card = Fintype.card ι
          · simp only [hSn, Fintype.card_ne_zero, ↓reduceDIte, le_rfl]
          · simp only [hS0, hSn, ↓reduceDIte, (y _).2.1]
      · simp only [hT0, hTn, ↓reduceDIte]
        by_cases hS0 : S.card = 0
        · simp only [hS0, ↓reduceDIte, (y _).2.2]
        · have hSn : S.card ≠ Fintype.card ι := by omega
          simp only [hS0, hSn, ↓reduceDIte]
          exact hy (show (⟨Fintype.card ι - 1 - T.card, _⟩ : Fin (Fintype.card ι - 1)) ≤
            ⟨Fintype.card ι - 1 - S.card, _⟩ by
              change Fintype.card ι - 1 - T.card ≤ Fintype.card ι - 1 - S.card
              omega)
  boundary_empty := by simp only [Finset.card_empty, ↓reduceDIte]
  boundary_univ := by simp only [Finset.card_univ, Fintype.card_ne_zero, ↓reduceDIte]

/-- Explicit parameter value of `MoulinScheme.ofPhantoms` on proper nonempty coalitions
([SchummerVohra2007], Exercise 10.2, p. 264): `α_S = y (n - 1 - |S|)`. -/
theorem MoulinScheme.ofPhantoms_alpha (hab : a ≤ b)
    (y : Fin (Fintype.card ι - 1) → Set.Icc a b) (hy : Monotone y)
    {S : Finset ι} (h0 : 0 < S.card) (hn : S.card < Fintype.card ι) :
    (MoulinScheme.ofPhantoms hab y hy).alpha S =
      (y ⟨Fintype.card ι - 1 - S.card, by omega⟩ : ℝ) := by
  have h0' : S.card ≠ 0 := Nat.ne_of_gt h0
  have hn' : S.card ≠ Fintype.card ι := Nat.ne_of_lt hn
  simp only [MoulinScheme.ofPhantoms, h0', hn', ↓reduceDIte]

/-- **Exercise 10.2** ([SchummerVohra2007], p. 264): for monotone phantoms `y`, the explicit
generalized median voter scheme `MoulinScheme.ofPhantoms hab y hy` evaluates identically to the
`(n - 1)`-phantom median rule `phantomMedian y`. -/
theorem MoulinScheme.ofPhantoms_eval_eq_phantomMedian (hab : a ≤ b)
    (y : Fin (Fintype.card ι - 1) → Set.Icc a b) (hy : Monotone y) (x : ι → Set.Icc a b) :
    (MoulinScheme.ofPhantoms hab y hy).eval x = phantomMedian y x := by
  classical
  have hpos := Fintype.card_pos (α := ι)
  have hk_lt : Fintype.card ι - 1 < Fintype.card (ι ⊕ Fin (Fintype.card ι - 1)) := by
    rw [card_sum_phantoms]; omega
  have hcut : ∀ z : Set.Icc a b,
      (z : ℝ) < (MoulinScheme.ofPhantoms hab y hy).eval x ↔ (z : ℝ) < phantomMedian y x := by
    intro z
    rw [MoulinScheme.lt_eval_iff, phantomMedian_eq_orderStatistic]
    have hlt_sub : (z : ℝ) < Fintype.orderStatistic (Sum.elim x y) (Fintype.card ι - 1) ↔
        z < Fintype.orderStatistic (Sum.elim x y) (Fintype.card ι - 1) := Iff.rfl
    rw [hlt_sub, Fintype.lt_orderStatistic_iff _ hk_lt]
    set Sx := Finset.univ.filter fun i : ι => (x i : ℝ) ≤ z
    set Sy := Finset.univ.filter fun j : Fin (Fintype.card ι - 1) => (y j : ℝ) ≤ z
    have hsum_card : (Finset.univ.filter fun u => Sum.elim x y u ≤ z).card = Sx.card + Sy.card := by
      have heq : (Finset.univ.filter fun u : ι ⊕ Fin (Fintype.card ι - 1) => Sum.elim x y u ≤ z) =
          Sx.map ⟨Sum.inl, Sum.inl_injective⟩ ∪ Sy.map ⟨Sum.inr, Sum.inr_injective⟩ := by
        ext u
        cases u with
        | inl i =>
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sum.elim_inl, Finset.mem_union,
            Finset.mem_map, Function.Embedding.coeFn_mk, Sum.inl.injEq, exists_eq_right,
            reduceCtorEq, and_false, exists_false, or_false, Sx]
          rfl
        | inr j =>
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sum.elim_inr, Finset.mem_union,
            Finset.mem_map, Function.Embedding.coeFn_mk, reduceCtorEq, and_false, exists_false,
            Sum.inr.injEq, exists_eq_right, false_or, Sy]
          rfl
      rw [heq, Finset.card_union_of_disjoint, Finset.card_map, Finset.card_map]
      rw [Finset.disjoint_left]
      intro u hu1 hu2
      rcases Finset.mem_map.mp hu1 with ⟨i, _, rfl⟩
      rcases Finset.mem_map.mp hu2 with ⟨j, _, h⟩
      cases h
    rw [hsum_card]
    change (z : ℝ) < (if h0 : Sx.card = 0 then b
      else if hn : Sx.card = Fintype.card ι then a
      else (y ⟨Fintype.card ι - 1 - Sx.card, _⟩ : ℝ)) ↔ Sx.card + Sy.card ≤ Fintype.card ι - 1
    have hSy_le : Sy.card ≤ Fintype.card ι - 1 := by
      simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_univ Sy
    split_ifs with h0 hn
    · have hzb : (z : ℝ) < b := by
        by_contra hge
        have hzb_eq : (z : ℝ) = b := le_antisymm z.2.2 (le_of_not_gt hge)
        obtain ⟨i₀⟩ := ‹Nonempty ι›
        have hi₀ : i₀ ∈ Sx := Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, by
          rw [hzb_eq]; exact (x i₀).2.2⟩
        have hpos_x : 0 < Sx.card := Finset.card_pos.mpr ⟨i₀, hi₀⟩
        omega
      rw [h0, zero_add]
      exact iff_of_true hzb hSy_le
    · rw [hn]
      exact iff_of_false (not_lt_of_ge z.2.1) (by omega)
    · have hSx_le : Sx.card ≤ Fintype.card ι := by
        simpa only [Finset.card_univ] using Finset.card_le_univ Sx
      set m : ℕ := Fintype.card ι - 1 - Sx.card
      have hm_lt : m < Fintype.card ι - 1 := by omega
      constructor
      · intro hz_lt
        have hsub : Sy ⊆ Finset.univ.filter fun j : Fin (Fintype.card ι - 1) => j.val < m := by
          intro j hj
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ j, ?_⟩
          by_contra hge
          have hmj : (⟨m, hm_lt⟩ : Fin (Fintype.card ι - 1)) ≤ j :=
            Fin.mk_le_mk.mpr (le_of_not_gt hge)
          have hy_le : (y ⟨m, hm_lt⟩ : ℝ) ≤ y j := hy hmj
          linarith [(Finset.mem_filter.mp hj).2]
        have hcard_lt : (Finset.univ.filter fun j : Fin (Fintype.card ι - 1) => j.val < m).card =
            m := by
          have hbij : (Finset.univ.filter fun j : Fin (Fintype.card ι - 1) => j.val < m).card =
              (Finset.range m).card := by
            refine Finset.card_bij (fun j _ => j.val) ?_ ?_ ?_
            · intro j hj; exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
            · intro j₁ _ j₂ _ h; exact Fin.ext h
            · intro k hk
              have hkm : k < m := Finset.mem_range.mp hk
              exact ⟨⟨k, hkm.trans hm_lt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkm⟩, rfl⟩
          rw [hbij, Finset.card_range]
        have hSy_le_m : Sy.card ≤ m := (Finset.card_le_card hsub).trans_eq hcard_lt
        omega
      · intro hsum
        by_contra hle
        have hy_le : (y ⟨m, hm_lt⟩ : ℝ) ≤ z := le_of_not_gt hle
        have hsub : (Finset.univ.filter fun j : Fin (Fintype.card ι - 1) => j.val ≤ m) ⊆ Sy := by
          intro j hj
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ j, ?_⟩
          have hjm : j ≤ ⟨m, hm_lt⟩ := Fin.mk_le_mk.mpr (Finset.mem_filter.mp hj).2
          exact (hy hjm).trans hy_le
        have hcard_le : (Finset.univ.filter fun j : Fin (Fintype.card ι - 1) => j.val ≤ m).card =
            m + 1 := by
          have hbij : (Finset.univ.filter fun j : Fin (Fintype.card ι - 1) => j.val ≤ m).card =
              (Finset.range (m + 1)).card := by
            refine Finset.card_bij (fun j _ => j.val) ?_ ?_ ?_
            · intro j hj
              exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hj).2)
            · intro j₁ _ j₂ _ h; exact Fin.ext h
            · intro k hk
              have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
              exact ⟨⟨k, Nat.lt_of_le_of_lt hkm hm_lt⟩,
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkm⟩, rfl⟩
          rw [hbij, Finset.card_range]
        have hge : m + 1 ≤ Sy.card := hcard_le ▸ Finset.card_le_card hsub
        omega
  refine Subtype.ext (le_antisymm ?_ ?_)
  · by_contra hgt
    exact lt_irrefl _ ((hcut (phantomMedian y x)).mp (lt_of_not_ge hgt))
  · by_contra hgt
    exact lt_irrefl _ ((hcut ((MoulinScheme.ofPhantoms hab y hy).eval x)).mpr (lt_of_not_ge hgt))

/-- Any (possibly unsorted) phantom vector `y` defines the same rule as `MoulinScheme.ofPhantoms`
applied to its sorted rearrangement `y ∘ Tuple.sort y`. -/
theorem phantomMedian_eq_eval_ofPhantoms_sort (hab : a ≤ b)
    (y : Fin (Fintype.card ι - 1) → Set.Icc a b) :
    phantomMedian y =
      (MoulinScheme.ofPhantoms hab (y ∘ Tuple.sort y) (Tuple.monotone_sort y)).eval := by
  funext x
  rw [MoulinScheme.ofPhantoms_eval_eq_phantomMedian, phantomMedian_comp_perm]

theorem phantomMedian_isGroupStrategyProof [DecidableEq ι]
    [MeasurableSpace (Set.Icc a b)] [OpensMeasurableSpace (Set.Icc a b)]
    (hab : a ≤ b) (y : Fin (Fintype.card ι - 1) → Set.Icc a b) :
    (Mechanism.deterministic (phantomMedian y)).IsGroupStrategyProof := by
  rw [phantomMedian_eq_eval_ofPhantoms_sort hab y]
  exact (MoulinScheme.ofPhantoms hab (y ∘ Tuple.sort y)
    (Tuple.monotone_sort y)).eval_isGroupStrategyProof

theorem phantomMedian_isStrategyProof [DecidableEq ι]
    [MeasurableSpace (Set.Icc a b)] [OpensMeasurableSpace (Set.Icc a b)]
    (hab : a ≤ b) (y : Fin (Fintype.card ι - 1) → Set.Icc a b) :
    (Mechanism.deterministic (phantomMedian y)).IsStrategyProof :=
  (phantomMedian_isGroupStrategyProof hab y).isStrategyProof

theorem phantomMedian_surjective (hab : a ≤ b)
    (y : Fin (Fintype.card ι - 1) → Set.Icc a b) :
    Function.Surjective (phantomMedian y) := by
  rw [phantomMedian_eq_eval_ofPhantoms_sort hab y]
  exact (MoulinScheme.ofPhantoms hab (y ∘ Tuple.sort y) (Tuple.monotone_sort y)).eval_surjective

/-! ### Anonymous `MoulinScheme` characterization (Theorem 10.2) -/

/-- Every anonymous `MoulinScheme` on `Set.Icc a b` is realized by a monotone vector of `n - 1`
phantom voters ([Moulin1980]; [SchummerVohra2007], Theorem 10.2, pp. 247–250). -/
theorem MoulinScheme.exists_phantomMedian_of_isAnonymous (E : MoulinScheme ι a b)
    (hanon : IsAnonymous E.eval) :
    ∃ y : Fin (Fintype.card ι - 1) → Set.Icc a b, Monotone y ∧ E.eval = phantomMedian y := by
  classical
  have hab : a ≤ b := (E.mem_Icc ∅).1.trans (E.mem_Icc ∅).2
  have hpos := Fintype.card_pos (α := ι)
  have halpha_card : ∀ S T : Finset ι, S.card = T.card → E.alpha S = E.alpha T := by
    intro S T hcard
    have hc_card : Sᶜ.card = Tᶜ.card := by
      rw [Finset.card_compl, Finset.card_compl, hcard]
    have heq := hanon.apply_ite_eq_of_card_eq hc_card ⟨b, hab, le_rfl⟩ ⟨a, le_rfl, hab⟩
    have h1 := E.eval_extremeProfile Sᶜ
    have h2 := E.eval_extremeProfile Tᶜ
    rw [compl_compl] at h1 h2
    exact h1.symm.trans ((congrArg Subtype.val heq).trans h2)
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let stdSet (k : ℕ) : Finset ι :=
    (Finset.univ.filter fun j : Fin (Fintype.card ι) => j.val < k).map e.symm.toEmbedding
  have hstd_card : ∀ k ≤ Fintype.card ι, (stdSet k).card = k := by
    intro k hk
    rw [Finset.card_map]
    have hbij : (Finset.univ.filter fun j : Fin (Fintype.card ι) => j.val < k).card =
        (Finset.range k).card := by
      refine Finset.card_bij (fun j _ => j.val) ?_ ?_ ?_
      · intro j hj; exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
      · intro j₁ _ j₂ _ h; exact Fin.ext h
      · intro r hr
        have hrk : r < k := Finset.mem_range.mp hr
        exact ⟨⟨r, Nat.lt_of_lt_of_le hrk hk⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrk⟩, rfl⟩
    rw [hbij, Finset.card_range]
  have hstd_mono : ∀ {k₁ k₂ : ℕ}, k₁ ≤ k₂ → stdSet k₁ ⊆ stdSet k₂ := by
    intro k₁ k₂ hle i hi
    rcases Finset.mem_map.mp hi with ⟨j, hj, rfl⟩
    exact Finset.mem_map.mpr
      ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, (Finset.mem_filter.mp hj).2.trans_le hle⟩, rfl⟩
  let y : Fin (Fintype.card ι - 1) → Set.Icc a b :=
    fun m => ⟨E.alpha (stdSet (Fintype.card ι - 1 - m.val)),
      E.mem_Icc (stdSet (Fintype.card ι - 1 - m.val))⟩
  have hy : Monotone y := by
    intro m₁ m₂ hm
    exact E.antitone (hstd_mono (by omega))
  refine ⟨y, hy, ?_⟩
  have hE : E = MoulinScheme.ofPhantoms hab y hy := by
    cases E with
    | mk alpha mem_Icc antitone boundary_empty boundary_univ =>
      congr 1
      funext S
      change alpha S =
        if h0 : S.card = 0 then b
        else if hn : S.card = Fintype.card ι then a
        else alpha (stdSet (Fintype.card ι - 1 - (Fintype.card ι - 1 - S.card)))
      split_ifs with h0 hn
      · rw [Finset.card_eq_zero.mp h0, boundary_empty]
      · have hSu : S = Finset.univ := Finset.eq_univ_of_card S hn
        rw [hSu, boundary_univ]
      · have hSle : S.card ≤ Fintype.card ι := by
          simpa only [Finset.card_univ] using Finset.card_le_univ S
        have hsub_eq : Fintype.card ι - 1 - (Fintype.card ι - 1 - S.card) = S.card := by omega
        rw [hsub_eq]
        exact halpha_card S (stdSet S.card) (hstd_card S.card hSle).symm
  rw [hE]
  funext x
  exact MoulinScheme.ofPhantoms_eval_eq_phantomMedian hab y hy x

/-- **Theorem 10.2 on symmetric single-peaked preferences** ([Moulin1980]; [SchummerVohra2007],
§10.2.1, pp. 247–250): a deterministic facility-location mechanism on `Set.Icc a b` (`a ≤ b`) is
strategy-proof, surjective, and anonymous if and only if it is a `(n - 1)`-phantom-voter median
rule `phantomMedian y` (which may equivalently be chosen monotone). -/
theorem isStrategyProof_surjective_anonymous_iff_phantomMedian [DecidableEq ι]
    [MeasurableSpace (Set.Icc a b)] [OpensMeasurableSpace (Set.Icc a b)]
    (hab : a ≤ b) (f : (ι → Set.Icc a b) → Set.Icc a b) :
    ((Mechanism.deterministic f).IsStrategyProof ∧ Function.Surjective f ∧ IsAnonymous f) ↔
      ∃ y : Fin (Fintype.card ι - 1) → Set.Icc a b, f = phantomMedian y := by
  constructor
  · rintro ⟨hf_sp, hf_onto, hf_anon⟩
    obtain ⟨E, rfl⟩ :=
      (isStrategyProof_and_surjective_iff_exists_moulinScheme hab f).mp ⟨hf_sp, hf_onto⟩
    obtain ⟨y, _, hy⟩ := E.exists_phantomMedian_of_isAnonymous hf_anon
    exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    exact ⟨phantomMedian_isStrategyProof hab y, phantomMedian_surjective hab y,
      phantomMedian_isAnonymous y⟩

end PhantomMedian

end Cslib.GameTheory.FacilityLocation
