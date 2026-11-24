/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.FacilityLocation.PhantomMedian
public import CslibFrontier.GameTheory.SocialChoice.SinglePeaked.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Tactic.Linarith

/-!
# Moulin–Ching characterizations on ordinal single-peaked preferences

This module proves **Theorems 10.2 and 10.4** of [SchummerVohra2007] (§10.2.1, pp. 247–251;
[Moulin1980]; [Ching1997]) on the full ordinal domain of single-peaked preferences over a closed
real interval `Set.Icc a b` (`a ≤ b`):

* **Theorem 10.4** (`isStrategyProof_and_surjective_iff_exists_moulinScheme`): a rule on ordinal
  single-peaked preferences is strategy-proof and surjective (onto) if and only if it is the lift
  of a generalized median voter scheme (`Cslib.GameTheory.FacilityLocation.MoulinScheme`). We also
  prove that every such rule is strongly group strategy-proof (a strengthening not stated in
  [SchummerVohra2007], Theorem 10.4).
* **Theorem 10.2** (`isStrategyProof_surjective_anonymous_iff_phantomMedian`):
  a rule on ordinal single-peaked preferences is strategy-proof, surjective, and anonymous if and
  only if it chooses the median of the `n` agents' peaks together with `n - 1` fixed phantom
  points in `Set.Icc a b` (`phantomMedian y`, Eq. (10.1)).
* **Duality with Definition 10.3** (`eval_eq_maxMinEval`): `MoulinScheme.eval` coincides pointwise
  with the dual formula `max_{S ⊆ N} min{β_S, p_i : i ∈ S}` where `β_S = E.alpha Sᶜ` is monotone
  in `S` ([SchummerVohra2007], p. 250).
* **Individual rationality uniqueness** ([SchummerVohra2007], §10.2.2, p. 252): the minimum-peak
  rule is the unique strategy-proof, surjective rule on `Set.Icc a b` that is individually rational
  with respect to `a` (together with the symmetric right-endpoint addition for `b`).
* **Exercise 10.1** ([SchummerVohra2007], p. 264): Lemma 10.1 (`surjective ↔ unanimous ↔
  Pareto-optimal` under strategy-proofness) still holds when restricted to symmetric (Euclidean)
  single-peaked preferences (`Cslib.GameTheory.FacilityLocation` on `Set.Icc a b`).

## Main definitions

* `Cslib.GameTheory.SocialChoice.SinglePeaked.ofMoulinScheme`: lifts a `MoulinScheme ι a b` to an
  ordinal single-peaked `Rule ι a b`.
* `Cslib.GameTheory.SocialChoice.SinglePeaked.ofPhantomMedian`: lifts `phantomMedian y` to an
  ordinal single-peaked `Rule ι a b`.
* `Cslib.GameTheory.SocialChoice.SinglePeaked.maxMinEval`: the dual
  `max_S min{α_{Sᶜ}, p_i : i ∈ S}` evaluation formula of [SchummerVohra2007], Definition 10.3.
* `Cslib.GameTheory.SocialChoice.SinglePeaked.minPeakScheme`,
  `Cslib.GameTheory.SocialChoice.SinglePeaked.maxPeakScheme`: the minimum-peak and maximum-peak
  generalized median voter schemes.

## Main results

* `SinglePeaked.eval_eq_maxMinEval`: pointwise equivalence between `MoulinScheme.eval` and
  [SchummerVohra2007] Definition 10.3.
* `SinglePeaked.ofMoulinScheme_isGroupStrategyProof`: every generalized median voter scheme is
  strongly group strategy-proof on ordinal single-peaked preferences.
* `SinglePeaked.isStrategyProof_and_surjective_iff_exists_moulinScheme`:
  **Theorem 10.4** ([SchummerVohra2007], p. 251; [Moulin1980]; [Ching1997]).
* `SinglePeaked.isStrategyProof_surjective_anonymous_iff_phantomMedian`:
  **Theorem 10.2** ([SchummerVohra2007], pp. 247–250; [Moulin1980]; [Ching1997]).
* `SinglePeaked.isGroupStrategyProof_of_isStrategyProof_of_surjective`:
  strategy-proof onto rules on ordinal single-peaked preferences are strongly group strategy-proof.
* `SinglePeaked.isStrategyProof_surjective_isIR_left_iff`:
  uniqueness of the minimum-peak rule under individual rationality at `a`
  ([SchummerVohra2007], §10.2.2, p. 252).
* `SinglePeaked.symmetric_surjective_iff_paretoOptimal`:
  **Exercise 10.1** ([SchummerVohra2007], p. 264).

## References

* [S. Ching, *Strategy-proofness and "median voters"*][Ching1997]
* [H. Moulin, *On Strategy-Proofness and Single Peakedness*][Moulin1980]
* [J. Schummer and R. V. Vohra, *Mechanism Design without Money*][SchummerVohra2007]
-/

public section

namespace Cslib.GameTheory.SocialChoice.SinglePeaked

open Cslib.GameTheory.FacilityLocation

/-! ### Duality with Definition 10.3 -/

section MoulinDuality

variable {ι : Type*} [Fintype ι] {a b : ℝ}

open Classical in
/-- The dual evaluation formula `max_{S ⊆ N} min{β_S, p_i : i ∈ S}` of [SchummerVohra2007]
(Definition 10.3, p. 250), with monotone parameters `β_S = E.alpha Sᶜ`. -/
noncomputable def maxMinEval (E : MoulinScheme ι a b) (x : ι → Set.Icc a b) : ℝ :=
  Finset.univ.fold max a fun S : Finset ι =>
    min (E.alpha Sᶜ) (S.fold min b fun i => (x i : ℝ))

private lemma le_maxMinEval_branch (E : MoulinScheme ι a b) (x : ι → Set.Icc a b) (S : Finset ι) :
    by classical exact min (E.alpha Sᶜ) (S.fold min b fun i => (x i : ℝ)) ≤ maxMinEval E x := by
  classical
  exact (Finset.le_fold_max _).mpr (Or.inr ⟨S, Finset.mem_univ S, le_rfl⟩)

private lemma maxMinEval_mem_Icc (E : MoulinScheme ι a b) (x : ι → Set.Icc a b) :
    maxMinEval E x ∈ Set.Icc a b := by
  classical
  have hab : a ≤ b := (E.mem_Icc ∅).1.trans (E.mem_Icc ∅).2
  refine ⟨(Finset.le_fold_max a).mpr (Or.inl le_rfl),
    (Finset.fold_max_le b).mpr ⟨hab, fun S _ => (min_le_left _ _).trans (E.mem_Icc Sᶜ).2⟩⟩

private lemma lt_maxMinEval_iff (E : MoulinScheme ι a b) (x : ι → Set.Icc a b) (y : Set.Icc a b) :
    (y : ℝ) < maxMinEval E x ↔
      by classical exact (y : ℝ) < E.alpha (Finset.univ.filter fun i => (x i : ℝ) ≤ y) := by
  classical
  let Sle : Finset ι := Finset.univ.filter fun i => (x i : ℝ) ≤ y
  constructor
  · intro hy
    rw [maxMinEval, Finset.lt_fold_max] at hy
    rcases hy with hy_a | ⟨S, _, hS⟩
    · linarith [y.2.1]
    · have h1 : (y : ℝ) < E.alpha Sᶜ := lt_of_lt_of_le hS (min_le_left _ _)
      have h2 : (y : ℝ) < S.fold min b fun i => (x i : ℝ) := lt_of_lt_of_le hS (min_le_right _ _)
      have hsub : Sle ⊆ Sᶜ := by
        intro i hi
        rw [Finset.mem_compl]
        intro hiS
        have hxi : (y : ℝ) < x i := ((Finset.lt_fold_min _).mp h2).2 i hiS
        linarith [(Finset.mem_filter.mp hi).2]
      exact h1.trans_le (E.antitone hsub)
  · intro hy
    have hyb : (y : ℝ) < b := hy.trans_le (E.mem_Icc Sle).2
    have hfold : (y : ℝ) < Sleᶜ.fold min b fun i => (x i : ℝ) := by
      rw [Finset.lt_fold_min]
      refine ⟨hyb, fun i hi => ?_⟩
      rw [Finset.mem_compl, Finset.mem_filter] at hi
      push Not at hi
      exact hi (Finset.mem_univ i)
    have hmin : (y : ℝ) < min (E.alpha Sleᶜᶜ) (Sleᶜ.fold min b fun i => (x i : ℝ)) := by
      rw [compl_compl]
      exact lt_min hy hfold
    exact hmin.trans_le (le_maxMinEval_branch E x Sleᶜ)

/-- `MoulinScheme.eval` coincides pointwise with the dual `max_S min{β_S, p_i : i ∈ S}` formula
of [SchummerVohra2007] (Definition 10.3, p. 250) with `β_S = E.alpha Sᶜ`. -/
theorem eval_eq_maxMinEval (E : MoulinScheme ι a b) (x : ι → Set.Icc a b) :
    (E.eval x : ℝ) = maxMinEval E x := by
  let m : Set.Icc a b := ⟨maxMinEval E x, maxMinEval_mem_Icc E x⟩
  refine le_antisymm ?_ ?_
  · by_contra hgt
    have hlt : (m : ℝ) < E.eval x := lt_of_not_ge hgt
    have hlt' : (m : ℝ) < maxMinEval E x :=
      (lt_maxMinEval_iff E x m).mpr ((E.lt_eval_iff x m).mp hlt)
    exact lt_irrefl _ hlt'
  · by_contra hgt
    have hlt : (E.eval x : ℝ) < maxMinEval E x := lt_of_not_ge hgt
    have hlt' : (E.eval x : ℝ) < E.eval x :=
      (E.lt_eval_iff x (E.eval x)).mpr ((lt_maxMinEval_iff E x (E.eval x)).mp hlt)
    exact lt_irrefl _ hlt'

/-- A `MoulinScheme` always evaluates within the convex hull of the reported peaks. -/
theorem eval_mem_peaks_bounds [Nonempty ι] (E : MoulinScheme ι a b) (x : ι → Set.Icc a b) :
    (∃ i : ι, (x i : ℝ) ≤ E.eval x) ∧ (∃ j : ι, (E.eval x : ℝ) ≤ x j) := by
  obtain ⟨i, _, hi⟩ :=
    Finset.exists_min_image Finset.univ (fun k => (x k : ℝ)) Finset.univ_nonempty
  obtain ⟨j, _, hj⟩ :=
    Finset.exists_max_image Finset.univ (fun k => (x k : ℝ)) Finset.univ_nonempty
  refine ⟨⟨i, ?_⟩, ⟨j, ?_⟩⟩
  · simpa only [E.eval_const] using E.eval_mono (x := fun _ => x i) (z := x) fun k =>
      hi k (Finset.mem_univ k)
  · simpa only [E.eval_const] using E.eval_mono (x := x) (z := fun _ => x j) fun k =>
      hj k (Finset.mem_univ k)

end MoulinDuality

/-! ### Theorems 10.4 and 10.2 on ordinal single-peaked preferences -/

section Characterization

variable {ι : Type*} [Fintype ι] {a b : ℝ}

/-- Lifts a `MoulinScheme ι a b` to a peaks-only rule on ordinal single-peaked preferences. -/
noncomputable def ofMoulinScheme (E : MoulinScheme ι a b) : Rule ι a b :=
  fun P => E.eval (fun i => (P i).peak)

@[simp] theorem ofMoulinScheme_apply (E : MoulinScheme ι a b) (P : Profile ι a b) :
    ofMoulinScheme E P = E.eval (fun i => (P i).peak) := by rfl

/-- Lifts an `(n - 1)`-phantom-voter median rule to ordinal single-peaked preferences
([SchummerVohra2007], Theorem 10.2, Eq. (10.1), p. 247). -/
noncomputable def ofPhantomMedian [Nonempty ι]
    (y : Fin (Fintype.card ι - 1) → Set.Icc a b) : Rule ι a b :=
  fun P => phantomMedian y (fun i => (P i).peak)

@[simp] theorem ofPhantomMedian_apply [Nonempty ι]
    (y : Fin (Fintype.card ι - 1) → Set.Icc a b) (P : Profile ι a b) :
    ofPhantomMedian y P = phantomMedian y (fun i => (P i).peak) := by rfl

theorem ofMoulinScheme_isPeaksOnly (E : MoulinScheme ι a b) :
    (ofMoulinScheme E).IsPeaksOnly := by
  intro P Q hpeaks
  simp only [ofMoulinScheme, funext hpeaks]

theorem ofMoulinScheme_surjective [Nonempty ι] (E : MoulinScheme ι a b) :
    Function.Surjective (ofMoulinScheme E) := fun y =>
  ⟨fun _ => Preference.symmetric y, by
    simp only [ofMoulinScheme, Preference.symmetric_peak, E.eval_const]⟩

/-- Every generalized median voter scheme is strongly group strategy-proof on the full ordinal
domain of single-peaked preferences. -/
theorem ofMoulinScheme_isGroupStrategyProof (E : MoulinScheme ι a b) :
    (ofMoulinScheme E).IsGroupStrategyProof := by
  classical
  rintro P Q A hPQ ⟨hle, i₀, hi₀A, hlt⟩
  let p : ι → Set.Icc a b := fun i => (P i).peak
  let q : ι → Set.Icc a b := fun i => (Q i).peak
  let y : Set.Icc a b := E.eval p
  let y' : Set.Icc a b := E.eval q
  have hne : (y : ℝ) ≠ y' := fun heq => by
    have hy : y = y' := Subtype.ext heq
    have hlt' : (P i₀).Prefers y' y := hlt
    rw [hy] at hlt'
    exact (P i₀).prefers_irrefl y' hlt'
  rcases lt_or_gt_of_ne hne with hy_lt | hy'_lt
  · have hA_gt : ∀ i ∈ A, (y : ℝ) < p i := fun i hi => by
      by_contra hle_p
      exact (P i).prefers_of_between_right (le_of_not_gt hle_p) hy_lt (hle i hi)
    have hsub : (Finset.univ.filter fun i => (p i : ℝ) ≤ y) ⊆
        (Finset.univ.filter fun i => (q i : ℝ) ≤ y) := by
      intro i hi
      have hpi : (p i : ℝ) ≤ y := (Finset.mem_filter.mp hi).2
      have hiA : i ∉ A := fun h => (hA_gt i h).not_ge hpi
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
      simpa only [p, q, hPQ i hiA] using hpi
    have h1 : (y : ℝ) < E.alpha (Finset.univ.filter fun i => (q i : ℝ) ≤ y) :=
      (E.lt_eval_iff q y).mp hy_lt
    have h2 : (y : ℝ) < E.eval p :=
      (E.lt_eval_iff p y).mpr (h1.trans_le (E.antitone hsub))
    exact lt_irrefl _ h2
  · have hA_lt : ∀ i ∈ A, (p i : ℝ) < y := fun i hi => by
      by_contra hge_p
      exact (P i).prefers_of_between_left hy'_lt (le_of_not_gt hge_p) (hle i hi)
    have hsub : (Finset.univ.filter fun i => (q i : ℝ) < y) ⊆
        (Finset.univ.filter fun i => (p i : ℝ) < y) := by
      intro i hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
      by_cases hiA : i ∈ A
      · exact hA_lt i hiA
      · simpa only [p, q, hPQ i hiA] using (Finset.mem_filter.mp hi).2
    have h1 : E.alpha (Finset.univ.filter fun i => (q i : ℝ) < y) < y :=
      (E.eval_lt_iff q y).mp hy'_lt
    have h2 : (E.eval p : ℝ) < y :=
      (E.eval_lt_iff p y).mpr ((E.antitone hsub).trans_lt h1)
    exact lt_irrefl _ h2

theorem ofMoulinScheme_isStrategyProof (E : MoulinScheme ι a b) :
    (ofMoulinScheme E).IsStrategyProof :=
  (ofMoulinScheme_isGroupStrategyProof E).isStrategyProof

/-- **Theorem 10.4** ([SchummerVohra2007], §10.2.1, p. 251; [Moulin1980]; [Ching1997]):
on the ordinal single-peaked preference domain over `Set.Icc a b` (`a ≤ b`) for a finite nonempty
electorate `ι`, a rule is strategy-proof and surjective if and only if it is the lift of a
generalized median voter scheme (`MoulinScheme ι a b`). -/
theorem isStrategyProof_and_surjective_iff_exists_moulinScheme [Nonempty ι] (hab : a ≤ b)
    (f : Rule ι a b) :
    (f.IsStrategyProof ∧ Function.Surjective f) ↔
      ∃ E : MoulinScheme ι a b, f = ofMoulinScheme E := by
  classical
  constructor
  · rintro ⟨hf_sp, hf_onto⟩
    have hf_po : f.IsPeaksOnly := hf_sp.isPeaksOnly_of_surjective hf_onto
    let g : (ι → Set.Icc a b) → Set.Icc a b := fun x => f (fun i => Preference.symmetric (x i))
    have hg_eq : ∀ P : Profile ι a b, f P = g (fun i => (P i).peak) := fun P =>
      hf_po P (fun i => Preference.symmetric (P i).peak) fun i =>
        (Preference.symmetric_peak (P i).peak).symm
    let _ : MeasurableSpace (Set.Icc a b) := borel (Set.Icc a b)
    have _ : OpensMeasurableSpace (Set.Icc a b) := ⟨le_rfl⟩
    have hg_sp : (Mechanism.deterministic g).IsStrategyProof := by
      rw [Mechanism.isStrategyProof_deterministic_iff]
      intro x i z
      have hsp := hf_sp.atLeast_update (fun j => Preference.symmetric (x j)) i
        (Preference.symmetric z)
      have hupd : Function.update (fun j => Preference.symmetric (x j)) i (Preference.symmetric z) =
          fun j => Preference.symmetric (Function.update x i z j) :=
        funext fun j => (Function.apply_update (fun _ => Preference.symmetric) x i z j).symm
      rw [hupd] at hsp
      simpa only [g, Preference.symmetric_atLeast_iff, Subtype.dist_eq, Real.dist_eq,
        abs_sub_comm] using hsp
    have hg_onto : Function.Surjective g := fun y => by
      obtain ⟨P, hP⟩ := hf_onto y
      exact ⟨fun i => (P i).peak, (hg_eq P).symm.trans hP⟩
    obtain ⟨E, hE⟩ :=
      (FacilityLocation.isStrategyProof_and_surjective_iff_exists_moulinScheme hab g).mp
        ⟨hg_sp, hg_onto⟩
    refine ⟨E, funext fun P => ?_⟩
    rw [hg_eq P, hE]
    rfl
  · rintro ⟨E, rfl⟩
    exact ⟨ofMoulinScheme_isStrategyProof E, ofMoulinScheme_surjective E⟩

/-- **Theorem 10.2** ([SchummerVohra2007], §10.2.1, pp. 247–250; [Moulin1980]; [Ching1997]):
on the ordinal single-peaked preference domain over `Set.Icc a b` (`a ≤ b`) for a finite nonempty
electorate `ι`, a rule is strategy-proof, surjective, and anonymous if and only if there exist
`n - 1` phantom points `y : Fin (Fintype.card ι - 1) → Set.Icc a b` such that `f` always chooses
the median of the agents' peaks and `y`. -/
theorem isStrategyProof_surjective_anonymous_iff_phantomMedian [Nonempty ι]
    (hab : a ≤ b) (f : Rule ι a b) :
    (f.IsStrategyProof ∧ Function.Surjective f ∧ f.IsAnonymous) ↔
      ∃ y : Fin (Fintype.card ι - 1) → Set.Icc a b, f = ofPhantomMedian y := by
  constructor
  · rintro ⟨hf_sp, hf_onto, hf_anon⟩
    obtain ⟨E, rfl⟩ :=
      (isStrategyProof_and_surjective_iff_exists_moulinScheme hab f).mp ⟨hf_sp, hf_onto⟩
    have hE_anon : FacilityLocation.IsAnonymous E.eval := by
      intro σ x
      have h := hf_anon σ (fun i => Preference.symmetric (x i))
      simpa only [ofMoulinScheme, Function.comp_def, Preference.symmetric_peak] using h
    obtain ⟨y, _, hy⟩ := E.exists_phantomMedian_of_isAnonymous hE_anon
    exact ⟨y, funext fun P => congrFun hy (fun i => (P i).peak)⟩
  · rintro ⟨y, rfl⟩
    have hEq : ofPhantomMedian y =
        ofMoulinScheme (MoulinScheme.ofPhantoms hab (y ∘ Tuple.sort y) (Tuple.monotone_sort y)) :=
      funext fun P => by
        rw [ofPhantomMedian, ofMoulinScheme, ← phantomMedian_eq_eval_ofPhantoms_sort hab y]
    refine ⟨hEq ▸ ofMoulinScheme_isStrategyProof _, hEq ▸ ofMoulinScheme_surjective _, ?_⟩
    intro σ P
    exact phantomMedian_isAnonymous y σ (fun i => (P i).peak)

/-- Every strategy-proof, surjective rule on ordinal single-peaked preferences is automatically
strongly group strategy-proof. This strengthening is proved here and is not stated in
[SchummerVohra2007], Theorem 10.4. -/
theorem isGroupStrategyProof_of_isStrategyProof_of_surjective {ι : Type*} [Finite ι] [Nonempty ι]
    {a b : ℝ} (hab : a ≤ b) {f : Rule ι a b}
    (hf_sp : f.IsStrategyProof) (hf_onto : Function.Surjective f) :
    f.IsGroupStrategyProof := by
  let _ := Fintype.ofFinite ι
  obtain ⟨E, rfl⟩ :=
    (isStrategyProof_and_surjective_iff_exists_moulinScheme hab f).mp ⟨hf_sp, hf_onto⟩
  exact ofMoulinScheme_isGroupStrategyProof E

end Characterization

/-! ### Individual rationality uniqueness (§10.2.2) -/

section IndividualRationality

variable {ι : Type*} [Fintype ι] {a b : ℝ}

/-- The minimum-peak `MoulinScheme`: `alpha ∅ = b` and `alpha S = a` for all nonempty `S`. -/
noncomputable def minPeakScheme [Nonempty ι] (hab : a ≤ b) : MoulinScheme ι a b where
  alpha S := by classical exact if S = ∅ then b else a
  mem_Icc S := by
    classical
    split_ifs
    · exact ⟨hab, le_rfl⟩
    · exact ⟨le_rfl, hab⟩
  antitone S T hST := by
    classical
    by_cases hT : T = ∅
    · subst hT
      rw [Finset.subset_empty.mp hST]
    · by_cases hS : S = ∅
      · simp only [hT, hS, ↓reduceIte, hab]
      · simp only [hT, hS, ↓reduceIte, le_rfl]
  boundary_empty := by classical simp only [↓reduceIte]
  boundary_univ := by
    classical
    simp only [Finset.univ_nonempty.ne_empty, ↓reduceIte]

/-- The maximum-peak `MoulinScheme`: `alpha Finset.univ = a` and `alpha S = b` for all proper
subsets `S ≠ Finset.univ`. -/
noncomputable def maxPeakScheme [Nonempty ι] (hab : a ≤ b) : MoulinScheme ι a b where
  alpha S := by classical exact if S = Finset.univ then a else b
  mem_Icc S := by
    classical
    split_ifs
    · exact ⟨le_rfl, hab⟩
    · exact ⟨hab, le_rfl⟩
  antitone S T hST := by
    classical
    by_cases hT : T = Finset.univ
    · by_cases hS : S = Finset.univ
      · simp only [hT, hS, ↓reduceIte, le_rfl]
      · simp only [hT, hS, ↓reduceIte, hab]
    · have hS : S ≠ Finset.univ := fun h => hT (Finset.eq_univ_iff_forall.mpr fun i =>
        hST (h ▸ Finset.mem_univ i))
      simp only [hT, hS, ↓reduceIte, le_rfl]
  boundary_empty := by
    classical
    simp only [Finset.univ_nonempty.ne_empty.symm, ↓reduceIte]
  boundary_univ := by classical simp only [↓reduceIte]

/-- `minPeakScheme` evaluates to the minimum reported peak. -/
theorem minPeakScheme_eval [Nonempty ι] (hab : a ≤ b) (x : ι → Set.Icc a b) :
    ((minPeakScheme (ι := ι) hab).eval x : ℝ) =
      Finset.univ.inf' Finset.univ_nonempty (fun i => (x i : ℝ)) := by
  classical
  set m : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun i => (x i : ℝ))
  have hm_mem : m ∈ Set.Icc a b := by
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    refine ⟨(Finset.le_inf'_iff _ _).mpr fun i _ => (x i).2.1,
      (Finset.inf'_le (fun i => (x i : ℝ)) (Finset.mem_univ i₀)).trans (x i₀).2.2⟩
  let mPt : Set.Icc a b := ⟨m, hm_mem⟩
  refine le_antisymm ?_ ?_
  · by_contra hgt
    have hlt := ((minPeakScheme (ι := ι) hab).lt_eval_iff x mPt).mp (lt_of_not_ge hgt)
    obtain ⟨i₀, _, hi₀⟩ :=
      Finset.exists_min_image Finset.univ (fun i => (x i : ℝ)) Finset.univ_nonempty
    have hmem : i₀ ∈ Finset.univ.filter fun i => (x i : ℝ) ≤ m := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, ?_⟩
      exact (Finset.le_inf'_iff _ _).mpr fun i hi => hi₀ i hi
    have hne : (Finset.univ.filter fun i => (x i : ℝ) ≤ m) ≠ ∅ :=
      Finset.nonempty_iff_ne_empty.mp ⟨i₀, hmem⟩
    have hα : (minPeakScheme (ι := ι) hab).alpha
        (Finset.univ.filter fun i => (x i : ℝ) ≤ m) = a := by
      change (if (Finset.univ.filter fun i => (x i : ℝ) ≤ m) = ∅ then b else a) = a
      simp only [hne, ↓reduceIte]
    rw [hα] at hlt
    exact hlt.not_ge hm_mem.1
  · obtain ⟨⟨i, hi⟩, _⟩ := eval_mem_peaks_bounds (minPeakScheme (ι := ι) hab) x
    exact (Finset.inf'_le (fun k => (x k : ℝ)) (Finset.mem_univ i)).trans hi

/-- `maxPeakScheme` evaluates to the maximum reported peak. -/
theorem maxPeakScheme_eval [Nonempty ι] (hab : a ≤ b) (x : ι → Set.Icc a b) :
    ((maxPeakScheme (ι := ι) hab).eval x : ℝ) =
      Finset.univ.sup' Finset.univ_nonempty (fun i => (x i : ℝ)) := by
  classical
  set m : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i => (x i : ℝ))
  have hm_mem : m ∈ Set.Icc a b := by
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    refine ⟨(x i₀).2.1.trans (Finset.le_sup' (fun i => (x i : ℝ)) (Finset.mem_univ i₀)),
      (Finset.sup'_le_iff _ _).mpr fun i _ => (x i).2.2⟩
  let mPt : Set.Icc a b := ⟨m, hm_mem⟩
  refine le_antisymm ?_ ?_
  · obtain ⟨_, ⟨j, hj⟩⟩ := eval_mem_peaks_bounds (maxPeakScheme (ι := ι) hab) x
    exact hj.trans (Finset.le_sup' (fun k => (x k : ℝ)) (Finset.mem_univ j))
  · by_contra hlt
    have hlt' := ((maxPeakScheme (ι := ι) hab).eval_lt_iff x mPt).mp (lt_of_not_ge hlt)
    obtain ⟨j₀, _, hj₀⟩ :=
      Finset.exists_max_image Finset.univ (fun i => (x i : ℝ)) Finset.univ_nonempty
    have hnotmem : j₀ ∉ Finset.univ.filter fun i => (x i : ℝ) < m := by
      intro hm
      have hlt_j : (x j₀ : ℝ) < m := (Finset.mem_filter.mp hm).2
      have hle_j : m ≤ (x j₀ : ℝ) := (Finset.sup'_le_iff _ _).mpr fun i hi => hj₀ i hi
      linarith
    have hne : (Finset.univ.filter fun i => (x i : ℝ) < m) ≠ Finset.univ := fun h =>
      hnotmem (h.symm ▸ Finset.mem_univ j₀)
    have hα : (maxPeakScheme (ι := ι) hab).alpha
        (Finset.univ.filter fun i => (x i : ℝ) < m) = b := by
      change (if (Finset.univ.filter fun i => (x i : ℝ) < m) = Finset.univ then a else b) = b
      simp only [hne, ↓reduceIte]
    rw [hα] at hlt'
    exact hlt'.not_ge hm_mem.2

private lemma ofMoulinScheme_eval_extreme [DecidableEq ι] (hab : a ≤ b)
    (E : MoulinScheme ι a b) (T : Finset ι) :
    (ofMoulinScheme E
      (fun i => if i ∈ Tᶜ then Preference.rightExtreme hab else Preference.leftExtreme hab) : ℝ) =
      E.alpha T := by
  have hpeak : (fun i =>
      ((if i ∈ Tᶜ then Preference.rightExtreme hab else Preference.leftExtreme hab) :
        Preference a b).peak) =
      fun i => if i ∈ Tᶜ then ⟨b, hab, le_rfl⟩ else ⟨a, le_rfl, hab⟩ := by
    funext i
    by_cases hi : i ∈ Tᶜ <;> simp only [hi, ↓reduceIte, Preference.rightExtreme_peak,
      Preference.leftExtreme_peak]
  change (E.eval _ : ℝ) = E.alpha T
  rw [hpeak]
  simpa only [compl_compl] using E.eval_extremeProfile Tᶜ

/-- **Public-good individual rationality uniqueness** ([SchummerVohra2007], §10.2.2, p. 252):
the minimum-peak rule (`ofMoulinScheme (minPeakScheme hab)`) is the unique strategy-proof,
surjective rule on `Set.Icc a b` that is individually rational with respect to the left endpoint
`a`. -/
theorem isStrategyProof_surjective_isIR_left_iff [Nonempty ι]
    (hab : a ≤ b) (f : Rule ι a b) :
    (f.IsStrategyProof ∧ Function.Surjective f ∧ f.IsIndividuallyRational ⟨a, le_rfl, hab⟩) ↔
      f = ofMoulinScheme (minPeakScheme hab) := by
  classical
  constructor
  · rintro ⟨hf_sp, hf_onto, hf_ir⟩
    obtain ⟨E, rfl⟩ :=
      (isStrategyProof_and_surjective_iff_exists_moulinScheme hab f).mp ⟨hf_sp, hf_onto⟩
    have hE : E = minPeakScheme hab := by
      cases E with
      | mk alpha mem_Icc antitone boundary_empty boundary_univ =>
        congr 1
        funext T
        by_cases hT : T = ∅
        · subst hT; simp only [boundary_empty, ↓reduceIte]
        · simp only [hT, ↓reduceIte]
          obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hT
          let P : Profile ι a b :=
            fun i => if i ∈ Tᶜ then Preference.rightExtreme hab else Preference.leftExtreme hab
          have hir := hf_ir P i₀
          have hi₀_not : i₀ ∉ Tᶜ := by simp only [Finset.mem_compl, not_not]; exact hi₀
          simp only [P, hi₀_not, ↓reduceIte, Preference.leftExtreme_atLeast_iff] at hir
          let E₀ : MoulinScheme ι a b := ⟨alpha, mem_Icc, antitone, boundary_empty, boundary_univ⟩
          have heval : (ofMoulinScheme E₀ P : ℝ) = alpha T :=
            ofMoulinScheme_eval_extreme hab E₀ T
          rw [heval] at hir
          exact le_antisymm hir (mem_Icc T).1
    rw [hE]
  · rintro rfl
    refine ⟨ofMoulinScheme_isStrategyProof _, ofMoulinScheme_surjective _, fun P i => ?_⟩
    have hle : ((ofMoulinScheme (minPeakScheme hab) P : Set.Icc a b) : ℝ) ≤ (P i).peak := by
      rw [ofMoulinScheme, minPeakScheme_eval]
      exact Finset.inf'_le (fun k => ((P k).peak : ℝ)) (Finset.mem_univ i)
    exact (P i).atLeast_of_between_left (ofMoulinScheme (minPeakScheme hab) P).2.1 hle

/-- Symmetric right-endpoint counterpart to `isStrategyProof_surjective_isIR_left_iff` (a library
addition not stated in [SchummerVohra2007], §10.2.2): the maximum-peak rule
(`ofMoulinScheme (maxPeakScheme hab)`) is the unique strategy-proof, surjective rule on
`Set.Icc a b` that is individually rational with respect to the right endpoint `b`. -/
theorem isStrategyProof_surjective_isIR_right_iff [Nonempty ι]
    (hab : a ≤ b) (f : Rule ι a b) :
    (f.IsStrategyProof ∧ Function.Surjective f ∧ f.IsIndividuallyRational ⟨b, hab, le_rfl⟩) ↔
      f = ofMoulinScheme (maxPeakScheme hab) := by
  classical
  constructor
  · rintro ⟨hf_sp, hf_onto, hf_ir⟩
    obtain ⟨E, rfl⟩ :=
      (isStrategyProof_and_surjective_iff_exists_moulinScheme hab f).mp ⟨hf_sp, hf_onto⟩
    have hE : E = maxPeakScheme hab := by
      cases E with
      | mk alpha mem_Icc antitone boundary_empty boundary_univ =>
        congr 1
        funext T
        by_cases hT : T = Finset.univ
        · subst hT; simp only [boundary_univ, ↓reduceIte]
        · simp only [hT, ↓reduceIte]
          have hTc_ne : Tᶜ.Nonempty := by
            rw [Finset.nonempty_iff_ne_empty]
            intro h
            apply hT
            ext i
            simp only [Finset.mem_univ, iff_true]
            by_contra hi
            have : i ∈ Tᶜ := Finset.mem_compl.mpr hi
            rw [h] at this
            exact Finset.notMem_empty i this
          obtain ⟨i₀, hi₀⟩ := hTc_ne
          let P : Profile ι a b :=
            fun i => if i ∈ Tᶜ then Preference.rightExtreme hab else Preference.leftExtreme hab
          have hir := hf_ir P i₀
          simp only [P, hi₀, ↓reduceIte, Preference.rightExtreme_atLeast_iff] at hir
          let E₀ : MoulinScheme ι a b := ⟨alpha, mem_Icc, antitone, boundary_empty, boundary_univ⟩
          have heval : (ofMoulinScheme E₀ P : ℝ) = alpha T :=
            ofMoulinScheme_eval_extreme hab E₀ T
          rw [heval] at hir
          exact le_antisymm (mem_Icc T).2 hir
    rw [hE]
  · rintro rfl
    refine ⟨ofMoulinScheme_isStrategyProof _, ofMoulinScheme_surjective _, fun P i => ?_⟩
    have hge : ((P i).peak : ℝ) ≤ ofMoulinScheme (maxPeakScheme hab) P := by
      rw [ofMoulinScheme, maxPeakScheme_eval]
      exact Finset.le_sup' (fun k => ((P k).peak : ℝ)) (Finset.mem_univ i)
    exact (P i).atLeast_of_between_right hge (ofMoulinScheme (maxPeakScheme hab) P).2.2

end IndividualRationality

/-! ### Exercise 10.1: Lemma 10.1 on symmetric single-peaked preferences -/

section SymmetricDomain

variable {ι : Type*} [Finite ι] [Nonempty ι] {a b : ℝ}

/-- **Exercise 10.1** ([SchummerVohra2007], p. 264): even when preferences are restricted to the
smaller domain of symmetric (Euclidean-distance) single-peaked preferences on `Set.Icc a b`, a
strategy-proof deterministic rule is surjective if and only if it is Pareto-optimal (no point is
strictly closer to every agent's peak). -/
theorem symmetric_surjective_iff_paretoOptimal [DecidableEq ι]
    [MeasurableSpace (Set.Icc a b)] [OpensMeasurableSpace (Set.Icc a b)]
    (hab : a ≤ b) {f : (ι → Set.Icc a b) → Set.Icc a b}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof) :
    Function.Surjective f ↔
      (∀ (x : ι → Set.Icc a b) (y : Set.Icc a b), ¬ ∀ i, dist (x i) y < dist (x i) (f x)) := by
  let _ := Fintype.ofFinite ι
  constructor
  · intro hf_onto x y hstrict
    obtain ⟨E, rfl⟩ :=
      (FacilityLocation.isStrategyProof_and_surjective_iff_exists_moulinScheme hab f).mp
        ⟨hf_sp, hf_onto⟩
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := eval_mem_peaks_bounds E x
    rcases lt_trichotomy (y : ℝ) (E.eval x) with hlt | heq | hgt
    · have hdj := hstrict j
      rw [Subtype.dist_eq, Real.dist_eq, Subtype.dist_eq, Real.dist_eq,
        abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at hdj
      linarith
    · obtain ⟨i₀⟩ := ‹Nonempty ι›
      have h0 := hstrict i₀
      rw [Subtype.ext heq] at h0
      exact lt_irrefl _ h0
    · have hdi := hstrict i
      rw [Subtype.dist_eq, Real.dist_eq, Subtype.dist_eq, Real.dist_eq,
        abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at hdi
      linarith
  · intro hPO y
    refine ⟨fun _ => y, ?_⟩
    by_contra hne
    refine hPO (fun _ => y) y fun _ => ?_
    rw [dist_self]
    exact dist_pos.mpr (Ne.symm hne)

/-- On symmetric single-peaked preferences over `Set.Icc a b`, strategy-proofness also makes
surjectivity equivalent to unanimity ([SchummerVohra2007], Exercise 10.1, p. 264). -/
theorem symmetric_surjective_iff_unanimous [DecidableEq ι]
    [MeasurableSpace (Set.Icc a b)] [OpensMeasurableSpace (Set.Icc a b)]
    (hab : a ≤ b) {f : (ι → Set.Icc a b) → Set.Icc a b}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof) :
    Function.Surjective f ↔ ∀ y : Set.Icc a b, f (fun _ => y) = y := by
  let _ := Fintype.ofFinite ι
  constructor
  · intro hf_onto y
    obtain ⟨E, rfl⟩ :=
      (FacilityLocation.isStrategyProof_and_surjective_iff_exists_moulinScheme hab f).mp
        ⟨hf_sp, hf_onto⟩
    exact E.eval_const y
  · intro hU y
    exact ⟨fun _ => y, hU y⟩

end SymmetricDomain

end Cslib.GameTheory.SocialChoice.SinglePeaked
