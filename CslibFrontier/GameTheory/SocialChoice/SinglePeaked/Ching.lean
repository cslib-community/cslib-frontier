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
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · rw [maxMinEval, Finset.lt_fold_max] at hy
    rcases hy with hy_a | ⟨S, _, hS⟩
    · linarith [y.property.1]
    · refine (lt_of_lt_of_le hS (min_le_left _ _)).trans_le (E.antitone fun i hi => ?_)
      rw [Finset.mem_compl]
      intro hiS
      exact (((Finset.lt_fold_min _).mp (lt_of_lt_of_le hS (min_le_right _ _))).2 i hiS).not_ge
        (Finset.mem_filter.mp hi).2
  · have hfold : (y : ℝ) < Sleᶜ.fold min b fun i => (x i : ℝ) := by
      rw [Finset.lt_fold_min]
      refine ⟨hy.trans_le (E.mem_Icc Sle).2, fun i hi => ?_⟩
      simpa only [Sle, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_le]
        using hi
    exact (lt_min (by rwa [compl_compl]) hfold).trans_le (le_maxMinEval_branch E x Sleᶜ)

/-- `MoulinScheme.eval` coincides pointwise with the dual `max_S min{β_S, p_i : i ∈ S}` formula
of [SchummerVohra2007] (Definition 10.3, p. 250) with `β_S = E.alpha Sᶜ`. -/
theorem eval_eq_maxMinEval (E : MoulinScheme ι a b) (x : ι → Set.Icc a b) :
    (E.eval x : ℝ) = maxMinEval E x := by
  let m : Set.Icc a b := ⟨maxMinEval E x, maxMinEval_mem_Icc E x⟩
  refine le_antisymm (not_lt.mp fun hlt => ?_) (not_lt.mp fun hlt => ?_)
  · exact lt_irrefl (m : ℝ) ((lt_maxMinEval_iff E x m).mpr ((E.lt_eval_iff x m).mp hlt))
  · exact lt_irrefl (E.eval x : ℝ)
      ((E.lt_eval_iff x (E.eval x)).mpr ((lt_maxMinEval_iff E x (E.eval x)).mp hlt))

/-- A `MoulinScheme` always evaluates within the convex hull of the reported peaks. -/
theorem eval_mem_peaks_bounds [Nonempty ι] (E : MoulinScheme ι a b) (x : ι → Set.Icc a b) :
    (∃ i : ι, (x i : ℝ) ≤ E.eval x) ∧ (∃ j : ι, (E.eval x : ℝ) ≤ x j) := by
  obtain ⟨i, hi⟩ := Finite.exists_min (fun k => (x k : ℝ))
  obtain ⟨j, hj⟩ := Finite.exists_max (fun k => (x k : ℝ))
  exact ⟨⟨i, by simpa only [E.eval_const] using E.eval_mono hi⟩,
    ⟨j, by simpa only [E.eval_const] using E.eval_mono hj⟩⟩

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
  rintro P Q A hPQ ⟨hle, i₀, _, hlt⟩
  let p : ι → Set.Icc a b := fun i => (P i).peak
  let q : ι → Set.Icc a b := fun i => (Q i).peak
  let y : Set.Icc a b := E.eval p
  let y' : Set.Icc a b := E.eval q
  have hne : (y : ℝ) ≠ y' := fun heq => by
    have hy : ofMoulinScheme E P = ofMoulinScheme E Q := Subtype.ext heq
    exact (P i₀).prefers_irrefl _ (hy ▸ hlt)
  rcases lt_or_gt_of_ne hne with hy_lt | hy'_lt
  · have hsub : (Finset.univ.filter fun i => (p i : ℝ) ≤ y) ⊆
        (Finset.univ.filter fun i => (q i : ℝ) ≤ y) := fun i hi => by
      have hpi : (p i : ℝ) ≤ y := (Finset.mem_filter.mp hi).2
      have hiA : i ∉ A := fun h => (P i).prefers_of_between_right hpi hy_lt (hle i h)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, by simpa only [p, q, hPQ i hiA] using hpi⟩
    exact lt_irrefl (y : ℝ)
      ((E.lt_eval_iff p y).mpr (((E.lt_eval_iff q y).mp hy_lt).trans_le (E.antitone hsub)))
  · have hsub : (Finset.univ.filter fun i => (q i : ℝ) < y) ⊆
        (Finset.univ.filter fun i => (p i : ℝ) < y) := fun i hi => by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
      by_cases hiA : i ∈ A
      · exact not_le.mp fun hge => (P i).prefers_of_between_left hy'_lt hge (hle i hiA)
      · simpa only [p, q, hPQ i hiA] using (Finset.mem_filter.mp hi).2
    exact lt_irrefl (y : ℝ)
      ((E.eval_lt_iff p y).mpr ((E.antitone hsub).trans_lt ((E.eval_lt_iff q y).mp hy'_lt)))

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
  obtain ⟨i₀, _, hi₀⟩ :=
    Finset.exists_min_image Finset.univ (fun i => (x i : ℝ)) Finset.univ_nonempty
  have hm_mem : m ∈ Set.Icc a b :=
    ⟨(Finset.le_inf'_iff _ _).mpr fun i _ => (x i).property.1,
      (Finset.inf'_le (fun i => (x i : ℝ)) (Finset.mem_univ i₀)).trans (x i₀).property.2⟩
  refine le_antisymm (not_lt.mp fun hlt => ?_) ?_
  · have hlt' := ((minPeakScheme (ι := ι) hab).lt_eval_iff x ⟨m, hm_mem⟩).mp hlt
    have hne : (Finset.univ.filter fun i => (x i : ℝ) ≤ m) ≠ ∅ :=
      Finset.ne_empty_iff_nonempty.mpr
        ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, (Finset.le_inf'_iff _ _).mpr hi₀⟩⟩
    simp only [minPeakScheme, hne, ↓reduceIte] at hlt'
    exact hlt'.not_ge hm_mem.1
  · obtain ⟨⟨i, hi⟩, _⟩ := eval_mem_peaks_bounds (minPeakScheme (ι := ι) hab) x
    exact (Finset.inf'_le (fun k => (x k : ℝ)) (Finset.mem_univ i)).trans hi

/-- `maxPeakScheme` evaluates to the maximum reported peak. -/
theorem maxPeakScheme_eval [Nonempty ι] (hab : a ≤ b) (x : ι → Set.Icc a b) :
    ((maxPeakScheme (ι := ι) hab).eval x : ℝ) =
      Finset.univ.sup' Finset.univ_nonempty (fun i => (x i : ℝ)) := by
  classical
  set m : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i => (x i : ℝ))
  obtain ⟨j₀, _, hj₀⟩ :=
    Finset.exists_max_image Finset.univ (fun i => (x i : ℝ)) Finset.univ_nonempty
  have hm_mem : m ∈ Set.Icc a b :=
    ⟨(x j₀).property.1.trans (Finset.le_sup' (fun i => (x i : ℝ)) (Finset.mem_univ j₀)),
      (Finset.sup'_le_iff _ _).mpr fun i _ => (x i).property.2⟩
  refine le_antisymm ?_ (not_lt.mp fun hlt => ?_)
  · obtain ⟨_, ⟨j, hj⟩⟩ := eval_mem_peaks_bounds (maxPeakScheme (ι := ι) hab) x
    exact hj.trans (Finset.le_sup' (fun k => (x k : ℝ)) (Finset.mem_univ j))
  · have hlt' := ((maxPeakScheme (ι := ι) hab).eval_lt_iff x ⟨m, hm_mem⟩).mp hlt
    have hne : (Finset.univ.filter fun i => (x i : ℝ) < m) ≠ Finset.univ := fun h => by
      have hj_mem : j₀ ∈ Finset.univ.filter fun i => (x i : ℝ) < m := h.symm ▸ Finset.mem_univ j₀
      exact ((Finset.sup'_le_iff _ _).mpr hj₀).not_gt (Finset.mem_filter.mp hj_mem).2
    simp only [maxPeakScheme, hne, ↓reduceIte] at hlt'
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
  refine ⟨?_, ?_⟩
  · rintro ⟨hf_sp, hf_onto, hf_ir⟩
    obtain ⟨E, rfl⟩ :=
      (isStrategyProof_and_surjective_iff_exists_moulinScheme hab f).mp ⟨hf_sp, hf_onto⟩
    congr 1
    cases E with
    | mk alpha mem_Icc antitone boundary_empty boundary_univ =>
      congr 1
      funext T
      by_cases hT : T = ∅
      · subst hT; simp only [boundary_empty, ↓reduceIte]
      · simp only [hT, ↓reduceIte]
        obtain ⟨i₀, hi₀⟩ := Finset.ne_empty_iff_nonempty.mp hT
        have hi₀' : i₀ ∉ Tᶜ := Finset.notMem_compl.mpr hi₀
        let E₀ : MoulinScheme ι a b := ⟨alpha, mem_Icc, antitone, boundary_empty, boundary_univ⟩
        have hir := hf_ir
          (fun i => if i ∈ Tᶜ then Preference.rightExtreme hab else Preference.leftExtreme hab) i₀
        simp only [hi₀', ↓reduceIte, Preference.leftExtreme_atLeast_iff] at hir
        rw [ofMoulinScheme_eval_extreme hab E₀ T] at hir
        exact le_antisymm hir (mem_Icc T).1
  · rintro rfl
    refine ⟨ofMoulinScheme_isStrategyProof _, ofMoulinScheme_surjective _, fun P i => ?_⟩
    refine (P i).atLeast_of_between_left (ofMoulinScheme (minPeakScheme hab) P).property.1 ?_
    rw [ofMoulinScheme, minPeakScheme_eval]
    exact Finset.inf'_le (fun k => ((P k).peak : ℝ)) (Finset.mem_univ i)

/-- Symmetric right-endpoint counterpart to `isStrategyProof_surjective_isIR_left_iff` (a library
addition not stated in [SchummerVohra2007], §10.2.2): the maximum-peak rule
(`ofMoulinScheme (maxPeakScheme hab)`) is the unique strategy-proof, surjective rule on
`Set.Icc a b` that is individually rational with respect to the right endpoint `b`. -/
theorem isStrategyProof_surjective_isIR_right_iff [Nonempty ι]
    (hab : a ≤ b) (f : Rule ι a b) :
    (f.IsStrategyProof ∧ Function.Surjective f ∧ f.IsIndividuallyRational ⟨b, hab, le_rfl⟩) ↔
      f = ofMoulinScheme (maxPeakScheme hab) := by
  classical
  refine ⟨?_, ?_⟩
  · rintro ⟨hf_sp, hf_onto, hf_ir⟩
    obtain ⟨E, rfl⟩ :=
      (isStrategyProof_and_surjective_iff_exists_moulinScheme hab f).mp ⟨hf_sp, hf_onto⟩
    congr 1
    cases E with
    | mk alpha mem_Icc antitone boundary_empty boundary_univ =>
      congr 1
      funext T
      by_cases hT : T = Finset.univ
      · subst hT; simp only [boundary_univ, ↓reduceIte]
      · simp only [hT, ↓reduceIte]
        obtain ⟨i₀, hi₀⟩ := Finset.ne_empty_iff_nonempty.mp fun (h : Tᶜ = ∅) =>
          hT (by simpa only [compl_compl, Finset.compl_empty] using congrArg compl h)
        let E₀ : MoulinScheme ι a b := ⟨alpha, mem_Icc, antitone, boundary_empty, boundary_univ⟩
        have hir := hf_ir
          (fun i => if i ∈ Tᶜ then Preference.rightExtreme hab else Preference.leftExtreme hab) i₀
        simp only [hi₀, ↓reduceIte, Preference.rightExtreme_atLeast_iff] at hir
        rw [ofMoulinScheme_eval_extreme hab E₀ T] at hir
        exact le_antisymm (mem_Icc T).2 hir
  · rintro rfl
    refine ⟨ofMoulinScheme_isStrategyProof _, ofMoulinScheme_surjective _, fun P i => ?_⟩
    refine (P i).atLeast_of_between_right ?_ (ofMoulinScheme (maxPeakScheme hab) P).property.2
    rw [ofMoulinScheme, maxPeakScheme_eval]
    exact Finset.le_sup' (fun k => ((P k).peak : ℝ)) (Finset.mem_univ i)

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
