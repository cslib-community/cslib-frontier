/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Basic
import CslibFrontier.Foundations.Data.Fintype.UpdateInduction
import Mathlib.Data.Finset.Fold

/-!
# Strategyproof facility location on closed real intervals

This module formalizes Moulin's characterization ([Moulin1980]) of deterministic, surjective,
strategyproof facility-location mechanisms on a closed interval `[a, b] ⊆ ℝ` (`Set.Icc a b`), along
with transfer lemmas for isometric intervals in an arbitrary metric space.

## Main definitions

* `Cslib.GameTheory.FacilityLocation.MoulinScheme`: a generalized median voter scheme on
  `Set.Icc a b` for a finite nonempty agent set `ι`, determined by an antitone family of phantom
  parameters `alpha : Finset ι → ℝ` valued in `Set.Icc a b` with `alpha ∅ = b` and
  `alpha Finset.univ = a`.
* `Cslib.GameTheory.FacilityLocation.MoulinScheme.eval`: evaluates the generalized median rule
  `min_{S} max(alpha S, max(a, sup_{i ∈ S} x i))`.

## Main results

* `Cslib.GameTheory.FacilityLocation.MoulinScheme.eval_isGroupStrategyProof`: every Moulin scheme
  defines a group-strategyproof deterministic mechanism.
* `Cslib.GameTheory.FacilityLocation.isStrategyProof_and_surjective_iff_exists_moulinScheme`:
  a deterministic rule on `Set.Icc a b` is surjective and strategyproof if and only if it is the
  evaluation map of a `MoulinScheme`.
* `Cslib.GameTheory.FacilityLocation.moulinScheme_of_isometry`: transfers any strategyproof
  mechanism preserving and surjecting onto an isometric copy of `[0, d]` in a metric space to a
  `MoulinScheme ι 0 d`.
* `Cslib.GameTheory.FacilityLocation.moulinScheme_finTwo_eq`: explicit two-agent formula
  `min (max α₀ x₀) (min (max α₁ x₁) (max x₀ x₁))`.

## References

* [Moulin1980] H. Moulin, "On strategy-proofness and single peakedness", Public Choice 35 (1980).
-/

public section

namespace Cslib.GameTheory.FacilityLocation

section Moulin

private noncomputable def finMax {ι : Type*} (a : ℝ) (S : Finset ι) (g : ι → ℝ) : ℝ :=
  S.fold max a g

private noncomputable def finMin {ι : Type*} (b : ℝ) (T : Finset (Finset ι))
    (g : Finset ι → ℝ) : ℝ :=
  T.fold min b g

private lemma le_finMax {ι : Type*} (a : ℝ) (S : Finset ι) (g : ι → ℝ) : a ≤ finMax a S g :=
  (Finset.le_fold_max a).mpr (Or.inl le_rfl)

private lemma mem_le_finMax {ι : Type*} (a : ℝ) {S : Finset ι} (g : ι → ℝ) {i : ι}
    (hi : i ∈ S) : g i ≤ finMax a S g :=
  (Finset.le_fold_max (g i)).mpr (Or.inr ⟨i, hi, le_rfl⟩)

private lemma finMax_le {ι : Type*} {a c : ℝ} {S : Finset ι} {g : ι → ℝ}
    (ha : a ≤ c) (hg : ∀ i ∈ S, g i ≤ c) : finMax a S g ≤ c :=
  (Finset.fold_max_le c).mpr ⟨ha, hg⟩

private lemma finMax_lt {ι : Type*} {a c : ℝ} {S : Finset ι} {g : ι → ℝ}
    (ha : a < c) (hg : ∀ i ∈ S, g i < c) : finMax a S g < c :=
  (Finset.fold_max_lt c).mpr ⟨ha, hg⟩

private lemma finMax_mono_fun {ι : Type*} (a : ℝ) (S : Finset ι) {g₁ g₂ : ι → ℝ}
    (hg : ∀ i ∈ S, g₁ i ≤ g₂ i) : finMax a S g₁ ≤ finMax a S g₂ :=
  finMax_le (le_finMax a S g₂) fun i hi => (hg i hi).trans (mem_le_finMax a g₂ hi)

private lemma finMax_eq_of_eqOn {ι : Type*} (a : ℝ) (S : Finset ι) {g₁ g₂ : ι → ℝ}
    (hg : ∀ i ∈ S, g₁ i = g₂ i) : finMax a S g₁ = finMax a S g₂ :=
  Finset.fold_congr hg

private lemma finMin_le {ι : Type*} (b : ℝ) {T : Finset (Finset ι)} (g : Finset ι → ℝ)
    {S : Finset ι} (hS : S ∈ T) : finMin b T g ≤ g S :=
  (Finset.fold_min_le (g S)).mpr (Or.inr ⟨S, hS, le_rfl⟩)

private lemma le_finMin {ι : Type*} {b c : ℝ} {T : Finset (Finset ι)} {g : Finset ι → ℝ}
    (hb : c ≤ b) (hg : ∀ S ∈ T, c ≤ g S) : c ≤ finMin b T g :=
  (Finset.le_fold_min c).mpr ⟨hb, hg⟩

private lemma finMin_le_base {ι : Type*} (b : ℝ) (T : Finset (Finset ι)) (g : Finset ι → ℝ) :
    finMin b T g ≤ b :=
  (Finset.fold_min_le b).mpr (Or.inl le_rfl)

private lemma exists_finMin_eq {ι : Type*} {b : ℝ} {T : Finset (Finset ι)} {g : Finset ι → ℝ}
    (hT : T.Nonempty) (hbd : ∃ S ∈ T, g S ≤ b) :
    ∃ S ∈ T, g S = finMin b T g := by
  classical
  obtain ⟨S₀, hS₀_mem, hS₀_le⟩ := T.exists_min_image g hT
  refine ⟨S₀, hS₀_mem, le_antisymm ?_ (finMin_le b g hS₀_mem)⟩
  obtain ⟨S₁, hS₁_mem, hS₁_le⟩ := hbd
  exact le_finMin ((hS₀_le S₁ hS₁_mem).trans hS₁_le) fun S hS => hS₀_le S hS

private lemma finMin_eq_of_eqOn {ι : Type*} (b : ℝ) {T : Finset (Finset ι)}
    {g₁ g₂ : Finset ι → ℝ} (hg : ∀ S ∈ T, g₁ S = g₂ S) : finMin b T g₁ = finMin b T g₂ :=
  Finset.fold_congr hg

private lemma finMin_union {ι : Type*} [DecidableEq ι] (b : ℝ) (T₁ T₂ : Finset (Finset ι))
    (g : Finset ι → ℝ) :
    finMin b (T₁ ∪ T₂) g = min (finMin b T₁ g) (finMin b T₂ g) := by
  refine le_antisymm (le_min ?_ ?_) (le_finMin (min_le_of_left_le (finMin_le_base b _ _)) ?_)
  · exact le_finMin (finMin_le_base b _ _) fun S hS => finMin_le b g (Finset.mem_union_left T₂ hS)
  · exact le_finMin (finMin_le_base b _ _) fun S hS => finMin_le b g (Finset.mem_union_right T₁ hS)
  · intro S hS
    rcases Finset.mem_union.mp hS with h | h
    · exact min_le_of_left_le (finMin_le b g h)
    · exact min_le_of_right_le (finMin_le b g h)

private lemma finMin_max_right {ι : Type*} (b : ℝ) (T : Finset (Finset ι)) (g : Finset ι → ℝ)
    {t : ℝ} (ht : t ≤ b) :
    finMin b T (fun S => max (g S) t) = max (finMin b T g) t := by
  classical
  dsimp only [finMin]
  induction T using Finset.induction with
  | empty => simp [ht]
  | insert U T hU ih =>
    rw [Finset.fold_insert hU, Finset.fold_insert hU, ih, max_min_distrib_right]

/-- A **Moulin generalized median voter scheme** on `Set.Icc a b` for a finite nonempty agent
type `ι`: an antitone family of phantom thresholds `alpha : Finset ι → ℝ` taking values in
`Set.Icc a b` with boundary conditions `alpha ∅ = b` and `alpha Finset.univ = a`. -/
structure MoulinScheme (ι : Type*) [Fintype ι] (a b : ℝ) where
  /-- Coalition phantom parameters `α_S ∈ [a, b]`. -/
  alpha : Finset ι → ℝ
  /-- Every phantom parameter lies in `[a, b]`. -/
  mem_Icc : ∀ S : Finset ι, alpha S ∈ Set.Icc a b
  /-- Larger coalitions receive weakly smaller phantom thresholds. -/
  antitone : Antitone alpha
  /-- Empty coalition takes the upper endpoint `b`. -/
  boundary_empty : alpha ∅ = b
  /-- Grand coalition takes the lower endpoint `a`. -/
  boundary_univ : alpha Finset.univ = a

namespace MoulinScheme

section Eval

variable {ι : Type*} [Fintype ι] {a b : ℝ} (E : MoulinScheme ι a b)

private noncomputable def evalVal (x : ι → Set.Icc a b) : ℝ :=
  finMin b Finset.univ fun S => max (E.alpha S) (finMax a S fun i => (x i : ℝ))

private lemma evalVal_mem_Icc (x : ι → Set.Icc a b) : E.evalVal x ∈ Set.Icc a b :=
  ⟨le_finMin ((E.mem_Icc Finset.univ).1.trans (E.mem_Icc Finset.univ).2) fun S _ =>
    le_max_of_le_left (E.mem_Icc S).1, finMin_le_base b Finset.univ _⟩

/-- Evaluates a `MoulinScheme` on an agent profile `x : ι → Set.Icc a b`, returning
`min_{S} max(α_S, max(a, sup_{i ∈ S} x_i)) ∈ Set.Icc a b`. -/
noncomputable def eval (x : ι → Set.Icc a b) : Set.Icc a b :=
  ⟨E.evalVal x, E.evalVal_mem_Icc x⟩

@[simp]
private theorem eval_coe (x : ι → Set.Icc a b) : (E.eval x : ℝ) = E.evalVal x := rfl

private lemma eval_le_branch (x : ι → Set.Icc a b) (S : Finset ι) :
    (E.eval x : ℝ) ≤ max (E.alpha S) (finMax a S fun i => (x i : ℝ)) :=
  finMin_le b (T := Finset.univ)
    (fun T => max (E.alpha T) (finMax a T fun i => (x i : ℝ))) (Finset.mem_univ S)

private lemma exists_eval_witness (x : ι → Set.Icc a b) :
    ∃ S : Finset ι, max (E.alpha S) (finMax a S fun i => (x i : ℝ)) = (E.eval x : ℝ) := by
  obtain ⟨S, _, hS⟩ := exists_finMin_eq (b := b) (T := Finset.univ)
    (g := fun S => max (E.alpha S) (finMax a S fun i => (x i : ℝ))) Finset.univ_nonempty
    ⟨∅, Finset.mem_univ _, by
      have ha : a ≤ b := (E.mem_Icc ∅).1.trans (E.mem_Icc ∅).2
      rw [E.boundary_empty]; simp [finMax, ha]⟩
  exact ⟨S, hS⟩

theorem eval_const [Nonempty ι] (y : Set.Icc a b) : E.eval (fun _ => y) = y := by
  ext
  refine le_antisymm ?_ ?_
  · have hle := E.eval_le_branch (fun _ => y) Finset.univ
    have hmax : (finMax a Finset.univ fun _ : ι => (y : ℝ)) = y := by
      obtain ⟨i₀⟩ := ‹Nonempty ι›
      exact le_antisymm (finMax_le y.2.1 fun _ _ => le_rfl)
        (mem_le_finMax a (fun _ => (y : ℝ)) (Finset.mem_univ i₀))
    rwa [E.boundary_univ, hmax, max_eq_right y.2.1] at hle
  · refine le_finMin y.2.2 fun S _ => ?_
    rcases eq_or_ne S ∅ with rfl | hS
    · rw [E.boundary_empty]; exact le_max_of_le_left y.2.2
    · obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      exact le_max_of_le_right (mem_le_finMax a (fun _ => (y : ℝ)) hi₀)

theorem eval_surjective [Nonempty ι] : Function.Surjective E.eval :=
  fun y => ⟨fun _ => y, E.eval_const y⟩

theorem eval_mono {x z : ι → Set.Icc a b} (hxz : ∀ i, (x i : ℝ) ≤ (z i : ℝ)) :
    (E.eval x : ℝ) ≤ E.eval z := by
  obtain ⟨S₀, hS₀⟩ := E.exists_eval_witness z
  exact (E.eval_le_branch x S₀).trans <|
    (max_le (le_max_left _ _) (le_max_of_le_right (finMax_mono_fun a S₀ fun i _ => hxz i))).trans_eq
      hS₀

theorem lt_eval_iff (x : ι → Set.Icc a b) (y : Set.Icc a b) :
    (y : ℝ) < E.eval x ↔ (y : ℝ) < E.alpha (Finset.univ.filter fun i => (x i : ℝ) ≤ y) := by
  classical
  let Sle : Finset ι := Finset.univ.filter fun i => (x i : ℝ) ≤ y
  constructor
  · intro hy
    have hmax : (finMax a Sle fun i => (x i : ℝ)) ≤ y :=
      finMax_le y.2.1 fun i hi => (Finset.mem_filter.mp hi).2
    exact (lt_max_iff.mp (hy.trans_le (E.eval_le_branch x Sle))).resolve_right (not_lt.mpr hmax)
  · intro hy
    obtain ⟨S₀, hS₀⟩ := E.exists_eval_witness x
    rw [← hS₀]
    by_cases hsub : S₀ ⊆ Sle
    · exact lt_of_lt_of_le hy ((E.antitone hsub).trans (le_max_left _ _))
    · obtain ⟨i, hiS₀, hi_not⟩ := Finset.not_subset.mp hsub
      have hi_gt : (y : ℝ) < x i :=
        by_contra fun hle => hi_not (Finset.mem_filter.mpr ⟨Finset.mem_univ i, not_lt.mp hle⟩)
      exact lt_max_of_lt_right (hi_gt.trans_le (mem_le_finMax a (fun j => (x j : ℝ)) hiS₀))

theorem eval_lt_iff (x : ι → Set.Icc a b) (y : Set.Icc a b) :
    (E.eval x : ℝ) < y ↔ E.alpha (Finset.univ.filter fun i => (x i : ℝ) < y) < y := by
  classical
  let Slt : Finset ι := Finset.univ.filter fun i => (x i : ℝ) < y
  constructor
  · intro hy
    obtain ⟨S₀, hS₀⟩ := E.exists_eval_witness x
    rw [← hS₀] at hy
    have hsub : S₀ ⊆ Slt := fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ i,
      (mem_le_finMax a (fun j => (x j : ℝ)) hi).trans_lt ((le_max_right _ _).trans_lt hy)⟩
    exact (E.antitone hsub).trans_lt ((le_max_left _ _).trans_lt hy)
  · intro hy
    exact (E.eval_le_branch x Slt).trans_lt <|
      max_lt hy (finMax_lt ((E.mem_Icc Slt).1.trans_lt hy) fun i hi => (Finset.mem_filter.mp hi).2)

theorem eval_isGroupStrategyProof [DecidableEq ι] [MeasurableSpace (Set.Icc a b)]
    [OpensMeasurableSpace (Set.Icc a b)] :
    (Mechanism.deterministic E.eval).IsGroupStrategyProof := by
  rw [Mechanism.isGroupStrategyProof_deterministic_iff]
  rintro x z A ⟨hle, i₀, _, hlt⟩
  let y : ℝ := (E.eval x : ℝ)
  let y' : ℝ := (E.eval (A.piecewise z x) : ℝ)
  have hne : y ≠ y' := fun heq => hlt.ne (by rw [Subtype.ext heq])
  have hdist_le : ∀ i ∈ A, |y' - (x i : ℝ)| ≤ |y - (x i : ℝ)| := fun i hi => by
    simpa [Subtype.dist_eq, Real.dist_eq, abs_sub_comm, y, y'] using hle i hi
  rcases lt_or_gt_of_ne hne with hy_lt | hy'_lt
  · have hA_gt (i : ι) (hi : i ∈ A) : y < (x i : ℝ) := by nlinarith [sq_le_sq.mpr (hdist_le i hi)]
    obtain ⟨S₀, hS₀⟩ := E.exists_eval_witness x
    have hdisj : ∀ j ∈ S₀, j ∉ A := fun j hjS hjA => (hA_gt j hjA).not_ge <|
      (le_max_of_le_right (mem_le_finMax a (fun k => (x k : ℝ)) hjS)).trans_eq hS₀
    have hfin_eq : (finMax a S₀ fun j => ((A.piecewise z x j : Set.Icc a b) : ℝ)) =
        finMax a S₀ fun j => (x j : ℝ) :=
      finMax_eq_of_eqOn a S₀ fun j hj => by simp [Finset.piecewise_eq_of_notMem _ _ _ (hdisj j hj)]
    exact hy_lt.not_ge ((E.eval_le_branch (A.piecewise z x) S₀).trans_eq (by rw [hfin_eq, hS₀]))
  · have hA_lt (i : ι) (hi : i ∈ A) : (x i : ℝ) < y := by nlinarith [sq_le_sq.mpr (hdist_le i hi)]
    obtain ⟨S₁, hS₁⟩ := E.exists_eval_witness (A.piecewise z x)
    have hα : E.alpha (S₁ ∪ A) < y := (E.antitone Finset.subset_union_left).trans_lt <|
      ((le_max_left _ _).trans_eq hS₁).trans_lt hy'_lt
    have hmem_lt : ∀ j ∈ S₁ ∪ A, (x j : ℝ) < y := fun j hj => by
      by_cases hjA : j ∈ A
      · exact hA_lt j hjA
      · simpa [Finset.piecewise_eq_of_notMem _ _ _ hjA] using
          ((le_max_of_le_right
            (mem_le_finMax a _ ((Finset.mem_union.mp hj).resolve_right hjA))).trans_eq hS₁).trans_lt
            hy'_lt
    exact (E.eval_le_branch x (S₁ ∪ A)).not_gt
      (max_lt hα (finMax_lt ((E.mem_Icc _).1.trans_lt hα) hmem_lt))

theorem eval_isStrategyProof [DecidableEq ι] [MeasurableSpace (Set.Icc a b)]
    [OpensMeasurableSpace (Set.Icc a b)] :
    (Mechanism.deterministic E.eval).IsStrategyProof :=
  E.eval_isGroupStrategyProof.isStrategyProof

private lemma evalVal_update_eq [DecidableEq ι] (x : ι → Set.Icc a b) (i₀ : ι) (t : Set.Icc a b) :
    E.evalVal (Function.update x i₀ t) =
      min (E.evalVal (Function.update x i₀ ⟨b, (E.mem_Icc ∅).1.trans (E.mem_Icc ∅).2, le_rfl⟩))
        (max (E.evalVal (Function.update x i₀ ⟨a, le_rfl, (E.mem_Icc ∅).1.trans (E.mem_Icc ∅).2⟩))
          (t : ℝ)) := by
  classical
  let hab : a ≤ b := (E.mem_Icc ∅).1.trans (E.mem_Icc ∅).2
  let g : Finset ι → ℝ := fun S => max (E.alpha S) (finMax a (S.erase i₀) fun j => (x j : ℝ))
  let T₀ := Finset.univ.filter fun S : Finset ι => i₀ ∉ S
  let T₁ := Finset.univ.filter fun S : Finset ι => i₀ ∈ S
  have huniv : (Finset.univ : Finset (Finset ι)) = T₀ ∪ T₁ := by
    ext S; simp only [T₀, T₁, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
  have hxz : ∀ (z : Set.Icc a b) (S : Finset ι),
      max (E.alpha S) (finMax a S fun j => ((Function.update x i₀ z j : Set.Icc a b) : ℝ)) =
        if i₀ ∈ S then max (g S) (z : ℝ) else g S := by
    intro z S
    split_ifs with hi
    · have hfin : (finMax a S fun j => ((Function.update x i₀ z j : Set.Icc a b) : ℝ)) =
          max (z : ℝ) (finMax a (S.erase i₀) fun j => (x j : ℝ)) := by
        dsimp only [finMax]
        conv_lhs => rw [← Finset.insert_erase hi]
        rw [Finset.fold_insert (Finset.notMem_erase _ _), Function.update_self]
        exact congrArg _ (Finset.fold_congr fun j hj => by
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
      rw [hfin]; dsimp only [g]; rw [max_left_comm, max_comm]
    · dsimp only [g]; rw [Finset.erase_eq_of_notMem hi]; congr 1
      exact finMax_eq_of_eqOn a S fun j hj => by simp [show j ≠ i₀ from fun h => hi (h ▸ hj)]
  have hmin_eq : ∀ z : Set.Icc a b,
      E.evalVal (Function.update x i₀ z) = min (finMin b T₀ g) (max (finMin b T₁ g) (z : ℝ)) := by
    intro z
    dsimp only [evalVal]
    rw [huniv, finMin_union]
    have hT0 : finMin b T₀ (fun S => max (E.alpha S)
        (finMax a S fun j => ((Function.update x i₀ z j : Set.Icc a b) : ℝ))) = finMin b T₀ g :=
      finMin_eq_of_eqOn b fun S hS => by
        rw [hxz z S, ite_eq_right (Finset.mem_filter.mp hS).2]
    have hT1 : finMin b T₁ (fun S => max (E.alpha S)
        (finMax a S fun j => ((Function.update x i₀ z j : Set.Icc a b) : ℝ))) =
        max (finMin b T₁ g) (z : ℝ) := by
      rw [← finMin_max_right b T₁ g z.2.2]
      exact finMin_eq_of_eqOn b fun S hS => by
        rw [hxz z S, ite_eq_left (Finset.mem_filter.mp hS).2]
    rw [hT0, hT1]
  have hb_eq : E.evalVal (Function.update x i₀ ⟨b, hab, le_rfl⟩) = finMin b T₀ g := by
    rw [hmin_eq, max_eq_right (finMin_le_base b T₁ g), min_eq_left (finMin_le_base b T₀ g)]
  have ha_eq : E.evalVal (Function.update x i₀ ⟨a, le_rfl, hab⟩) =
      min (finMin b T₀ g) (finMin b T₁ g) := by
    rw [hmin_eq, max_eq_left (le_finMin hab fun S _ => le_max_of_le_left (E.mem_Icc S).1)]
  rw [hmin_eq t, hb_eq, ha_eq]
  rcases le_total (finMin b T₀ g) (finMin b T₁ g) with h01 | h10
  · rw [min_eq_left h01, min_eq_left (h01.trans (le_max_left _ _)), min_eq_left (le_max_left _ _)]
  · rw [min_eq_right h10]

end Eval

end MoulinScheme

section Characterization

variable {ι : Type*} [Finite ι] [Nonempty ι] {a b : ℝ}

omit [Finite ι] [Nonempty ι] in
private lemma coord_mono_of_sp [DecidableEq ι] {f : (ι → Set.Icc a b) → Set.Icc a b}
    (hf_sp : ∀ x i z, dist (f x) (x i) ≤ dist (f (Function.update x i z)) (x i))
    (x : ι → Set.Icc a b) (i : ι) {z₁ z₂ : Set.Icc a b} (hz : (z₁ : ℝ) ≤ (z₂ : ℝ)) :
    (f (Function.update x i z₁) : ℝ) ≤ (f (Function.update x i z₂) : ℝ) := by
  rcases hz.eq_or_lt with hzeq | hzlt
  · rw [Subtype.ext hzeq]
  have h1 : ((f (Function.update x i z₁) : ℝ) - z₁) ^ 2 ≤
      ((f (Function.update x i z₂) : ℝ) - z₁) ^ 2 :=
    sq_le_sq.mpr <| by
      simpa [Subtype.dist_eq, Real.dist_eq] using hf_sp (Function.update x i z₁) i z₂
  have h2 : ((f (Function.update x i z₂) : ℝ) - z₂) ^ 2 ≤
      ((f (Function.update x i z₁) : ℝ) - z₂) ^ 2 :=
    sq_le_sq.mpr <| by
      simpa [Subtype.dist_eq, Real.dist_eq] using hf_sp (Function.update x i z₂) i z₁
  nlinarith

omit [Nonempty ι] in
private lemma profile_mono_of_sp [DecidableEq ι] {f : (ι → Set.Icc a b) → Set.Icc a b}
    (hf_sp : ∀ x i z, dist (f x) (x i) ≤ dist (f (Function.update x i z)) (x i))
    {x y : ι → Set.Icc a b} (hxy : ∀ i, (x i : ℝ) ≤ (y i : ℝ)) :
    (f x : ℝ) ≤ (f y : ℝ) := by
  refine Function.update_induction (P := fun z => (f x : ℝ) ≤ f z) le_rfl ?_
  intro z _ hfz i hzi _
  have h := coord_mono_of_sp hf_sp z i (z₁ := x i) (z₂ := y i) (hxy i)
  rw [← hzi, Function.update_eq_self] at h
  exact hfz.trans h

omit [Nonempty ι] in
private lemma pareto_bounds_of_sp [DecidableEq ι] {f : (ι → Set.Icc a b) → Set.Icc a b}
    (hf_sp : ∀ x i z, dist (f x) (x i) ≤ dist (f (Function.update x i z)) (x i))
    (hf_unan : ∀ c : Set.Icc a b, f (fun _ => c) = c)
    (x : ι → Set.Icc a b) {c d : Set.Icc a b}
    (hc : ∀ i, (c : ℝ) ≤ (x i : ℝ)) (hd : ∀ i, (x i : ℝ) ≤ (d : ℝ)) :
    (c : ℝ) ≤ (f x : ℝ) ∧ (f x : ℝ) ≤ (d : ℝ) :=
  ⟨by simpa [hf_unan c] using profile_mono_of_sp hf_sp hc,
    by simpa [hf_unan d] using profile_mono_of_sp hf_sp hd⟩

omit [Nonempty ι] in
private lemma no_jump_at_midpoint [DecidableEq ι] {f : (ι → Set.Icc a b) → Set.Icc a b}
    (hf_sp : ∀ x i z, dist (f x) (x i) ≤ dist (f (Function.update x i z)) (x i))
    (hf_unan : ∀ c : Set.Icc a b, f (fun _ => c) = c)
    (x : ι → Set.Icc a b) (i₀ : ι) {c η w t : ℝ} (hη : 0 < η)
    (hw_mem : w ∈ Set.Icc a b) (ht_mem : t ∈ Set.Icc a b)
    (hm1_mem : c - η ∈ Set.Icc a b) (hm2_mem : c + η ∈ Set.Icc a b)
    (hw_lo : c - η / 2 < w) (_hw_c : w ≤ c) (_hc_t : c ≤ t) (ht_hi : t < c + η / 2)
    (hfw_lo : c - 9 * η < (f (Function.update x i₀ ⟨w, hw_mem⟩) : ℝ))
    (hfw_hi : (f (Function.update x i₀ ⟨w, hw_mem⟩) : ℝ) ≤ c - 7 * η)
    (hft_lo : c + 8 * η ≤ (f (Function.update x i₀ ⟨t, ht_mem⟩) : ℝ)) :
    False := by
  classical
  let _ := Fintype.ofFinite ι
  let wPt : Set.Icc a b := ⟨w, hw_mem⟩
  let tPt : Set.Icc a b := ⟨t, ht_mem⟩
  let m₁ : Set.Icc a b := ⟨c - η, hm1_mem⟩
  let m₂ : Set.Icc a b := ⟨c + η, hm2_mem⟩
  let y : ι → Set.Icc a b := fun k => if k ≠ i₀ ∧ (x k : ℝ) < c - η then m₁ else x k
  have hphase1 : c - 9 * η < (f (Function.update y i₀ wPt) : ℝ) ∧
      (f (Function.update y i₀ wPt) : ℝ) ≤ c - 7 * η ∧
      c + 8 * η ≤ (f (Function.update y i₀ tPt) : ℝ) := by
    refine Function.update_induction (y := y) (P := fun z =>
      c - 9 * η < (f (Function.update z i₀ wPt) : ℝ) ∧
      (f (Function.update z i₀ wPt) : ℝ) ≤ c - 7 * η ∧
      c + 8 * η ≤ (f (Function.update z i₀ tPt) : ℝ)) ⟨hfw_lo, hfw_hi, hft_lo⟩ ?_
    intro z _ ⟨ih_lo, ih_hi, ih_t⟩ j hzj hne
    have hj : j ≠ i₀ ∧ (x j : ℝ) < c - η :=
      by_contra fun h => hne (by simp only [y, ite_eq_right h, hzj])
    simp only [ite_eq_left hj, y]
    rw [Function.update_comm hj.1 m₁ wPt z, Function.update_comm hj.1 m₁ tPt z]
    set zw := Function.update z i₀ wPt
    set zt := Function.update z i₀ tPt
    have hzw_j : zw j = x j := by simp [zw, hj.1, hzj]
    have hmono : ∀ v : ι → Set.Icc a b, v j = x j → (f v : ℝ) ≤ f (Function.update v j m₁) :=
      fun v hv => by
        have h := coord_mono_of_sp hf_sp v j (z₁ := x j) (z₂ := m₁) hj.2.le
        rwa [← hv, Function.update_eq_self] at h
    have ht_new : c + 8 * η ≤ (f (Function.update zt j m₁) : ℝ) :=
      ih_t.trans (hmono zt (by simp [zt, hj.1, hzj]))
    have hw_new_lo : c - 9 * η < (f (Function.update zw j m₁) : ℝ) :=
      ih_lo.trans_le (hmono zw hzw_j)
    have hj_sp : |(f (Function.update zw j m₁) : ℝ) - (c - η)| < 8 * η := by
      have h1 := hf_sp (Function.update zw j m₁) j (x j)
      rw [Function.update_idem, ← hzw_j, Function.update_eq_self] at h1
      have h1' : |(f (Function.update zw j m₁) : ℝ) - (m₁ : ℝ)| ≤ |(f zw : ℝ) - (m₁ : ℝ)| := by
        simpa [Subtype.dist_eq, Real.dist_eq] using h1
      dsimp only [m₁] at h1'
      exact h1'.trans_lt (by rw [abs_of_nonpos (by linarith)]; linarith)
    have hw_new_cap : (f (Function.update zw j m₁) : ℝ) < c + 7 * η := by
      linarith [(abs_lt.mp hj_sp).2]
    have hi0_sp : |(f (Function.update zt j m₁) : ℝ) - t| ≤
        |(f (Function.update zw j m₁) : ℝ) - t| := by
      have h1 := hf_sp (Function.update zt j m₁) i₀ wPt
      have hupd : Function.update (Function.update zt j m₁) i₀ wPt =
          Function.update zw j m₁ := by
        rw [Function.update_comm hj.1.symm, Function.update_idem, Function.update_comm hj.1]
      rw [hupd] at h1
      simpa [tPt, zt, hj.1.symm, Subtype.dist_eq, Real.dist_eq] using h1
    have hw_lt_t : (f (Function.update zw j m₁) : ℝ) < t := by_contra fun hge => by
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at hi0_sp
      linarith
    have hw_new_hi : (f (Function.update zw j m₁) : ℝ) ≤ c - 7 * η := by
      rw [abs_of_nonneg (by linarith), abs_of_neg (by linarith)] at hi0_sp
      linarith
    exact ⟨hw_new_lo, hw_new_hi, ht_new⟩
  let x₁ := Function.update y i₀ wPt
  let x₂ : ι → Set.Icc a b := fun k => if c + η < (x₁ k : ℝ) then m₂ else x₁ k
  have hf_x2 : (f x₂ : ℝ) ≤ c - 7 * η :=
    (profile_mono_of_sp hf_sp fun k => by
      dsimp only [x₂]; split_ifs with h; exacts [h.le, le_rfl]).trans hphase1.2.1
  have hpareto := (pareto_bounds_of_sp hf_sp hf_unan x₂ (c := m₁) (d := m₂)
    (fun k => by
      dsimp only [x₂, m₁]; split_ifs with h
      · dsimp only [m₂]; linarith
      · by_cases hki : k = i₀
        · subst hki; simp [x₁, wPt]; linarith
        · simp only [x₁, Function.update_of_ne hki, y, ne_eq, hki, not_false_eq_true, true_and]
          split_ifs with hlt; exacts [le_rfl, not_lt.mp hlt])
    (fun k => by dsimp only [x₂, m₂]; split_ifs with h; exacts [le_rfl, not_lt.mp h])).1
  dsimp only [m₁] at hpareto
  linarith

omit [Nonempty ι] in
private lemma coord_no_right_jump [DecidableEq ι] {f : (ι → Set.Icc a b) → Set.Icc a b}
    (hf_sp : ∀ x i z, dist (f x) (x i) ≤ dist (f (Function.update x i z)) (x i))
    (hf_unan : ∀ c : Set.Icc a b, f (fun _ => c) = c)
    (x : ι → Set.Icc a b) (i₀ : ι) (t₀ : Set.Icc a b) {ε : ℝ} (hε : 0 < ε)
    (hR : ∀ δ > 0, ∃ t : Set.Icc a b, (t₀ : ℝ) < t ∧ (t : ℝ) < t₀ + δ ∧
      (f (Function.update x i₀ t₀) : ℝ) + ε ≤ (f (Function.update x i₀ t) : ℝ)) :
    False := by
  let g : Set.Icc a b → ℝ := fun t => (f (Function.update x i₀ t) : ℝ)
  have hg_mono : Monotone g := fun s t hst => coord_mono_of_sp hf_sp x i₀ hst
  have hg_sp : ∀ s t : Set.Icc a b, |g s - (s : ℝ)| ≤ |g t - (s : ℝ)| := fun s t => by
    simpa [g, Function.update_idem, Subtype.dist_eq, Real.dist_eq] using
      hf_sp (Function.update x i₀ s) i₀ t
  set u₀ := g t₀ with hu₀_def
  let S := g '' { t : Set.Icc a b | (t₀ : ℝ) < t }
  obtain ⟨t₁, ht₁, _, _⟩ := hR 1 one_pos
  have hS_ne : S.Nonempty := ⟨g t₁, t₁, ht₁, rfl⟩
  have hS_lo : ∀ y ∈ S, u₀ + ε ≤ y := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨t', _, ht'lt, ht'g⟩ := hR ((t : ℝ) - t₀) (sub_pos.mpr ht)
    change g t₀ + ε ≤ g t' at ht'g
    exact ht'g.trans (hg_mono (show (t' : ℝ) ≤ t by linarith))
  set v₀ := sInf S with hv₀_def
  have hu₀_le_v₀ : u₀ + ε ≤ v₀ := le_csInf hS_ne hS_lo
  have hu₀_ge_a : a ≤ u₀ := (f (Function.update x i₀ t₀)).2.1
  have hv₀_le_b : v₀ ≤ b :=
    (csInf_le ⟨u₀ + ε, hS_lo⟩ ⟨t₁, ht₁, rfl⟩).trans (f (Function.update x i₀ t₁)).2.2
  have ht₀_eq : (t₀ : ℝ) = (u₀ + v₀) / 2 := by
    rcases lt_trichotomy (t₀ : ℝ) ((u₀ + v₀) / 2) with hlt | heq | hgt
    · let t' := ((t₀ : ℝ) + min ((u₀ + v₀) / 2) (t₁ : ℝ)) / 2
      have ht'_gt : (t₀ : ℝ) < t' := by dsimp only [t']; linarith [lt_min hlt ht₁]
      have ht'_le : t' ≤ t₁ := by dsimp only [t']; linarith [min_le_right ((u₀ + v₀) / 2) (t₁ : ℝ)]
      have ht'_lt : t' < (u₀ + v₀) / 2 := by
        dsimp only [t']; linarith [min_le_left ((u₀ + v₀) / 2) (t₁ : ℝ)]
      have ht'_mem : t' ∈ Set.Icc a b := ⟨t₀.2.1.trans ht'_gt.le, ht'_le.trans t₁.2.2⟩
      have hv_le : v₀ ≤ g ⟨t', ht'_mem⟩ :=
        csInf_le ⟨u₀ + ε, hS_lo⟩ ⟨⟨t', ht'_mem⟩, ht'_gt, rfl⟩
      have h1 : v₀ - t' ≤ |g ⟨t', ht'_mem⟩ - t'| := by rw [abs_of_nonneg (by linarith)]; linarith
      have h2 : |u₀ - t'| < v₀ - t' := abs_lt.mpr ⟨by linarith, by linarith⟩
      linarith [hg_sp ⟨t', ht'_mem⟩ t₀]
    · exact heq
    · obtain ⟨_, ⟨t, ht_gt, rfl⟩, hy_lt⟩ :=
        (csInf_lt_iff ⟨u₀ + ε, hS_lo⟩ hS_ne).mp
          (show sInf S < v₀ + (2 * (t₀ : ℝ) - u₀ - v₀) by rw [← hv₀_def]; linarith)
      have hv_le : v₀ ≤ g t := csInf_le ⟨u₀ + ε, hS_lo⟩ ⟨t, ht_gt, rfl⟩
      have h1 : |g t - (t₀ : ℝ)| < (t₀ : ℝ) - u₀ := abs_lt.mpr ⟨by linarith, by linarith⟩
      have h2 : |u₀ - (t₀ : ℝ)| = (t₀ : ℝ) - u₀ := by rw [abs_of_neg (by linarith)]; ring
      linarith [hg_sp t₀ t]
  set η := (v₀ - u₀) / 16 with hη_def
  have hη : 0 < η := by linarith [hu₀_le_v₀, hε, hη_def]
  have htplus_mem : (t₀ : ℝ) + η / 4 ∈ Set.Icc a b :=
    ⟨t₀.2.1.trans (by linarith),
      (by linarith [hη_def, ht₀_eq] : (t₀ : ℝ) + η / 4 ≤ v₀).trans hv₀_le_b⟩
  have hm1_mem : (t₀ : ℝ) - η ∈ Set.Icc a b :=
    ⟨hu₀_ge_a.trans (by linarith [hη_def, ht₀_eq]),
      (by linarith : (t₀ : ℝ) - η ≤ t₀).trans t₀.2.2⟩
  have hm2_mem : (t₀ : ℝ) + η ∈ Set.Icc a b :=
    ⟨t₀.2.1.trans (by linarith), (by linarith [hη_def, ht₀_eq] : (t₀ : ℝ) + η ≤ v₀).trans hv₀_le_b⟩
  have hft_lo : (t₀ : ℝ) + 8 * η ≤ g ⟨(t₀ : ℝ) + η / 4, htplus_mem⟩ := by
    rw [show (t₀ : ℝ) + 8 * η = v₀ by linarith [hη_def, ht₀_eq]]
    exact csInf_le ⟨u₀ + ε, hS_lo⟩ ⟨⟨(t₀ : ℝ) + η / 4, htplus_mem⟩,
      show (t₀ : ℝ) < (t₀ : ℝ) + η / 4 by linarith, rfl⟩
  exact no_jump_at_midpoint hf_sp hf_unan x i₀ hη t₀.2 htplus_mem hm1_mem hm2_mem
    (by linarith) le_rfl (by linarith) (by linarith)
    (by change _ < g t₀; linarith [hu₀_def, hη_def, ht₀_eq])
    (by change g t₀ ≤ _; linarith [hu₀_def, hη_def, ht₀_eq]) hft_lo

omit [Nonempty ι] in
private lemma coord_continuous_of_sp [DecidableEq ι] {f : (ι → Set.Icc a b) → Set.Icc a b}
    (hf_sp : ∀ x i z, dist (f x) (x i) ≤ dist (f (Function.update x i z)) (x i))
    (hf_unan : ∀ c : Set.Icc a b, f (fun _ => c) = c)
    (x : ι → Set.Icc a b) (i₀ : ι) :
    Continuous fun t : Set.Icc a b => (f (Function.update x i₀ t) : ℝ) := by
  let g : Set.Icc a b → ℝ := fun t => (f (Function.update x i₀ t) : ℝ)
  have hg_mono : Monotone g := fun s t hst => coord_mono_of_sp hf_sp x i₀ hst
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [Metric.continuousAt_iff]
  by_contra hnc
  push Not at hnc
  obtain ⟨ε, hε, hδ_all⟩ := hnc
  have hcases : (∀ δ > 0, ∃ t : Set.Icc a b, (t₀ : ℝ) < t ∧ (t : ℝ) < t₀ + δ ∧ g t₀ + ε ≤ g t) ∨
      (∀ δ > 0, ∃ t : Set.Icc a b, (t₀ : ℝ) - δ < t ∧ (t : ℝ) < t₀ ∧ g t + ε ≤ g t₀) := by
    by_contra hboth
    push Not at hboth
    obtain ⟨⟨δ₁, hδ₁, hnoR⟩, ⟨δ₂, hδ₂, hnoL⟩⟩ := hboth
    obtain ⟨t, ht_dist, ht_g⟩ := hδ_all (min δ₁ δ₂) (lt_min hδ₁ hδ₂)
    rw [Subtype.dist_eq, Real.dist_eq] at ht_dist
    rw [Real.dist_eq] at ht_g
    rcases lt_trichotomy (t : ℝ) t₀ with hlt | heq | hgt
    · have hge : g t + ε ≤ g t₀ := by
        rw [abs_of_nonpos (by linarith [hg_mono hlt.le])] at ht_g; linarith
      exact (hnoL t (by linarith [(abs_lt.mp ht_dist).1, min_le_right δ₁ δ₂]) hlt).not_ge hge
    · rw [Subtype.ext heq, sub_self, abs_zero] at ht_g; linarith
    · have hge : g t₀ + ε ≤ g t := by
        rw [abs_of_nonneg (by linarith [hg_mono hgt.le])] at ht_g; linarith
      exact (hnoR t hgt (by linarith [(abs_lt.mp ht_dist).2, min_le_left δ₁ δ₂])).not_ge hge
  rcases hcases with hR | hL
  · exact coord_no_right_jump hf_sp hf_unan x i₀ t₀ hε hR
  · let negPt : Set.Icc (-b) (-a) → Set.Icc a b := fun z =>
      ⟨-z, by linarith [z.2.2], by linarith [z.2.1]⟩
    let posPt : Set.Icc a b → Set.Icc (-b) (-a) := fun z =>
      ⟨-z, by linarith [z.2.2], by linarith [z.2.1]⟩
    let f' : (ι → Set.Icc (-b) (-a)) → Set.Icc (-b) (-a) :=
      fun z => posPt (f (fun i => negPt (z i)))
    have hf'_sp : ∀ z i w, dist (f' z) (z i) ≤ dist (f' (Function.update z i w)) (z i) :=
      fun z i w => by
        have h := hf_sp (fun j => negPt (z j)) i (negPt w)
        rw [show Function.update (fun j => negPt (z j)) i (negPt w) =
          fun j => negPt (Function.update z i w j) from
            funext fun j => (Function.apply_update (fun _ => negPt) z i w j).symm] at h
        rw [Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq, Real.dist_eq] at h ⊢
        have habs : ∀ u v : ℝ, |-u - v| = |u - -v| := fun u v => by
          rw [← abs_neg (-u - v)]; ring_nf
        change |-(f (fun j => negPt (z j)) : ℝ) - (z i : ℝ)| ≤
          |-(f (fun j => negPt (Function.update z i w j)) : ℝ) - (z i : ℝ)|
        simpa only [habs] using h
    have hf'_unan : ∀ c, f' (fun _ => c) = c := fun c => by
      ext; change -(f (fun _ => negPt c) : ℝ) = _; rw [hf_unan (negPt c)]; simp [negPt]
    refine coord_no_right_jump hf'_sp hf'_unan
      (fun i => posPt (x i)) i₀ (posPt t₀) hε fun δ hδ => ?_
    obtain ⟨t, ht1, ht2, htg⟩ := hL δ hδ
    refine ⟨posPt t, by change (-t₀ : ℝ) < -t; linarith,
      by change (-t : ℝ) < -t₀ + δ; linarith, ?_⟩
    change -(f (fun i => negPt (Function.update (fun i => posPt (x i)) i₀ (posPt t₀) i)) : ℝ) + ε ≤
      -(f (fun i => negPt (Function.update (fun i => posPt (x i)) i₀ (posPt t) i)) : ℝ)
    have hupd : ∀ w, Function.update (fun i => posPt (x i)) i₀ (posPt w) =
        fun i => posPt (Function.update x i₀ w i) := fun w =>
      funext fun j => (Function.apply_update (fun _ => posPt) x i₀ w j).symm
    rw [hupd t₀, hupd t]
    have hnp : ∀ w : Set.Icc a b, (fun i => negPt (posPt (Function.update x i₀ w i))) =
        Function.update x i₀ w := fun w => funext fun _ => Subtype.ext (neg_neg _)
    rw [hnp t₀, hnp t]
    exact by change -g t₀ + ε ≤ -g t; linarith

omit [Nonempty ι] in
private lemma coord_clamp_eq [DecidableEq ι]
    (hab : a ≤ b) {f : (ι → Set.Icc a b) → Set.Icc a b}
    (hf_sp : ∀ x i z, dist (f x) (x i) ≤ dist (f (Function.update x i z)) (x i))
    (hf_unan : ∀ c : Set.Icc a b, f (fun _ => c) = c)
    (x : ι → Set.Icc a b) (i₀ : ι) (t : Set.Icc a b) :
    (f (Function.update x i₀ t) : ℝ) =
      min (f (Function.update x i₀ ⟨b, hab, le_rfl⟩) : ℝ)
        (max (f (Function.update x i₀ ⟨a, le_rfl, hab⟩) : ℝ) (t : ℝ)) := by
  let aPt : Set.Icc a b := ⟨a, le_rfl, hab⟩
  let bPt : Set.Icc a b := ⟨b, hab, le_rfl⟩
  let u : ℝ := (f (Function.update x i₀ aPt) : ℝ)
  let v : ℝ := (f (Function.update x i₀ bPt) : ℝ)
  have huv : u ≤ v := coord_mono_of_sp hf_sp x i₀ hab
  have hg_sp : ∀ s : Set.Icc a b,
      |(f (Function.update x i₀ t) : ℝ) - (t : ℝ)| ≤
        |(f (Function.update x i₀ s) : ℝ) - (t : ℝ)| := fun s => by
    simpa [Function.update_idem, Subtype.dist_eq, Real.dist_eq] using
      hf_sp (Function.update x i₀ t) i₀ s
  rcases le_or_gt (t : ℝ) u with htu | hut
  · rw [max_eq_left htu, min_eq_right huv]
    have ha_le : u ≤ (f (Function.update x i₀ t) : ℝ) :=
      coord_mono_of_sp hf_sp x i₀ (z₁ := aPt) (z₂ := t) t.2.1
    have hsp' := hg_sp aPt
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at hsp'
    linarith
  · rcases le_or_gt v (t : ℝ) with hvt | htv
    · rw [max_eq_right (huv.trans hvt), min_eq_left hvt]
      have hb_ge : (f (Function.update x i₀ t) : ℝ) ≤ v :=
        coord_mono_of_sp hf_sp x i₀ (z₁ := t) (z₂ := bPt) t.2.2
      have hsp' := hg_sp bPt
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at hsp'
      linarith
    · rw [max_eq_right hut.le, min_eq_right htv.le]
      let g' : ℝ → ℝ := fun r => (f (Function.update x i₀ (Set.projIcc a b hab r)) : ℝ)
      have hg'_cont : Continuous g' :=
        (coord_continuous_of_sp hf_sp hf_unan x i₀).comp continuous_projIcc
      have ht_mem : (t : ℝ) ∈ Set.Icc (g' a) (g' b) := by
        simpa [g', aPt, bPt, Set.projIcc_left, Set.projIcc_right] using ⟨hut.le, htv.le⟩
      obtain ⟨s, hs_mem, hgs⟩ := intermediate_value_Icc hab hg'_cont.continuousOn ht_mem
      have hsp' := hg_sp ⟨s, hs_mem⟩
      rw [show (f (Function.update x i₀ ⟨s, hs_mem⟩) : ℝ) = t by
        simpa [g', Set.projIcc_of_mem hab hs_mem] using hgs, sub_self, abs_zero] at hsp'
      linarith [abs_eq_zero.mp (le_antisymm hsp' (abs_nonneg _))]

/-- A deterministic facility-location mechanism on a nonempty closed interval `Set.Icc a b` is
strategyproof and surjective if and only if it is the evaluation map of a `MoulinScheme`. -/
theorem isStrategyProof_and_surjective_iff_exists_moulinScheme
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] {a b : ℝ} (hab : a ≤ b)
    [MeasurableSpace (Set.Icc a b)] [OpensMeasurableSpace (Set.Icc a b)]
    (f : (ι → Set.Icc a b) → Set.Icc a b) :
    ((Mechanism.deterministic f).IsStrategyProof ∧ Function.Surjective f) ↔
      ∃ E : MoulinScheme ι a b, f = E.eval := by
  classical
  constructor
  · rintro ⟨hf_sp, hf_onto⟩
    have hf_sp' : ∀ x i z, dist (f x) (x i) ≤ dist (f (Function.update x i z)) (x i) :=
      fun x i z => by
        simpa only [dist_comm] using (Mechanism.isStrategyProof_deterministic_iff f).mp hf_sp x i z
    have hf_unan : ∀ y : Set.Icc a b, f (fun _ => y) = y :=
      unanimous_of_surjective_isStrategyProof hf_sp hf_onto
    let aPt : Set.Icc a b := ⟨a, le_rfl, hab⟩
    let bPt : Set.Icc a b := ⟨b, hab, le_rfl⟩
    let indProf : Finset ι → ι → Set.Icc a b := fun S i => if i ∈ S then aPt else bPt
    let E : MoulinScheme ι a b :=
      { alpha := fun S => (f (indProf S) : ℝ)
        mem_Icc := fun S => (f (indProf S)).2
        antitone := fun S T hST => profile_mono_of_sp hf_sp' fun i => by
          by_cases hS : i ∈ S
          · simp [indProf, hS, hST hS]
          · by_cases hT : i ∈ T <;> simp [indProf, hS, hT, aPt, bPt, hab]
        boundary_empty := by
          rw [show indProf ∅ = fun _ => bPt by ext; simp [indProf], hf_unan]
        boundary_univ := by
          rw [show indProf Finset.univ = fun _ => aPt by ext; simp [indProf], hf_unan] }
    refine ⟨E, funext fun x => Subtype.ext ?_⟩
    suffices h : ∀ (n : ℕ) (y : ι → Set.Icc a b),
        (Finset.univ.filter fun i => y i ≠ aPt ∧ y i ≠ bPt).card = n →
        (f y : ℝ) = E.evalVal y from h _ x rfl
    intro n
    induction n with
    | zero =>
      intro y hcard
      have hemp : (Finset.univ.filter fun i => y i ≠ aPt ∧ y i ≠ bPt) = ∅ :=
        Finset.card_eq_zero.mp hcard
      let S := Finset.univ.filter fun i => y i = aPt
      have hy_eq : y = indProf S := funext fun i => by
        by_cases hia : y i = aPt
        · simp [indProf, S, hia]
        · have hib : y i = bPt := by_contra fun hne =>
            Finset.notMem_empty i (hemp ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ i, hia, hne⟩)
          simp [indProf, S, hib]
      rw [hy_eq]
      dsimp only [MoulinScheme.evalVal, E]
      refine le_antisymm ?_ ?_
      · refine le_finMin (f (indProf S)).2.2 fun T _ => ?_
        by_cases hTS : T ⊆ S
        · exact le_max_of_le_left (E.antitone hTS)
        · obtain ⟨j, hjT, hjS⟩ := Finset.not_subset.mp hTS
          have hjb : indProf S j = bPt := by
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hjS
            simp [indProf, S, hjS]
          exact le_max_of_le_right ((f (indProf S)).2.2.trans <| by
            simpa [hjb, bPt] using mem_le_finMax a (fun k => (indProf S k : ℝ)) hjT)
      · refine (finMin_le b (T := Finset.univ)
          (fun T => max (E.alpha T) (finMax a T fun k => (indProf S k : ℝ)))
          (Finset.mem_univ S)).trans_eq ?_
        have hmax : (finMax a S fun k => (indProf S k : ℝ)) = a :=
          le_antisymm (finMax_le le_rfl fun k hk => by simp [indProf, hk, aPt]) (le_finMax a S _)
        simp [E, hmax, max_eq_left (f (indProf S)).2.1]
    | succ k ih =>
      intro y hcard
      obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp (by rw [hcard]; exact Nat.succ_pos k)
      have hcard_upd (z : Set.Icc a b) (hz : z = aPt ∨ z = bPt) :
          (Finset.univ.filter fun i =>
            Function.update y i₀ z i ≠ aPt ∧ Function.update y i₀ z i ≠ bPt).card = k := by
        suffices (Finset.univ.filter fun i =>
            Function.update y i₀ z i ≠ aPt ∧ Function.update y i₀ z i ≠ bPt) =
            (Finset.univ.filter fun i => y i ≠ aPt ∧ y i ≠ bPt).erase i₀ by
          rw [this, Finset.card_erase_of_mem hi₀, hcard]; rfl
        ext j; rcases eq_or_ne j i₀ with rfl | hj <;> rcases hz with rfl | rfl <;> simp [*]
      have hy_upd : Function.update y i₀ (y i₀) = y := Function.update_eq_self i₀ y
      calc
        (f y : ℝ) = (f (Function.update y i₀ (y i₀)) : ℝ) := by rw [hy_upd]
        _ = min (f (Function.update y i₀ bPt) : ℝ)
              (max (f (Function.update y i₀ aPt) : ℝ) (y i₀ : ℝ)) :=
          coord_clamp_eq hab hf_sp' hf_unan y i₀ (y i₀)
        _ = min (E.evalVal (Function.update y i₀ bPt))
              (max (E.evalVal (Function.update y i₀ aPt)) (y i₀ : ℝ)) := by
          rw [ih _ (hcard_upd aPt (Or.inl rfl)), ih _ (hcard_upd bPt (Or.inr rfl))]
        _ = E.evalVal (Function.update y i₀ (y i₀)) := (E.evalVal_update_eq y i₀ (y i₀)).symm
        _ = E.evalVal y := by rw [hy_upd]
  · rintro ⟨E, rfl⟩
    exact ⟨E.eval_isStrategyProof, E.eval_surjective⟩

/-- Transfers a strategyproof mechanism on any metric space `G` that preserves and surjects onto
the image of an isometric embedding `φ : Set.Icc 0 d → G` to a `MoulinScheme ι 0 d`. -/
theorem moulinScheme_of_isometry {ι G : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [MetricSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    {d : ℝ} (hd : 0 ≤ d) (φ : Set.Icc (0 : ℝ) d → G) (hφ : Isometry φ)
    {f : (ι → G) → G} (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_range : ∀ x : ι → G, (∀ i, x i ∈ Set.range φ) → f x ∈ Set.range φ)
    (hf_onto : ∀ y ∈ Set.range φ, ∃ x : ι → G, (∀ i, x i ∈ Set.range φ) ∧ f x = y) :
    ∃ E : MoulinScheme ι 0 d, ∀ x : ι → Set.Icc (0 : ℝ) d,
      f (fun i => φ (x i)) = φ (E.eval x) := by
  classical
  have hf'_mem : ∀ x : ι → Set.Icc (0 : ℝ) d, f (fun i => φ (x i)) ∈ Set.range φ :=
    fun x => hf_range (fun i => φ (x i)) fun i => ⟨x i, rfl⟩
  let f' : (ι → Set.Icc (0 : ℝ) d) → Set.Icc (0 : ℝ) d := fun x => Classical.choose (hf'_mem x)
  have hf'_spec : ∀ x, φ (f' x) = f (fun i => φ (x i)) := fun x => Classical.choose_spec (hf'_mem x)
  have hf'_sp : (Mechanism.deterministic f').IsStrategyProof := by
    rw [Mechanism.isStrategyProof_deterministic_iff]
    intro x i z
    have hsp := (Mechanism.isStrategyProof_deterministic_iff f).mp hf_sp (fun j => φ (x j)) i (φ z)
    rw [show Function.update (fun j => φ (x j)) i (φ z) =
        fun j => φ (Function.update x i z j) from
          funext fun j => (Function.apply_update (fun _ => φ) x i z j).symm,
      ← hf'_spec x, ← hf'_spec (Function.update x i z)] at hsp
    simpa only [hφ.dist_eq] using hsp
  have hf'_onto : Function.Surjective f' := by
    intro y
    obtain ⟨x₀, hx₀_mem, hx₀_eq⟩ := hf_onto (φ y) ⟨y, rfl⟩
    refine ⟨fun i => Classical.choose (hx₀_mem i), hφ.injective ?_⟩
    rw [hf'_spec, show (fun i => φ (Classical.choose (hx₀_mem i))) = x₀ from
      funext fun i => Classical.choose_spec (hx₀_mem i), hx₀_eq]
  obtain ⟨E, hE⟩ :=
    (isStrategyProof_and_surjective_iff_exists_moulinScheme hd f').mp ⟨hf'_sp, hf'_onto⟩
  exact ⟨E, fun x => by rw [← hf'_spec x, hE]⟩

/-- Explicit two-agent formula for a `MoulinScheme (Fin 2) a b`: `(E.eval x : ℝ)` equals
`min (max (E.alpha {0}) (x 0 : ℝ))` paired with
`min (max (E.alpha {1}) (x 1 : ℝ)) (max (x 0 : ℝ) (x 1 : ℝ))`. -/
theorem moulinScheme_finTwo_eq {a b : ℝ} (E : MoulinScheme (Fin 2) a b)
    (x : Fin 2 → Set.Icc a b) :
    (E.eval x : ℝ) =
      min (max (E.alpha {0}) (x 0 : ℝ))
        (min (max (E.alpha {1}) (x 1 : ℝ)) (max (x 0 : ℝ) (x 1 : ℝ))) := by
  classical
  have hmem : ∀ j : Fin 2, max (E.alpha {j}) (finMax a {j} fun i => (x i : ℝ)) =
      max (E.alpha {j}) (x j : ℝ) := fun j => by
    simp [finMax, max_eq_left (x j).2.1]
  have hu : (finMax a Finset.univ fun i => (x i : ℝ)) = max (x 0 : ℝ) (x 1 : ℝ) :=
    le_antisymm (finMax_le (le_max_of_le_left (x 0).2.1) fun i _ => by
      fin_cases i; exacts [le_max_left _ _, le_max_right _ _])
      (max_le (mem_le_finMax a (fun i => (x i : ℝ)) (Finset.mem_univ (0 : Fin 2)))
        (mem_le_finMax a (fun i => (x i : ℝ)) (Finset.mem_univ (1 : Fin 2))))
  rw [MoulinScheme.eval_coe, MoulinScheme.evalVal]
  refine le_antisymm (le_min ?_ (le_min ?_ ?_)) (le_finMin ?_ fun S _ => ?_)
  · exact (E.eval_le_branch x {0}).trans_eq (hmem 0)
  · exact (E.eval_le_branch x {1}).trans_eq (hmem 1)
  · exact (E.eval_le_branch x Finset.univ).trans_eq <| by
      rw [E.boundary_univ, hu, max_eq_right (le_max_of_le_left (x 0).2.1)]
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (max_le (x 0).2.2 (x 1).2.2))
  · by_cases h0 : (0 : Fin 2) ∈ S <;> by_cases h1 : (1 : Fin 2) ∈ S
    · exact (min_le_right _ _).trans <| (min_le_right _ _).trans <| le_max_of_le_right <|
        max_le (mem_le_finMax a (fun i => (x i : ℝ)) h0)
          (mem_le_finMax a (fun i => (x i : ℝ)) h1)
    · have hsub : S ⊆ ({0} : Finset (Fin 2)) := fun i hi => by
        fin_cases i; exacts [Finset.mem_singleton_self _, absurd hi h1]
      exact (min_le_left _ _).trans <| max_le ((E.antitone hsub).trans (le_max_left _ _))
        ((mem_le_finMax a (fun i => (x i : ℝ)) h0).trans (le_max_right _ _))
    · have hsub : S ⊆ ({1} : Finset (Fin 2)) := fun i hi => by
        fin_cases i; exacts [absurd hi h0, Finset.mem_singleton_self _]
      exact (min_le_right _ _).trans <| (min_le_left _ _).trans <|
        max_le ((E.antitone hsub).trans (le_max_left _ _))
          ((mem_le_finMax a (fun i => (x i : ℝ)) h1).trans (le_max_right _ _))
    · have hemp : S = ∅ := Finset.eq_empty_of_forall_notMem fun i hi => by
        fin_cases i; exacts [h0 hi, h1 hi]
      rw [hemp, E.boundary_empty]
      exact (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (max_le (x 0).2.2 (x 1).2.2).trans (le_max_left _ _)

end Characterization

end Moulin

end Cslib.GameTheory.FacilityLocation
