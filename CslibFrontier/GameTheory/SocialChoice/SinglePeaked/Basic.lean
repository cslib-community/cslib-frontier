/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.SocialChoice.Ranking
public import Mathlib.Topology.Instances.Real.Lemmas
import CslibFrontier.Foundations.Data.Fintype.UpdateInduction
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

/-!
# Single-peaked preferences on a closed real interval

The ordinal single-peaked preference model of social choice over a one-dimensional policy space
`Set.Icc a b ⊆ ℝ` ([SchummerVohra2007], §10.2, pp. 244–251, where `[a, b] = [0, 1]`). Each agent
holds a weak order (`WeakRanking (Set.Icc a b)`) with a unique most-preferred point (`peak`) such
that preference strictly decreases as one moves away from `peak` on either side.

This module establishes the foundational structural theorems on the full ordinal single-peaked
domain:

* **Lemma 10.1** ([SchummerVohra2007], §10.2, pp. 245–246): for a strategy-proof rule on finitely
  many agents, surjectivity (onto), unanimity, and Pareto-optimality are all equivalent. Moreover,
  weak and strong Pareto-optimality coincide and characterize outcomes in the convex hull of the
  agents' peaks.
* **Option-set characterization** ([SchummerVohra2007], §10.2.1 footnote 6, p. 249; Exercise 10.3,
  pp. 264–265): strategy-proofness alone forces every single-agent option set to be closed in `ℝ`;
  together with surjectivity it forces the option set to be the closed interval between the extreme
  reports at `a` and `b`, proved directly without invoking the generalized median characterization.
* **Peaks-only property** ([Ching1997]; [SchummerVohra2007], §10.2.1, p. 247 and §10.6, p. 263):
  every strategy-proof onto rule on ordinal single-peaked preferences depends only on the profile
  of peaks.

## Main definitions

* `Cslib.GameTheory.SocialChoice.SinglePeaked.Preference`: a single-peaked weak order on
  `Set.Icc a b` with its unique `peak`.
* `Cslib.GameTheory.SocialChoice.SinglePeaked.Preference.symmetric`,
  `Preference.preferLeft`, `Preference.preferRight`, `Preference.leftExtreme`,
  `Preference.rightExtreme`: standard single-peaked preference constructors.
* `Cslib.GameTheory.SocialChoice.SinglePeaked.Profile`,
  `Cslib.GameTheory.SocialChoice.SinglePeaked.Rule`: preference profiles and social choice rules.
* `Cslib.GameTheory.SocialChoice.SinglePeaked.Rule.IsStrategyProof`,
  `Rule.IsGroupStrategyProof`, `Rule.IsAnonymous`, `Rule.IsUnanimous`, `Rule.IsParetoOptimal`,
  `Rule.IsStrongParetoOptimal`, `Rule.IsPeaksOnly`, `Rule.IsIndividuallyRational`,
  `Rule.optionSet`: axioms and single-agent option sets.

## Main results

* `Cslib.GameTheory.SocialChoice.SinglePeaked.Preference.isSinglePeaked_iff_convex`: equivalence
  between betweenness and the convex-combination definition of [SchummerVohra2007], p. 245.
* `Cslib.GameTheory.SocialChoice.SinglePeaked.Preference.eq_leftExtreme_of_peak_eq`,
  `Preference.eq_rightExtreme_of_peak_eq`: uniqueness of the extreme preferences at `a` and `b`
  ([SchummerVohra2007], p. 247).
* `Cslib.GameTheory.SocialChoice.SinglePeaked.Rule.isParetoOptimal_iff_isStrongParetoOptimal`,
  `Rule.isParetoOptimal_iff_peaks_bounds`: characterization of Pareto-optimality on single-peaked
  profiles.
* `Cslib.GameTheory.SocialChoice.SinglePeaked.Rule.IsStrategyProof.surjective_iff_isUnanimous`,
  `Rule.IsStrategyProof.surjective_iff_isParetoOptimal`,
  `Rule.IsStrategyProof.isUnanimous_iff_isParetoOptimal`: **Lemma 10.1** of
  [SchummerVohra2007], pp. 245–246.
* `Cslib.GameTheory.SocialChoice.SinglePeaked.Rule.IsStrategyProof.isClosed_optionSet`:
  closedness of option sets under strategy-proofness alone ([SchummerVohra2007], footnote 6,
  p. 249).
* `Cslib.GameTheory.SocialChoice.SinglePeaked.Rule.IsStrategyProof.optionSet_eq_Icc`,
  `Rule.IsStrategyProof.apply_update_eq_clamp`: standalone closed-interval characterization of
  option sets ([SchummerVohra2007], Exercise 10.3, pp. 264–265).
* `Cslib.GameTheory.SocialChoice.SinglePeaked.Rule.IsStrategyProof.isPeaksOnly_of_surjective`:
  **Ching's peaks-only theorem** ([Ching1997]; [SchummerVohra2007], §10.2.1, p. 247).

## References

* [S. Ching, *Strategy-proofness and "median voters"*][Ching1997]
* [J. Schummer and R. V. Vohra, *Mechanism Design without Money*][SchummerVohra2007]
-/

public section

namespace Cslib.GameTheory.SocialChoice.SinglePeaked

/-- A **single-peaked preference** on `Set.Icc a b` ([SchummerVohra2007], §10.2, p. 245): a
complete preorder (`WeakRanking`) with a unique most-preferred point `peak` whose preference
strictly decreases as one moves away from `peak` on either side. -/
structure Preference (a b : ℝ) where
  /-- The underlying complete preorder on `Set.Icc a b`. -/
  ranking : WeakRanking (Set.Icc a b)
  /-- The unique most-preferred point (peak) of the preference relation. -/
  peak : Set.Icc a b
  /-- Moving strictly right of a point at or right of `peak` is strictly worse. -/
  prefers_of_between_right : ∀ {x y : Set.Icc a b},
    (peak : ℝ) ≤ y → (y : ℝ) < x → ranking.Prefers y x
  /-- Moving strictly left of a point at or left of `peak` is strictly worse. -/
  prefers_of_between_left : ∀ {x y : Set.Icc a b},
    (x : ℝ) < y → (y : ℝ) ≤ peak → ranking.Prefers y x

namespace Preference

variable {a b : ℝ}

/-- Weak preference `x ⪰ y` under `R`. -/
@[expose] def AtLeast (R : Preference a b) (x y : Set.Icc a b) : Prop :=
  R.ranking.AtLeast x y

/-- Strict preference `x ≻ y` under `R`. -/
@[expose] def Prefers (R : Preference a b) (x y : Set.Icc a b) : Prop :=
  R.ranking.Prefers x y

theorem refl (R : Preference a b) (x : Set.Icc a b) : R.AtLeast x x :=
  R.ranking.refl x

theorem total (R : Preference a b) (x y : Set.Icc a b) : R.AtLeast x y ∨ R.AtLeast y x :=
  R.ranking.total x y

theorem trans (R : Preference a b) {x y z : Set.Icc a b}
    (hxy : R.AtLeast x y) (hyz : R.AtLeast y z) : R.AtLeast x z :=
  R.ranking.trans x y z hxy hyz

theorem atLeast_of_prefers (R : Preference a b) {x y : Set.Icc a b} (h : R.Prefers x y) :
    R.AtLeast x y :=
  R.ranking.atLeast_of_prefers h

theorem prefers_irrefl (R : Preference a b) (x : Set.Icc a b) : ¬ R.Prefers x x :=
  R.ranking.prefers_irrefl x

theorem prefers_asymm (R : Preference a b) {x y : Set.Icc a b} (h : R.Prefers x y) :
    ¬ R.Prefers y x :=
  R.ranking.prefers_asymm h

theorem prefers_trans (R : Preference a b) {x y z : Set.Icc a b}
    (hxy : R.Prefers x y) (hyz : R.Prefers y z) : R.Prefers x z :=
  R.ranking.prefers_trans hxy hyz

theorem prefers_iff_not_atLeast (R : Preference a b) {x y : Set.Icc a b} :
    R.Prefers x y ↔ ¬ R.AtLeast y x :=
  Iff.rfl

theorem atLeast_iff_not_prefers (R : Preference a b) {x y : Set.Icc a b} :
    R.AtLeast x y ↔ ¬ R.Prefers y x :=
  not_not.symm

/-- The peak is strictly preferred to every other point of `Set.Icc a b`. -/
theorem prefers_peak (R : Preference a b) {x : Set.Icc a b} (hx : x ≠ R.peak) :
    R.Prefers R.peak x := by
  rcases lt_or_gt_of_ne (fun h => hx (Subtype.ext h)) with hlt | hgt
  · exact R.prefers_of_between_left hlt le_rfl
  · exact R.prefers_of_between_right le_rfl hgt

theorem isTop_peak (R : Preference a b) : R.ranking.IsTop R.peak :=
  fun _ hx => R.prefers_peak hx

theorem atLeast_peak (R : Preference a b) (x : Set.Icc a b) : R.AtLeast R.peak x := by
  by_cases hx : x = R.peak
  · subst hx; exact R.refl _
  · exact R.atLeast_of_prefers (R.prefers_peak hx)

theorem eq_peak_of_atLeast_peak (R : Preference a b) {x : Set.Icc a b}
    (h : R.AtLeast x R.peak) : x = R.peak := by
  by_contra hx
  exact R.prefers_peak hx h

theorem atLeast_of_between_right (R : Preference a b) {x y : Set.Icc a b}
    (hpy : (R.peak : ℝ) ≤ y) (hyx : (y : ℝ) ≤ x) : R.AtLeast y x := by
  rcases hyx.eq_or_lt with h | h
  · rw [Subtype.ext h]; exact R.refl _
  · exact R.atLeast_of_prefers (R.prefers_of_between_right hpy h)

theorem atLeast_of_between_left (R : Preference a b) {x y : Set.Icc a b}
    (hxy : (x : ℝ) ≤ y) (hyp : (y : ℝ) ≤ R.peak) : R.AtLeast y x := by
  rcases hxy.eq_or_lt with h | h
  · rw [Subtype.ext h]; exact R.refl _
  · exact R.atLeast_of_prefers (R.prefers_of_between_left h hyp)

/-- Two single-peaked preferences with the same underlying weak ranking are equal (their peaks
are uniquely determined as the strict top element). -/
@[ext] theorem ext {R₁ R₂ : Preference a b} (h : R₁.ranking = R₂.ranking) : R₁ = R₂ := by
  have hpeak : R₁.peak = R₂.peak := by_contra fun hne =>
    R₁.ranking.prefers_asymm (R₁.prefers_peak (Ne.symm hne)) (h ▸ R₂.prefers_peak hne)
  cases R₁
  cases R₂
  exact mk.injEq .. ▸ ⟨h, hpeak⟩

/-- Equivalence between the order-theoretic betweenness condition and the convex-combination
definition of single-peakedness in [SchummerVohra2007] (§10.2, p. 245): for every `x ≠ p` and
`t ∈ [0, 1)`, `t * x + (1 - t) * p` is strictly preferred to `x`. -/
theorem isSinglePeaked_iff_convex (R : WeakRanking (Set.Icc a b)) (p : Set.Icc a b) :
    ((∀ {x y : Set.Icc a b}, (p : ℝ) ≤ y → (y : ℝ) < x → R.Prefers y x) ∧
     (∀ {x y : Set.Icc a b}, (x : ℝ) < y → (y : ℝ) ≤ p → R.Prefers y x)) ↔
    ∀ (x : Set.Icc a b), x ≠ p → ∀ (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1),
      R.Prefers ⟨t * x + (1 - t) * p,
        ⟨by nlinarith [x.2.1, p.2.1], by nlinarith [x.2.2, p.2.2]⟩⟩ x := by
  refine ⟨fun ⟨hR, hL⟩ x hx t ht0 ht1 => ?_, fun hconv => ?_⟩
  · rcases lt_or_gt_of_ne (fun h => hx (Subtype.ext h)) with hlt | hgt
    · exact hL (by nlinarith) (by nlinarith)
    · exact hR (by nlinarith) (by nlinarith)
  · have hstep : ∀ {x y : Set.Icc a b}, x ≠ p →
        (((p : ℝ) ≤ y ∧ (y : ℝ) < x) ∨ ((x : ℝ) < y ∧ (y : ℝ) ≤ p)) → R.Prefers y x := by
      intro x y hxp hbet
      have hne : (x : ℝ) - p ≠ 0 := sub_ne_zero.mpr fun h => hxp (Subtype.ext h)
      let t : ℝ := ((y : ℝ) - p) / ((x : ℝ) - p)
      have ht : 0 ≤ t ∧ t < 1 := by
        rcases hbet with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨div_nonneg (by linarith) (by linarith),
            (div_lt_one (by linarith)).mpr (by linarith)⟩
        · refine ⟨div_nonneg_of_nonpos (by linarith) (by linarith), ?_⟩
          rw [show t = ((p : ℝ) - y) / ((p : ℝ) - x) by
            dsimp [t]
            rw [← neg_div_neg_eq]
            congr 1 <;> ring]
          exact (div_lt_one (by linarith)).mpr (by linarith)
      have hy_eq : (⟨t * x + (1 - t) * p,
          ⟨by nlinarith [x.2.1, p.2.1], by nlinarith [x.2.2, p.2.2]⟩⟩ : Set.Icc a b) = y := by
        ext
        dsimp [t]
        field_simp [hne]; ring
      exact hy_eq ▸ hconv x hxp t ht.1 ht.2
    exact ⟨fun hpy hyx => hstep (fun h => by rw [h] at hyx; linarith) (.inl ⟨hpy, hyx⟩),
      fun hxy hyp => hstep (fun h => by rw [h] at hxy; linarith) (.inr ⟨hxy, hyp⟩)⟩

/-! ### Standard single-peaked preference constructors -/

/-- The **symmetric** (Euclidean-distance) single-peaked preference with peak `p`: `x ⪰ y` iff
`|x - p| ≤ |y - p|`. -/
def symmetric (p : Set.Icc a b) : Preference a b where
  ranking :=
    { AtLeast := fun x y => |(x : ℝ) - p| ≤ |(y : ℝ) - p|
      total := fun x y => le_total _ _
      trans := fun _ _ _ h1 h2 => h1.trans h2 }
  peak := p
  prefers_of_between_right := fun {x y} hpy hyx => by
    change ¬ |(x : ℝ) - p| ≤ |(y : ℝ) - p|
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  prefers_of_between_left := fun {x y} hxy hyp => by
    change ¬ |(x : ℝ) - p| ≤ |(y : ℝ) - p|
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

@[simp] theorem symmetric_peak (p : Set.Icc a b) : (symmetric p).peak = p := by
  unfold symmetric; rfl

@[simp] theorem symmetric_atLeast_iff (p x y : Set.Icc a b) :
    (symmetric p).AtLeast x y ↔ |(x : ℝ) - p| ≤ |(y : ℝ) - p| := by
  unfold symmetric AtLeast; rfl

@[simp] theorem symmetric_prefers_iff (p x y : Set.Icc a b) :
    (symmetric p).Prefers x y ↔ |(x : ℝ) - p| < |(y : ℝ) - p| := by
  unfold symmetric Prefers WeakRanking.Prefers; exact not_le

/-- The left-skewed single-peaked preference with peak `p`: every point in `[a, p]` is ranked
strictly above every point in `(p, b]`, ordered ascending on `[a, p]` and descending on `(p, b]`. -/
def preferLeft (p : Set.Icc a b) : Preference a b where
  ranking :=
    { AtLeast := fun x y =>
        ((x : ℝ) ≤ p ∧ (p : ℝ) < y) ∨
        ((x : ℝ) ≤ p ∧ (y : ℝ) ≤ p ∧ (y : ℝ) ≤ x) ∨
        ((p : ℝ) < x ∧ (p : ℝ) < y ∧ (x : ℝ) ≤ y)
      total := fun x y => by
        rcases le_or_gt (x : ℝ) p with hx | hx <;> rcases le_or_gt (y : ℝ) p with hy | hy
        · rcases le_total (x : ℝ) y with hxy | hyx
          · exact Or.inr (Or.inr (Or.inl ⟨hy, hx, hxy⟩))
          · exact Or.inl (Or.inr (Or.inl ⟨hx, hy, hyx⟩))
        · exact Or.inl (Or.inl ⟨hx, hy⟩)
        · exact Or.inr (Or.inl ⟨hy, hx⟩)
        · rcases le_total (x : ℝ) y with hxy | hyx
          · exact Or.inl (Or.inr (Or.inr ⟨hx, hy, hxy⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨hy, hx, hyx⟩))
      trans := fun x y z hxy hyz => by
        rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy, h1⟩ | ⟨hx, hy, h1⟩ <;>
          rcases hyz with ⟨hy', hz⟩ | ⟨hy', hz, h2⟩ | ⟨hy', hz, h2⟩
        · linarith
        · linarith
        · exact Or.inl ⟨hx, hz⟩
        · exact Or.inl ⟨hx, hz⟩
        · exact Or.inr (Or.inl ⟨hx, hz, h2.trans h1⟩)
        · linarith
        · linarith
        · linarith
        · exact Or.inr (Or.inr ⟨hx, hz, h1.trans h2⟩) }
  peak := p
  prefers_of_between_right := fun {x y} hpy hyx => by
    change ¬ (((x : ℝ) ≤ p ∧ (p : ℝ) < y) ∨
      ((x : ℝ) ≤ p ∧ (y : ℝ) ≤ p ∧ (y : ℝ) ≤ x) ∨
      ((p : ℝ) < x ∧ (p : ℝ) < y ∧ (x : ℝ) ≤ y))
    rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) <;> linarith
  prefers_of_between_left := fun {x y} hxy hyp => by
    change ¬ (((x : ℝ) ≤ p ∧ (p : ℝ) < y) ∨
      ((x : ℝ) ≤ p ∧ (y : ℝ) ≤ p ∧ (y : ℝ) ≤ x) ∨
      ((p : ℝ) < x ∧ (p : ℝ) < y ∧ (x : ℝ) ≤ y))
    rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) <;> linarith

@[simp] theorem preferLeft_peak (p : Set.Icc a b) : (preferLeft p).peak = p := by
  unfold preferLeft; rfl

theorem preferLeft_prefers_of_le_of_gt {p x y : Set.Icc a b}
    (hx : (x : ℝ) ≤ p) (hy : (p : ℝ) < y) : (preferLeft p).Prefers x y := by
  change ¬ (((y : ℝ) ≤ p ∧ (p : ℝ) < x) ∨
    ((y : ℝ) ≤ p ∧ (x : ℝ) ≤ p ∧ (x : ℝ) ≤ y) ∨
    ((p : ℝ) < y ∧ (p : ℝ) < x ∧ (y : ℝ) ≤ x))
  rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) <;> linarith

/-- The right-skewed single-peaked preference with peak `p`: every point in `[p, b]` is ranked
strictly above every point in `[a, p)`, ordered descending on `[p, b]` and ascending on `[a, p)`. -/
def preferRight (p : Set.Icc a b) : Preference a b where
  ranking :=
    { AtLeast := fun x y =>
        ((p : ℝ) ≤ x ∧ (y : ℝ) < p) ∨
        ((p : ℝ) ≤ x ∧ (p : ℝ) ≤ y ∧ (x : ℝ) ≤ y) ∨
        ((x : ℝ) < p ∧ (y : ℝ) < p ∧ (y : ℝ) ≤ x)
      total := fun x y => by
        rcases le_or_gt (p : ℝ) x with hx | hx <;> rcases le_or_gt (p : ℝ) y with hy | hy
        · rcases le_total (x : ℝ) y with hxy | hyx
          · exact Or.inl (Or.inr (Or.inl ⟨hx, hy, hxy⟩))
          · exact Or.inr (Or.inr (Or.inl ⟨hy, hx, hyx⟩))
        · exact Or.inl (Or.inl ⟨hx, hy⟩)
        · exact Or.inr (Or.inl ⟨hy, hx⟩)
        · rcases le_total (x : ℝ) y with hxy | hyx
          · exact Or.inr (Or.inr (Or.inr ⟨hy, hx, hxy⟩))
          · exact Or.inl (Or.inr (Or.inr ⟨hx, hy, hyx⟩))
      trans := fun x y z hxy hyz => by
        rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy, h1⟩ | ⟨hx, hy, h1⟩ <;>
          rcases hyz with ⟨hy', hz⟩ | ⟨hy', hz, h2⟩ | ⟨hy', hz, h2⟩
        · linarith
        · linarith
        · exact Or.inl ⟨hx, hz⟩
        · exact Or.inl ⟨hx, hz⟩
        · exact Or.inr (Or.inl ⟨hx, hz, h1.trans h2⟩)
        · linarith
        · linarith
        · linarith
        · exact Or.inr (Or.inr ⟨hx, hz, h2.trans h1⟩) }
  peak := p
  prefers_of_between_right := fun {x y} hpy hyx => by
    change ¬ (((p : ℝ) ≤ x ∧ (y : ℝ) < p) ∨
      ((p : ℝ) ≤ x ∧ (p : ℝ) ≤ y ∧ (x : ℝ) ≤ y) ∨
      ((x : ℝ) < p ∧ (y : ℝ) < p ∧ (y : ℝ) ≤ x))
    rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) <;> linarith
  prefers_of_between_left := fun {x y} hxy hyp => by
    change ¬ (((p : ℝ) ≤ x ∧ (y : ℝ) < p) ∨
      ((p : ℝ) ≤ x ∧ (p : ℝ) ≤ y ∧ (x : ℝ) ≤ y) ∨
      ((x : ℝ) < p ∧ (y : ℝ) < p ∧ (y : ℝ) ≤ x))
    rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) <;> linarith

@[simp] theorem preferRight_peak (p : Set.Icc a b) : (preferRight p).peak = p := by
  unfold preferRight; rfl

theorem preferRight_prefers_of_ge_of_lt {p x y : Set.Icc a b}
    (hx : (p : ℝ) ≤ x) (hy : (y : ℝ) < p) : (preferRight p).Prefers x y := by
  change ¬ (((p : ℝ) ≤ y ∧ (x : ℝ) < p) ∨
    ((p : ℝ) ≤ y ∧ (p : ℝ) ≤ x ∧ (y : ℝ) ≤ x) ∨
    ((y : ℝ) < p ∧ (x : ℝ) < p ∧ (x : ℝ) ≤ y))
  rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) <;> linarith

/-- The unique single-peaked preference with peak at the left endpoint `a`
([SchummerVohra2007], §10.2.1, p. 247, `⪰^0`). -/
def leftExtreme (hab : a ≤ b) : Preference a b where
  ranking :=
    { AtLeast := fun x y => (x : ℝ) ≤ y
      total := fun x y => le_total _ _
      trans := fun _ _ _ h1 h2 => h1.trans h2 }
  peak := ⟨a, le_rfl, hab⟩
  prefers_of_between_right := fun _ hyx => not_le_of_gt hyx
  prefers_of_between_left := fun {x y} hxy hyp => by linarith [x.2.1]

/-- The unique single-peaked preference with peak at the right endpoint `b`
([SchummerVohra2007], §10.2.1, p. 247, `⪰^1`). -/
def rightExtreme (hab : a ≤ b) : Preference a b where
  ranking :=
    { AtLeast := fun x y => (y : ℝ) ≤ x
      total := fun x y => le_total _ _
      trans := fun _ _ _ h1 h2 => h2.trans h1 }
  peak := ⟨b, hab, le_rfl⟩
  prefers_of_between_right := fun {x y} hpy hyx => by linarith [x.2.2]
  prefers_of_between_left := fun hxy _ => not_le_of_gt hxy

@[simp] theorem leftExtreme_peak (hab : a ≤ b) :
    (leftExtreme hab).peak = ⟨a, le_rfl, hab⟩ := by
  unfold leftExtreme; rfl

@[simp] theorem rightExtreme_peak (hab : a ≤ b) :
    (rightExtreme hab).peak = ⟨b, hab, le_rfl⟩ := by
  unfold rightExtreme; rfl

@[simp] theorem leftExtreme_atLeast_iff (hab : a ≤ b) (x y : Set.Icc a b) :
    (leftExtreme hab).AtLeast x y ↔ (x : ℝ) ≤ y := by
  unfold leftExtreme AtLeast; rfl

@[simp] theorem rightExtreme_atLeast_iff (hab : a ≤ b) (x y : Set.Icc a b) :
    (rightExtreme hab).AtLeast x y ↔ (y : ℝ) ≤ x := by
  unfold rightExtreme AtLeast; rfl

/-- There is a unique single-peaked preference with peak at the left endpoint `a`
([SchummerVohra2007], §10.2.1, p. 247). -/
theorem eq_leftExtreme_of_peak_eq {hab : a ≤ b} {R : Preference a b}
    (hpeak : R.peak = ⟨a, le_rfl, hab⟩) : R = leftExtreme hab := by
  ext x y
  exact ⟨fun hxy => not_lt.mp fun hyx =>
    R.prefers_of_between_right (by rw [hpeak]; exact y.2.1) hyx hxy,
    fun hxy => R.atLeast_of_between_right (by rw [hpeak]; exact x.2.1) hxy⟩

/-- There is a unique single-peaked preference with peak at the right endpoint `b`
([SchummerVohra2007], §10.2.1, p. 247). -/
theorem eq_rightExtreme_of_peak_eq {hab : a ≤ b} {R : Preference a b}
    (hpeak : R.peak = ⟨b, hab, le_rfl⟩) : R = rightExtreme hab := by
  ext x y
  exact ⟨fun hxy => not_lt.mp fun hlt =>
    R.prefers_of_between_left hlt (by rw [hpeak]; exact y.2.2) hxy,
    fun hxy => R.atLeast_of_between_left hxy (by rw [hpeak]; exact x.2.2)⟩

end Preference

/-! ### Profiles, rules, and axioms -/

/-- A profile of single-peaked preferences over `Set.Icc a b` for agents `ι`. -/
abbrev Profile (ι : Type*) (a b : ℝ) := ι → Preference a b

/-- A social choice rule mapping single-peaked preference profiles to outcomes in `Set.Icc a b`. -/
abbrev Rule (ι : Type*) (a b : ℝ) := Profile ι a b → Set.Icc a b

namespace Rule

variable {ι : Type*} {a b : ℝ} (f : Rule ι a b)

/-- `f` is **strategy-proof**: no agent can obtain a strictly preferred outcome by misreporting
its preference relation ([SchummerVohra2007], §10.1–10.2, pp. 244–245). -/
@[expose] def IsStrategyProof : Prop :=
  ∀ (P Q : Profile ι a b) (i : ι), (∀ j, j ≠ i → P j = Q j) → (P i).AtLeast (f P) (f Q)

/-- `f` is **strongly group strategy-proof**: no coalition `A` can jointly misreport so that
every member of `A` is weakly better off and at least one member is strictly better off. -/
@[expose] def IsGroupStrategyProof : Prop :=
  ∀ (P Q : Profile ι a b) (A : Set ι), (∀ j, j ∉ A → P j = Q j) →
    ¬ ((∀ i ∈ A, (P i).AtLeast (f Q) (f P)) ∧ ∃ i ∈ A, (P i).Prefers (f Q) (f P))

/-- `f` is **anonymous**: permuting the agents does not change the outcome
([SchummerVohra2007], §10.2.1, p. 247). -/
@[expose] def IsAnonymous : Prop :=
  ∀ (σ : Equiv.Perm ι) (P : Profile ι a b), f (P ∘ σ) = f P

/-- `f` is **unanimous**: whenever every agent has peak `x`, the outcome is `x`
([SchummerVohra2007], §10.2, p. 245). -/
@[expose] def IsUnanimous : Prop :=
  ∀ (P : Profile ι a b) (x : Set.Icc a b), (∀ i, (P i).peak = x) → f P = x

/-- `f` is **Pareto-optimal** (weak Pareto): at no profile is there an alternative strictly
preferred to `f P` by every agent ([SchummerVohra2007], §10.2, p. 245). -/
@[expose] def IsParetoOptimal : Prop :=
  ∀ (P : Profile ι a b) (x : Set.Icc a b), ¬ ∀ i, (P i).Prefers x (f P)

/-- `f` is **strongly Pareto-optimal**: at no profile is there an alternative weakly preferred by
every agent and strictly preferred by at least one agent. -/
@[expose] def IsStrongParetoOptimal : Prop :=
  ∀ (P : Profile ι a b) (x : Set.Icc a b),
    ¬ ((∀ i, (P i).AtLeast x (f P)) ∧ ∃ i, (P i).Prefers x (f P))

/-- `f` is **peaks-only**: its outcome depends only on the profile of peaks
([Ching1997]; [SchummerVohra2007], §10.2.1, p. 247). -/
@[expose] def IsPeaksOnly : Prop :=
  ∀ P Q : Profile ι a b, (∀ i, (P i).peak = (Q i).peak) → f P = f Q

/-- `f` is **individually rational** with respect to `statusQuo`: at every profile, every agent
weakly prefers `f P` to `statusQuo` ([SchummerVohra2007], §10.2.2, p. 252). -/
@[expose] def IsIndividuallyRational (statusQuo : Set.Icc a b) : Prop :=
  ∀ (P : Profile ι a b) (i : ι), (P i).AtLeast (f P) statusQuo

/-- The **option set** of agent `i` at profile `P`: the outcomes obtainable by varying agent `i`'s
preference while keeping all other agents fixed ([SchummerVohra2007], §10.2.1, p. 248 and
Exercise 10.3, p. 264). -/
@[expose] def optionSet (P : Profile ι a b) (i : ι) : Set (Set.Icc a b) :=
  { x | ∃ Q : Profile ι a b, (∀ j, j ≠ i → P j = Q j) ∧ f Q = x }

variable {f}

theorem mem_optionSet_iff_update [DecidableEq ι] (P : Profile ι a b) (i : ι) (x : Set.Icc a b) :
    x ∈ f.optionSet P i ↔ ∃ R' : Preference a b, f (Function.update P i R') = x :=
  ⟨fun ⟨Q, hQ, h⟩ => ⟨Q i, h ▸ congrArg f (funext fun j => by
    by_cases hj : j = i <;> simp [hj, hQ])⟩,
   fun ⟨R', h⟩ => ⟨Function.update P i R', fun _ hji => (Function.update_of_ne hji R' P).symm, h⟩⟩

theorem IsGroupStrategyProof.isStrategyProof (hf : f.IsGroupStrategyProof) : f.IsStrategyProof :=
  fun P Q i hPQ => by_contra fun hnot =>
    hf P Q {i} (fun j hj => hPQ j hj) ⟨fun _ hj =>
      Set.mem_singleton_iff.mp hj ▸ (P i).atLeast_of_prefers hnot, i, Set.mem_singleton i, hnot⟩

theorem IsStrategyProof.atLeast_update [DecidableEq ι] (hf : f.IsStrategyProof)
    (P : Profile ι a b) (i : ι) (R' : Preference a b) :
    (P i).AtLeast (f P) (f (Function.update P i R')) :=
  hf P (Function.update P i R') i fun _ hji => (Function.update_of_ne hji R' P).symm

theorem IsStrategyProof.atLeast_of_mem_optionSet (hf : f.IsStrategyProof)
    (P : Profile ι a b) (i : ι) {x : Set.Icc a b} (hx : x ∈ f.optionSet P i) :
    (P i).AtLeast (f P) x := by
  rcases hx with ⟨Q, hQ, rfl⟩
  exact hf P Q i hQ

/-! ### Pareto-optimality and Lemma 10.1 -/

/-- On single-peaked profiles with finitely many agents, `f` is Pareto-optimal iff at every profile
the outcome lies within the convex hull of the agents' peaks. -/
theorem isParetoOptimal_iff_peaks_bounds [Finite ι] [Nonempty ι] :
    f.IsParetoOptimal ↔
      ∀ P : Profile ι a b,
        (∃ i : ι, ((P i).peak : ℝ) ≤ f P) ∧ (∃ j : ι, (f P : ℝ) ≤ (P j).peak) := by
  let _ := Fintype.ofFinite ι
  refine ⟨fun hPO P => ⟨?_, ?_⟩, fun hbounds P x hpref => ?_⟩
  · by_contra! h
    obtain ⟨i₀, _, hi₀⟩ :=
      Finset.exists_min_image Finset.univ (fun i => ((P i).peak : ℝ)) Finset.univ_nonempty
    exact hPO P (P i₀).peak fun i =>
      (P i).prefers_of_between_left (h i₀) (hi₀ i (Finset.mem_univ i))
  · by_contra! h
    obtain ⟨j₀, _, hj₀⟩ :=
      Finset.exists_max_image Finset.univ (fun i => ((P i).peak : ℝ)) Finset.univ_nonempty
    exact hPO P (P j₀).peak fun i =>
      (P i).prefers_of_between_right (hj₀ i (Finset.mem_univ i)) (h j₀)
  · obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hbounds P
    rcases lt_trichotomy (x : ℝ) (f P) with hlt | heq | hgt
    · exact (P j).prefers_asymm ((P j).prefers_of_between_left hlt hj) (hpref j)
    · obtain ⟨i₀⟩ := ‹Nonempty ι›
      exact (P i₀).prefers_irrefl (f P) (Subtype.ext heq ▸ hpref i₀)
    · exact (P i).prefers_asymm ((P i).prefers_of_between_right hi hgt) (hpref i)

/-- On single-peaked profiles with finitely many agents, weak and strong Pareto-optimality
coincide. -/
theorem isParetoOptimal_iff_isStrongParetoOptimal [Finite ι] [Nonempty ι] :
    f.IsParetoOptimal ↔ f.IsStrongParetoOptimal := by
  constructor
  · intro hPO P x ⟨hatLeast, i₀, hpref⟩
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := (isParetoOptimal_iff_peaks_bounds.mp hPO) P
    rcases lt_trichotomy (x : ℝ) (f P) with hlt | heq | hgt
    · exact (P j).prefers_of_between_left hlt hj (hatLeast j)
    · exact (P i₀).prefers_irrefl (f P) (Subtype.ext heq ▸ hpref)
    · exact (P i).prefers_of_between_right hi hgt (hatLeast i)
  · intro hSPO P x hpref
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    exact hSPO P x ⟨fun i => (P i).atLeast_of_prefers (hpref i), i₀, hpref i₀⟩

theorem IsParetoOptimal.isUnanimous [Finite ι] [Nonempty ι] (hPO : f.IsParetoOptimal) :
    f.IsUnanimous := by
  intro P x hpeaks
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := (isParetoOptimal_iff_peaks_bounds.mp hPO) P
  rw [hpeaks i] at hi
  rw [hpeaks j] at hj
  exact Subtype.ext (le_antisymm hj hi)

theorem IsUnanimous.surjective (hU : f.IsUnanimous) : Function.Surjective f :=
  fun x => ⟨fun _ => Preference.symmetric x, hU _ x fun _ => rfl⟩

/-- Strategy-proofness and surjectivity imply unanimity ([SchummerVohra2007], Lemma 10.1,
pp. 245–246). -/
theorem IsStrategyProof.isUnanimous_of_surjective [Finite ι]
    (hf : f.IsStrategyProof) (hsurj : Function.Surjective f) : f.IsUnanimous := by
  classical
  intro Q x hpeaks
  obtain ⟨P, hP⟩ := hsurj x
  refine Function.update_induction (x := P) (y := Q) (P := fun R => f R = x) hP ?_
  intro R _ hR i _ _
  have hsp : (Q i).AtLeast (f (Function.update R i (Q i))) (f R) := by
    have h := hf (Function.update R i (Q i)) R i fun j hji => Function.update_of_ne hji (Q i) R
    simpa only [Function.update_self] using h
  rw [hR, ← hpeaks i] at hsp
  rw [(Q i).eq_peak_of_atLeast_peak hsp, hpeaks i]

/-- Strategy-proofness and unanimity imply Pareto-optimality ([SchummerVohra2007], Lemma 10.1,
pp. 245–246). -/
theorem IsStrategyProof.isParetoOptimal_of_isUnanimous [Finite ι] [Nonempty ι]
    (hf : f.IsStrategyProof) (hU : f.IsUnanimous) : f.IsParetoOptimal := by
  classical
  let _ := Fintype.ofFinite ι
  refine isParetoOptimal_iff_peaks_bounds.mpr fun P => ⟨?_, ?_⟩
  · by_contra! h
    obtain ⟨i₀, _, hi₀⟩ :=
      Finset.exists_min_image Finset.univ (fun i => ((P i).peak : ℝ)) Finset.univ_nonempty
    let p₁ := (P i₀).peak
    let Q : Profile ι a b := fun _ => Preference.preferLeft p₁
    have hQ : f Q = f P := Function.update_induction (x := P) (y := Q)
      (P := fun R => f R = f P) rfl fun R _ hR i hRi _ => by
      set y := f (Function.update R i (Q i))
      have hsp1 : (P i).AtLeast (f P) y := hR ▸ hRi ▸ hf.atLeast_update R i (Q i)
      have hsp2 : (Q i).AtLeast y (f P) := by
        simpa only [Function.update_self, hR] using
          hf (Function.update R i (Q i)) R i fun _ hji => Function.update_of_ne hji _ _
      have hy_ge : (f P : ℝ) ≤ y := not_lt.mp fun hlt =>
        (Q i).prefers_of_between_left hlt (h i₀).le hsp2
      have hy_le : (y : ℝ) ≤ p₁ := not_lt.mp fun hgt =>
        Preference.preferLeft_prefers_of_le_of_gt (h i₀).le hgt hsp2
      exact Subtype.ext <| le_antisymm (not_lt.mp fun hgt =>
        (P i).prefers_of_between_left hgt (hy_le.trans (hi₀ i (Finset.mem_univ i))) hsp1) hy_ge
    linarith [h i₀,
      congrArg Subtype.val (hQ.symm.trans (hU Q p₁ fun _ => Preference.preferLeft_peak p₁))]
  · by_contra! h
    obtain ⟨j₀, _, hj₀⟩ :=
      Finset.exists_max_image Finset.univ (fun i => ((P i).peak : ℝ)) Finset.univ_nonempty
    let pₙ := (P j₀).peak
    let Q : Profile ι a b := fun _ => Preference.preferRight pₙ
    have hQ : f Q = f P := Function.update_induction (x := P) (y := Q)
      (P := fun R => f R = f P) rfl fun R _ hR i hRi _ => by
      set y := f (Function.update R i (Q i))
      have hsp1 : (P i).AtLeast (f P) y := hR ▸ hRi ▸ hf.atLeast_update R i (Q i)
      have hsp2 : (Q i).AtLeast y (f P) := by
        simpa only [Function.update_self, hR] using
          hf (Function.update R i (Q i)) R i fun _ hji => Function.update_of_ne hji _ _
      have hy_le : (y : ℝ) ≤ f P := not_lt.mp fun hgt =>
        (Q i).prefers_of_between_right (h j₀).le hgt hsp2
      have hy_ge : (pₙ : ℝ) ≤ y := not_lt.mp fun hlt =>
        Preference.preferRight_prefers_of_ge_of_lt (h j₀).le hlt hsp2
      exact Subtype.ext <| le_antisymm hy_le (not_lt.mp fun hlt =>
        (P i).prefers_of_between_right ((hj₀ i (Finset.mem_univ i)).trans hy_ge) hlt hsp1)
    linarith [h j₀,
      congrArg Subtype.val (hQ.symm.trans (hU Q pₙ fun _ => Preference.preferRight_peak pₙ))]

/-- **Lemma 10.1** ([SchummerVohra2007], §10.2, pp. 245–246): for a strategy-proof rule on
single-peaked preferences, surjectivity is equivalent to unanimity. -/
theorem IsStrategyProof.surjective_iff_isUnanimous [Finite ι] (hf : f.IsStrategyProof) :
    Function.Surjective f ↔ f.IsUnanimous :=
  ⟨hf.isUnanimous_of_surjective, IsUnanimous.surjective⟩

/-- **Lemma 10.1** ([SchummerVohra2007], §10.2, pp. 245–246): for a strategy-proof rule on
single-peaked preferences, surjectivity is equivalent to Pareto-optimality. -/
theorem IsStrategyProof.surjective_iff_isParetoOptimal [Finite ι] [Nonempty ι]
    (hf : f.IsStrategyProof) :
    Function.Surjective f ↔ f.IsParetoOptimal :=
  ⟨fun hs => hf.isParetoOptimal_of_isUnanimous (hf.isUnanimous_of_surjective hs),
    fun hPO => hPO.isUnanimous.surjective⟩

/-- **Lemma 10.1** ([SchummerVohra2007], §10.2, pp. 245–246): for a strategy-proof rule on
single-peaked preferences, unanimity is equivalent to Pareto-optimality. -/
theorem IsStrategyProof.isUnanimous_iff_isParetoOptimal [Finite ι] [Nonempty ι]
    (hf : f.IsStrategyProof) :
    f.IsUnanimous ↔ f.IsParetoOptimal :=
  ⟨hf.isParetoOptimal_of_isUnanimous, IsParetoOptimal.isUnanimous⟩

/-! ### Option sets (Footnote 6, Exercise 10.3) and Ching's peaks-only theorem -/

/-- Under strategy-proofness alone (without surjectivity), every single-agent option set is closed
in `ℝ` ([SchummerVohra2007], §10.2.1 footnote 6, p. 249). -/
theorem IsStrategyProof.isClosed_optionSet (hf : f.IsStrategyProof)
    (P : Profile ι a b) (i : ι) :
    IsClosed (Subtype.val '' f.optionSet P i) := by
  classical
  rw [← closure_subset_iff_isClosed]
  intro z hz
  let zPt : Set.Icc a b := ⟨z, isClosed_Icc.closure_subset_iff.mpr
    (by rintro _ ⟨x, -, rfl⟩; exact x.2) hz⟩
  have hopt_upd : ∀ {R' : Preference a b} {y : Set.Icc a b}, y ∈ f.optionSet P i →
      R'.AtLeast (f (Function.update P i R')) y := by
    rintro R' y ⟨Q, hQ, hQy⟩
    have h := hf (Function.update P i R') Q i fun j hji => by
      rw [Function.update_of_ne hji, hQ j hji]
    rwa [Function.update_self, hQy] at h
  rw [show Subtype.val '' f.optionSet P i =
      ((Subtype.val '' f.optionSet P i) ∩ Set.Iic z) ∪
      ((Subtype.val '' f.optionSet P i) ∩ Set.Ici z) by
    ext t
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ici]
    exact ⟨fun ht => (le_total t z).imp (⟨ht, ·⟩) (⟨ht, ·⟩), fun h => h.elim And.left And.left⟩,
    closure_union] at hz
  rcases hz with hzL | hzR
  · let P_L := Function.update P i (Preference.preferLeft zPt)
    refine ⟨f P_L, (mem_optionSet_iff_update P i _).mpr ⟨_, rfl⟩, ?_⟩
    rcases lt_trichotomy (f P_L : ℝ) z with hlt | heq | hgt
    · obtain ⟨_, ⟨⟨y, hyO, rfl⟩, hyz⟩, ht2⟩ :=
        Metric.mem_closure_iff.mp hzL (z - f P_L) (by linarith)
      rw [Real.dist_eq] at ht2
      exact absurd (hopt_upd hyO) ((Preference.preferLeft zPt).prefers_of_between_left
        (by linarith [(abs_lt.mp ht2).2]) (Set.mem_Iic.mp hyz))
    · exact heq
    · obtain ⟨_, ⟨⟨y, hyO, rfl⟩, hyz⟩, _⟩ := Metric.mem_closure_iff.mp hzL 1 one_pos
      exact absurd (hopt_upd hyO)
        (Preference.preferLeft_prefers_of_le_of_gt (p := zPt) (Set.mem_Iic.mp hyz) hgt)
  · let P_R := Function.update P i (Preference.preferRight zPt)
    refine ⟨f P_R, (mem_optionSet_iff_update P i _).mpr ⟨_, rfl⟩, ?_⟩
    rcases lt_trichotomy (f P_R : ℝ) z with hlt | heq | hgt
    · obtain ⟨_, ⟨⟨y, hyO, rfl⟩, hyz⟩, _⟩ := Metric.mem_closure_iff.mp hzR 1 one_pos
      exact absurd (hopt_upd hyO)
        (Preference.preferRight_prefers_of_ge_of_lt (p := zPt) (Set.mem_Ici.mp hyz) hlt)
    · exact heq
    · obtain ⟨_, ⟨⟨y, hyO, rfl⟩, hyz⟩, ht2⟩ :=
        Metric.mem_closure_iff.mp hzR (f P_R - z) (by linarith)
      rw [Real.dist_eq] at ht2
      exact absurd (hopt_upd hyO) ((Preference.preferRight zPt).prefers_of_between_right
        (Set.mem_Ici.mp hyz) (by linarith [(abs_lt.mp ht2).1]))

/-- **Exercise 10.3** ([SchummerVohra2007], pp. 264–265): for a strategy-proof onto rule on
single-peaked preferences, every single-agent option set is the closed interval between the
outcomes at the two extreme reports `leftExtreme` and `rightExtreme`, proved directly without
appealing to the generalized median characterization (Theorem 10.4). -/
theorem IsStrategyProof.optionSet_eq_Icc [Finite ι] [DecidableEq ι]
    (hf : f.IsStrategyProof) (hsurj : Function.Surjective f)
    (P : Profile ι a b) (i : ι) (hab : a ≤ b) :
    f.optionSet P i =
      Set.Icc (f (Function.update P i (Preference.leftExtreme hab)))
        (f (Function.update P i (Preference.rightExtreme hab))) := by
  have : Nonempty ι := ⟨i⟩
  have hPO : f.IsParetoOptimal := (hf.surjective_iff_isParetoOptimal).mp hsurj
  set l := f (Function.update P i (Preference.leftExtreme hab))
  set u := f (Function.update P i (Preference.rightExtreme hab))
  ext z
  simp only [Set.mem_Icc]
  refine ⟨fun ⟨Q, hQ, hQz⟩ => ?_, fun ⟨hlz, hzu⟩ => ?_⟩
  · subst hQz
    refine ⟨?_, ?_⟩
    · have h := hf (Function.update P i (Preference.leftExtreme hab)) Q i fun j hji => by
        rw [Function.update_of_ne hji, hQ j hji]
      rw [Function.update_self, Preference.leftExtreme_atLeast_iff] at h
      exact Subtype.coe_le_coe.mp h
    · have h := hf (Function.update P i (Preference.rightExtreme hab)) Q i fun j hji => by
        rw [Function.update_of_ne hji, hQ j hji]
      rw [Function.update_self, Preference.rightExtreme_atLeast_iff] at h
      exact Subtype.coe_le_coe.mp h
  · let P_L := Function.update P i (Preference.preferLeft z)
    let P_R := Function.update P i (Preference.preferRight z)
    have hxL_le : (f P_L : ℝ) ≤ z := not_lt.mp fun hgt =>
      Preference.preferLeft_prefers_of_le_of_gt hlz hgt <| by
        have h := hf.atLeast_update P_L i (Preference.leftExtreme hab)
        dsimp only [P_L] at h ⊢
        rw [Function.update_self, Function.update_idem] at h
        exact h
    have hxR_ge : (z : ℝ) ≤ f P_R := not_lt.mp fun hlt =>
      Preference.preferRight_prefers_of_ge_of_lt hzu hlt <| by
        have h := hf.atLeast_update P_R i (Preference.rightExtreme hab)
        dsimp only [P_R] at h ⊢
        rw [Function.update_self, Function.update_idem] at h
        exact h
    by_cases hEq : f P_R = z
    · exact (mem_optionSet_iff_update P i z).mpr ⟨Preference.preferRight z, hEq⟩
    · exfalso
      have hxR_gt : (z : ℝ) < f P_R := lt_of_le_of_ne hxR_ge fun h => hEq (Subtype.ext h.symm)
      let Q_L : Profile ι a b :=
        fun j => if j = i ∨ ((P j).peak : ℝ) ≤ z then Preference.preferLeft z else P j
      let Q_R : Profile ι a b :=
        fun j => if j = i ∨ ((P j).peak : ℝ) ≤ z then Preference.preferRight z else P j
      have hfQL_le : (f Q_L : ℝ) ≤ z := Function.update_induction (x := P_L) (y := Q_L)
        (P := fun R => (f R : ℝ) ≤ z) hxL_le fun R _ hR j hjP hjne => by
        have hj_cond : j = i ∨ ((P j).peak : ℝ) ≤ z := by_contra fun hnot => hjne <| by
          rw [hjP]
          dsimp only [P_L, Q_L]
          rw [Function.update_of_ne fun h => hnot (.inl h), ite_eq_right hnot]
        set yL := f (Function.update R j (Q_L j))
        refine not_lt.mp fun hgt => Preference.preferLeft_prefers_of_le_of_gt hR hgt ?_
        have h := hf (Function.update R j (Q_L j)) R j fun _ hkj => Function.update_of_ne hkj _ _
        change (Function.update R j (Q_L j) j).AtLeast yL (f R) at h
        rw [Function.update_self, show Q_L j = Preference.preferLeft z from ite_eq_left hj_cond]
          at h
        exact h
      obtain ⟨⟨j₀, hj₀⟩, _⟩ := (isParetoOptimal_iff_peaks_bounds.mp hPO) Q_L
      have hfQL_eq : f Q_L = z := Subtype.ext <| le_antisymm hfQL_le <|
        (show (z : ℝ) ≤ (Q_L j₀).peak by
          dsimp only [Q_L]
          split_ifs with hc
          · simp
          · push Not at hc; exact hc.2.le).trans hj₀
      have hfQR_eq_z : f Q_R = z := Function.update_induction (x := Q_L) (y := Q_R)
        (P := fun R => f R = z) hfQL_eq fun R _ hR j hjQL hjne => by
        have hj_cond : j = i ∨ ((P j).peak : ℝ) ≤ z := by_contra fun hnot => hjne <| by
          rw [hjQL]
          dsimp only [Q_L, Q_R]
          rw [ite_eq_right hnot, ite_eq_right hnot]
        set yR := f (Function.update R j (Q_R j))
        have h := hf (Function.update R j (Q_R j)) R j fun _ hkj => Function.update_of_ne hkj _ _
        change (Function.update R j (Q_R j) j).AtLeast yR (f R) at h
        rw [Function.update_self, hR,
          show Q_R j = Preference.preferRight z from ite_eq_left hj_cond] at h
        exact (Preference.preferRight z).eq_peak_of_atLeast_peak
          ((Preference.preferRight_peak z).symm ▸ h)
      have hfQR_eq_xR : f Q_R = f P_R := Function.update_induction (x := P_R) (y := Q_R)
        (P := fun R => f R = f P_R) rfl fun R _ hR j hjPR hjne => by
        have hj_not_i : j ≠ i := fun h => hjne <| by
          subst h
          rw [hjPR]
          dsimp only [P_R, Q_R]
          rw [Function.update_self, ite_eq_left (.inl rfl)]
        have hj_le : ((P j).peak : ℝ) ≤ z := by_contra fun hgt => hjne <| by
          rw [hjPR]
          dsimp only [P_R, Q_R]
          rw [Function.update_of_ne hj_not_i, ite_eq_right (not_or.mpr ⟨hj_not_i, hgt⟩)]
        have hQRj : Q_R j = Preference.preferRight z := ite_eq_left (.inr hj_le)
        set y := f (Function.update R j (Q_R j))
        have hsp1 : (P j).AtLeast (f P_R) y := by
          have hRj : R j = P j := hjPR.trans (Function.update_of_ne hj_not_i _ _)
          exact hR ▸ hRj ▸ hf.atLeast_update R j (Q_R j)
        have hsp2 : (Preference.preferRight z).AtLeast y (f P_R) := by
          have h := hf (Function.update R j (Q_R j)) R j fun _ hkj => Function.update_of_ne hkj _ _
          change (Function.update R j (Q_R j) j).AtLeast y (f R) at h
          rwa [Function.update_self, hR, hQRj] at h
        have hy_ge_z : (z : ℝ) ≤ y := not_lt.mp fun hlt =>
          Preference.preferRight_prefers_of_ge_of_lt hxR_ge hlt hsp2
        exact Subtype.ext <| le_antisymm
          (not_lt.mp fun hgt => (Preference.preferRight z).prefers_of_between_right hxR_ge hgt hsp2)
          (not_lt.mp fun hlt => (P j).prefers_of_between_right (hj_le.trans hy_ge_z) hlt hsp1)
      exact hxR_gt.ne' (congrArg Subtype.val (hfQR_eq_xR.symm.trans hfQR_eq_z))

/-- For a strategy-proof onto rule on single-peaked preferences, agent `i`'s response is its peak
clamped to the option-set endpoints `[l, u]`. -/
theorem IsStrategyProof.apply_update_eq_clamp [Finite ι] [DecidableEq ι]
    (hf : f.IsStrategyProof) (hsurj : Function.Surjective f)
    (P : Profile ι a b) (i : ι) (R' : Preference a b) (hab : a ≤ b) :
    (f (Function.update P i R') : ℝ) =
      max (f (Function.update P i (Preference.leftExtreme hab)) : ℝ)
        (min (R'.peak : ℝ) (f (Function.update P i (Preference.rightExtreme hab)) : ℝ)) := by
  set l := f (Function.update P i (Preference.leftExtreme hab))
  set u := f (Function.update P i (Preference.rightExtreme hab))
  set y := f (Function.update P i R')
  have hO := hf.optionSet_eq_Icc hsurj P i hab
  have hy_mem : y ∈ Set.Icc l u := hO ▸ (mem_optionSet_iff_update P i y).mpr ⟨R', rfl⟩
  have hlu : (l : ℝ) ≤ u := hy_mem.1.trans hy_mem.2
  have hO' : f.optionSet (Function.update P i R') i = Set.Icc l u := by
    ext w
    rw [mem_optionSet_iff_update, ← hO, mem_optionSet_iff_update]
    simp only [Function.update_idem]
  have hsp : ∀ x ∈ Set.Icc l u, R'.AtLeast y x := fun x hx => by
    have h := hf.atLeast_of_mem_optionSet (Function.update P i R') i (hO' ▸ hx)
    rwa [Function.update_self] at h
  rcases le_or_gt (R'.peak : ℝ) l with hpl | hlp
  · rw [show y = l from by_contra fun hne => R'.prefers_of_between_right hpl
      (lt_of_le_of_ne hy_mem.1 fun h => hne (Subtype.ext h.symm)) (hsp l ⟨le_rfl, hlu⟩),
      min_eq_left (hpl.trans hlu), max_eq_left hpl]
  · rcases le_or_gt (R'.peak : ℝ) u with hpu | hup
    · rw [R'.eq_peak_of_atLeast_peak (hsp R'.peak ⟨hlp.le, hpu⟩),
        min_eq_left hpu, max_eq_right hlp.le]
    · rw [show y = u from by_contra fun hne => R'.prefers_of_between_left
        (lt_of_le_of_ne hy_mem.2 fun h => hne (Subtype.ext h)) hup.le (hsp u ⟨hlu, le_rfl⟩),
        min_eq_right hup.le, max_eq_right hlu]

/-- **Ching's peaks-only theorem** ([Ching1997]; [SchummerVohra2007], §10.2.1, p. 247 and §10.6,
p. 263): every strategy-proof onto rule on ordinal single-peaked preferences depends only on the
profile of agents' peaks. -/
theorem IsStrategyProof.isPeaksOnly_of_surjective [Finite ι]
    (hf : f.IsStrategyProof) (hsurj : Function.Surjective f) : f.IsPeaksOnly := by
  classical
  intro P Q hpeaks
  symm
  refine Function.update_induction (x := P) (y := Q) (P := fun R => f R = f P) rfl
    fun R _ hR i hRi _ => ?_
  have hab : a ≤ b := (P i).peak.2.1.trans (P i).peak.2.2
  have h1 := hf.apply_update_eq_clamp hsurj R i (Q i) hab
  have h2 := hf.apply_update_eq_clamp hsurj R i (P i) hab
  have hupd : Function.update R i (P i) = R := hRi ▸ Function.update_eq_self i R
  rw [hupd, hR] at h2
  rw [← hpeaks i] at h1
  exact Subtype.ext (h1.trans h2.symm)

end Rule

end Cslib.GameTheory.SocialChoice.SinglePeaked
