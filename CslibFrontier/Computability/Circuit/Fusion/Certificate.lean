/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Fusion.Extension

/-!
# Finite certificates for semi-ultrafilter covers

A certificate labels both components and the intersection of each cover pair. A fixed additional
empty set is rejected. Invalid labels are detected by a rejected superset of an accepted or
required set, or two rejected sets covering the carrier. All pairs, including equal pairs and
the fixed empty set, participate in these tests. A valid certificate extends to a semi-ultrafilter;
if it also preserves every listed pair it contradicts a cover above a target point.

Only the two component labels need to be guessed. Defining an intersection's label to be the
conjunction of its component labels preserves that pair automatically. A rejected intersection's
consistency violation is also a violation at a rejected component, since each kind of conflict
persists when its set is enlarged. Thus the compressed test checks just the two components per
pair and the fixed empty set. This compression is an original refinement of the construction.

## Main definitions

* `Cslib.Circuits.Fusion.PairCertificate.size`,
  `Cslib.Circuits.Fusion.PairCertificate.left`,
  `Cslib.Circuits.Fusion.PairCertificate.right`,
  `Cslib.Circuits.Fusion.PairCertificate.inter`: the certificate bit count and the indices for each
  pair's first set, second set, and intersection.
* `Cslib.Circuits.Fusion.PairCertificate.sets`,
  `Cslib.Circuits.Fusion.PairCertificate.label`,
  `Cslib.Circuits.Fusion.PairCertificate.pointLabels`: the three sets per pair and fixed empty set,
  extended certificate labels, and point-membership labels.
* `Cslib.Circuits.Fusion.PairCertificate.Invalid`: the grouped consistency violations.
* `Cslib.Circuits.Fusion.PairCertificate.BreaksPair`: failure of pair preservation.
* `Cslib.Circuits.Fusion.PairCertificate.compactSize`,
  `Cslib.Circuits.Fusion.PairCertificate.expandLabels`: two component bits per pair and their
  extension by conjunctions at the intersections.
* `Cslib.Circuits.Fusion.PairCertificate.conflicts`,
  `Cslib.Circuits.Fusion.PairCertificate.compactInvalid`: consistency conflicts and the compressed
  rejection test.

## Main results

* `Cslib.Circuits.Fusion.PairCertificate.exists_filter_of_not_invalid`: realize a valid certificate.
* `Cslib.Circuits.Fusion.PairCertificate.invalid_expandLabels_iff`: intersection rejection groups
  are redundant for compressed labels.
* `Cslib.Circuits.Fusion.PairCertificate.expandLabels_compactPointLabels`: compression preserves
  every point-membership certificate.

## References

* [B. P. Cavalar and I. C. Oliveira, *Boolean Circuit Complexity and Two-Dimensional Cover
  Problems*][CavalarOliveira2025], Theorem 45, credited there to Karchmer.
-/

@[expose] public section

namespace Cslib.Circuits.Fusion.PairCertificate

variable {U : Type*} (pairs : List (Set U × Set U))

/-- Three certificate bits per pair: its first set, second set and intersection. -/
abbrev size := pairs.length + (pairs.length + pairs.length)

/-- The first-component certificate index. -/
def left (i : Fin pairs.length) : Fin (size pairs) := Fin.castAdd _ i

/-- The second-component certificate index. -/
def right (i : Fin pairs.length) : Fin (size pairs) :=
  Fin.natAdd _ (Fin.castAdd _ i)

/-- The intersection certificate index. -/
def inter (i : Fin pairs.length) : Fin (size pairs) := Fin.natAdd _ (Fin.natAdd _ i)

/-- A fixed empty set supplements the three sets for each pair. -/
def sets : Option (Fin (size pairs)) → Set U
  | none => ∅
  | some i => Fin.append (fun i => (pairs.get i).1)
      (Fin.append (fun i => (pairs.get i).2) (fun i => (pairs.get i).1 ∩ (pairs.get i).2)) i

/-- The fixed empty set has label false. -/
def label (y : Fin (size pairs) → Bool) : Option (Fin (size pairs)) → Bool
  | none => false
  | some i => y i

/-- The set at `left pairs i` is the first component of the `i`-th pair. -/
@[simp] theorem sets_left (i : Fin pairs.length) :
    sets pairs (some (left pairs i)) = (pairs.get i).1 := Fin.append_left ..

/-- The set at `right pairs i` is the second component of the `i`-th pair. -/
@[simp] theorem sets_right (i : Fin pairs.length) :
    sets pairs (some (right pairs i)) = (pairs.get i).2 := by simp [sets, right]

/-- The set at `inter pairs i` is the intersection of the two components of the `i`-th pair. -/
@[simp] theorem sets_inter (i : Fin pairs.length) :
    sets pairs (some (inter pairs i)) = (pairs.get i).1 ∩ (pairs.get i).2 := by
  simp only [sets, inter, Fin.append_right]

/-- Accepting a subset, rejecting a covering partner, or requiring a source contained in `s`
prevents a consistent semi-ultrafilter certificate from rejecting `s`. -/
def conflicts {n : ℕ} (sources : Fin n → Set U) (x : Fin n → Bool)
    (y : Fin (size pairs) → Bool) (s : Set U) : Prop :=
  (∃ i, sets pairs i ⊆ s ∧ label pairs y i = true) ∨
    (∃ k, s ∪ sets pairs k = Set.univ ∧ label pairs y k = false) ∨
    (∃ l, sources l ⊆ s ∧ x l = true)

/-- Consistency violations, grouped by a rejected set. The sources marked true must be accepted. -/
def Invalid {n : ℕ} (sources : Fin n → Set U) (x : Fin n → Bool)
    (y : Fin (size pairs) → Bool) : Prop :=
  ∃ j, label pairs y j = false ∧ conflicts pairs sources x y (sets pairs j)

/-- An accepted pair with rejected intersection. -/
def BreaksPair (y : Fin (size pairs) → Bool) : Prop :=
  ∃ i, y (left pairs i) = true ∧ y (right pairs i) = true ∧ y (inter pairs i) = false

/-- Two certificate bits per pair, ordered as all first components then all second components. -/
abbrev compactSize := pairs.length + pairs.length

/-- Extend component labels by assigning each intersection the conjunction of its two labels. -/
def expandLabels (y : Fin (compactSize pairs) → Bool) : Fin (size pairs) → Bool :=
  Fin.append (fun i => y (Fin.castAdd pairs.length i))
    (Fin.append (fun i => y (Fin.natAdd pairs.length i))
      (fun i => y (Fin.castAdd pairs.length i) && y (Fin.natAdd pairs.length i)))

/-- Expansion preserves first-component labels. -/
@[simp] theorem expandLabels_left (y : Fin (compactSize pairs) → Bool) (i : Fin pairs.length) :
    expandLabels pairs y (left pairs i) = y (Fin.castAdd pairs.length i) :=
  Fin.append_left ..

/-- Expansion preserves second-component labels. -/
@[simp] theorem expandLabels_right (y : Fin (compactSize pairs) → Bool) (i : Fin pairs.length) :
    expandLabels pairs y (right pairs i) = y (Fin.natAdd pairs.length i) := by
  simp only [expandLabels, right, Fin.append_left, Fin.append_right]

/-- An expanded intersection label is the conjunction of its component labels. -/
@[simp] theorem expandLabels_inter (y : Fin (compactSize pairs) → Bool) (i : Fin pairs.length) :
    expandLabels pairs y (inter pairs i) =
      (y (Fin.castAdd pairs.length i) && y (Fin.natAdd pairs.length i)) := by
  simp only [expandLabels, inter, Fin.append_right]

/-- Component labels expanded by conjunction never violate pair preservation. -/
theorem not_breaksPair_expandLabels (y : Fin (compactSize pairs) → Bool) :
    ¬ BreaksPair pairs (expandLabels pairs y) := by
  rintro ⟨i, hi, hj, hk⟩
  simp_all [expandLabels_left, expandLabels_right, expandLabels_inter]

/-- Compressed consistency checks the fixed empty set and each rejected component, with
intersection labels supplied by `expandLabels`. -/
def compactInvalid {n : ℕ} (sources : Fin n → Set U) (x : Fin n → Bool)
    (y : Fin (compactSize pairs) → Bool) : Prop :=
  conflicts pairs sources x (expandLabels pairs y) ∅ ∨
    (∃ i, y (Fin.castAdd pairs.length i) = false ∧
      conflicts pairs sources x (expandLabels pairs y) (pairs.get i).1) ∨
    (∃ i, y (Fin.natAdd pairs.length i) = false ∧
      conflicts pairs sources x (expandLabels pairs y) (pairs.get i).2)

private theorem conflicts_mono {n : ℕ} (sources : Fin n → Set U) (x : Fin n → Bool)
    (y : Fin (size pairs) → Bool) {s t : Set U} (hst : s ⊆ t) :
    conflicts pairs sources x y s → conflicts pairs sources x y t := by
  rintro (⟨i, hi, hl⟩ | ⟨i, hi, hl⟩ | ⟨i, hi, hl⟩)
  · exact Or.inl ⟨i, hi.trans hst, hl⟩
  · exact Or.inr (Or.inl ⟨i, Set.univ_subset_iff.mp
      (hi ▸ Set.union_subset_union_left _ hst), hl⟩)
  · exact Or.inr (Or.inr ⟨i, hi.trans hst, hl⟩)

/-- Checking rejected intersections adds no constraint: a rejected factor has the same conflict.
No nonemptiness or distinctness assumption is imposed on the carrier or the cover pairs. -/
theorem invalid_expandLabels_iff {n : ℕ} (sources : Fin n → Set U) (x : Fin n → Bool)
    (y : Fin (compactSize pairs) → Bool) :
    Invalid pairs sources x (expandLabels pairs y) ↔ compactInvalid pairs sources x y := by
  constructor
  · rintro ⟨_ | j, hj, h⟩
    · exact Or.inl h
    · induction j using Fin.addCases with
      | left i =>
        exact Or.inr (Or.inl ⟨i, by simpa only [label, expandLabels, Fin.append_left] using hj,
          by simpa only [sets, Fin.append_left] using h⟩)
      | right j =>
        induction j using Fin.addCases with
        | left i =>
          exact Or.inr (Or.inr ⟨i,
            by simpa only [label, expandLabels, Fin.append_left, Fin.append_right] using hj,
            by simpa only [sets, Fin.append_left, Fin.append_right] using h⟩)
        | right i =>
          have hconf : conflicts pairs sources x (expandLabels pairs y)
              ((pairs.get i).1 ∩ (pairs.get i).2) := by
            simpa only [sets, Fin.append_right] using h
          have hab : y (Fin.castAdd pairs.length i) = false ∨
              y (Fin.natAdd pairs.length i) = false := by
            simpa only [label, expandLabels, Fin.append_right, Bool.and_eq_false_iff] using hj
          rcases hab with ha | hb
          · exact Or.inr (Or.inl ⟨i, ha,
              conflicts_mono pairs sources x _ Set.inter_subset_left hconf⟩)
          · exact Or.inr (Or.inr ⟨i, hb,
              conflicts_mono pairs sources x _ Set.inter_subset_right hconf⟩)
  · rintro (h | ⟨i, hi, h⟩ | ⟨i, hi, h⟩)
    · exact ⟨none, rfl, h⟩
    · exact ⟨some (left pairs i), by simpa only [label, expandLabels_left] using hi,
        by simpa only [sets_left] using h⟩
    · exact ⟨some (right pairs i), by simpa only [label, expandLabels_right] using hi,
        by simpa only [sets_right] using h⟩

/-- Every valid labeling is realized by a semi-ultrafilter accepting all required sources. -/
theorem exists_filter_of_not_invalid {n : ℕ} (sources : Fin n → Set U) (x : Fin n → Bool)
    (y : Fin (size pairs) → Bool) (h : ¬ Invalid pairs sources x y) :
    ∃ F : Semifilter U, F.IsUltra ∧ (∀ i, F (sets pairs i) ↔ label pairs y i = true) ∧
      ∀ l, x l = true → F (sources l) := by
  obtain ⟨F, hF, hl, hmax⟩ := Semifilter.exists_isUltra_of_labels (sets pairs) (label pairs y)
    none rfl rfl
    (fun i j hij hi => by
      by_contra hj
      exact h ⟨j, by simpa using hj, Or.inl ⟨i, hij, hi⟩⟩)
    (fun i j hij => by
      by_contra h'
      simp only [not_or, Bool.not_eq_true] at h'
      exact h ⟨i, h'.1, Or.inr (Or.inl ⟨j, hij, h'.2⟩)⟩)
  exact ⟨F, hF, hl, fun l hx => (hmax _).mpr fun j hj hsub =>
    h ⟨j, hj, Or.inr (Or.inr ⟨l, hsub, hx⟩)⟩⟩

/-- A point supplies a consistent certificate, including when the pair list is empty. -/
noncomputable def pointLabels (u : U) (i : Fin (size pairs)) : Bool :=
  @decide (u ∈ sets pairs (some i)) (Classical.propDecidable _)

/-- A point's two component-membership labels per pair. -/
noncomputable def compactPointLabels (u : U) : Fin (compactSize pairs) → Bool :=
  Fin.append (fun i => pointLabels pairs u (left pairs i))
    (fun i => pointLabels pairs u (right pairs i))

/-- Conjunction expansion reconstructs the full point-membership certificate. -/
@[simp] theorem expandLabels_compactPointLabels (u : U) :
    expandLabels pairs (compactPointLabels pairs u) = pointLabels pairs u := by
  funext j
  induction j using Fin.addCases with
  | left i =>
    simp only [show Fin.castAdd _ i = left pairs i from rfl, expandLabels_left,
      compactPointLabels, Fin.append_left]
  | right j =>
    induction j using Fin.addCases with
    | left i =>
      simp only [show Fin.natAdd pairs.length (Fin.castAdd pairs.length i) = right pairs i from rfl,
        expandLabels_right, compactPointLabels, Fin.append_right]
    | right i =>
      rw [show Fin.natAdd pairs.length (Fin.natAdd pairs.length i) = inter pairs i from rfl,
        expandLabels_inter, Bool.eq_iff_iff]
      simp only [compactPointLabels, Fin.append_left, Fin.append_right, pointLabels,
        sets_left, sets_right, sets_inter, Bool.and_eq_true, decide_eq_true_eq,
        Set.mem_inter_iff]

/-- The extended point certificate labels `i` by `true` if and only if `u ∈ sets pairs i`. -/
@[simp] theorem label_pointLabels (u : U) (i : Option (Fin (size pairs))) :
    label pairs (pointLabels pairs u) i = true ↔ u ∈ sets pairs i := by
  cases i with
  | none => simp [label, sets]
  | some i => simp only [label, pointLabels, decide_eq_true_eq]

/-- Point membership has no consistency violation whenever all required sources contain it. -/
theorem not_invalid_pointLabels {n : ℕ} (sources : Fin n → Set U) (x : Fin n → Bool)
    (u : U) (hx : ∀ l, x l = true → u ∈ sources l) :
    ¬ Invalid pairs sources x (pointLabels pairs u) := by
  rintro ⟨j, hj, ⟨i, hij, hi⟩ | ⟨k, hjk, hk⟩ | ⟨l, hlj, hl⟩⟩
  all_goals simp only [Bool.eq_false_iff, ne_eq, label_pointLabels] at *
  · exact hj (hij hi)
  · exact (hjk ▸ Set.mem_univ u).elim hj hk
  · exact hj (hlj (hx l hl))

/-- Point membership preserves every intersection pair. -/
theorem not_breaksPair_pointLabels (u : U) : ¬ BreaksPair pairs (pointLabels pairs u) := by
  rintro ⟨i, hi, hj, hk⟩
  simp_all [pointLabels]

end Cslib.Circuits.Fusion.PairCertificate

namespace Cslib.Circuits.Fusion

open PairCertificate

/-- Above a target point, every certificate either is inconsistent or breaks a cover pair. -/
theorem PairCover.invalid_or_breaksPair {X : Type*} {n : ℕ} {target : Set X}
    {input : Fin n → Set X} (c : PairCover target input Semifilter.IsUltra) (x : target)
    (y : Fin (size c.pairs) → Bool) :
    Invalid c.pairs (fun i => Subtype.val ⁻¹' input i)
      (fun i => @decide (x.val ∈ input i) (Classical.propDecidable _)) y ∨
      BreaksPair c.pairs y := by
  classical
  by_contra h
  obtain ⟨h1, h2⟩ := not_or.mp h
  obtain ⟨F, hF, hl, ha⟩ := exists_filter_of_not_invalid c.pairs _ _ y h1
  refine c.isCover ⟨x, F, hF, fun i hi => ha i (by simpa using hi)⟩ fun p hp hleft hright => ?_
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hp
  by_contra hinter
  refine h2 ⟨i, (hl (some (left c.pairs i))).mp (by simpa using hleft),
    (hl (some (right c.pairs i))).mp (by simpa using hright), ?_⟩
  by_contra hk
  exact hinter (by simpa using (hl (some (inter c.pairs i))).mpr (by simpa [label] using hk))

end Cslib.Circuits.Fusion

