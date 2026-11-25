/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import CslibFrontier.Foundations.Geometry.Polygonal.RayParityDirection
import CslibFrontier.Foundations.Geometry.Polygonal.RayParity
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Choosing points away from finitely many proper lines

`Cslib.exists_mem_ball_avoiding_lines` chooses an actual point in any positive open ball.
`Cslib.exists_injective_perturbation_avoiding_spans_and_crossings` perturbs finitely many
points by an arbitrarily small distance while fixing the remaining points. Every triple
of distinct final points containing a moved point is noncollinear.
`Cslib.NoTripleLineContact` says that three distinct supporting lines can meet only at
one of their defining points when at least one line has a moved endpoint. The perturbation
also ensures this property for the final configuration.
`segment_inter_subsingleton_of_affineSpan_ne` bounds intersections on distinct supports.
-/

public section

namespace Cslib

/-- Every positive complex-plane ball contains a point outside all members of a finite
family of proper supporting lines. The finite direction and intercept choices are internal. -/
theorem exists_mem_ball_avoiding_lines {ι : Type*} [Finite ι]
    (a b : ι → ℂ) (hab : ∀ i, a i ≠ b i) (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ w ∈ Metric.ball z ρ, ∀ i (t : ℝ), AffineMap.lineMap (a i) (b i) t ≠ w := by
  classical
  let _ := Fintype.ofFinite ι
  let endpoints := Finset.univ.image a ∪ Finset.univ.image b
  obtain ⟨u, hu, hinj⟩ := Polygonal.exists_mul_im_injOn endpoints
  have hheight (i : ι) : (u * a i).im ≠ (u * b i).im := fun h =>
    hab i (hinj (by simp [endpoints]) (by simp [endpoints]) h)
  let bad := Finset.univ.image fun i : ι =>
    Polygonal.horizontalIntercept (u * a i) (u * b i) (u * z).im - (u * z).re
  have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  obtain ⟨t, ht, hnot⟩ := (Set.Ioo_infinite (mul_pos hρ hnorm)).exists_notMem_finset bad
  let w := z + (t : ℂ) / u
  have huw : u * w = u * z + (t : ℂ) := by
    dsimp only [w]
    field_simp [hu]
  refine ⟨w, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm,
      show w - z = (t : ℂ) / u by dsimp only [w]; ring,
      norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
    exact (div_lt_iff₀ hnorm).mpr ht.2
  · intro i s heq
    have hm : (s : ℂ) * (u * b i - u * a i) + u * a i = u * z + t := by
      rw [← huw, ← heq, AffineMap.lineMap_apply_module', Complex.real_smul]
      ring
    have him := congrArg Complex.im hm
    have hre := congrArg Complex.re hm
    simp only [Complex.add_im, Complex.im_ofReal_mul, Complex.sub_im, Complex.ofReal_im,
      add_zero] at him
    simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.sub_re, Complex.ofReal_re] at hre
    have hden : (u * b i).im - (u * a i).im ≠ 0 := sub_ne_zero.mpr (hheight i).symm
    refine hnot (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩)
    rw [Polygonal.horizontalIntercept, ← him, add_sub_cancel_right, mul_div_cancel_right₀ _ hden]
    linarith

private theorem exists_mem_ball_avoiding_spans (points : Finset ℂ) (z : ℂ)
    {ρ : ℝ} (hρ : 0 < ρ) : ∃ w ∈ Metric.ball z ρ, w ∉ points ∧
      ∀ a ∈ points, ∀ b ∈ points, a ≠ b → w ∉ affineSpan ℝ ({a, b} : Set ℂ) := by
  let P := {p : (↑points : Set ℂ) × (↑points : Set ℂ) // p.1.val ≠ p.2.val}
  let a : (↑points : Set ℂ) ⊕ P → ℂ := Sum.elim Subtype.val fun p => p.val.1.val
  let b : (↑points : Set ℂ) ⊕ P → ℂ := Sum.elim (fun p => p.val + 1) fun p => p.val.2.val
  have hne (i : (↑points : Set ℂ) ⊕ P) : a i ≠ b i := by
    cases i with
    | inl p => exact (by simp : p.val ≠ p.val + 1)
    | inr p => exact p.property
  obtain ⟨w, hw, havoid⟩ := exists_mem_ball_avoiding_lines a b hne z hρ
  refine ⟨w, hw, ?_, ?_⟩
  · intro h
    exact havoid (.inl ⟨w, h⟩) 0 (AffineMap.lineMap_apply_zero _ _)
  · intro x hx y hy hxy h
    obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp h
    exact havoid (.inr ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, hxy⟩) t ht

/-- Three distinct supporting lines determined by the specified endpoints can meet
only at one of their endpoints if at least one line uses a moved point. -/
@[expose] def NoTripleLineContact (points moved : Set ℂ) : Prop :=
  ∀ (a b : Fin 3 → ℂ) (z : ℂ),
    (∀ i, a i ∈ points ∧ b i ∈ points ∧ a i ≠ b i) →
    (∃ i, a i ∈ moved ∨ b i ∈ moved) →
    Pairwise (fun i j => affineSpan ℝ ({a i, b i} : Set ℂ) ≠ affineSpan ℝ ({a j, b j} : Set ℂ)) →
    (∀ i, z ∈ affineSpan ℝ ({a i, b i} : Set ℂ)) →
    ∃ i, z = a i ∨ z = b i

/-- The closed segment lies on the affine line through its endpoints. -/
private theorem segment_subset_affineSpan_pair (a b : ℂ) :
    segment ℝ a b ⊆ ↑(affineSpan ℝ ({a, b} : Set ℂ)) := by
  rw [segment_eq_image_lineMap]
  rintro _ ⟨t, _, rfl⟩
  exact AffineMap.lineMap_mem_affineSpan_pair t _ _

/-- Distinct affine spans of point pairs in the plane intersect in at most one point. -/
private theorem affineSpan_pair_inter_subsingleton {a b c d : ℂ}
    (hne : affineSpan ℝ ({a, b} : Set ℂ) ≠ affineSpan ℝ ({c, d} : Set ℂ)) :
    ((↑(affineSpan ℝ ({a, b} : Set ℂ)) : Set ℂ) ∩
      ↑(affineSpan ℝ ({c, d} : Set ℂ))).Subsingleton := by
  intro x hx y hy
  by_contra hxy
  exact hne ((affineSpan_pair_eq_of_mem_of_mem_of_ne hx.1 hy.1 hxy).symm.trans
    (affineSpan_pair_eq_of_mem_of_mem_of_ne hx.2 hy.2 hxy))

/-- Segments on distinct supporting lines share at most one point. -/
theorem segment_inter_subsingleton_of_affineSpan_ne {a b c d : ℂ}
    (hne : affineSpan ℝ ({a, b} : Set ℂ) ≠ affineSpan ℝ ({c, d} : Set ℂ)) :
    (segment ℝ a b ∩ segment ℝ c d).Subsingleton := by
  exact (affineSpan_pair_inter_subsingleton hne).anti
    (Set.inter_subset_inter (segment_subset_affineSpan_pair a b)
      (segment_subset_affineSpan_pair c d))

private noncomputable def pointPairLine {S : Set ℂ} (p : S × S) : AffineSubspace ℝ ℂ :=
  affineSpan ℝ ({p.1.val, p.2.val} : Set ℂ)

private noncomputable def lineCrossings (S : Set ℂ) : Set ℂ :=
  ⋃ p : {p : (S × S) × (S × S) // pointPairLine p.1 ≠ pointPairLine p.2},
    (↑(pointPairLine p.val.1) : Set ℂ) ∩ ↑(pointPairLine p.val.2)

private theorem lineCrossings_finite {S : Set ℂ} (hS : S.Finite) :
    (lineCrossings S).Finite := by
  let _ := hS.fintype
  apply Set.finite_iUnion
  intro p
  exact (affineSpan_pair_inter_subsingleton p.property).finite

private theorem NoTripleLineContact.insert_point {points moved : Set ℂ}
    (h : NoTripleLineContact points moved)
    {w : ℂ} (havoid : ∀ a ∈ points, ∀ z ∈ lineCrossings points, a ≠ z →
      w ∉ affineSpan ℝ ({a, z} : Set ℂ)) :
    NoTripleLineContact (insert w points) (insert w moved) := by
  classical
  intro a b z hpoints hmoved hdistinct hz
  let line := fun i => affineSpan ℝ ({a i, b i} : Set ℂ)
  by_cases hused : ∃ i, a i = w ∨ b i = w
  · obtain ⟨i, hi⟩ := hused
    by_contra hnot
    have he (j : Fin 3) : z ≠ a j ∧ z ≠ b j :=
      ⟨fun he => hnot ⟨j, Or.inl he⟩, fun he => hnot ⟨j, Or.inr he⟩⟩
    have hzw : z ≠ w := hi.elim (· ▸ (he i).1) (· ▸ (he i).2)
    have hline (j : Fin 3) (hj : a j = w ∨ b j = w) : w ∈ line j :=
      hj.elim (· ▸ left_mem_affineSpan_pair ℝ (a j) (b j))
        (· ▸ right_mem_affineSpan_pair ℝ (a j) (b j))
    have hold (j : Fin 3) (hij : i ≠ j) : a j ∈ points ∧ b j ∈ points := by
      have hnotUse : ¬(a j = w ∨ b j = w) := by
        intro hj
        apply hdistinct hij
        exact (affineSpan_pair_eq_of_mem_of_mem_of_ne (hz i) (hline i hi) hzw).symm.trans
          (affineSpan_pair_eq_of_mem_of_mem_of_ne (hz j) (hline j hj) hzw)
      exact ⟨(Set.mem_insert_iff.mp (hpoints j).1).resolve_left (fun h => hnotUse (Or.inl h)),
        (Set.mem_insert_iff.mp (hpoints j).2.1).resolve_left (fun h => hnotUse (Or.inr h))⟩
    let j : Fin 3 := i + 1
    let k : Fin 3 := i + 2
    obtain ⟨hij, hik, hjk⟩ : i ≠ j ∧ i ≠ k ∧ j ≠ k := by fin_cases i <;> decide
    have hzCross : z ∈ lineCrossings points := by
      exact Set.mem_iUnion.mpr
        ⟨⟨(⟨⟨a j, (hold j hij).1⟩, ⟨b j, (hold j hij).2⟩⟩,
            ⟨⟨a k, (hold k hik).1⟩, ⟨b k, (hold k hik).2⟩⟩), hdistinct hjk⟩, hz j, hz k⟩
    have hother (c : ℂ) (hc : c ∈ insert w points) (hcw : c ≠ w)
        (hcz : c ≠ z) (hcl : c ∈ line i) : False := by
      apply havoid c ((Set.mem_insert_iff.mp hc).resolve_left hcw) z hzCross hcz
      rw [affineSpan_pair_eq_of_mem_of_mem_of_ne hcl (hz i) hcz]
      exact hline i hi
    rcases hi with ha | hb
    · exact hother (b i) (hpoints i).2.1 (ha ▸ (hpoints i).2.2.symm)
        (he i).2.symm (right_mem_affineSpan_pair ℝ (a i) (b i))
    · exact hother (a i) (hpoints i).1 (hb ▸ (hpoints i).2.2)
        (he i).1.symm (left_mem_affineSpan_pair ℝ (a i) (b i))
  · have hne (i) : a i ≠ w ∧ b i ≠ w :=
      ⟨fun ha => hused ⟨i, Or.inl ha⟩, fun hb => hused ⟨i, Or.inr hb⟩⟩
    apply h a b z ?_ ?_ hdistinct hz
    · intro i
      exact ⟨(Set.mem_insert_iff.mp (hpoints i).1).resolve_left (hne i).1,
        (Set.mem_insert_iff.mp (hpoints i).2.1).resolve_left (hne i).2, (hpoints i).2.2⟩
    · exact hmoved.imp fun i => Or.imp (fun ha => (Set.mem_insert_iff.mp ha).resolve_left (hne i).1)
        fun hb => (Set.mem_insert_iff.mp hb).resolve_left (hne i).2

/-- Arbitrarily small perturbations separate movable points, keep them off lines
through other points, and exclude triple contacts away from the defining endpoints
of distinct lines when at least one of those endpoints is movable. -/
theorem exists_injective_perturbation_avoiding_spans_and_crossings {ι : Type*} [Finite ι]
    (center : ι → ℂ) (fixed : Finset ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ q : ι → ℂ, (∀ i, dist (q i) (center i) < ρ) ∧ Function.Injective q ∧
      (∀ i, q i ∉ fixed) ∧ (∀ i a b,
        a ∈ (↑fixed : Set ℂ) ∪ Set.range q → b ∈ (↑fixed : Set ℂ) ∪ Set.range q →
        a ≠ b → q i ≠ a → q i ≠ b → q i ∉ affineSpan ℝ ({a, b} : Set ℂ)) ∧
      NoTripleLineContact ((↑fixed : Set ℂ) ∪ Set.range q) (Set.range q) := by
  classical
  let _ := Fintype.ofFinite ι
  have extend (s : Finset ι) : ∃ q : ι → ℂ,
      (∀ i ∈ s, dist (q i) (center i) < ρ) ∧ Set.InjOn q (↑s : Set ι) ∧
      (∀ i ∈ s, q i ∉ fixed) ∧ (∀ i ∈ s, ∀ a b,
        a ∈ (↑fixed : Set ℂ) ∪ q '' (↑s : Set ι) →
        b ∈ (↑fixed : Set ℂ) ∪ q '' (↑s : Set ι) →
        a ≠ b → q i ≠ a → q i ≠ b → q i ∉ affineSpan ℝ ({a, b} : Set ℂ)) ∧
      NoTripleLineContact ((↑fixed : Set ℂ) ∪ q '' (↑s : Set ι)) (q '' (↑s : Set ι)) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨center, by simp [NoTripleLineContact]⟩
    | @insert i s hi ih =>
      obtain ⟨old, hnear, hinj, hfixed, hspans, htriple⟩ := ih
      let present := fixed ∪ s.image old
      have hpresent : (↑present : Set ℂ) = (↑fixed : Set ℂ) ∪ old '' (↑s : Set ι) := by
        simp only [present, Finset.coe_union, Finset.coe_image]
      let crossings := lineCrossings (↑present : Set ℂ)
      have hc := lineCrossings_finite present.finite_toSet
      obtain ⟨w, hw, hwne', hwspans'⟩ :=
        exists_mem_ball_avoiding_spans (present ∪ hc.toFinset) (center i) hρ
      have hwne : w ∉ present := fun h => hwne' (Finset.mem_union_left _ h)
      have hwspans (a) (ha : a ∈ present) (b) (hb : b ∈ present) (hne : a ≠ b) :
          w ∉ affineSpan ℝ ({a, b} : Set ℂ) :=
        hwspans' a (Finset.mem_union_left _ ha) b (Finset.mem_union_left _ hb) hne
      have hwcross (a) (ha : a ∈ present) (z) (hz : z ∈ crossings) (hne : a ≠ z) :
          w ∉ affineSpan ℝ ({a, z} : Set ℂ) :=
        hwspans' a (Finset.mem_union_left _ ha) z
          (Finset.mem_union_right _ (Set.Finite.mem_toFinset hc |>.mpr hz)) hne
      let q := Function.update old i w
      have hqnew : q i = w := Function.update_self ..
      have hqold : Set.EqOn q old (↑s : Set ι) :=
        fun j hj => Function.update_of_ne (ne_of_mem_of_not_mem hj hi) _ _
      have hold (j : ι) (hj : j ∈ s) : old j ∈ present :=
        Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj)
      have hfixed' : ∀ a ∈ fixed, a ∈ present := fun a ha => Finset.mem_union_left _ ha
      have hplaced : q '' (↑(insert i s) : Set ι) = insert w (old '' (↑s : Set ι)) := by
        rw [Finset.coe_insert, Set.image_insert_eq, hqnew, hqold.image_eq]
      have hpool : (↑fixed : Set ℂ) ∪ q '' (↑(insert i s) : Set ι) =
          insert w (↑present : Set ℂ) := by
        rw [hplaced, Set.union_insert, hpresent]
      refine ⟨q, ?_, ?_, ?_, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        exacts [hqnew ▸ hw, hqold hj ▸ hnear j hj]
      · rw [Finset.coe_insert, Set.injOn_insert (by simpa using hi), hqnew, hqold.injOn_iff,
          hqold.image_eq]
        exact ⟨hinj, fun ⟨j, hj, h⟩ => hwne (h ▸ hold j hj)⟩
      · intro j hj h
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hwne (hqnew ▸ hfixed' _ h)
        · exact hfixed j hj (hqold hj ▸ h)
      · intro j hj a b ha hb hab hja hjb h
        rw [hpool] at ha hb
        rcases Finset.mem_insert.mp hj with rfl | hj
        · rw [hqnew] at hja hjb h
          have ha' := (Set.mem_insert_iff.mp ha).resolve_left (Ne.symm hja)
          have hb' := (Set.mem_insert_iff.mp hb).resolve_left (Ne.symm hjb)
          exact hwspans a ha' b hb' hab h
        · rw [hqold hj] at hja hjb h
          rcases Set.mem_insert_iff.mp ha with haw | ha'
          · subst a
            have hb' := (Set.mem_insert_iff.mp hb).resolve_left hab.symm
            apply hwspans _ (hold j hj) _ hb' hjb
            rw [affineSpan_pair_eq_of_left_mem_of_ne h hjb]
            exact left_mem_affineSpan_pair _ _ _
          · rcases Set.mem_insert_iff.mp hb with hbw | hb'
            · subst b
              apply hwspans _ ha' _ (hold j hj) hja.symm
              rw [affineSpan_pair_eq_of_right_mem_of_ne h hja]
              exact right_mem_affineSpan_pair _ _ _
            · exact hspans j hj a b (hpresent ▸ ha') (hpresent ▸ hb') hab hja hjb h
      · rw [hpool, hplaced]
        exact (hpresent.symm ▸ htriple).insert_point hwcross
  obtain ⟨q, hnear, hinj, hfixed, hspans, htriple⟩ := extend Finset.univ
  refine ⟨q, fun i => hnear i (Finset.mem_univ i),
    fun _ _ => hinj (Finset.mem_univ _) (Finset.mem_univ _),
    fun i => hfixed i (Finset.mem_univ i), ?_, ?_⟩
  · simpa only [Finset.coe_univ, Set.image_univ] using fun i => hspans i (Finset.mem_univ i)
  · simpa only [Finset.coe_univ, Set.image_univ] using htriple

end Cslib
