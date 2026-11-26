/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Lupanov.FormulaSelectors
public import CslibFrontier.Computability.Circuit.Boolean.Lupanov.FormulaBounds
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Finite local coding for De Morgan formulas

This is a finite construction used toward Lupanov's unrestricted formula synthesis bound.
It is not the asymptotic theorem and does not assert alternating depth three. The construction
uses the open-sphere partition of [Lupanov1961Formulas, Section 4], groups rows into bounded
blocks, and groups columns by their patterns on each block. Factoring the sphere selectors
outside the pattern disjunctions gives a simpler leaf count when alternating depth is unrestricted.
-/

public section

namespace Cslib.Circuits.Boolean.LupanovFormula

open Finset Formula

variable {c d : ℕ}

private def columnPattern (f : BooleanFunction (c + d)) (center : BitString d)
    (T : Finset (BitString c)) (i : Fin d) : T → Bool :=
  fun z => f (Fin.append z.1 (BitString.flipOn {i} center))

private noncomputable def rowSet (T : Finset (BitString c)) (pattern : T → Bool) :
    Finset (BitString c) :=
  (T.attach.filter fun z => pattern z = true).image Subtype.val

private theorem mem_rowSet (T : Finset (BitString c)) (pattern : T → Bool) (z : BitString c) :
    z ∈ rowSet T pattern ↔ ∃ hz : z ∈ T, pattern ⟨z, hz⟩ = true := by
  classical
  simp [rowSet]

private theorem card_rowSet_le (T : Finset (BitString c)) (pattern : T → Bool) :
    (rowSet T pattern).card ≤ T.card :=
  card_image_le.trans ((card_filter_le _ _).trans_eq T.card_attach)

private noncomputable def blockFormula (f : BooleanFunction (c + d)) (center : BitString d)
    (T : Finset (BitString c)) : Formula signature (c + d) := by
  classical
  exact orList ((univ : Finset (T → Bool)).toList.map fun pattern =>
    ((indicator (rowSet T pattern)).rename (Fin.castAdd d)).and
      ((neighborSelector center (univ.filter fun i => columnPattern f center T i = pattern)).rename
        (Fin.natAdd c)))

private theorem eval_blockFormula (f : BooleanFunction (c + d)) (center : BitString d)
    (T : Finset (BitString c)) (z : BitString c) (i : Fin d) :
    (blockFormula f center T).eval interpretation (Fin.append z (BitString.flipOn {i} center)) =
      (decide (z ∈ T) && f (Fin.append z (BitString.flipOn {i} center))) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [blockFormula, eval_orList, List.any_map, List.any_eq_true, mem_toList, mem_univ,
    true_and, Formula.eval_and, Bool.and_eq_true, eval_rename, Function.comp_def, Fin.append_left,
    Fin.append_right, eval_indicator, decide_eq_true_eq, eval_neighborSelector_flip, mem_filter,
    mem_rowSet]
  exact ⟨fun ⟨_, ⟨hz, hp⟩, hcol⟩ => ⟨hz, (congrFun hcol ⟨z, hz⟩).trans hp⟩,
    fun ⟨hz, hf⟩ => ⟨columnPattern f center T i, ⟨hz, hf⟩, rfl⟩⟩

private theorem leafSize_blockFormula_le (f : BooleanFunction (c + d)) (center : BitString d)
    (T : Finset (BitString c)) :
    (blockFormula f center T).leafSize ≤ 2 ^ T.card * c * T.card + d := by
  classical
  simp only [blockFormula, leafSize_orList, List.map_map, Function.comp_def, leafSize_and,
    leafSize_rename, leafSize_indicator, leafSize_neighborSelector]
  rw [Finset.sum_map_toList, sum_add_distrib]
  have hrow : (∑ pattern : T → Bool, c * (rowSet T pattern).card) ≤
      2 ^ T.card * c * T.card := by
    calc
      _ ≤ ∑ _ : T → Bool, c * T.card :=
        sum_le_sum fun pattern _ => Nat.mul_le_mul_left c (card_rowSet_le T pattern)
      _ = _ := by simp [Nat.mul_assoc]
  have hcol : (∑ pattern : T → Bool,
      (univ.filter fun i => columnPattern f center T i = pattern).card) = d := by
    simpa only [leafSize_neighborSelector] using
      sum_leafSize_neighborSelector_fibers center (columnPattern f center T)
  omega

private noncomputable def rowBlock (c s b : ℕ) : Finset (BitString c) :=
  univ.filter fun z => (BitString.equivFin c z).val / s = b

private theorem card_rowBlock_le (c s b : ℕ) (hs : 0 < s) :
    (rowBlock c s b).card ≤ s := by
  classical
  calc
    (rowBlock c s b).card ≤ (range s).card := by
      apply card_le_card_of_injOn (fun z : BitString c => (BitString.equivFin c z).val % s)
      · intro z _
        exact mem_range.mpr (Nat.mod_lt _ hs)
      · intro z hz w hw heq
        apply (BitString.equivFin c).injective
        apply Fin.ext
        have hz' : (BitString.equivFin c z).val / s = b := (mem_filter.mp hz).2
        have hw' : (BitString.equivFin c w).val / s = b := (mem_filter.mp hw).2
        have hzm := Nat.mod_add_div (BitString.equivFin c z).val s
        have hwm := Nat.mod_add_div (BitString.equivFin c w).val s
        rw [hz'] at hzm
        rw [hw'] at hwm
        change (BitString.equivFin c z).val % s = (BitString.equivFin c w).val % s at heq
        exact hzm.symm.trans ((congrArg (· + s * b) heq).trans hwm)
    _ = s := card_range s

private theorem exists_mem_rowBlock (s : ℕ) (z : BitString c) :
    ∃ b : Fin (2 ^ c / s + 1), z ∈ rowBlock c s b := by
  classical
  have hq : (BitString.equivFin c z).val / s ≤ 2 ^ c / s :=
    Nat.div_le_div_right (BitString.equivFin c z).isLt.le
  refine ⟨⟨(BitString.equivFin c z).val / s, by omega⟩, ?_⟩
  simp only [rowBlock, mem_filter, mem_univ, true_and]

private noncomputable def sphereFormula (f : BooleanFunction (c + d))
    (center : BitString d) (s : ℕ) : Formula signature (c + d) :=
  ((openSphere center).rename (Fin.natAdd c)).and
    (orList ((univ : Finset (Fin (2 ^ c / s + 1))).toList.map
      fun (b : Fin (2 ^ c / s + 1)) => blockFormula f center (rowBlock c s b.val)))

private theorem eval_sphereFormula (f : BooleanFunction (c + d)) (center : BitString d)
    (s : ℕ) (z : BitString c) (y : BitString d) :
    (sphereFormula f center s).eval interpretation (Fin.append z y) =
      (decide (∃ i, y = BitString.flipOn {i} center) && f (Fin.append z y)) := by
  classical
  by_cases hy : ∃ i, y = BitString.flipOn {i} center
  · obtain ⟨i, rfl⟩ := hy
    obtain ⟨b, hb⟩ := exists_mem_rowBlock s z
    apply Bool.eq_iff_iff.mpr
    simp only [sphereFormula, eval_and, eval_rename, Function.comp_def, Fin.append_right,
      eval_openSphere, decide_eq_true_eq, Bool.and_eq_true, eval_orList, List.any_map,
      List.any_eq_true, mem_toList, mem_univ, true_and, eval_blockFormula]
    exact ⟨fun ⟨_, _, _, hf⟩ => ⟨⟨i, rfl⟩, hf⟩, fun ⟨_, hf⟩ => ⟨⟨i, rfl⟩, b, hb, hf⟩⟩
  · simp only [sphereFormula, eval_and, eval_rename, Function.comp_def, Fin.append_right,
      eval_openSphere, decide_eq_false hy, Bool.false_and]

private theorem leafSize_sphereFormula_le (f : BooleanFunction (c + d))
    (center : BitString d) {s : ℕ} (hs : 0 < s) :
    (sphereFormula f center s).leafSize ≤
      d ^ 2 + (2 ^ c / s + 1) * (2 ^ s * c * s + d) := by
  classical
  simp only [sphereFormula, leafSize_and, leafSize_rename, leafSize_openSphere,
    leafSize_orList, List.map_map, Function.comp_def]
  rw [Finset.sum_map_toList]
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ _ : Fin (2 ^ c / s + 1), (2 ^ s * c * s + d) :=
      sum_le_sum fun b _ => (leafSize_blockFormula_le f center _).trans <| by
        have hb := card_rowBlock_le c s b hs
        exact Nat.add_le_add_right
          (Nat.mul_le_mul (Nat.mul_le_mul_right c (Nat.pow_le_pow_right two_pos hb)) hb) d
    _ = _ := by simp

private theorem exists_localFormula (c r s : ℕ) (hs : 0 < s)
    (f : BooleanFunction (c + 2 ^ r)) :
    ∃ F : Formula signature (c + 2 ^ r), F.Computes interpretation f ∧
      F.leafSize ≤ (2 ^ (2 ^ r) / 2 ^ r) *
        ((2 ^ r) ^ 2 + (2 ^ c / s + 1) * (2 ^ s * c * s + 2 ^ r)) := by
  classical
  obtain ⟨C, hcard, hbij⟩ := BitString.exists_openSpherePartition r
  let F : Formula signature (c + 2 ^ r) :=
    orList (C.toList.map fun center => sphereFormula f center s)
  have hcard' : C.card = 2 ^ (2 ^ r) / 2 ^ r := by
    rw [← hcard, Nat.mul_div_cancel _ (Nat.two_pow_pos r)]
  refine ⟨F, fun x => ?_, ?_⟩
  · obtain ⟨z, y, rfl⟩ : ∃ z y, Fin.append z y = x := ⟨_, _, Fin.append_castAdd_natAdd⟩
    obtain ⟨⟨⟨center, hc⟩, i⟩, hy⟩ := hbij.surjective y
    apply Bool.eq_iff_iff.mpr
    simp only [F, eval_orList, List.any_map, Function.comp_def, List.any_eq_true, mem_toList,
      eval_sphereFormula, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨fun ⟨_, _, _, hf⟩ => hf, fun hf => ⟨center, hc, ⟨i, hy.symm⟩, hf⟩⟩
  · simp only [F, leafSize_orList, List.map_map, Function.comp_def]
    rw [Finset.sum_map_toList]
    calc _ ≤ ∑ _ ∈ C, ((2 ^ r) ^ 2 + (2 ^ c / s + 1) * (2 ^ s * c * s + 2 ^ r)) :=
        sum_le_sum fun center _ => leafSize_sphereFormula_le f center hs
      _ = _ := by simp [hcard']

private theorem exists_formula_of_sections {a b B : ℕ} (f : BooleanFunction (a + b))
    (h : ∀ z : BitString a, ∃ F : Formula signature b,
      F.Computes interpretation (fun y => f (Fin.append z y)) ∧ F.leafSize ≤ B) :
    ∃ F : Formula signature (a + b), F.Computes interpretation f ∧
      F.leafSize ≤ 2 ^ a * (a + B) := by
  classical
  choose sections hsections hcost using h
  let F : Formula signature (a + b) := orList ((univ : Finset (BitString a)).toList.map fun z =>
    ((minterm z).rename (Fin.castAdd b)).and ((sections z).rename (Fin.natAdd a)))
  refine ⟨F, fun x => ?_, ?_⟩
  · obtain ⟨z, y, rfl⟩ : ∃ z y, Fin.append z y = x := ⟨_, _, Fin.append_castAdd_natAdd⟩
    apply Bool.eq_iff_iff.mpr
    simp only [F, eval_orList, List.any_map, List.any_eq_true, mem_toList, mem_univ, true_and,
      eval_and, Bool.and_eq_true, eval_rename, Function.comp_def, Fin.append_left,
      Fin.append_right, eval_minterm, decide_eq_true_eq, exists_eq_left']
    exact (congrArg (· = true) (hsections z y)).to_iff
  · simp only [F, leafSize_orList, List.map_map, Function.comp_def, leafSize_and,
      leafSize_rename, leafSize_minterm]
    rw [Finset.sum_map_toList]
    calc _ ≤ ∑ _ : BitString a, (a + B) :=
        sum_le_sum fun z _ => Nat.add_le_add_left (hcost z) a
      _ = _ := by simp [BitString]

/-- The finite local-coding construction: every Boolean function of `a + (c + 2 ^ r)`
variables has a native De Morgan formula satisfying `formulaBound`. This is the finite
realizability step for Lupanov's unrestricted-depth formula upper bound. -/
theorem exists_computes_leafSize_le_formulaBound (a c r s : ℕ) (hs : 0 < s)
    (f : BooleanFunction (a + (c + 2 ^ r))) :
    ∃ F : Formula signature (a + (c + 2 ^ r)), F.Computes interpretation f ∧
      F.leafSize ≤ formulaBound a c (2 ^ r) s := by
  exact exists_formula_of_sections f (fun z =>
    exists_localFormula c r s hs (fun y => f (Fin.append z y)))

end Cslib.Circuits.Boolean.LupanovFormula
