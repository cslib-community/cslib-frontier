/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.VanEmdeBoas.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Tauto

/-!
# Correctness of van Emde Boas insertion

The recursive minimum-excluded insertion algorithm follows [Demaine2015VanEmdeBoas], pp. 4–5.
The results here concern the functional Lean implementation and its represented set, with no
machine running-time claim.

## Main definitions

The algorithm and recursive invariant are `Tree.insert` and `Tree.Valid`, imported from `Basic`.

## Main results

* `Tree.valid_insert`: insertion of a bounded key preserves the recursive invariant.
* `Tree.contains_insert`: insertion represents exactly the union with the inserted key.

## References

* [E. Demaine, *Divide and conquer: van Emde Boas trees*, Lecture 4][Demaine2015VanEmdeBoas]
-/

public section

namespace Cslib.DataStructure.VanEmdeBoas.Tree

variable {d : ℕ}

/-- A leaf with bounds `some (m, M)` contains `y` iff `y = m` or `y = M`. -/
@[simp] theorem contains_leaf_some (m M y : ℕ) :
    (leaf (some (m, M))).Contains y ↔ y = m ∨ y = M := by
  simp [Contains]

/-- An internal node with bounds `some (m, M)` contains `y` iff `y = m` or `y` is in some
cluster. -/
@[simp] theorem contains_node_some (m M : ℕ) (s : Tree d)
    (c : Fin (universeSize d) → Tree d) (y : ℕ) :
    (node (some (m, M)) s c).Contains y ↔
      y = m ∨ ∃ i a, (c i).Contains a ∧ y = i.val * universeSize d + a := by
  simp [Contains]

private theorem extrema_insert_of_contains {t t' : Tree d} (ht : t.Valid)
    {m M x : ℕ} (hb : t.bounds = some (m, M))
    (hb' : t'.bounds = some (min m x, max M x)) (hx : x < universeSize d)
    (hs : ∀ y, t'.Contains y ↔ y = x ∨ t.Contains y) : t'.Extrema := by
  have he := ht.extrema_of_bounds hb
  simp only [Extrema, hb']
  refine ⟨Nat.le_trans (min_le_right m x) (le_max_right M x), max_lt he.2.1 hx, ?_, ?_, ?_⟩
  · apply (hs _).mpr
    rcases le_total m x with h | h
    · exact Or.inr (by simpa only [min_eq_left h] using he.2.2.1)
    · exact Or.inl (min_eq_right h)
  · apply (hs _).mpr
    rcases le_total M x with h | h
    · exact Or.inl (max_eq_right h)
    · exact Or.inr (by simpa only [max_eq_left h] using he.2.2.2.1)
  · intro y hy
    rcases (hs y).mp hy with rfl | hy
    · exact ⟨min_le_right _ _, le_max_right _ _⟩
    · exact ⟨Nat.le_trans (min_le_left _ _) (he.2.2.2.2 y hy).1,
        Nat.le_trans (he.2.2.2.2 y hy).2 (le_max_left _ _)⟩

/-- Installing the first key changes only an empty node's local header. -/
private theorem singleton_of_bounds_none {t : Tree d} (ht : t.Valid) (hb : t.bounds = none)
    {x : ℕ} (hx : x < universeSize d) :
    (t.withBounds (some (x, x))).Valid ∧
      ∀ y, (t.withBounds (some (x, x))).Contains y ↔ y = x ∨ t.Contains y := by
  have hnot : ∀ y, ¬t.Contains y := not_contains_of_bounds_none hb
  cases t with
  | leaf b =>
    simp only [bounds] at hb
    subst b
    simp only [withBounds, Valid, Extrema, bounds, contains_leaf_some, hnot, or_false]
    simp only [universeSize_zero] at hx
    simpa using hx
  | @node d b s c =>
    simp only [bounds] at hb
    subst b
    obtain ⟨he, hs, hc, ho, hsb, hcb⟩ := ht
    have hnone : ∀ i y, ¬(c i).Contains y := fun i y =>
      not_contains_of_bounds_none (hcb i) y
    have hset : ∀ y, (node (some (x, x)) s c).Contains y ↔ y = x := fun y => by simp [hnone]
    refine ⟨⟨?_, hs, hc, ho, fun i y hy => (hnone i y hy).elim⟩, fun y => ?_⟩
    · simp only [Extrema, bounds]
      exact ⟨le_rfl, hx, (hset x).mpr rfl, (hset x).mpr rfl,
        fun y hy => by have := (hset y).mp hy; omega⟩
    · simp only [withBounds, hset, hnot, or_false]

private theorem contains_node_update {s s' : Tree d}
    {c c' : Fin (universeSize d) → Tree d} {m M x : ℕ}
    {i : Fin (universeSize d)} {a : ℕ} (hz : max m x = i.val * universeSize d + a)
    (hc : ∀ j y, (c' j).Contains y ↔ (j = i ∧ y = a) ∨ (c j).Contains y) :
    ∀ y, (node (some (min m x, max M x)) s' c').Contains y ↔
      y = x ∨ (node (some (m, M)) s c).Contains y := by
  intro y
  simp only [contains_node_some, hc, or_and_right, exists_or, and_assoc, exists_and_left,
    exists_eq_left, ← hz]
  grind

/-- A valid node is occupied exactly when it represents at least one key. -/
theorem Valid.bounds_isSome_iff {t : Tree d} (ht : t.Valid) :
    t.bounds.isSome = true ↔ ∃ y, t.Contains y := by
  cases hb : t.bounds with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_exists]
    exact not_contains_of_bounds_none hb
  | some b =>
    obtain ⟨m, M⟩ := b
    simp only [Option.isSome_some, true_iff]
    exact ⟨m, ht.contains_minimum hb⟩

private theorem valid_node_update {s s' : Tree d}
    {c c' : Fin (universeSize d) → Tree d} {m M x : ℕ}
    (ht : (node (some (m, M)) s c).Valid) (hx : x < universeSize (d + 1))
    (hm : x ≠ m) {i : Fin (universeSize d)} {a : ℕ}
    (hz : max m x = i.val * universeSize d + a)
    (hs' : s'.Valid) (hc' : ∀ j, (c' j).Valid)
    (hss : ∀ j, s'.Contains j ↔ j = i.val ∨ s.Contains j)
    (hcc : ∀ j y, (c' j).Contains y ↔ (j = i ∧ y = a) ∨ (c j).Contains y) :
    (node (some (min m x, max M x)) s' c').Valid ∧
      ∀ y, (node (some (min m x, max M x)) s' c').Contains y ↔
        y = x ∨ (node (some (m, M)) s c).Contains y := by
  have hset := contains_node_update (s := s) (s' := s') (M := M) hz hcc
  refine ⟨⟨extrema_insert_of_contains ht rfl rfl hx hset, hs', hc', ?_, ?_⟩, hset⟩
  · intro j
    rw [hss, ht.2.2.2.1 j, (ht.2.2.1 j).bounds_isSome_iff, (hc' j).bounds_isSome_iff]
    simp only [hcc, exists_or, exists_and_left, exists_eq, and_true, Fin.val_inj]
  · intro j y hy
    rcases (hcc j y).mp hy with ⟨rfl, rfl⟩ | hy
    · rw [← hz]; omega
    · exact Nat.lt_of_le_of_lt (min_le_left m x) (ht.2.2.2.2 j y hy)

private theorem update_cluster_spec {c : Fin (universeSize d) → Tree d}
    (hc : ∀ j, (c j).Valid) {i : Fin (universeSize d)} {a : ℕ} {t : Tree d}
    (ht : t.Valid) (hs : ∀ y, t.Contains y ↔ y = a ∨ (c i).Contains y) :
    (∀ j, (Function.update c i t j).Valid) ∧
      ∀ j y, (Function.update c i t j).Contains y ↔
        (j = i ∧ y = a) ∨ (c j).Contains y := by
  refine ⟨(Function.forall_update_iff c fun _ u => u.Valid).mpr ⟨ht, fun j _ => hc j⟩,
    fun j y => ?_⟩
  rw [Function.pred_update (fun {_} (u : Tree d) => u.Contains y) c i t j, hs]
  by_cases h : j = i <;> simp [h]

private theorem insert_spec {t : Tree d} (ht : t.Valid) {x : ℕ}
    (hx : x < universeSize d) :
    (t.insert x).Valid ∧ ∀ y, (t.insert x).Contains y ↔ y = x ∨ t.Contains y := by
  induction d generalizing x with
  | zero =>
    cases t with
    | leaf b =>
      cases b with
      | none => exact singleton_of_bounds_none ht rfl hx
      | some b =>
        obtain ⟨m, M⟩ := b
        have he := ht.extrema_of_bounds rfl
        have hset : ∀ y, ((leaf (some (m, M))).insert x).Contains y ↔
            y = x ∨ (leaf (some (m, M))).Contains y := by
          intro y
          simp only [insert, contains_leaf_some]
          simp only [universeSize_zero] at hx he
          omega
        exact ⟨extrema_insert_of_contains ht rfl rfl hx hset, hset⟩
  | succ d ih =>
    cases t with
    | node b s c =>
      cases b with
      | none => exact singleton_of_bounds_none ht rfl hx
      | some b =>
        obtain ⟨m, M⟩ := b
        by_cases hm : x = m
        · simp only [insert, ite_eq_left hm]
          exact ⟨ht, fun y => (or_iff_right_of_imp fun h => by
            simpa only [h, hm] using ht.contains_minimum rfl).symm⟩
        · have hm_lt := ht.contains_lt (ht.contains_minimum rfl)
          have hzlt : max m x < universeSize (d + 1) := max_lt hm_lt hx
          have hi : max m x / universeSize d < universeSize d :=
            (Nat.div_lt_iff_lt_mul (universeSize_pos d)).mpr hzlt
          let i : Fin (universeSize d) := ⟨max m x / universeSize d, hi⟩
          let a := max m x % universeSize d
          have ha : a < universeSize d := Nat.mod_lt _ (universeSize_pos d)
          have hz : max m x = i.val * universeSize d + a :=
            (Nat.div_add_mod' (max m x) (universeSize d)).symm
          cases hb : (c i).bounds with
          | none =>
            obtain ⟨hv, hset⟩ := singleton_of_bounds_none (ht.2.2.1 i) hb ha
            obtain ⟨hcv, hcs⟩ := update_cluster_spec ht.2.2.1 hv hset
            obtain ⟨hsv, hss⟩ := ih ht.2.1 i.isLt
            have hresult := valid_node_update ht hx hm hz hsv hcv hss hcs
            dsimp only [i] at hb
            simpa only [insert, ite_eq_right hm, dite_eq_left hi, i, a, hb] using hresult
          | some b =>
            obtain ⟨hv, hs⟩ := ih (ht.2.2.1 i) ha
            obtain ⟨hcv, hcs⟩ := update_cluster_spec ht.2.2.1 hv hs
            have hi_mem : s.Contains i.val :=
              (ht.2.2.2.1 i).mpr (by simp [hb])
            have hss : ∀ j, s.Contains j ↔ j = i.val ∨ s.Contains j := fun j =>
              (or_iff_right_of_imp fun h => h ▸ hi_mem).symm
            have hresult := valid_node_update ht hx hm hz ht.2.1 hcv hss hcs
            dsimp only [i] at hb
            simpa only [insert, ite_eq_right hm, dite_eq_left hi, i, a, hb] using hresult

/-- Bounded insertion preserves the recursive representation invariant. -/
theorem valid_insert {t : Tree d} (ht : t.Valid) {x : ℕ} (hx : x < universeSize d) :
    (t.insert x).Valid :=
  (insert_spec ht hx).1

/-- The represented set after bounded insertion is exactly the old set plus the inserted key. -/
theorem contains_insert {t : Tree d} (ht : t.Valid) {x : ℕ} (hx : x < universeSize d)
    (y : ℕ) : (t.insert x).Contains y ↔ y = x ∨ t.Contains y :=
  (insert_spec ht hx).2 y

end Cslib.DataStructure.VanEmdeBoas.Tree
