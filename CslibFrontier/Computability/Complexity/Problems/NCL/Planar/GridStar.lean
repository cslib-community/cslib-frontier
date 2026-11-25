/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridPath
public import Mathlib.Data.Fin.Basic

/-!
# Orthogonal drawings of three-port cells

Every split of three ordered ports between the top and bottom of a cell admits a drawing in a
`2 × 2` integer rectangle. The three paths intersect precisely at the vertex.

## Main definitions

* `Cslib.Complexity.NCL.GridStar.Contains`: the two-segment path of a cell port.

## Main results

* `Cslib.Complexity.NCL.GridStar.intersection`: different ports meet only at the vertex.
-/

public section

namespace Cslib.Complexity.NCL.GridStar

/-- The center column: one for three ports on the same side, and zero otherwise. -/
@[expose] def center (a : ℕ) : ℕ := if a = 0 ∨ a = 3 then 1 else 0

/-- The port-to-vertex path: one vertical and one horizontal segment. -/
@[expose] def Contains {a b : ℕ} (e : Fin a ⊕ Fin b) (p : ℕ × ℕ) : Prop :=
  match e with
  | .inl i => (p.1 = i ∧ p.2 ≤ 1) ∨
      (p.2 = 1 ∧ min i.val (center a) ≤ p.1 ∧ p.1 ≤ max i.val (center a))
  | .inr j => (p.1 = j ∧ 1 ≤ p.2 ∧ p.2 ≤ 2) ∨
      (p.2 = 1 ∧ min j.val (center a) ≤ p.1 ∧ p.1 ≤ max j.val (center a))

/-- Draw the upper port down to the vertex, or the vertex down to the lower port. -/
@[expose] def path {a b : ℕ} (e : Fin a ⊕ Fin b) :
    GridRouting.Path
      (e.elim (fun i => (i.val, 0)) (fun _ => (center a, 1)))
      (e.elim (fun _ => (center a, 1)) (fun j => (j.val, 2))) :=
  match e with
  | .inl i => (GridRouting.Path.vertical i.val 0 1 (by omega)).comp
      (GridRouting.Path.horizontal i.val (center a) 1)
  | .inr j => (GridRouting.Path.horizontal (center a) j.val 1).comp
      (GridRouting.Path.vertical j.val 1 2 (by omega))

/-- Each declared cell-port trace is an actual two-segment orthogonal path. -/
theorem path_contains_iff {a b : ℕ} (e : Fin a ⊕ Fin b) (p : ℕ × ℕ) :
    (path e).Contains p ↔ Contains e p := by
  cases e <;> simp only [path, GridRouting.Path.Contains, Contains] <;> omega

/-- The path starts at its port. -/
theorem endpoint_mem {a b : ℕ} (e : Fin a ⊕ Fin b) :
    Contains e (e.elim Fin.val Fin.val, e.elim (fun _ => 0) (fun _ => 2)) := by
  cases e <;> exact Or.inl (by simp)

/-- The cell paths lie inside their integer rectangle. -/
theorem bounded {a b : ℕ} (h : a + b = 3) {e : Fin a ⊕ Fin b} {p : ℕ × ℕ}
    (hp : Contains e p) : p.1 ≤ 2 ∧ p.2 ≤ 2 := by
  have hc : center a ≤ 1 := by unfold center; split <;> omega
  cases e with
  | inl i => have := i.isLt; simp only [Contains] at hp; rcases hp with hp | hp <;> omega
  | inr j => have := j.isLt; simp only [Contains] at hp; rcases hp with hp | hp <;> omega

/-- At the top boundary the cell meets exactly its top ports. -/
theorem top_iff {a b : ℕ} (e : Fin a ⊕ Fin b) (x : ℕ) :
    Contains e (x, 0) ↔ ∃ i : Fin a, e = .inl i ∧ x = i := by
  cases e <;> simp [Contains]

/-- At the bottom boundary the cell meets exactly its bottom ports. -/
theorem bottom_iff {a b : ℕ} (e : Fin a ⊕ Fin b) (x : ℕ) :
    Contains e (x, 2) ↔ ∃ j : Fin b, e = .inr j ∧ x = j := by
  cases e <;> simp [Contains]

/-- Distinct port paths intersect only at the cell's vertex. -/
theorem intersection {a b : ℕ} (h : a + b = 3) {e f : Fin a ⊕ Fin b}
    (hef : e ≠ f) {p : ℕ × ℕ} (he : Contains e p) (hf : Contains f p) :
    p = (center a, 1) := by
  have hc : (a = 0 ∧ center a = 1) ∨ (a = 1 ∧ center a = 0) ∨
      (a = 2 ∧ center a = 0) ∨ (a = 3 ∧ center a = 1) := by
    unfold center
    split_ifs <;> omega
  suffices hp : p.1 = center a ∧ p.2 = 1 from Prod.ext hp.1 hp.2
  rcases e with i | i <;> rcases f with j | j
  on_goal 1 => have : i.val ≠ j.val := fun hh => hef (congrArg Sum.inl (Fin.ext hh))
  on_goal 4 => have : i.val ≠ j.val := fun hh => hef (congrArg Sum.inr (Fin.ext hh))
  all_goals
    have := i.isLt
    have := j.isLt
    simp only [Contains] at he hf
    rcases hc with hc | hc | hc | hc <;> omega

end Cslib.Complexity.NCL.GridStar
