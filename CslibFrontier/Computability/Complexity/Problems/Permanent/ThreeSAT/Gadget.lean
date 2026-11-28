/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Matrix.Permanent.Gadget

/-!
# Goldreich's clause gadget for the permanent

Goldreich's proof of Proposition 6.21 [Goldreich, Section 6.2.1][Goldreich2007Draft] replaces
every clause of a 3CNF formula by an eight-vertex weighted digraph, the clause gadget of his
Figure 6.3, with entries in `{-1, 0, 1, 2, 3}`. Vertices `0, 1, 2` are the entry vertices and
`3, 4, 5` the exit vertices of the three literals. Removing the rows of the exits `Out` and the
columns of the entries `In`, the remaining minor of the gadget is `12` when `Out = In` is
nonempty and `0` otherwise (`gadget_minor`, checked by evaluation). In cycle-cover language: the
cycle covers of the gadget that leave it at the exits of `Out` and come back at the entries of
`In` weigh `12` in total if the same nonempty set of literal tracks passes through, and cancel
otherwise.

`permOn_gadget_add` specializes the general elimination rule `Matrix.permOn_add_of_gadget` to
these minors: if a matrix is the gadget `A`, placed on eight vertices, plus a matrix `D` that
meets the gadget only in exit rows and entry columns, then its permanent sum is `12` times the
sum, over the nonempty sets `Q` of literals, of the permanent sum of `D` in which the gadget is
replaced by the exits and entries of `Q`. This is the matrix form of Goldreich's three postulated
gadget properties.

This is Goldreich's gadget with `c = 12`, not the XOR gadget of the Arora–Barak draft
[Arora and Barak, Theorem 9.8][AroraBarak07], which is `Cslib.Complexity.XorGadget.gadget`.

## Main definitions

* `Cslib.Complexity.PermanentGadget.gadget`: the clause gadget.
* `Cslib.Complexity.PermanentGadget.entryE`, `Cslib.Complexity.PermanentGadget.exitE`: the
  entry and exit vertices of the three literals.

## Main results

* `Cslib.Complexity.PermanentGadget.gadget_minor`: the minors of the gadget.
* `Cslib.Complexity.PermanentGadget.permOn_gadget_add`: elimination of a placed gadget.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, 2007 draft]
  [Goldreich2007Draft]
* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
-/

@[expose] public section

open Finset Matrix

namespace Cslib.Complexity.PermanentGadget

/-- The rows of Goldreich's clause gadget (Figure 6.3). -/
def gadgetRows : List (List ℤ) :=
  [[1, 0, 0, 2, 0, 0, 0, 0],
   [0, 1, 0, 0, 3, 0, 0, 0],
   [0, 0, 0, 0, 0, 1, 0, 0],
   [0, 0, -1, 1, -1, 0, 1, 1],
   [0, 0, -1, -1, 2, 0, 1, 1],
   [0, 0, 0, -1, -1, 0, 1, 1],
   [0, 0, 1, 1, 1, 0, 2, -1],
   [0, 0, 1, 1, 1, 0, 0, 1]]

/-- Entry `(a, b)` of the clause gadget, for natural indices, `0` outside the gadget. -/
def gadgetEntry (a b : ℕ) : ℤ :=
  (gadgetRows.getD a []).getD b 0

/-- Goldreich's clause gadget: entry vertices `0, 1, 2`, exit vertices `3, 4, 5`. -/
def gadget : Matrix (Fin 8) (Fin 8) ℤ :=
  fun a b => gadgetEntry a b

/-- The entry vertex of a literal. -/
def entryE : Fin 3 ↪ Fin 8 :=
  ⟨fun p => ⟨p, by omega⟩, fun p q h => Fin.ext (by simpa using congrArg Fin.val h)⟩

/-- The exit vertex of a literal. -/
def exitE : Fin 3 ↪ Fin 8 :=
  ⟨fun p => ⟨p + 3, by omega⟩, fun p q h => Fin.ext (by simpa using congrArg Fin.val h)⟩

/-- Rows of the gadget left after removing the exits of the literals flagged `true`. -/
def rowsB (o₀ o₁ o₂ : Bool) : List (Fin 8) :=
  [0, 1, 2] ++ (if o₀ then [] else [3]) ++ (if o₁ then [] else [4]) ++
    (if o₂ then [] else [5]) ++ [6, 7]

/-- Columns of the gadget left after removing the entries of the literals flagged `true`. -/
def colsB (i₀ i₁ i₂ : Bool) : List (Fin 8) :=
  (if i₀ then [] else [0]) ++ (if i₁ then [] else [1]) ++ (if i₂ then [] else [2]) ++
    [3, 4, 5, 6, 7]

/-- The gadget vertices other than the exits of `Out`, in order. -/
def keptRows (Out : Finset (Fin 3)) : List (Fin 8) :=
  rowsB (decide (0 ∈ Out)) (decide (1 ∈ Out)) (decide (2 ∈ Out))

/-- The gadget vertices other than the entries of `In`, in order. -/
def keptCols (In : Finset (Fin 3)) : List (Fin 8) :=
  colsB (decide (0 ∈ In)) (decide (1 ∈ In)) (decide (2 ∈ In))

theorem mem_rowsB (o₀ o₁ o₂ : Bool) (a : Fin 8) : a ∈ rowsB o₀ o₁ o₂ ↔
    ¬((a = 3 ∧ o₀ = true) ∨ (a = 4 ∧ o₁ = true) ∨ (a = 5 ∧ o₂ = true)) := by
  revert o₀ o₁ o₂ a
  decide

theorem mem_colsB (i₀ i₁ i₂ : Bool) (a : Fin 8) : a ∈ colsB i₀ i₁ i₂ ↔
    ¬((a = 0 ∧ i₀ = true) ∨ (a = 1 ∧ i₁ = true) ∨ (a = 2 ∧ i₂ = true)) := by
  revert i₀ i₁ i₂ a
  decide

theorem mem_keptRows (Out : Finset (Fin 3)) (a : Fin 8) :
    a ∈ keptRows Out ↔ a ∉ Out.map exitE := by
  rw [keptRows, mem_rowsB, not_iff_not]
  simp only [decide_eq_true_eq, mem_map]
  constructor
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩) <;> exact ⟨_, h, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    fin_cases p
    exacts [Or.inl ⟨rfl, hp⟩, Or.inr (Or.inl ⟨rfl, hp⟩), Or.inr (Or.inr ⟨rfl, hp⟩)]

theorem mem_keptCols (In : Finset (Fin 3)) (a : Fin 8) :
    a ∈ keptCols In ↔ a ∉ In.map entryE := by
  rw [keptCols, mem_colsB, not_iff_not]
  simp only [decide_eq_true_eq, mem_map]
  constructor
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩) <;> exact ⟨_, h, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    fin_cases p
    exacts [Or.inl ⟨rfl, hp⟩, Or.inr (Or.inl ⟨rfl, hp⟩), Or.inr (Or.inr ⟨rfl, hp⟩)]

theorem keptRows_nodup (Out : Finset (Fin 3)) : (keptRows Out).Nodup := by
  unfold keptRows
  generalize decide (0 ∈ Out) = a, decide (1 ∈ Out) = b, decide (2 ∈ Out) = c
  revert a b c
  decide

theorem keptCols_nodup (In : Finset (Fin 3)) : (keptCols In).Nodup := by
  unfold keptCols
  generalize decide (0 ∈ In) = a, decide (1 ∈ In) = b, decide (2 ∈ In) = c
  revert a b c
  decide

/-- Laplace expansion skipping zero entries; equal to `permOnList` (`permOnListZ_eq`). -/
def permOnListZ (M : Fin 8 → Fin 8 → ℤ) : List (Fin 8) → List (Fin 8) → ℤ
  | [], [] => 1
  | [], _ :: _ => 0
  | i :: is, cols =>
    (cols.map fun j => if M i j = 0 then 0 else M i j * permOnListZ M is (cols.erase j)).sum

theorem permOnListZ_eq (M : Fin 8 → Fin 8 → ℤ) (l c : List (Fin 8)) :
    permOnListZ M l c = permOnList M l c := by
  induction l generalizing c with
  | nil => cases c <;> rfl
  | cons i is ih =>
    simp only [permOnListZ, permOnList]
    congr 1
    refine List.map_congr_left fun j _ => ?_
    split_ifs with h
    · rw [h, zero_mul]
    · rw [ih]

/-- The gadget minors for all flag combinations, checked by evaluation. -/
theorem gadget_minorB : ∀ o₀ o₁ o₂ i₀ i₁ i₂ : Bool,
    permOnListZ gadget (rowsB o₀ o₁ o₂) (colsB i₀ i₁ i₂) =
      if (o₀ = i₀ ∧ o₁ = i₁ ∧ o₂ = i₂) ∧ (o₀ = true ∨ o₁ = true ∨ o₂ = true) then 12 else 0 := by
  decide +kernel

/-- **The minors of the clause gadget**: without the exit rows `Out` and the entry columns `In`,
the permanent is `12` if `Out = In` is nonempty, and `0` otherwise. -/
theorem gadget_minor (Out In : Finset (Fin 3)) :
    permOnList gadget (keptRows Out) (keptCols In) =
      if Out = In ∧ Out.Nonempty then 12 else 0 := by
  rw [show permOnList gadget (keptRows Out) (keptCols In) =
      permOnListZ gadget (keptRows Out) (keptCols In) from (permOnListZ_eq _ _ _).symm,
    keptRows, keptCols, gadget_minorB]
  have hOI : Out = In ↔ (decide (0 ∈ Out) = decide (0 ∈ In) ∧
      decide (1 ∈ Out) = decide (1 ∈ In) ∧ decide (2 ∈ Out) = decide (2 ∈ In)) := by
    simp only [decide_eq_decide]
    refine ⟨fun h => h ▸ ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩, fun ⟨h0, h1, h2⟩ => ?_⟩
    ext p
    fin_cases p <;> assumption
  have hne : Out.Nonempty ↔ (decide (0 ∈ Out) = true ∨ decide (1 ∈ Out) = true ∨
      decide (2 ∈ Out) = true) := by
    simp only [decide_eq_true_eq]
    refine ⟨fun ⟨p, hp⟩ => by fin_cases p <;> simp_all, ?_⟩
    rintro (h | h | h) <;> exact ⟨_, h⟩
  simp only [hOI, hne]

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The minors of a placed gadget. -/
private theorem permOn_placed_gadget (g : Fin 8 ↪ V) (A : Matrix V V ℤ)
    (hA : ∀ a b, A (g a) (g b) = gadget a b) (Out In : Finset (Fin 3)) :
    permOn A (univ.map g \ (Out.map exitE).map g) (univ.map g \ (In.map entryE).map g) =
      if Out = In ∧ Out.Nonempty then 12 else 0 := by
  rw [permOn_map_sdiff_eq_permOnList g A (keptRows_nodup Out) (keptCols_nodup In)
    (mem_keptRows Out) (mem_keptCols In)]
  simp only [hA]
  exact gadget_minor Out In

/-- **Elimination of a placed clause gadget.** Let `A` be the clause gadget placed on the vertices
`g`, and `D` a matrix whose rows at non-exit gadget vertices and columns at non-entry gadget
vertices vanish. If the row and column sets contain the gadget, the permanent sum of `A + D` is
`12` times the sum over nonempty literal sets `Q` of the permanent sum of `D` in which the gadget
is replaced by the exits of `Q` (rows) and the entries of `Q` (columns). This is
`Matrix.permOn_add_of_gadget` with the minors of `gadget_minor`. -/
theorem permOn_gadget_add (g : Fin 8 ↪ V) (A D : Matrix V V ℤ)
    (hA : ∀ a b, A (g a) (g b) = gadget a b)
    (hArow : ∀ u, (∀ a, u ≠ g a) → ∀ v, A u v = 0)
    (hAcol : ∀ v, (∀ b, v ≠ g b) → ∀ u, A u v = 0)
    (hDrow : ∀ a, (∀ p, a ≠ exitE p) → ∀ v, D (g a) v = 0)
    (hDcol : ∀ b, (∀ p, b ≠ entryE p) → ∀ u, D u (g b) = 0)
    {S T : Finset V} (hS : univ.map g ⊆ S) (hT : univ.map g ⊆ T) :
    permOn (A + D) S T = 12 * ∑ Q ∈ univ.filter fun Q : Finset (Fin 3) => Q.Nonempty,
      permOn D (S \ univ.map g ∪ (Q.map exitE).map g)
        (T \ univ.map g ∪ (Q.map entryE).map g) := by
  rw [permOn_add_of_gadget g entryE exitE A D hArow hAcol hDrow hDcol hS hT, mul_sum,
    sum_filter]
  refine sum_congr rfl fun Out _ => ?_
  simp only [permOn_placed_gadget g A hA, ite_mul, zero_mul]
  by_cases hO : Out.Nonempty
  · simp only [hO, and_true]
    rw [sum_ite_eq univ Out]
    simp
  · simp [hO]

end Cslib.Complexity.PermanentGadget
