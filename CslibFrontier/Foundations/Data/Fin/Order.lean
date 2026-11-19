/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Order/Fin/Basic.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Equal neighbors and index-sum bounds in finite arrays

A repeated value in a monotone finite array has an equal predecessor or successor.
The value type needs only a partial order. Also bounds the sum of all indices in `Fin n` by
`n * n`.

## Main results

* `Fin.exists_ne_apply_eq_iff_adjacent`: an adjacent witness suffices for any repeated value.
* `Fin.exists_adjacent_ne_of_monotone_comp`: two distinct entries with equal keys in a monotone-key
  array force an adjacent pair of distinct entries with that key.
* `Fin.exists_le_lt_adjacent`: a threshold between the first and last entries is crossed
  by an actual adjacent pair, without a monotonicity premise.
* `Fin.sum_val_le_mul_self`: `(∑ j : Fin n, j.val) ≤ n * n`.

## References

* Adapted from MassProduction/Nonuniform/AdjacentDuplicates.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
* Adapted from lean/Proofs/{Collisions,Selection}.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
* [OpenAI2026RationalHitting]
-/

public section

/-- In a monotone finite array, every repeated value has an equal neighbor. -/
theorem Fin.exists_ne_apply_eq_iff_adjacent {α : Type*} [PartialOrder α] {count : ℕ}
    (f : Fin count → α) (ordered : Monotone f) (i : Fin count) :
    (∃ j, j ≠ i ∧ f j = f i) ↔
      ((∃ positive : 0 < i.val, f ⟨i.val - 1, by lia⟩ = f i) ∨
        (∃ fits : i.val + 1 < count, f ⟨i.val + 1, fits⟩ = f i)) := by
  constructor
  · rintro ⟨j, different, same⟩
    rcases lt_or_gt_of_ne different with before | after
    · refine Or.inl ⟨by lia, ?_⟩
      exact (ordered.eq_of_ge_of_le same (by change j.val ≤ i.val - 1; lia)
        (by change i.val - 1 ≤ i.val; lia)).trans same
    · have fits : i.val + 1 < count := (Nat.succ_le_of_lt after).trans_lt j.isLt
      exact Or.inr ⟨fits, ordered.eq_of_ge_of_le same.symm
        (by change i.val ≤ i.val + 1; lia) (by exact Nat.succ_le_of_lt after)⟩
  · rintro (⟨positive, same⟩ | ⟨fits, same⟩)
    · refine ⟨⟨i.val - 1, by lia⟩, ?_, same⟩
      intro equal
      have := congrArg Fin.val equal
      dsimp only at this
      lia
    · refine ⟨⟨i.val + 1, fits⟩, ?_, same⟩
      intro equal
      have := congrArg Fin.val equal
      dsimp only at this
      lia

/-- In a finite array with monotone keys, two different records with equal keys force an adjacent
pair of different records with that key. -/
theorem Fin.exists_adjacent_ne_of_monotone_comp {α β : Type*} [PartialOrder β] {R : ℕ}
    (records : Fin R → α) (key : α → β)
    (hs : Monotone (key ∘ records)) (i j : Fin R) (hij : i < j)
    (hne : records i ≠ records j) (heq : key (records i) = key (records j)) :
    ∃ (p : ℕ) (hp : p + 1 < R),
      records ⟨p, by omega⟩ ≠ records ⟨p + 1, hp⟩ ∧
      key (records ⟨p, by omega⟩) = key (records ⟨p + 1, hp⟩) ∧
      key (records ⟨p, by omega⟩) = key (records i) := by
  classical
  have hex : ∃ q, ∃ hq : q < R, i.val < q ∧ q ≤ j.val ∧ records ⟨q, hq⟩ ≠ records i :=
    ⟨j.val, j.isLt, hij, le_rfl, hne.symm⟩
  obtain ⟨hq, hiq, hqj, hdiff⟩ := Nat.find_spec hex
  generalize hqdef : Nat.find hex = q at hq hiq hqj hdiff
  have hmin : ∀ q' < q, ¬∃ hq : q' < R, i.val < q' ∧ q' ≤ j.val ∧ records ⟨q', hq⟩ ≠ records i :=
    fun q' hq' => Nat.find_min hex (by omega)
  have hsame : records ⟨q - 1, by omega⟩ = records i := by
    by_contra h
    have hlt : i.val < q - 1 := by
      have hne : i.val ≠ q - 1 := fun he => h (congrArg records (Fin.ext he.symm))
      omega
    exact hmin (q - 1) (by omega) ⟨by omega, hlt, by omega, h⟩
  have hqkey : key (records ⟨q, hq⟩) = key (records i) :=
    le_antisymm ((hs (show (⟨q, hq⟩ : Fin R) ≤ j from hqj)).trans_eq heq.symm)
      (hs (show i ≤ (⟨q, hq⟩ : Fin R) from hiq.le))
  have hqp : q - 1 + 1 = q := by omega
  refine ⟨q - 1, by omega, ?_, ?_, congrArg key hsame⟩
  · simpa only [hqp, hsame] using hdiff.symm
  · simpa only [hqp, hsame] using hqkey.symm

/-- The sum of all values in `Fin n` is at most `n * n`. -/
theorem Fin.sum_val_le_mul_self (n : ℕ) : (∑ j : Fin n, j.val) ≤ n * n := by
  calc
    _ ≤ ∑ _j : Fin n, n := Finset.sum_le_sum fun j _ => Nat.le_of_lt j.isLt
    _ = n * n := by simp

/-- A threshold at least the first value and strictly below the last is crossed by an
actual adjacent pair. The finite sequence need not be monotone. -/
theorem Fin.exists_le_lt_adjacent {α : Type*} [LinearOrder α] {n : ℕ}
    {f : Fin (n + 1) → α} {x : α} (hfirst : f 0 ≤ x) (hlast : x < f (Fin.last n)) :
    ∃ i : Fin n, f i.castSucc ≤ x ∧ x < f i.succ := by
  classical
  by_contra hn
  let R : α → α → Prop := fun a b => a ≤ x → b ≤ x
  let : IsTrans α R := ⟨fun _ _ _ hab hbc => hbc ∘ hab⟩
  have hadj : ∀ i : Fin n, R (f i.castSucc) (f i.succ) := by
    intro i hi
    exact le_of_not_gt (fun hh => hn ⟨i, hi, hh⟩)
  have hall := (Fin.liftFun_iff_succ R).mpr hadj
  by_cases hn0 : n = 0
  · subst n
    have he : (Fin.last 0 : Fin 1) = 0 := rfl
    exact (not_le_of_gt hlast) (he.symm ▸ hfirst)
  · have hz : (0 : Fin (n + 1)) < Fin.last n := by
      change 0 < n
      exact Nat.pos_of_ne_zero hn0
    exact (not_le_of_gt hlast) (hall hz hfirst)
