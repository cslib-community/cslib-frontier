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
  refine ⟨fun ⟨j, different, same⟩ => ?_, ?_⟩
  · rcases lt_or_gt_of_ne different with before | after
    · exact Or.inl ⟨by lia, (ordered.eq_of_ge_of_le same
        (by change j.val ≤ i.val - 1; lia)
        (by change i.val - 1 ≤ i.val; lia)).trans same⟩
    · exact Or.inr ⟨(Nat.succ_le_of_lt after).trans_lt j.isLt, ordered.eq_of_ge_of_le same.symm
        (by change i.val ≤ i.val + 1; lia) (Nat.succ_le_of_lt after)⟩
  · rintro (⟨positive, same⟩ | ⟨fits, same⟩)
    · refine ⟨⟨i.val - 1, by lia⟩, fun h => ?_, same⟩
      have := congrArg Fin.val h; dsimp at this
      lia
    · refine ⟨⟨i.val + 1, fits⟩, fun h => ?_, same⟩
      have := congrArg Fin.val h; dsimp at this
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
  have hsame : records ⟨q - 1, by omega⟩ = records i := by
    by_contra h
    have hne' : i.val ≠ q - 1 := fun he => h (congrArg records (Fin.ext he.symm))
    exact Nat.find_min hex (m := q - 1) (by omega) ⟨by omega, by omega, by omega, h⟩
  have hqkey : key (records ⟨q, hq⟩) = key (records i) :=
    le_antisymm ((hs (show (⟨q, hq⟩ : Fin R) ≤ j from hqj)).trans_eq heq.symm)
      (hs (show i ≤ (⟨q, hq⟩ : Fin R) from hiq.le))
  have hqp : q - 1 + 1 = q := by omega
  exact ⟨q - 1, by omega, by simpa only [hqp, hsame] using hdiff.symm,
    by simpa only [hqp, hsame] using hqkey.symm, congrArg key hsame⟩

/-- The sum of all values in `Fin n` is at most `n * n`. -/
theorem Fin.sum_val_le_mul_self (n : ℕ) : (∑ j : Fin n, j.val) ≤ n * n :=
  (Finset.sum_le_sum fun j _ => j.isLt.le).trans_eq <| by
    rw [Finset.sum_const_nat fun _ _ => rfl, Finset.card_univ, Fintype.card_fin]

/-- A threshold at least the first value and strictly below the last is crossed by an
actual adjacent pair. The finite sequence need not be monotone. -/
theorem Fin.exists_le_lt_adjacent {α : Type*} [LinearOrder α] {n : ℕ}
    {f : Fin (n + 1) → α} {x : α} (hfirst : f 0 ≤ x) (hlast : x < f (Fin.last n)) :
    ∃ i : Fin n, f i.castSucc ≤ x ∧ x < f i.succ := by
  classical
  by_contra hn
  let R : α → α → Prop := fun a b => a ≤ x → b ≤ x
  let : IsTrans α R := ⟨fun _ _ _ hab hbc => hbc ∘ hab⟩
  have hall := (Fin.liftFun_iff_succ R).mpr fun i hi => le_of_not_gt fun hh => hn ⟨i, hi, hh⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · exact (not_le_of_gt hlast) (show f (Fin.last 0) ≤ x from hfirst)
  · exact (not_le_of_gt hlast) (hall (show (0 : Fin (n + 1)) < Fin.last n from hn0) hfirst)
